#!/usr/bin/env python3
"""Validate the Lean problem solutions with Lean, leanchecker, Comparator, and AXLE."""

from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import hashlib
import json
import os
import pathlib
import random
import re
import signal
import shlex
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from typing import Iterable, Sequence


ROOT = pathlib.Path(__file__).resolve().parent
AXLE_URL = "https://axle.axiommath.ai/api/v1/verify_proof"
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
ALL_CHECKS = ("compile", "axioms", "leanchecker", "comparator", "axle")

FORMAL_SHA256: dict[int, str] = {
    1: "98695afb49630475105d6a6abdfff173b8ef4ac16f66d5800c3c928ea40febc7",
    2: "3671b9089e8e3c9a5681dbc90553d420a32d3eb64ca81610d0e66db58ed8883e",
    3: "30e97d46ec4d8ea02a5a14a46743881b36f79aeecf93ced9dac230bf19ba5016",
    4: "fdcb9357fa1d806ba0032fad20a08b22e827eb9f1797e1a4800dfdeb67ccf52f",
    5: "7ee9e76cdd3bf1c3c10e2fe97624ffe3ff4706b756b59708c2581999a9a102b5",
    6: "be69ab42345adb64c5a9b27a0ab873b0ed974ca664d94b599198f15e970b33e2",
}

THEOREM_NAMES: dict[int, tuple[str, ...]] = {
    1: (
        "statement_a_termination",
        "statement_a_unique_large",
        "statement_b_invariance",
        "terminal_value_eq_Mval",
        "Mval_gt_one",
    ),
    2: ("main_theorem",),
    3: (
        "LiuBangXiangYu.pieceLengths_sum",
        "LiuBangXiangYu.pieceLengths_length",
        "LiuBangXiangYu.L_mem_Icc",
        "LiuBangXiangYu.V_eq",
        "LiuBangXiangYu.lower_bound",
        "LiuBangXiangYu.upper_bound",
    ),
    4: ("TriangleGame.main_theorem",),
    5: ("main_theorem",),
    6: ("main_theorem",),
}


@dataclasses.dataclass(frozen=True)
class Target:
    agent: str
    problem: int
    formal: pathlib.Path
    solution: pathlib.Path
    theorem_names: tuple[str, ...]

    @property
    def label(self) -> str:
        return f"{self.agent}/p{self.problem}"

    @property
    def module(self) -> str:
        return self.solution.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")

    @property
    def olean(self) -> pathlib.Path:
        return self.solution.with_suffix(".olean")


@dataclasses.dataclass(frozen=True)
class CheckResult:
    target: str
    check: str
    status: str
    detail: str
    output: str = ""


@dataclasses.dataclass(frozen=True)
class CommandResult:
    returncode: int | None
    output: str
    elapsed: float
    timed_out: bool = False


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Validate root problem statements against the GPT pN_solution.lean files. "
            "The default suite checks the six GPT solutions."
        )
    )
    parser.add_argument(
        "--problems",
        metavar="N",
        type=int,
        nargs="+",
        default=list(range(1, 7)),
        help="problem numbers to validate (default: 1 2 3 4 5 6)",
    )
    parser.add_argument(
        "--checks",
        choices=ALL_CHECKS,
        nargs="+",
        default=list(ALL_CHECKS),
        help="checks to run (default: all)",
    )
    parser.add_argument(
        "--skip-leanchecker",
        action="store_true",
        help="skip built-in leanchecker replay",
    )
    parser.add_argument(
        "--fresh-leanchecker",
        action="store_true",
        help="also attempt --fresh replay; a timeout is reported as a skip",
    )
    parser.add_argument(
        "--leanchecker-timeout",
        type=float,
        default=1800,
        help="per-module leanchecker timeout in seconds (default: 1800)",
    )
    parser.add_argument(
        "--compile-timeout",
        type=float,
        default=1800,
        help="per-file Lean compile/audit timeout in seconds (default: 1800)",
    )
    parser.add_argument(
        "--comparator-timeout",
        type=float,
        default=1800,
        help="per-problem Comparator timeout in seconds (default: 1800)",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=2,
        help="parallel jobs; leanchecker is capped at two (default: 2)",
    )
    parser.add_argument(
        "--axle-environment",
        default=os.environ.get("AXLE_ENVIRONMENT", "lean-4.31.0"),
        help="AXLE Lean environment (default: lean-4.31.0)",
    )
    parser.add_argument(
        "--axle-timeout",
        type=float,
        default=900,
        help="AXLE proof timeout in seconds, at most 900 (default: 900)",
    )
    parser.add_argument(
        "--no-cache",
        action="store_true",
        help="add a random anti-cache value to AXLE requests",
    )
    parser.add_argument("--comparator-bin", help="path to the Comparator binary")
    parser.add_argument("--landrun-bin", help="path to landrun")
    parser.add_argument("--lean4export-bin", help="path to lean4export")
    parser.add_argument("--nanoda-bin", help="path to nanoda_bin")
    parser.add_argument(
        "--nanoda",
        action="store_true",
        help="enable Comparator's optional independent nanoda kernel",
    )
    parser.add_argument(
        "--no-systemd",
        action="store_true",
        help="run Comparator without its documented systemd network guard",
    )
    parser.add_argument(
        "--keep-work",
        action="store_true",
        help="retain generated Comparator projects under .verify-work",
    )
    args = parser.parse_args(argv)

    invalid = sorted(set(args.problems) - set(range(1, 7)))
    if invalid:
        parser.error(f"problem numbers must be between 1 and 6: {invalid}")
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.leanchecker_timeout <= 0 or args.compile_timeout <= 0:
        parser.error("timeouts must be positive")
    if args.comparator_timeout <= 0 or args.axle_timeout <= 0:
        parser.error("timeouts must be positive")
    if args.axle_timeout > 900:
        parser.error("AXLE limits non-admin proof timeouts to 900 seconds")
    return args


def selected_targets(args: argparse.Namespace) -> tuple[list[Target], list[CheckResult]]:
    agent = "gpt"
    targets: list[Target] = []
    skipped: list[CheckResult] = []
    for problem in sorted(set(args.problems)):
        solution = ROOT / agent / f"p{problem}_solution.lean"
        formal = ROOT / f"p{problem}.lean"
        if not solution.is_file():
            skipped.append(
                CheckResult(
                    f"{agent}/p{problem}",
                    "selection",
                    "SKIP",
                    f"{solution.relative_to(ROOT)} is not present",
                )
            )
            continue
        if not formal.is_file():
            skipped.append(
                CheckResult(
                    f"{agent}/p{problem}",
                    "selection",
                    "FAIL",
                    f"trusted statement {formal.relative_to(ROOT)} is missing",
                )
            )
            continue
        digest = hashlib.sha256(formal.read_bytes()).hexdigest()
        if digest != FORMAL_SHA256[problem]:
            skipped.append(
                CheckResult(
                    f"{agent}/p{problem}",
                    "selection",
                    "FAIL",
                    f"trusted statement p{problem}.lean has SHA-256 {digest}, expected {FORMAL_SHA256[problem]}",
                )
            )
            continue
        targets.append(Target(agent, problem, formal, solution, THEOREM_NAMES[problem]))
    return targets, skipped


def sanitized_environment(base: dict[str, str] | None = None) -> dict[str, str]:
    """Remove credentials before invoking any local candidate-controlled code."""
    environment = dict(os.environ if base is None else base)
    secret_markers = ("API_KEY", "TOKEN", "SECRET", "PASSWORD", "CREDENTIAL")
    for name in list(environment):
        upper = name.upper()
        if any(marker in upper for marker in secret_markers) or upper in {
            "SSH_AUTH_SOCK",
            "GPG_AGENT_INFO",
        }:
            environment.pop(name, None)
    return environment


def stop_process_group(process: subprocess.Popen[str]) -> str:
    if process.poll() is None:
        try:
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGTERM)
            else:
                process.terminate()
        except ProcessLookupError:
            pass
    try:
        output, _ = process.communicate(timeout=5)
        return output or ""
    except subprocess.TimeoutExpired:
        try:
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGKILL)
            else:
                process.kill()
        except ProcessLookupError:
            pass
        output, _ = process.communicate()
        return output or ""


def run_command(
    command: Sequence[str],
    *,
    cwd: pathlib.Path = ROOT,
    timeout: float,
    env: dict[str, str] | None = None,
    input_text: str | None = None,
) -> CommandResult:
    started = time.monotonic()
    try:
        process = subprocess.Popen(
            list(command),
            cwd=cwd,
            env=sanitized_environment(env),
            stdin=subprocess.PIPE if input_text is not None else None,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            start_new_session=os.name == "posix",
        )
    except OSError as exc:
        return CommandResult(127, f"{type(exc).__name__}: {exc}\n", time.monotonic() - started)
    try:
        output, _ = process.communicate(input=input_text, timeout=timeout)
        return CommandResult(process.returncode, output or "", time.monotonic() - started)
    except subprocess.TimeoutExpired:
        output = stop_process_group(process)
        return CommandResult(None, output, time.monotonic() - started, timed_out=True)
    except KeyboardInterrupt:
        stop_process_group(process)
        raise


def strip_lean_comments_and_strings(source: str) -> str:
    """Preserve newlines while removing nested comments and string contents."""
    output: list[str] = []
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    while i < len(source):
        char = source[i]
        following = source[i + 1] if i + 1 < len(source) else ""
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                output.append("\n")
            else:
                output.append(" ")
            i += 1
            continue
        if block_depth:
            if char == "/" and following == "-":
                output.extend((" ", " "))
                block_depth += 1
                i += 2
            elif char == "-" and following == "/":
                output.extend((" ", " "))
                block_depth -= 1
                i += 2
            else:
                output.append("\n" if char == "\n" else " ")
                i += 1
            continue
        if in_string:
            if char == "\\" and following:
                output.extend((" ", "\n" if following == "\n" else " "))
                i += 2
            elif char == '"':
                output.append(" ")
                in_string = False
                i += 1
            else:
                output.append("\n" if char == "\n" else " ")
                i += 1
            continue
        if char == "-" and following == "-":
            output.extend((" ", " "))
            in_line_comment = True
            i += 2
        elif char == "/" and following == "-":
            output.extend((" ", " "))
            block_depth = 1
            i += 2
        elif char == '"':
            output.append(" ")
            in_string = True
            i += 1
        else:
            output.append(char)
            i += 1
    return "".join(output)


FORBIDDEN_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("sorry", re.compile(r"\bsorry\b")),
    ("sorryAx", re.compile(r"\bsorryAx\b")),
    ("admit", re.compile(r"\badmit\b")),
    (
        "axiom declaration",
        re.compile(r"(?m)^\s*(?:(?:private|protected|local)\s+)*axiom\b"),
    ),
    (
        "constant declaration",
        re.compile(r"(?m)^\s*(?:(?:private|protected|local)\s+)*constant\b"),
    ),
    (
        "unsafe declaration",
        re.compile(r"(?m)^\s*(?:(?:private|protected|local)\s+)*unsafe\b"),
    ),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("debug.skipKernelTC", re.compile(r"\bdebug\.skipKernelTC\b")),
)


def forbidden_findings(path: pathlib.Path) -> list[str]:
    cleaned = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
    findings: list[str] = []
    for description, pattern in FORBIDDEN_PATTERNS:
        for match in pattern.finditer(cleaned):
            line = cleaned.count("\n", 0, match.start()) + 1
            findings.append(f"{description} at line {line}")
    return findings


def build_target(target: Target, timeout: float) -> tuple[bool, CommandResult, list[str]]:
    findings = forbidden_findings(target.solution)
    command = [
        "lake",
        "env",
        "lean",
        "-o",
        str(target.olean.relative_to(ROOT)),
        str(target.solution.relative_to(ROOT)),
    ]
    command_result = run_command(command, timeout=timeout)
    passed = command_result.returncode == 0 and not findings
    return passed, command_result, findings


def compile_checks(
    targets: Sequence[Target], args: argparse.Namespace
) -> tuple[list[CheckResult], dict[Target, bool]]:
    results: list[CheckResult] = []
    built: dict[Target, bool] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        future_map = {
            executor.submit(build_target, target, args.compile_timeout): target for target in targets
        }
        completed: dict[Target, tuple[bool, CommandResult, list[str]]] = {}
        for future in concurrent.futures.as_completed(future_map):
            target = future_map[future]
            try:
                completed[target] = future.result()
            except Exception as exc:
                completed[target] = (
                    False,
                    CommandResult(1, f"{type(exc).__name__}: {exc}\n", 0),
                    [],
                )
    for target in targets:
        passed, command_result, findings = completed[target]
        built[target] = command_result.returncode == 0
        if command_result.timed_out:
            detail = f"Lean compilation timed out after {command_result.elapsed:.1f}s"
        elif command_result.returncode != 0:
            detail = f"Lean compilation exited {command_result.returncode} in {command_result.elapsed:.1f}s"
        elif findings:
            detail = "forbidden/incomplete source: " + ", ".join(findings)
        else:
            detail = f"compiled cleanly in {command_result.elapsed:.1f}s"
        results.append(
            CheckResult(
                target.label,
                "compile",
                "PASS" if passed else "FAIL",
                detail,
                command_result.output if not passed else "",
            )
        )
    return results, built


def ensure_built(
    target: Target, built: dict[Target, bool], args: argparse.Namespace
) -> CheckResult | None:
    if built.get(target, False) and target.olean.is_file():
        return None
    passed, command_result, findings = build_target(target, args.compile_timeout)
    built[target] = command_result.returncode == 0
    if not passed:
        detail = "could not build the module required by this check"
        if findings:
            detail += ": " + ", ".join(findings)
        return CheckResult(target.label, "build", "FAIL", detail, command_result.output)
    return None


def lake_tool_command(tool: str, *arguments: str) -> list[str]:
    command = f'LEAN_PATH="$VERIFY_ROOT:$LEAN_PATH" exec {shlex.quote(tool)}'
    command += ' "$@"'
    return ["lake", "env", "sh", "-c", command, tool, *arguments]


def axiom_check(target: Target, args: argparse.Namespace) -> CheckResult:
    audit = f"import {target.module}\n" + "".join(
        f"#print axioms {name}\n" for name in target.theorem_names
    )
    environment = os.environ.copy()
    environment["VERIFY_ROOT"] = str(ROOT)
    command_result = run_command(
        lake_tool_command("lean", "--stdin"),
        timeout=args.compile_timeout,
        env=environment,
        input_text=audit,
    )
    if command_result.timed_out:
        return CheckResult(
            target.label,
            "axioms",
            "FAIL",
            f"axiom audit timed out after {command_result.elapsed:.1f}s",
            command_result.output,
        )
    if command_result.returncode != 0:
        return CheckResult(
            target.label,
            "axioms",
            "FAIL",
            f"axiom audit exited {command_result.returncode}",
            command_result.output,
        )

    reports: dict[str, tuple[str, ...]] = {}
    malformed: list[str] = []
    for line in command_result.output.splitlines():
        depends = re.fullmatch(r"'([^']+)' depends on axioms: \[([^]]*)\]", line)
        independent = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
        if depends:
            name = depends.group(1)
            axioms = tuple(part.strip() for part in depends.group(2).split(",") if part.strip())
        elif independent:
            name = independent.group(1)
            axioms = ()
        elif "depends on axioms" in line:
            malformed.append(line)
            continue
        else:
            continue
        if name in reports:
            malformed.append(f"duplicate report for {name}")
        reports[name] = axioms

    expected = set(target.theorem_names)
    reported = set(reports)
    if malformed or reported != expected:
        problems = list(malformed)
        if expected - reported:
            problems.append("missing: " + ", ".join(sorted(expected - reported)))
        if reported - expected:
            problems.append("unexpected: " + ", ".join(sorted(reported - expected)))
        return CheckResult(
            target.label,
            "axioms",
            "FAIL",
            "invalid axiom report: " + "; ".join(problems),
            command_result.output,
        )
    unexpected = {
        axiom
        for axioms in reports.values()
        for axiom in axioms
        if axiom not in STANDARD_AXIOMS
    }
    if unexpected:
        return CheckResult(
            target.label,
            "axioms",
            "FAIL",
            "unexpected axioms: " + ", ".join(sorted(unexpected)),
            command_result.output,
        )
    exact_sets = "; ".join(
        f"{name}=[{', '.join(reports[name])}]" for name in target.theorem_names
    )
    return CheckResult(
        target.label,
        "axioms",
        "PASS",
        exact_sets,
    )


def leanchecker_check(
    target: Target, args: argparse.Namespace, *, fresh: bool = False
) -> CheckResult:
    environment = os.environ.copy()
    environment["VERIFY_ROOT"] = str(ROOT)
    arguments = ["--fresh", target.module] if fresh else [target.module]
    command_result = run_command(
        lake_tool_command("leanchecker", *arguments),
        timeout=args.leanchecker_timeout,
        env=environment,
    )
    check_name = "leanchecker --fresh" if fresh else "leanchecker"
    if command_result.timed_out:
        return CheckResult(
            target.label,
            check_name,
            "SKIP",
            f"timed out at the {args.leanchecker_timeout:g}s limit",
            command_result.output,
        )
    if command_result.returncode != 0:
        return CheckResult(
            target.label,
            check_name,
            "FAIL",
            f"exited {command_result.returncode} in {command_result.elapsed:.1f}s",
            command_result.output,
        )
    return CheckResult(
        target.label,
        check_name,
        "PASS",
        f"stored declarations replayed in {command_result.elapsed:.1f}s",
    )


def resolve_binary(
    explicit: str | None, environment_name: str, executable_name: str
) -> pathlib.Path | None:
    candidate = explicit or os.environ.get(environment_name) or shutil.which(executable_name)
    if not candidate:
        return None
    path = pathlib.Path(candidate).expanduser()
    if not path.is_absolute():
        resolved = shutil.which(str(path))
        if not resolved:
            return None
        path = pathlib.Path(resolved)
    try:
        path = path.resolve(strict=True)
    except OSError:
        return None
    return path if path.is_file() and os.access(path, os.X_OK) else None


def comparator_prerequisites(args: argparse.Namespace) -> tuple[dict[str, pathlib.Path], list[str]]:
    tools: dict[str, pathlib.Path] = {}
    missing: list[str] = []
    specifications = (
        ("comparator", args.comparator_bin, "COMPARATOR_BIN", "comparator"),
        ("landrun", args.landrun_bin, "COMPARATOR_LANDRUN", "landrun"),
        ("lean4export", args.lean4export_bin, "COMPARATOR_LEAN4EXPORT", "lean4export"),
    )
    for label, explicit, environment_name, executable in specifications:
        path = resolve_binary(explicit, environment_name, executable)
        if path is None:
            missing.append(f"{label} ({environment_name} or PATH)")
        else:
            tools[label] = path
    if args.nanoda:
        nanoda = resolve_binary(args.nanoda_bin, "COMPARATOR_NANODA", "nanoda_bin")
        if nanoda is None:
            missing.append("nanoda_bin (COMPARATOR_NANODA or PATH)")
        else:
            tools["nanoda"] = nanoda
    if not args.no_systemd and shutil.which("systemd-run") is None:
        missing.append("systemd-run")
    if not (ROOT / ".lake" / "packages" / "mathlib").is_dir():
        missing.append("root .lake/packages/mathlib")
    return tools, missing


def make_comparator_project(target: Target, work: pathlib.Path, args: argparse.Namespace) -> None:
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    lake_dir = work / ".lake"
    lake_dir.mkdir()
    (lake_dir / "packages").symlink_to(ROOT / ".lake" / "packages", target_is_directory=True)

    (work / "Challenge.lean").write_text(target.formal.read_text(encoding="utf-8"), encoding="utf-8")
    (work / "Solution.lean").write_text(target.solution.read_text(encoding="utf-8"), encoding="utf-8")
    (work / "lean-toolchain").write_text(
        (ROOT / "lean-toolchain").read_text(encoding="utf-8"), encoding="utf-8"
    )
    lakefile = f'''name = "verify_{target.agent}_p{target.problem}"
version = "0.1.0"

[[require]]
name = "mathlib"
path = ".lake/packages/mathlib"

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"
'''
    (work / "lakefile.toml").write_text(lakefile, encoding="utf-8")

    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = []
    for package in root_manifest.get("packages", []):
        if package.get("name") == "mathlib":
            packages.append(
                {
                    "type": "path",
                    "scope": "",
                    "name": "mathlib",
                    "manifestFile": "lake-manifest.json",
                    "inherited": False,
                    "dir": ".lake/packages/mathlib",
                    "configFile": "lakefile.lean",
                }
            )
        else:
            packages.append(package)
    root_manifest["packages"] = packages
    (work / "lake-manifest.json").write_text(
        json.dumps(root_manifest, indent=2) + "\n", encoding="utf-8"
    )

    configuration = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": list(target.theorem_names),
        "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "enable_nanoda": args.nanoda,
    }
    (work / "config.json").write_text(
        json.dumps(configuration, indent=2) + "\n", encoding="utf-8"
    )


def comparator_check(
    target: Target,
    args: argparse.Namespace,
    tools: dict[str, pathlib.Path],
    session_work: pathlib.Path,
) -> CheckResult:
    work = session_work / f"{target.agent}-p{target.problem}"
    make_comparator_project(target, work, args)
    environment = os.environ.copy()
    environment["COMPARATOR_LANDRUN"] = str(tools["landrun"])
    environment["COMPARATOR_LEAN4EXPORT"] = str(tools["lean4export"])
    if "nanoda" in tools:
        environment["COMPARATOR_NANODA"] = str(tools["nanoda"])

    if args.no_systemd:
        command = ["lake", "env", str(tools["comparator"]), "config.json"]
        unit = None
    else:
        unit = f"lean-verify-{target.agent}-p{target.problem}-{os.getpid()}"
        comparator_command = (
            f"exec lake env {shlex.quote(str(tools['comparator']))} config.json"
        )
        command = [
            "systemd-run",
            "--property=RestrictAddressFamilies=~AF_UNIX",
            "--user",
            "--pipe",
            "--wait",
            f"--unit={unit}",
            f"--working-directory={work}",
            "-E",
            f"PATH={environment.get('PATH', '')}",
            "-E",
            f"COMPARATOR_LANDRUN={tools['landrun']}",
            "-E",
            f"COMPARATOR_LEAN4EXPORT={tools['lean4export']}",
        ]
        if "nanoda" in tools:
            command.extend(("-E", f"COMPARATOR_NANODA={tools['nanoda']}"))
        command.extend(("--", "bash", "-c", comparator_command))

    command_result = run_command(
        command,
        cwd=work,
        timeout=args.comparator_timeout,
        env=environment,
    )
    if command_result.timed_out and unit:
        run_command(
            ["systemctl", "--user", "stop", unit],
            timeout=30,
            env=environment,
        )
    if command_result.timed_out:
        return CheckResult(
            target.label,
            "comparator",
            "FAIL",
            f"timed out after {command_result.elapsed:.1f}s",
            command_result.output,
        )
    passed = command_result.returncode == 0 and "Your solution is okay!" in command_result.output
    guard = "without systemd guard" if args.no_systemd else "with systemd network guard"
    return CheckResult(
        target.label,
        "comparator",
        "PASS" if passed else "FAIL",
        (
            f"statement, axioms, and kernel accepted {guard} in {command_result.elapsed:.1f}s"
            if passed
            else f"exited {command_result.returncode}; acceptance marker not found"
        ),
        "" if passed else command_result.output,
    )


def redact_secret(text: str, secret: str) -> str:
    redacted = text.replace(secret, "<redacted>") if secret else text
    return re.sub(r"(?i)Bearer\s+[^\s\"']+", "Bearer <redacted>", redacted)


def axle_error_field(
    result: dict[str, object], primary: str, nested: str
) -> tuple[list[object] | None, str | None]:
    values: list[object] = []
    seen = False
    if primary in result:
        seen = True
        value = result[primary]
        if value is None:
            pass
        elif isinstance(value, list):
            values.extend(value)
        else:
            return None, f"{primary} is neither null nor a list"
    if nested in result:
        seen = True
        container = result[nested]
        if not isinstance(container, dict):
            return None, f"{nested} is not an object"
        if "errors" not in container:
            return None, f"{nested}.errors is not present"
        value = container.get("errors")
        if value is None:
            pass
        elif isinstance(value, list):
            values.extend(value)
        else:
            return None, f"{nested}.errors is neither null nor a list"
    if not seen:
        return None, f"neither {primary} nor {nested}.errors is present"
    return values, None


def axle_check(target: Target, args: argparse.Namespace, api_key: str) -> CheckResult:
    payload: dict[str, object] = {
        "formal_statement": target.formal.read_text(encoding="utf-8"),
        "content": target.solution.read_text(encoding="utf-8"),
        "mathlib_options": False,
        "use_def_eq": True,
        "verify_negation": False,
        "ignore_imports": False,
        "environment": args.axle_environment,
        "timeout_seconds": args.axle_timeout,
    }
    if args.no_cache:
        payload["anti_cache"] = random.SystemRandom().getrandbits(64)
    request = urllib.request.Request(
        AXLE_URL,
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    started = time.monotonic()
    try:
        with urllib.request.urlopen(request, timeout=args.axle_timeout + 120) as response:
            result = json.load(response)
    except urllib.error.HTTPError as exc:
        body = redact_secret(exc.read().decode(errors="replace"), api_key)
        return CheckResult(
            target.label,
            "axle",
            "FAIL",
            f"HTTP {exc.code} after {time.monotonic() - started:.1f}s",
            body,
        )
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError, OSError) as exc:
        return CheckResult(
            target.label,
            "axle",
            "FAIL",
            redact_secret(f"{type(exc).__name__}: {exc}", api_key),
        )

    if not isinstance(result, dict):
        return CheckResult(
            target.label,
            "axle",
            "FAIL",
            f"malformed response: expected an object, got {type(result).__name__}",
        )
    failed_declarations = result.get("failed_declarations")
    schema_errors: list[str] = []
    if not isinstance(failed_declarations, list) or not all(
        isinstance(name, str) for name in failed_declarations
    ):
        schema_errors.append("failed_declarations is not a list of strings")
        failed_declarations = []
    lean_errors, lean_schema_error = axle_error_field(result, "lean_errors", "lean_messages")
    tool_errors, tool_schema_error = axle_error_field(result, "errors", "tool_messages")
    if lean_schema_error:
        schema_errors.append(lean_schema_error)
    if tool_schema_error:
        schema_errors.append(tool_schema_error)
    lean_errors = lean_errors or []
    tool_errors = tool_errors or []
    passed = (
        result.get("okay") is True
        and not schema_errors
        and not failed_declarations
        and not lean_errors
        and not tool_errors
    )
    elapsed = time.monotonic() - started
    if passed:
        detail = f"okay=true, no failed declarations or errors ({elapsed:.1f}s)"
        output = ""
    else:
        detail = redact_secret((
            f"okay={result.get('okay')}, failed declarations={failed_declarations}, "
            f"schema errors={schema_errors}"
        ), api_key)
        output = redact_secret(json.dumps(
            {
                "failed_declarations": failed_declarations,
                "lean_errors": lean_errors,
                "tool_errors": tool_errors,
                "schema_errors": schema_errors,
            },
            indent=2,
            default=str,
        ), api_key)
    return CheckResult(target.label, "axle", "PASS" if passed else "FAIL", detail, output)


def print_result(result: CheckResult) -> None:
    print(f"[{result.status}] {result.target} {result.check}: {result.detail}", flush=True)
    if result.output:
        output = result.output.rstrip()
        if len(output) > 12000:
            output = "... (truncated)\n" + output[-12000:]
        for line in output.splitlines():
            print(f"    {line}")


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    checks = list(dict.fromkeys(args.checks))
    if args.skip_leanchecker and "leanchecker" in checks:
        checks.remove("leanchecker")
    if not checks:
        print("No checks selected.")
        return 1
    targets, selection_results = selected_targets(args)
    results: list[CheckResult] = list(selection_results)
    for result in selection_results:
        print_result(result)
    if not targets:
        print("No solution files selected.")
        return 1

    # Capture and remove the credential before any local child process starts.
    # AXLE uses the in-process copy; run_command also scrubs credential-like variables.
    api_key = os.environ.pop("AXLE_API_KEY", "")
    session_work = ROOT / ".verify-work" / f"run-{os.getpid()}"
    built: dict[Target, bool] = {}
    interrupted = False
    try:
        # Remote statement checking and the guarded gold-standard check intentionally
        # precede every unsandboxed local elaboration of the candidate.
        if "axle" in checks:
            if not api_key:
                print("AXLE_API_KEY not set", flush=True)
                for target in targets:
                    result = CheckResult(target.label, "axle", "FAIL", "API key unavailable")
                    results.append(result)
                    print_result(result)
            else:
                with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
                    future_map = {
                        executor.submit(axle_check, target, args, api_key): target
                        for target in targets
                    }
                    axle_results: dict[Target, CheckResult] = {}
                    for future in concurrent.futures.as_completed(future_map):
                        target = future_map[future]
                        try:
                            axle_results[target] = future.result()
                        except Exception as exc:
                            axle_results[target] = CheckResult(
                                target.label,
                                "axle",
                                "FAIL",
                                redact_secret(f"{type(exc).__name__}: {exc}", api_key),
                            )
                for target in targets:
                    result = axle_results[target]
                    results.append(result)
                    print_result(result)
        api_key = ""

        if "comparator" in checks:
            tools, missing = comparator_prerequisites(args)
            if missing:
                print("Comparator prerequisites missing: " + ", ".join(missing), flush=True)
                for target in targets:
                    result = CheckResult(
                        target.label,
                        "comparator",
                        "FAIL",
                        "missing prerequisites: " + ", ".join(missing),
                    )
                    results.append(result)
                    print_result(result)
            else:
                if args.no_systemd:
                    print("WARNING: Comparator systemd network guard explicitly disabled", flush=True)
                for target in targets:
                    try:
                        result = comparator_check(target, args, tools, session_work)
                    except Exception as exc:
                        result = CheckResult(
                            target.label,
                            "comparator",
                            "FAIL",
                            f"{type(exc).__name__}: {exc}",
                        )
                    results.append(result)
                    print_result(result)

        if "compile" in checks:
            compile_results, built = compile_checks(targets, args)
            results.extend(compile_results)
            for result in compile_results:
                print_result(result)

        if "axioms" in checks or "leanchecker" in checks:
            for target in targets:
                try:
                    build_failure = ensure_built(target, built, args)
                except Exception as exc:
                    built[target] = False
                    build_failure = CheckResult(
                        target.label,
                        "build",
                        "FAIL",
                        f"{type(exc).__name__}: {exc}",
                    )
                if build_failure:
                    results.append(build_failure)
                    print_result(build_failure)

        if "axioms" in checks:
            for target in targets:
                if not built.get(target, False):
                    result = CheckResult(target.label, "axioms", "FAIL", "module did not build")
                else:
                    try:
                        result = axiom_check(target, args)
                    except Exception as exc:
                        result = CheckResult(
                            target.label,
                            "axioms",
                            "FAIL",
                            f"{type(exc).__name__}: {exc}",
                        )
                results.append(result)
                print_result(result)

        if "leanchecker" in checks:
            checker_targets = [target for target in targets if built.get(target, False)]

            def safe_checker(target: Target, fresh: bool = False) -> CheckResult:
                try:
                    return leanchecker_check(target, args, fresh=fresh)
                except Exception as exc:
                    return CheckResult(
                        target.label,
                        "leanchecker --fresh" if fresh else "leanchecker",
                        "FAIL",
                        f"{type(exc).__name__}: {exc}",
                    )

            with concurrent.futures.ThreadPoolExecutor(max_workers=min(args.jobs, 2)) as executor:
                future_map = {
                    executor.submit(safe_checker, target): target for target in checker_targets
                }
                checker_results = {future_map[future]: future.result() for future in future_map}
            for target in targets:
                result = checker_results.get(target)
                if result is None:
                    result = CheckResult(target.label, "leanchecker", "FAIL", "module did not build")
                results.append(result)
                print_result(result)

            if args.fresh_leanchecker:
                with concurrent.futures.ThreadPoolExecutor(max_workers=min(args.jobs, 2)) as executor:
                    future_map = {
                        executor.submit(safe_checker, target, True): target
                        for target in checker_targets
                    }
                    fresh_results = {future_map[future]: future.result() for future in future_map}
                for target in targets:
                    result = fresh_results.get(target)
                    if result is None:
                        result = CheckResult(
                            target.label, "leanchecker --fresh", "FAIL", "module did not build"
                        )
                    results.append(result)
                    print_result(result)
    except KeyboardInterrupt:
        interrupted = True
        result = CheckResult("repository", "validation", "FAIL", "interrupted")
        results.append(result)
        print_result(result)
    except Exception as exc:
        result = CheckResult(
            "repository", "validation", "FAIL", f"{type(exc).__name__}: {exc}"
        )
        results.append(result)
        print_result(result)
    finally:
        api_key = ""
        os.environ.pop("AXLE_API_KEY", None)
        if session_work.exists():
            if args.keep_work:
                print(f"Kept validation work at {session_work}")
            else:
                try:
                    shutil.rmtree(session_work)
                    try:
                        session_work.parent.rmdir()
                    except OSError:
                        pass
                except OSError as exc:
                    result = CheckResult(
                        "repository",
                        "cleanup",
                        "FAIL",
                        f"could not remove {session_work}: {exc}",
                    )
                    results.append(result)
                    print_result(result)

    passed_checks = {(result.target, result.check) for result in results if result.status == "PASS"}
    for skipped in list(results):
        if skipped.check != "leanchecker" or skipped.status != "SKIP":
            continue
        if (skipped.target, "comparator") not in passed_checks or (
            skipped.target,
            "axle",
        ) not in passed_checks:
            policy_failure = CheckResult(
                skipped.target,
                "leanchecker timeout policy",
                "FAIL",
                "ordinary replay may be skipped only when both Comparator and AXLE pass",
            )
            results.append(policy_failure)
            print_result(policy_failure)

    counts = {status: sum(result.status == status for result in results) for status in ("PASS", "FAIL", "SKIP")}
    print(
        f"Summary: {counts['PASS']} passed, {counts['FAIL']} failed, {counts['SKIP']} skipped",
        flush=True,
    )
    if interrupted:
        return 130
    return 1 if counts["FAIL"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
