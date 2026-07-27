# IMO 2026 with GPT-5.6 Sol in Lean

This repository contains independent Lean 4 solutions to all six IMO 2026 problems generated with **GPT-5.6 Sol**, together with the six formal statement files used as inputs.

The formal statements are exact copies of the `problem.lean` files released by [Axiom Math](https://github.com/AxiomMath/IMO2026). The GPT solution files were produced independently and do not contain or import Axiom's solutions.

[Read the mathematical proof notes and comparison with AxiomProver.](https://junaidhasan.com/blog/imo-2026-gpt-vs-axiom/index.html)

## The experiment

I gave GPT-5.6 Sol the six problem files (`.lean`). The model was not told that AxiomProver had already solved the problems. The instructions in [`gpt/AGENTS.md`](gpt/AGENTS.md) explicitly prohibited:

- web browsing or web search;
- GitHub, GitLab, or any other online repository;
- published solutions, benchmark submissions, proof databases, or cached answers;
- inspection of the other IMO problem files or prior attempts;
- remote theorem-search services or network-enabled agents.

The model could use the designated Lean file, the installed Lean/Mathlib environment, local declaration inspection, and compiler feedback. It was required to preserve every statement, replace every placeholder, compile the complete file, and pass proof-integrity and axiom checks.

The proofs were generated with **GPT-5.6 Sol in Ultracode mode**, which spawned subagents. The problems were attempted in the order P1, P4, P5, P6, P2, P3.

| Problem | GPT lines | Axiom lines | GPT Ultracode time | Axiom reported time |
| --- | ---: | ---: | ---: | ---: |
| P1 | 394 | 521 | 22 min | 24 min |
| P2 | 636 | 1,224 | 1 h 10 min | 360 min |
| P3* | 2,402 | 4,229 | 2 h 23 min | 869 min |
| P4 | 431 | 520 | 26 min | 39 min |
| P5 | 269 | 457 | 32 min | 65 min |
| P6 | 529 | 771 | 45 min | 139 min |
| **Total** | **4,661** | **7,722** | **about 3 h 25 min active session** | **1,496 min (24 h 56 min)** |

The GPT total is active wall-clock time for an Ultracode session with parallel subagents, not a sum of serial solver-hours. Axiom's numbers are the per-problem run times published in its README. The systems, hardware, orchestration, and stopping conditions differ, so this table is descriptive rather than a controlled speed benchmark.

\* P3 reports the compacted [`p3_solution_v2.lean`](gpt/p3_solution_v2.lean). The original 2,947-line successful artifact remains in [`p3_solution.lean`](gpt/p3_solution.lean); the verified cleanup removed 545 lines and added 25 minutes to the recorded GPT time.

## Main takeaway: `AGENTS.md`

The main reusable artifact is [`gpt/AGENTS.md`](gpt/AGENTS.md). It is a repository-level protocol for an end-to-end Lean autoformalization project:

- preserve the supplied theorem statements and work in a closed environment;
- separate mathematical proof design from Lean elaboration;
- use a tight whole-file compiler loop;
- coordinate local subagents without concurrent edits to the target file;
- run adversarial source, compilation, axiom, and kernel checks before declaring success.

The same protocol was used across all six problems and can serve as a starting point for other autoformalization projects.

## Repository layout

- `p1.lean` through `p6.lean`: challenge statements copied from Axiom Math. They intentionally retain their original `sorry` placeholders.
- `gpt/p1_solution.lean` through `gpt/p6_solution.lean`: complete independent GPT-5.6 Sol proofs.
- `gpt/p3_solution_v2.lean`: the shorter, independently revalidated P3 solution reported in the table above.
- `gpt/AGENTS.md`: the closed-environment autoformalization and audit protocol.
- `verify.py`: source, Lean, kernel, Comparator, and AXLE verification.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`: the pinned Lean project.
- `THIRD_PARTY_NOTICES.md` and `LICENSES/`: provenance and license information for the statement files.

## Setup

Install [elan](https://github.com/leanprover/elan), then initialize the pinned dependencies:

```sh
lake update
```

Compile one solution:

```sh
lake env lean gpt/p1_solution.lean
```

Compile all six:

```sh
for n in 1 2 3 4 5 6; do
  lake env lean "gpt/p${n}_solution.lean"
done
```

## Verification

By default, `verify.py` runs **three local checks and two independent external verifiers** on every selected solution:

1. **Source audit and Lean compilation.** It checks the SHA-256 hash of the trusted statement file, scans the candidate source for `sorry`, `admit`, new axioms or constants, unsafe declarations, `native_decide`, and kernel-skipping options, then compiles the complete solution to an `.olean` file.
2. **Axiom audit.** It imports the compiled module, runs `#print axioms` on the designated final theorems, and rejects dependencies outside `propext`, `Classical.choice`, and `Quot.sound`.
3. **`leanchecker` replay.** It replays the stored declarations from the compiled module. An optional `--fresh-leanchecker` mode performs a fresh replay.
4. **Comparator.** It creates a temporary `Challenge`/`Solution` project, supplies the theorem names and permitted axioms to [Comparator](https://github.com/leanprover/comparator), and runs it under a systemd network guard when available. The optional `--nanoda` flag also enables Comparator's independent nanoda kernel.
5. **AXLE `verify_proof`.** It sends the exact statement and solution text to [AXLE's `verify_proof`](https://axle.axiommath.ai/) endpoint. The check passes only when AXLE returns `okay=true` with no failed declarations, Lean errors, or tool errors. Set `AXLE_API_KEY` before running this check.

Run the complete default suite:

```sh
AXLE_API_KEY=... python3 verify.py
```

Run only the three local checks:

```sh
python3 verify.py --checks compile axioms leanchecker
```

Select particular problems with, for example:

```sh
python3 verify.py --problems 1 4 6 --checks compile axioms leanchecker
```

Use `python3 verify.py --help` for timeouts, parallelism, Comparator binary paths, AXLE settings, and cache controls.

## Provenance and licensing

- Original work in this repository is available under the root [MIT License](LICENSE).
- `p1.lean` through `p6.lean` are copied from Axiom Math's MIT-licensed repository and remain covered by Axiom Math's copyright and license notice.
