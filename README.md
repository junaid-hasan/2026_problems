# IMO 2026 with GPT-5.6 Sol in Lean

This repository contains independent Lean 4 solutions to all six IMO 2026 problems generated with **GPT-5.6 Sol**, together with the six formal statement files used as inputs.

The formal statements are exact copies of the `problem.lean` files released by [Axiom Math](https://github.com/AxiomMath/IMO2026). The GPT solution files were produced independently and do not contain or import Axiom's solutions.

## The experiment

I gave GPT-5.6 Sol one designated problem file at a time. The model was not told that AxiomProver had already solved the problems. The instructions in [`gpt/AGENTS.md`](gpt/AGENTS.md) explicitly prohibited:

- web browsing or web search;
- GitHub, GitLab, or any other online repository;
- published solutions, benchmark submissions, proof databases, or cached answers;
- inspection of the other IMO problem files or prior attempts;
- remote theorem-search services or network-enabled agents.

The model could use the designated Lean file, the installed Lean/Mathlib environment, local declaration inspection, and compiler feedback. It was required to preserve every statement, remove every placeholder, compile the complete file, and undergo axiom and proof-integrity checks.

All six GPT proof files were completed in about **three hours of elapsed time**. This is not a controlled runtime comparison with AxiomProver: the systems, hardware, orchestration, and parallelism differ. Axiom's repository reports 24, 360, 869, 39, 65, and 139 minutes for its six runs, totaling 1,496 solver-minutes.

## Repository layout

- `p1.lean` through `p6.lean`: trusted challenge statements copied from Axiom Math. They intentionally retain their original `sorry` placeholders.
- `gpt/p1_solution.lean` through `gpt/p6_solution.lean`: complete independent GPT-5.6 Sol proofs.
- `gpt/AGENTS.md`: the closed-environment proof prompt and audit protocol.
- `verify.py`: compilation, axiom, stored-proof, Comparator, and AXLE checks.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`: the pinned Lean project.
- `THIRD_PARTY_NOTICES.md` and `LICENSES/`: provenance and license for the Axiom statement files.

The six GPT solutions contain 5,206 physical source lines:

| Problem | GPT lines |
| --- | ---: |
| P1 | 394 |
| P2 | 636 |
| P3 | 2,947 |
| P4 | 431 |
| P5 | 269 |
| P6 | 529 |

## Why this is not a fork or submodule

This repository is a separate experiment, not a continuation of Axiom's repository. A fork would blur that distinction. A submodule would pull in the entire upstream repository, including the Axiom solutions, and would make cloning and validation less convenient.

Instead, the six statement files are vendored directly under the MIT License, with their provenance and checksums recorded. No Axiom solution file is mirrored here. Readers who want AxiomProver's proofs should use the [AxiomMath/IMO2026 repository](https://github.com/AxiomMath/IMO2026).

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

See the available checks with:

```sh
python3 verify.py --help
```

A local-only verification run is:

```sh
python3 verify.py --checks compile axioms leanchecker
```

The full verifier also supports Comparator and AXLE. Those checks require the external prerequisites documented by `python3 verify.py --help` and, for AXLE, an `AXLE_API_KEY` environment variable.

The verifier treats the six root statement files as trusted inputs and checks their SHA-256 hashes before comparing them with the candidate solutions. This prevents an accidental statement edit from being mistaken for a proof.


## Provenance and licensing

- Original work in this repository is available under the root [MIT License](LICENSE).
- `p1.lean` through `p6.lean` are copied from Axiom Math's MIT-licensed repository and remain covered by Axiom Math's copyright and license notice.
- Full details and file mappings appear in [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).
- No Axiom solution files are included.
