# Mission

Complete every original `sorry` in the user-designated Lean file. Produce genuine,
kernel-checkable proofs and finish with a clean compilation and axiom audit.

Treat this as a long-horizon proof task. Work very hard, use the highest available
reasoning effort, and do not stop merely because the first proof attempts fail. A
reduction, an informal argument, a plausible proof sketch, a list of useful lemmas,
or a file that still contains a placeholder is not completion.

The theorem statements are assumed to be provable as supplied. If an approach seems
to show otherwise, first suspect a misunderstood definition, coercion, namespace,
edge case, or mismatch between the informal reading and the formal statement. Test
the issue in Lean before changing direction.

# Scope and ground rules

- Work only inside this repository.
- The user-designated target `.lean` file is the only problem file in scope. If the
  repository contains several candidate problem files and the target is genuinely
  ambiguous, ask the user which one is intended before editing any of them.
- Do not inspect other problem files, prior attempts, generated answers, git history,
  branches, stashes, commits, or remote repositories for a solution.
- Git may be used only for non-destructive working-tree inspection such as
  `git status`, `git diff`, and `git diff --check`. Do not reset, discard, overwrite,
  or commit user changes unless explicitly requested.
- Do not modify files outside the repository.
- Keep build artifacts and any large local caches inside the repository when
  possible; do not fill the home directory. Do not download a new toolchain,
  Mathlib cache, package, or dependency.
- Preserve unrelated user changes. The final diff should touch only the target file
  unless a genuinely necessary, explicitly explained project-local helper is added.

# Closed environment

Derive the proof independently using only:

1. the supplied target file;
2. declarations made available by its existing imports;
3. the already installed Lean/Mathlib toolchain;
4. local compiler feedback;
5. local declaration inspection and theorem-discovery commands such as `#check`,
   `#print`, `#find`, `set_option pp.all true`, `library_search`, `exact?`,
   `apply?`, and `simp?`;
6. ordinary sound Lean tactics and proved helper lemmas.

Local inspection of declarations and source belonging to already imported Mathlib
modules is allowed. Searching unrelated local Lean files for a matching theorem or
solution is not.

Do not use or consult:

- web search or browsing;
- GitHub, GitLab, or any other online repository;
- search engines or online theorem-search services;
- published solutions, benchmark submissions, proof databases, or cached answers;
- code copied or retrieved from an external source;
- network-accessible tools, APIs, package registries, or remote agents with internet
  access.

Do not run commands that contact the network, including dependency or cache download
commands. If the existing local Lean environment is incomplete, report the exact
missing local prerequisite rather than fetching it.

# Non-negotiable proof integrity

Replace every original `sorry` with a genuine Lean proof. Never introduce or use:

- `sorry`, `sorryAx`, `admit`, or a disguised equivalent;
- new `axiom` or `constant` declarations used as assumptions;
- `unsafe` declarations or unsafe proof-generation mechanisms;
- fabricated hypotheses or strengthened premises;
- weakened theorem statements or altered definitions that trivialize the task;
- circular reasoning, including invoking the theorem currently being proved, an
  alias of it, or a later theorem that depends on it;
- a helper assertion known to be false, an inconsistency manufactured solely to use
  `False.elim`, or any other ex-falso bypass of the intended mathematics;
- opaque external proof objects or generated code whose trust chain is not checked
  by the ordinary Lean kernel.

Legitimate proof by contradiction is allowed when it directly follows from the
supplied hypotheses. Standard tactics such as `simp`, `aesop`, `omega`, `linarith`,
`nlinarith`, induction, extensionality, cases, contradiction, and classical reasoning
are allowed when logically appropriate. Tactic suggestions are only starting points:
inspect the generated proof, keep it understandable enough to audit, and recompile it.

# Preserve the problem

Preserve all existing:

- imports, unless an additional already-local import is genuinely necessary;
- theorem, lemma, definition, namespace, and notation names;
- declaration statements and binder types;
- definitions and their intended mathematical meaning;
- completed declarations, so they remain available to later proofs.

Do not change a theorem statement even if a nearby reformulation would be easier.
Do not silently add hypotheses, typeclass assumptions, nonemptiness assumptions,
decidability assumptions, or finiteness assumptions. You may add fully proved helper
lemmas, reorganize proof bodies, and introduce local notation when this does not alter
the public statements.

Avoid changing imports. If one is truly necessary, it must already exist in the local
environment, be narrower than `import Mathlib` when practical, and be explicitly
justified in the final report. Never add an import merely to obtain a theorem that is
already available through the original imports.

# Required proof workflow

## 1. Establish a clean baseline

Before editing:

1. Identify the repository root, target file, project configuration, and available
   `lean`/`lake` executable without searching for other problem solutions.
2. Read the complete target file once, including definitions, namespaces, local
   notation, options, and declaration order.
3. Record every original placeholder and the declaration containing it. Distinguish
   executable placeholders from occurrences of the word `sorry` in comments.
4. Run the narrowest correct baseline command, normally one of:

   ```bash
   lake env lean path/to/Target.lean
   lean path/to/Target.lean
   ```

5. Save the baseline diagnostics. Do not mistake expected `declaration uses 'sorry'`
   warnings for unrelated compiler failures.

## 2. Build a dependency map

Order the missing proofs by logical dependency, not merely by file position. For each
placeholder, identify:

- the exact formal goal after unfolding only the definitions that matter;
- earlier declarations that may be used safely;
- likely invariant, induction parameter, extremal quantity, algebraic identity, or
  structural decomposition;
- the relevant imported Mathlib domain and candidate local lemmas;
- edge cases involving empty types, zero, coercions, finite cardinalities, subtypes,
  quotient structures, or degenerate geometry.

Prove reusable foundational lemmas first. Keep earlier completed results available for
later declarations. Never use a later result to close an earlier theorem when doing so
would create a dependency cycle.

## 3. Separate mathematics from elaboration

For a difficult goal, first write a concise mathematical proof plan in the internal
working notes. Break it into statements that are both mathematically meaningful and
likely to match Mathlib abstractions. Then formalize one lemma at a time.

Do not tactic-thrash blindly. When a goal stalls:

1. inspect the exact goal and types;
2. check relevant definitions with `#check` and `#print`;
3. use local theorem discovery against imported declarations;
4. make a minimal scratch `example` or temporary `example` block in the target file;
5. compile immediately;
6. generalize a successful experiment into a proved helper lemma;
7. remove temporary probes once integrated.

Prefer robust proof terms over brittle chains of simplifier accidents. Use explicit
arguments where inference is fragile. Control rewriting direction deliberately. For
arithmetic, normalize coercions before calling arithmetic tactics. For finite and
combinatorial arguments, state the invariant and termination measure explicitly. For
analysis or geometry, isolate nonnegativity, nondegeneracy, and coercion facts before
the main calculation.

## 4. Use a tight compiler loop

After every meaningful edit:

1. compile the whole target file, not only a detached snippet;
2. fix the first relevant error before accumulating additional speculative edits;
3. recheck downstream declarations because elaboration and simplification can change;
4. periodically inspect the diff to ensure statements and definitions remain intact.

Use `apply_patch` or another controlled edit mechanism. Avoid broad mechanical rewrites
that may alter statements. Keep experimental code small and remove it after use.

## 5. Explore dynamically when blocked

Do not abandon the task after one approach fails. Maintain an internal registry of
genuinely different approach families, for example:

- direct use of an imported theorem;
- induction on the native recursive structure;
- well-founded induction using a decreasing measure;
- extensionality or equality through a canonical representation;
- algebraic normalization and arithmetic closure;
- order-theoretic bounds or extremal witnesses;
- finite enumeration justified by a proved completeness lemma;
- contradiction from a minimal counterexample;
- reformulation through an equivalent local invariant.

Mark a route blocked when it depends on a missing lemma essentially as strong as the
original theorem. Reopen it only after identifying a materially new mechanism. Do not
allow an elegant but incomplete reduction to crowd out independent routes.

Require concrete progress from every route: a compiled helper lemma, a precise missing
statement, a counterexample to a proposed helper, or a compiler-confirmed API fact.
Vague optimism and status summaries are not progress.

# Optional subagent protocol

If local subagents are available, use them dynamically for bounded, independent work
that stays inside this closed environment. Do not use remote or network-enabled agents.
The root agent remains responsible for every proof and for final compilation.

- Begin with a diverse portfolio: mathematical proof design, imported-lemma discovery,
  definition/API inspection, alternate formulations, and adversarial checking.
- Preserve independence early. Do not tell every subagent the currently favored route.
- Assign concrete questions, not generic requests to “solve it.” Ask for candidate Lean
  terms, exact lemma names verified locally, small compiled examples, or a rigorous
  mathematical sublemma.
- Group results by underlying proof idea and redirect duplicated effort toward
  underexplored approaches.
- Do not let multiple agents edit the target file concurrently. Subagents should work
  in isolated scratch files or return suggestions; the root agent integrates changes
  serially and recompiles the authoritative target.
- Use adversarial review throughout. A checker should try edge cases, examine hidden
  assumptions, challenge termination and nondegeneracy claims, and look for circular
  dependencies or accidental use of stronger results.
- Cross-pollinate approaches only after their independent strengths and gaps are clear.
- End or redirect agents that return only prose, unverified names, or theorem-strength
  missing lemmas without a new mechanism.

Subagents do not relax any scope, network, integrity, or file-preservation rule in this
document.

# Adversarial audit before completion

Do not declare success until all of the following have been performed.

## Source audit

- Compare the final target against the baseline and verify that all public names,
  statements, definitions, and intended meanings are unchanged.
- Confirm that every original placeholder has been replaced.
- Search the edited source for executable occurrences of `sorry`, `admit`, `sorryAx`,
  newly introduced `axiom`, `unsafe`, suspicious ex-falso helpers, and temporary test
  declarations.
- Inspect the diff for accidental edits outside proof bodies and approved helper lemmas.
- Run `git diff --check` when the repository uses git.

Do not treat a text search alone as proof integrity: comments may contain forbidden
words, and indirect axiom dependencies require the kernel audit below.

## Full compilation

Compile the complete target file from a clean invocation using the project toolchain.
There must be:

- no errors;
- no unsolved goals;
- no placeholder warnings;
- no reliance on stale output from a detached scratch example.

If feasible, remove only the target's local generated build output and compile again.
Do not delete broad caches, dependencies, user data, or unrelated build artifacts.

## Axiom audit

For every declaration that originally contained a placeholder, run `#print axioms` or
an equivalent local kernel check after the completed file has compiled. Temporary audit
commands may be appended and then removed after their output is recorded.

The audit must show no `sorryAx` and no newly introduced axiom. Standard axioms inherited
from Lean or Mathlib, such as `Classical.choice`, `propext`, or `Quot.sound`, are allowed
when appropriate and must be reported accurately. Do not describe a declaration as
“axiom-free” if the audit lists standard axioms; instead list exactly what Lean reports.

## Mathematical audit

Read each completed proof once without editing and check:

- every case is covered;
- all induction hypotheses are used at strictly smaller arguments;
- termination measures really decrease;
- divisibility, positivity, nonzero, finiteness, and nondegeneracy side conditions are
  proved rather than assumed;
- coercions and overloaded notation express the intended objects;
- helper lemmas are not equivalent to the theorem with the hard part hidden;
- no theorem depends, directly or indirectly, on itself.

# Completion contract

Continue until all original placeholders are gone, the entire target file compiles, and
the axiom audit passes. Do not return a partial file, isolated proof fragments, an
informal proof, a reduction to an unproved lemma, or a “best effort” summary.

The final response must:

1. state that the complete target file was successfully checked, naming the exact local
   compilation command used;
2. state that every original placeholder was removed;
3. summarize the `#print axioms` results exactly, including any standard inherited
   axioms;
4. mention and justify any added import or helper lemma;
5. return the complete contents of the finished `.lean` file, not merely a diff or
   selected proof fragments.

Never claim completion unless these statements are true.

# Solution-file layout

For this repository's six designated problems, preserve `p1.lean` through
`p6.lean` exactly as supplied at the repository root. Put the completed,
standalone sources in `gpt/p1_solution.lean` through `gpt/p6_solution.lean`.
The original file is the trusted challenge/formal-statement file for validation;
the matching `gpt/pN_solution.lean` file is the candidate proof. Do not import an
original problem file into its solution, because the original contains `sorry`
declarations with the same public names.

# Escalated proof-validation workflow

The user explicitly authorized the following narrow exceptions to the closed-network
rules above.  They apply only after deriving the proofs independently: official
validator documentation may be consulted, validator software may be installed inside
this repository, and completed solutions may be submitted to the named validation
service.  These exceptions do not authorize online theorem search, proof retrieval,
or consulting external solutions.  Never print, commit, copy into source, or otherwise
expose credentials from `keys.txt`; load them only into the validator process
environment.

After the ordinary source audit, full compilation, and `#print axioms` audit, validate
every `_solution.lean` file at these additional levels:

1. **Stored-proof replay (`leanchecker`).** Build an `.olean` for the complete
   solution module, then run the checker shipped with the pinned Lean toolchain as
   `lake env leanchecker <Module>` and require an error-free exit. No separate
   checker build or binary path is needed. At most two module checks may run in
   parallel. Cap every module replay at 30 minutes. A complete replay into a new
   environment may additionally be attempted with
   `lake env leanchecker --fresh <Module>`. If either mode reaches the limit,
   record the timeout and do not block completion on it when both Comparator and
   AXLE pass for that problem. Record the exact build and checker commands used.
2. **Comparator gold-standard check.** Use the official `leanprover/comparator`
   workflow with the untouched `pN.lean` as the trusted challenge and
   `pN_solution.lean` as the solution.  List every originally incomplete theorem in
   `theorem_names`; permit only `propext`, `Classical.choice`, and `Quot.sound` (or a
   strict subset); use the documented sandbox command; and enable the independent
   `nanoda` checker when locally available.  Require Comparator to confirm identical
   statements, permitted axioms only, and kernel acceptance.  Keep all cloned tools,
   build products, Cargo state, and caches inside this repository.
3. **AXLE `verify_proof`.** Submit the complete `_solution.lean` text as `content`
   and the complete untouched original `pN.lean` text as `formal_statement` to
   `https://axle.axiommath.ai/api/v1/verify_proof`, authenticating with
   `Authorization: Bearer $AXLE_API_KEY`.  Query the available environments and choose
   the compatible Lean/Mathlib environment; do not set `permitted_sorries`; preserve
   imports when supported; and use a sufficient timeout for the whole file.  Require
   `okay = true`, empty Lean/tool error lists, and an empty `failed_declarations` list.

For an untrusted candidate, run AXLE and the guarded Comparator workflow before any
unsandboxed local elaboration. Never pass `AXLE_API_KEY` or other credentials to a
candidate-controlled Lean process.

If a validator cannot run because a documented external prerequisite is genuinely
unavailable, report the precise prerequisite and all attempted commands.  A failure
of one of these additional validators is not permission to weaken or rewrite a
theorem, use an extra axiom, or skip the ordinary kernel and axiom audits.
