---
name: proof
description: Add, repair or move Lean proofs about EthLib, including mathematics bridges and security proofs. Covers proof design, dependency boundaries, kernel checking and repository checks.
---

# Adding or changing a proof

Read [AGENTS.md](../../../AGENTS.md) and the definition's normative source before writing.
Read the module README where one exists.
AGENTS.md governs wherever this guide and the repository rules differ.

## Plan the argument

Before a substantial proof, state the mathematical argument, its hypotheses and the main intermediate claims.
Search EthLib and the relevant upstream libraries for existing results.
Identify missing lemmas, abstractions or theory before expanding a large proof.

Repeated coordinate calculations, nearly identical proofs and growing case splits are reasons to reconsider the approach.
Look for a shared invariant, a generic theorem, a better representation or a different proof technique.
Separate reusable foundations from scheme-specific arguments, and propose them upstream where they belong.
If substantial foundations are missing, explain the gap and propose prerequisite work before proceeding.

When adapting an external proof, prefer instantiating its interfaces and proving a small correspondence with EthLib.
A separate model can be useful, but explain why it is needed and prove its relation to the actual definitions.
Avoid copying another specification merely to accommodate an existing proof.

For an expensive computation, first look for a structural argument or a compact checked calculation.
If a large certificate is justified, record its source and reproduction method, and measure build time and peak memory.
A generated certificate is proof input, not an independently sourced known answer.
Splitting a calculation across files may control memory without removing unnecessary work.

Do not change library behaviour merely to make a theorem true.
Check a failed claim's hypotheses and the definition against the source, and report any disagreement.
State assumptions explicitly when the result is conditional; the theorem does not discharge them.

## Choose the package and file

Follow the current layout in AGENTS.md:

```text
EthLib/<Domain>/<Module>/Foo.lean         definition
EthLib/<Domain>/Proofs/<Module>/Foo.lean  proofs about it
EthLib/<Domain>/Proofs/<Module>.lean      imports the proof files
```

Mathlib is currently a root-package dependency and may be imported by proofs in the `Proofs` library.
The specification code imports neither Mathlib nor any proof.
Import each new proof file from its module's proof root.
An unreferenced file in this layout is not built by the default `lake build` or CI.

[#107](https://github.com/ethereum/EthLib/issues/107) proposes a dependency-free core, a mathematics package for Mathlib bridges and a security package for libraries such as VCV-io.
The latter packages would depend on the core, never the reverse.
That split is undecided and is not implemented.
Do not create packages or move proofs merely to implement this proposal while doing another proof task.
For work needing a new dependency, make its placement an explicit design decision.
Separate folders or `lean_lib` targets within one package do not isolate dependencies.

## Keep proofs kernel-checkable

Automation may run compiled code or use external tools to search for a proof.
Its result must be a proof term the kernel accepts using only the permitted axioms: `propext`, `Classical.choice` and `Quot.sound`.
A theorem may use fewer.
Do not assert a computed result through a compiler-trusting axiom, as `native_decide`, `bv_decide` and `decide +native` do in Lean 4.35.

For closed computations, try `decide`, `decide +kernel` or proof-producing evaluation with `decide_cbv`.
If evaluation is too expensive, prove a faster form equivalent over the stated domain, rewrite the goal and evaluate that form.
Both the equivalence proof and the final theorem must pass the axiom audit.
Examples are `EthLib/Cryptography/Proofs/Hash/KeccakKernel.lean` and `EthLib/Cryptography/Proofs/Xmss/Kernel.lean`.

Compiler substitutions are a separate boundary.
`@[extern]` and `@[implemented_by]` do not require an equivalence proof.
`@[csimp]` uses a proved equality and does not itself add an axiom, but changes compiled execution rather than kernel reduction.
EthLib currently rejects all three in repository code.
The `@[csimp]` restriction is repository policy, not a claim that proved substitution is logically unsound.

## Check the result

For the current root package, run:

```bash
lake build EthLib.<Domain>.Proofs.<Module>.<File>
lake build --wfail
lake exe check-decls
python3 scripts/soundness_facts.py --check
```

Run the additional checks AGENTS.md requires for any library, bindings or vector changes.

`check-decls` audits axiom dependencies and attributes; it does not replay proof terms through the kernel.
Its summary must end with `0 new, 0 stale`.
Kernel replay and independent checking are additional validation, not substitutes for reviewing the statement and its assumptions.
Lean 4.35 provides `lake check` and `lake check --paranoid` for those checks; they are not current EthLib CI requirements.

The baseline records legacy findings, not permission to introduce new ones.
Do not add exceptions.
When resolving a finding, rebuild and confirm the remaining code is still checked before removing its entry in the same change.
Dropping an import or moving code outside the checked scope is not a resolution.
If a declaration is removed or renamed, account for that change explicitly.
The checker compares findings with the current baseline, not an earlier commit, so reviewers must also enforce the rule against new exceptions.
Regenerate the `SOUNDNESS.md` blocks and review affected prose when findings change.

## Prepare the pull request

Proofs for new or changed behaviour arrive finished with that change.
A `proof` pull request adds or changes theorems about existing behaviour.
It may make definitions public or restructure them without changing their computed results, as AGENTS.md permits.
Explain those source changes in the body.

Update the module README when the proof adds meaningful coverage or changes a documented hypothesis or limitation.
Name the theorem a reader needs, its file and its hypotheses, rather than listing its helper lemmas.
Correct any affected statement in `SOUNDNESS.md`.

Explain the argument, assumptions, remaining obligations and any substantial build cost in the pull request body.
Report the checks actually run, including the declaration-check summary, and identify any skipped checks.
