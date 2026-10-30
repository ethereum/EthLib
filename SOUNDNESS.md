# Soundness

What the proofs of EthLib establish, and what a user of EthLib trusts on top of them.

No formal verification is absolute.
A proof links a Lean definition to a theorem.
Each of them is assumed to match something outside Lean: the source document, the code that runs, and what the client needs.
This document names each of those assumptions.

It follows the structure of s2n-bignum's [`SOUNDNESS.md`](https://github.com/awslabs/s2n-bignum/blob/main/SOUNDNESS.md), adapted to a specification library.

This document describes the development tree that declares package version `0.2.0` in `pyproject.toml`.

It does not describe the tag `v0.2.0`, which points to an earlier commit, without the declaration check or the exports library.

The prose was reviewed for that package version.
CI fails when `pyproject.toml` declares another version, so each version bump reviews the document again and updates the line above.

The facts that change with the code, such as which theorems still use `native_decide`, are generated from the repository by `scripts/soundness_facts.py`.
CI fails when one of them is out of date, so they hold for every commit, not only for one version.

## Ways to use EthLib

Each way of using EthLib trusts a different set of things.
The table below marks which rows apply to which use:

- **P**, a Lean proof that imports the specification;
- **R**, a Lean program that runs the specification;
- **B**, a client that calls the Python bindings;
- **V**, a client that tests against the vectors in `tests/`.

## Summary

| ID | Risk | Mitigation in place | Applies to |
|----|------|---------------------|------------|
| A1 | A definition does not match its source | Definitions named and shaped after the source; vectors pinned to consensus-specs `v1.7.0-alpha.12`; consistency theorems on the constants | P R B V |
| A2 | A theorem holds only under a hypothesis | Each conditional theorem below lists its hypotheses | P |
| A3 | Timing reveals secret data | None: no constant-time claim | R B |
| A4 | A security theorem idealises a primitive | None needed yet: no security theorem exists | P |
| B1 | The Lean compiler, the C compiler or the Lean runtime is wrong | Regenerating the vectors locally, then checking them against their pinned digests | R B |
| B2 | Lean core runs code other than its definitions | Lean core is a declared baseline | R B |
| B3 | Elaboration runs native code | None | P |
| B4 | The hand-written C boundary is wrong | Regenerating the vectors locally, then checking them against their pinned digests | B |
| B5 | This repository substitutes compiled code | `lake exe check-decls` fails on any new substitution | R B |
| B6 | The build or the published wheel differs from the source | Fresh build per wheel in CI | B |
| C1 | The Lean kernel or its axioms are unsound | None: `lake exe check-decls` checks which axioms a theorem uses, not that the kernel or the axioms are sound | P |
| C2 | A proof trusts compiled code | `lake exe check-decls` fails on any new use; the remaining ones are listed in C2 | P |
| C3 | A declaration reached the environment unchecked | None yet | P |
| D1 | A client misuses an operation | Docstrings in Lean | R B |
| D2 | A dependency changes | Pinned in `lake-manifest.json` | P R B |
| D3 | The KZG trusted setup is not what it should be | Bytes match the consensus-specs setup | P R B V |
| D4 | The vectors are wrong | They match consensus-specs `v1.7.0-alpha.12`, and CI checks their pinned digests | V |

The sections below explain each row.

## What the proofs say

This section lists the main theorems by primitive.
It is not yet complete.

No theorem states a security property: unforgeability for XMSS or BLS, or binding for KZG.
No theorem covers the code that runs, the C boundary, or timing.

### XMSS

`verify_keyGen_sign` (`Proofs/Xmss/Correctness.lean`):
if `keyGen seed` returns a key pair, and `sign` returns a signature for a message at a leaf index, then `verify` accepts that signature under that public key.

It is a correctness statement.
It says nothing about unforgeability.

### VRF tree

`verify_unique` (`Proofs/Vrf/Verify.lean`): two openings that verify at one index under one root give one output, or Keccak-256 collides.
It holds for every root, including one built to cheat.

`verify_opening` (`Proofs/Vrf/Verify.lean`): the opening of an honest tree verifies, with the output of its secret.

Uniqueness is reduced to a collision, and no theorem bounds the cost of one.
No theorem says that an output is unpredictable before it is opened.

### BLS12-381

`modulus_prime` (`Proofs/Bls/FpZMod.lean` and `Proofs/Bls/FrZMod.lean`): both moduli are prime.

`seven_pow_card_sub_one` and `seven_pow_div_prime_ne_one` (`Proofs/Bls/FrZMod.lean`): `7` generates the multiplicative group of the scalar field.
`7` is also the KZG constant `PRIMITIVE_ROOT_OF_UNITY`.

`addOrderOf_toPoint_generator` (`Proofs/Bls/G1Order.lean`): the G1 generator has order `r`.

These check the constants.
A wrong digit in a modulus or in the generator would very likely make one of them fail.

### KZG

`Proofs/Kzg/Core.lean`: the public operations reject malformed inputs, such as a wrong size or lists of different lengths.

No theorem says what an accepted input returns.
The operations run in `IO` to read the trusted setup, so the kernel cannot evaluate them, and their results on success are unproved.

`checksSufficient` (`Proofs/Kzg/CeremonyChecks.lean`): the ceremony's pairing checks force each G1 and G2 point of a contribution to be the expected power of the trapdoor.
It holds under four hypotheses besides the checks themselves:

- `ConcreteBlsLaws`, one law the repository does not prove yet, `pairingEq_mul_iff`: on multiples of the generators, the concrete pairing check holds exactly when the scalar products agree, which is bilinearity and non-degeneracy;
- `SubgroupExponents`, exponents witnessing that every point involved is a multiple of its group's generator, which stands in for the subgroup checks;
- `previousTauNonzero`, that the previous transcript's tau point is not at infinity;
- `pubkeyNonzero`, that the contributor's public key is not at infinity.

### MODEXP

`compute_eq_pow_mod` (`Precompiles/Proofs/Modexp/Core.lean`): the output is `BASE ^ EXPONENT mod MODULUS`, or 0 for a zero modulus.
It rests on `powMod_eq` (`Precompiles/Proofs/Modexp/PowMod.lean`): the square-and-multiply loop equals `b ^ e % m`.

`modexp_out_of_gas` and `modexp_ok` (`Precompiles/Proofs/Modexp/Core.lean`): with every length within the EIP-7823 bound, a call fails exactly when the gas is below the price.

These state agreement with EIP-198 and EIP-7823.
No theorem relates the module to the execution-specs code it follows.

### What cannot be proved yet

These definitions prevent direct kernel evaluation.
Their intended computational properties remain unproved.
`lake exe check-decls` reports each one, and `scripts/check_decls_baseline.txt` lists those that remain, with the reason for each group.
A `partial` definition is defined by `partial` recursion.
An `opaque` one is an opaque constant, such as the global reference that holds the KZG trusted setup.
A `reaches-opaque` one unfolds to an opaque constant, such as `Loop.forIn`, which `while` compiles to, or the `IO` that reads that reference.

<!-- generated: unfoldable -->
- `EthLib.Cryptography.Kzg.KzgM`, `reaches-opaque`
- `EthLib.Cryptography.Kzg.TrustedSetup.get!`, `reaches-opaque`
- `EthLib.Cryptography.Kzg.TrustedSetup.globalRef`, `opaque`
<!-- end generated -->

## Gap A: does the definition say what the source and the client need?

### A1. A wrong definition

A definition can differ from its source while every theorem about it holds.

Mitigations:

- Each definition is named and shaped after its source, so that a reader can compare them line by line.
- The KZG and BLS vectors in `tests/cryptography/` match the consensus-specs `v1.7.0-alpha.12` general vectors byte for byte.
  Those were produced by the Python specification, not by EthLib.
- Consistency theorems on the constants, listed above.

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
`checksSufficient` is the main one today, and its four hypotheses are listed above.
What remains of them is part of what a reader trusts.

### A3. Side channels

EthLib makes no constant-time claim.

`Hash/Keccak.lean` says it "is not intended to be constant-time".
The field arithmetic uses Lean's `Nat`, which gives no timing guarantee.
XMSS `keyGen` and `sign` handle secret data.
The Python bindings expose both, as `key_gen` and `sign`, which take the secret seed.

### A4. Idealisations

A security theorem rests on a model, such as a random oracle for a hash.
None exists yet, so there is nothing to list.

## Gap B: does the code that runs match the definitions?

s2n-bignum proves its theorems about the object code, so a compiler bug cannot invalidate them.
EthLib is the other way round.
Its theorems are about the Lean definitions, and everything between them and the running code is trusted.

```text
 source document --A-- Lean definition == proof == theorem
                            |
                            B
                            |
        compiled code, C boundary, wheel --D-- client

 C: is the proof itself sound?
```

### B1. The compilers and the runtime

The Lean compiler turns the definitions into C, a C compiler turns that into machine code, and the Lean runtime runs it.
No theorem covers that path.

The vectors can test it end to end, but only through a comparison.
The Python suite regenerates every vector through the bindings and writes it over the committed one.
For most operations it does not compare the result with an expected answer, so a passing run proves nothing on its own.
The check is that the regenerated files are identical to the committed ones, which match consensus-specs `v1.7.0-alpha.12`.
`python3 tests/cryptography/check_vectors.py` makes that comparison against the pinned digests.
CI runs it on the committed vectors on every change, but it does not regenerate them, which takes hours.
So for B1 and B4 the regeneration is a local step, and only the check after it shows that the bindings still produce the committed answers.

### B2. Lean core's own implementations

Lean core implements `Array.forIn'`, `foldlM`, `foldrM`, `mapM` and `anyM` with `@[implemented_by]`.
It implements the `Nat`, `ByteArray` and `Array` primitives with `@[extern]`.
The compiled code runs those implementations, not the definitions the kernel checks.

Any loop or fold over an array reaches them, so Lean core is a declared trusted baseline.
`lake exe check-decls` does not report it.

### B3. Native code during elaboration

The `EthLib` and `Exports` libraries set `precompileModules := true`.
So `#eval`, or a tactic that evaluates, in any module that imports them runs natively compiled code.
A proof is unaffected unless it uses one of the tactics of C2.

### B4. The C boundary

<!-- generated: exports -->
Lean exports 19 operations and 21 size constants.
The Python extension calls 19 of the operations and 16 of the constants.
Exported constants it does not call: `eth_xmss_const_chains`, `eth_xmss_const_digest_len`, `eth_xmss_const_layer_height`, `eth_xmss_const_public_param_len`, `eth_xmss_const_randomizer_len`.
<!-- end generated -->

<!-- generated: c-lines -->
1364 lines of hand-written C sit between them and Python: `bls.c` (87), `kzg.c` (533), `modexp.c` (61), `module.c` (431), `wrappers.h` (129), `xmss.c` (123).
<!-- end generated -->

They convert arguments, own and free Lean objects, and turn errors into Python exceptions.
The vectors test this layer only through the regeneration and comparison of B1.

Each typed Lean error becomes a `RuntimeError` with the operation's name, and the Lean message is dropped.
A wrong argument size is caught in C first, and raises `ValueError`.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust.
It still means the code that runs is not the definition a reader reads.

The repository has none of the three today.
`lake exe check-decls` reports any of them, and fails on one that is not in its baseline.

### B6. The build and its publication

`setup.py` runs `lake build Exports`, and links the objects under `.lake/build/ir/EthLib/` with `libleanshared`, `libgmp` and `libuv`.
`.github/workflows/publish.yml` builds the wheels with `cibuildwheel`, cleans the build before each wheel, and publishes them to PyPI.

## Gap C: is the proof itself sound?

### C1. The Lean kernel and its axioms

Every theorem trusts the Lean kernel, and whichever of the three standard axioms it uses: `propext`, `Classical.choice` and `Quot.sound`.
Those three are the allowed set; a theorem may use fewer.

`lake exe check-decls` checks dependencies: that no declaration depends on an axiom outside that set, apart from those in its baseline.
It does not check the kernel, and it does not show that the axioms are consistent.
That rests on Lean's own design and review.
No independent checker replays the environment yet (C3).

### C2. Tactics that trust compiled code

`native_decide`, `bv_decide` and `decide +native` each add an axiom that trusts the compiled code.
A proof that uses one is no longer checked by the kernel alone.
It also trusts every `@[implemented_by]` and `@[extern]` that the compiled code reaches (B2).

`AGENTS.md` does not allow them.
A new use fails `lake exe check-decls`.

<!-- generated: native -->
No theorem uses them.
<!-- end generated -->

### C3. Declarations the kernel did not check

A metaprogram can add a declaration to the environment without the kernel checking it.
An independent checker that replays the environment, such as `lean4checker`, would catch it.
None runs yet.

## Gap D: does the use of EthLib hold together?

### D1. The client's obligations

A client chooses the right operation for its fork, passes inputs of the right form, and handles errors.

XMSS adds one more.
Never sign two different messages at one leaf index with one secret key.
Each leaf index names a one-time signing key, and nothing in EthLib records which leaf indices were used, so the caller must prevent reuse.
The Lean and Python docstrings of `sign` both say so.

### D2. Dependencies

`lake-manifest.json` pins every dependency.

<!-- generated: pins -->
The specification requires no package.
The package requires Mathlib, at `v4.35.0`, commit `56a0058`, which only the proofs import.
The Lean toolchain is `leanprover/lean4:v4.35.0`.
<!-- end generated -->

### D3. The KZG trusted setup

The setup raises three separate assumptions, and each use of KZG relies on a different subset.

- Provenance: the embedded bytes are the ceremony's output.
  They match consensus-specs `presets/mainnet/trusted_setups/trusted_setup_4096.json` byte for byte.
  `Kzg/TrustedSetupData.lean` records that source, the commit it comes from and its sha256.
- Algebraic consistency: the bytes decode to valid points, the monomial points are powers of one secret, and the Lagrange points are the matching basis.
  None of this is proved for the embedded bytes.
  `checksSufficient` covers the ceremony's monomial points, under its hypotheses.
- Secrecy: no one knows the secret, which holds if at least one ceremony participant was honest.
  Only binding, a security property, needs it.
  A theorem about parsing, or that an honest proof verifies, does not.

### D4. The vectors

A client that tests against the vectors trusts whatever produced their expected values.
The KZG and BLS vectors match the consensus-specs `v1.7.0-alpha.12` general vectors byte for byte.
`v1.7.0-alpha.12` was the last release before consensus-specs removed its KZG specification, in ethereum/consensus-specs#5398.
