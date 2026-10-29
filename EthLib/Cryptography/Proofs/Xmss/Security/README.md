# leanXMSS security proof

This directory holds a proof that leanXMSS is strongly unforgeable in the random oracle model, with 127 bits of classical security.

```text
    for every q >= 1 and every adversary whose experiment makes at most q hash calls:
    Pr[strong forgery] <= q / 2^127
```

The experiment counts every hash call: key generation, signing, the adversary's queries and the final verification.

The adversary chooses the leaf index of each signing request and may not use one twice.

The theorem is `XmssSecurity.leanXmss_has_127_bits_of_classical_security`, of statement `LeanXmss.LeanXmssSecurityStatement` (`LeanXmss/Statement.lean`).

It depends on Lean's three standard axioms only, which `XmssSecurity.lean` checks at build time.

## Source

The files are copied from [Verified-zkEVM/leanerVM](https://github.com/Verified-zkEVM/leanerVM) at commit [`c27abd774a274f745921dc1dd14a6a2c1728c3de`](https://github.com/Verified-zkEVM/leanerVM/tree/c27abd774a274f745921dc1dd14a6a2c1728c3de/lean_xmss), branch `mumbai`.

```text
here                        leanerVM
Statement/LeanXmss.lean     Statement/LeanXmss.lean
LeanXmss/, LeanXmss.lean    lean_xmss/LeanXmss/, lean_xmss/LeanXmss.lean
XmssSecurity/, ...          lean_xmss/XmssSecurity/, lean_xmss/XmssSecurity.lean
```

## License

These files keep leanerVM's license: MIT ([`LICENSE-MIT`](LICENSE-MIT)) or Apache-2.0 ([`LICENSE-APACHE`](LICENSE-APACHE)), at your option.

Both files are leanerVM's, copied unchanged.

The rest of EthLib is under CC0 (`LICENSE` at the root).

The proof's route is in [`lean_xmss/README.md`](https://github.com/Verified-zkEVM/leanerVM/blob/c27abd774a274f745921dc1dd14a6a2c1728c3de/lean_xmss/README.md), from the section "The random-oracle step".

The scheme the proof is about is the one of the leanXMSS note at leanVM commit `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`, the commit EthLib's leanXMSS implements.

The proof writes that scheme itself, in the namespace `LeanXmss`.

It does not mention EthLib's definitions.

The files keep leanerVM's style, not EthLib's, so they can be compared with leanerVM line by line.

## What changed here

Every import is renamed into `EthLib.Cryptography.Proofs.Xmss.Security`.

leanerVM also proves the theorem in the random-permutation model, where Keccak-256 is a sponge over a random permutation.

That part is left out:

- `Statement/RandomPermutation.lean`, `lean_xmss/LeanXmss/StatementRpm.lean`, `lean_xmss/XmssSecurity/Rpm.lean` and leanerVM's `common/` are not copied.
- `Statement/LeanXmss.lean` loses its section "Security in the random-permutation model", and imports the VCVio modules `Statement/RandomPermutation.lean` imported instead.
- `LeanXmss/Compat.lean` writes `SigningTranscript.Contains` out, rather than as `Common.SufCma.Contains`, which lived in the random-permutation model.
- `XmssSecurity/Proof/Bridge/Game.lean` no longer unfolds `Common.SufCma.Contains`.
- `LeanXmss.lean` and `XmssSecurity.lean` no longer import the left-out files, and `XmssSecurity.lean` no longer checks their theorems.
- The test target `lean_xmss/XmssSecurity/Tests/` is not copied.

The rest are fixes for this Lean, VCVio and EthLib:

- leanerVM builds with Lean v4.34.1 and VCVio `afa6593f`.
  EthLib builds with Lean v4.35.0 and VCVio `bbf05eee`, on the same Mathlib as EthLib.
- On Lean v4.35.0, unfolding `RevealProbeOracleSimulation.tableHits` at a concrete index type makes Lean evaluate its decision procedure over every index, past 30 GB of memory.
  `XmssSecurity/Proof/RevealProbeOracleSimulation.lean` gains `tableHits_eq_true_iff` and `tableHits_eq_false_iff`, proved at a generic index type.
  `CappedGlobalChainHighLocalCoupling.lean`, `CappedGlobalChainHighCoverage.lean` and `CappedGlobalChainHighReplay.lean` rewrite with them instead of unfolding.
- `lake exe check-decls` rejects `opaque` declarations, which the kernel cannot unfold.
  The four sampling instances `randomizerOutputsSampleableType` (`Deterministic/TableSigner.lean`), `bottomSampleable`, `topOtsSampleable` and `topRndSampleable` (`Bridge/Program.lean`) are `@[irreducible] noncomputable def` instead.
- CI treats warnings as errors.
  `Seeded/KeyDerivation.lean` writes `try first | ...` for `first | ... | skip`, whose `skip` the unused-tactic linter flags.
