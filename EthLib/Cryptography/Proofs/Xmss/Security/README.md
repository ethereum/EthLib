# leanXMSS security proof

This directory holds the proof that leanXMSS, as EthLib computes it, is strongly unforgeable in the random oracle model, with 127 bits of classical security.

```text
    for every q >= 1 and every adversary whose real game makes at most q hash calls:
    Pr[strong forgery] <= q / 2^127
```

The real game runs EthLib's own algorithms, with the hash a query to the random oracle.

Its signer keeps the scheme seed `S` and the parameter `P`.

The theorem is `XmssSecurity.Bridge.realGame_security` (`XmssSecurity/Proof/Bridge/Security.lean`).

`Proofs/Xmss/Unforgeability.lean` carries it to EthLib's game, whose signer re-derives `S` and `P`, as `Unforgeability.unforgeable`.

There is one definition of the scheme: EthLib's.

## The route

```text
    Bridge/          EthLib's real game, step by step, to the model's game
    Proof/           the model's game, two units of 2^-128 per hash call
    Scan/            the digest term of the second lane
    Scheme.lean      the model: leanXMSS with precomputed keys
```

The model is a device of the proof, not a second statement.

It holds every chain value and node in a table, so its signer makes only the calls an adversary can learn from.

Its verifier is EthLib's own `verifyWith`, so verification has one definition.

`Unforgeability/Translate.lean` proves that each hashing routine of EthLib, run with the oracle, is the model's, call for call.

The `Bridge/` files then use it on EthLib's algorithms directly.

- `SchemeSeed`: the seed hash `S = H("leanXMSS" | S_0)` becomes a uniform `S`, for one guess of `S_0` per call.
- `Derivation`, `Program`: every input that contains `S` is answered from a table drawn up front.
- `Real`: EthLib's key generation from `S` makes `K = 13,434,881` calls and erases to the model's key.
- `Signer`: EthLib's signer from `S` and `P` erases to the model's table signer.
- `Game`, `Reduction`, `Seed`, `Model`: the rest of the game, then the model's game.
- `Security`: the bound.

The argument, its units and its two lanes are explained in leanerVM's [`lean_xmss/README.md`](https://github.com/Verified-zkEVM/leanerVM/blob/c27abd774a274f745921dc1dd14a6a2c1728c3de/lean_xmss/README.md), from the section "The random-oracle step".

## Source

The proof is adapted from [Verified-zkEVM/leanerVM](https://github.com/Verified-zkEVM/leanerVM) at commit [`c27abd774a274f745921dc1dd14a6a2c1728c3de`](https://github.com/Verified-zkEVM/leanerVM/tree/c27abd774a274f745921dc1dd14a6a2c1728c3de/lean_xmss), branch `mumbai`, directory `lean_xmss/XmssSecurity/`.

The scheme it is about is the one of the leanXMSS note at leanVM commit `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`, the commit EthLib's leanXMSS implements.

## License

These files are under CC0, like the rest of EthLib (`LICENSE` at the root).

leanerVM ships them under MIT or Apache-2.0.

Their copyright holder, leanEthereum, releases them to EthLib under CC0.

## What changed here

leanerVM proves the bound for its own copy of leanXMSS, `LeanXmss` (`Statement/LeanXmss.lean`, `lean_xmss/LeanXmss/`).

Here that copy is gone.

- `Statement/`, `lean_xmss/LeanXmss/`, `lean_xmss/LeanXmss.lean` and `XmssSecurity/Proof/Bridge/Translate.lean` are not copied.
- The model's verifier is EthLib's.
  `Concrete.verify`, `Concrete.verifyAfterLeaf` and `Concrete.verifyTop` are EthLib's `verifyWith`, `fold` and top-layer `layerRoot`, read through the byte conversions (`Unforgeability/Convert.lean`).
  Their former bodies are theorems (`Concrete.verify_eq`, `Concrete.verifyAfterLeaf_eq`, `Concrete.verifyTop_eq`, in `Unforgeability/Translate.lean`), which the proof rewrites with where it unfolded them.
  The model's types and hash inputs move to `XmssSecurity/Types.lean`, so the conversions can come before the model.
- `Bridge/Real.lean`, `Bridge/Signer.lean` and `Bridge/Game.lean` are rewritten to reason about EthLib's `publicKeyOf`, `signDerived` and `verifyWith`.
- `Bridge/Derivation.lean` names its inputs by the model's byte layout.
- `Bridge/SchemeSeed.lean`, `Reduction.lean`, `Seed.lean`, `Model.lean` and `Security.lean` take EthLib's adversary and state the real game (`realGame`) directly.
- The codeword count of `LeanXmss/Code.lean`, which `Scan/Card.lean` needs, moves to `XmssSecurity/Code.lean`.

leanerVM also proves the theorem in the random-permutation model, where Keccak-256 is a sponge over a random permutation.

That part is left out: `lean_xmss/XmssSecurity/Rpm.lean`, leanerVM's `common/` and the test target `lean_xmss/XmssSecurity/Tests/` are not copied.

Declarations the theorem does not use are removed, about 1,600 lines.

Among them are the model's own statement of security and its own seeded scheme.

The rest are fixes for this Lean, VCVio and EthLib:

- leanerVM builds with Lean v4.34.1 and VCVio `afa6593f`.
  EthLib builds with Lean v4.35.0 and VCVio `bbf05eee`, on the same Mathlib as EthLib.
- On Lean v4.35.0, unfolding `RevealProbeOracleSimulation.tableHits` at a concrete index type makes Lean evaluate its decision procedure over every index, past 30 GB of memory.
  `XmssSecurity/Proof/RevealProbeOracleSimulation.lean` gains `tableHits_eq_true_iff` and `tableHits_eq_false_iff`, proved at a generic index type.
  `CappedGlobalChainHighLocalCoupling.lean`, `CappedGlobalChainHighCoverage.lean` and `CappedGlobalChainHighReplay.lean` rewrite with them instead of unfolding.
- `lake exe check-decls` rejects `opaque` declarations, which the kernel cannot unfold.
  The four sampling instances `randomizerOutputsSampleableType` (`Deterministic/TableSigner.lean`), `bottomSampleable`, `topOtsSampleable` and `topRndSampleable` (`Bridge/Program.lean`) are `@[irreducible] noncomputable def` instead.

The other files keep leanerVM's style, not EthLib's, so they can be compared with leanerVM file by file.
