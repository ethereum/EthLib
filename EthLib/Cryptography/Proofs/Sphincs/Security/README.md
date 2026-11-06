# leanSPHINCS security proof

This directory will hold a proof that leanSPHINCS is strongly unforgeable in the random oracle model.
The bound will give 127 bits of classical security for up to `2^30` signatures with one key.
Strong unforgeability means that an adversary who sees signatures of messages of its choice cannot produce a new valid pair of message and signature.
This includes a second signature of a message already signed.
The random oracle model treats the hash as an ideal random function that everyone, the adversary included, can only query.

The proof is a port, and it lands in parts.
So far it holds the model of the scheme and its lemmas, generic probability bounds and the first step of the game hops.
It also holds the first lemmas of the later steps.
The theorem itself is not stated here yet.
Nothing in this directory is a security claim about EthLib's leanSPHINCS until the last part connects the model to EthLib's algorithms.

## The model

The proof does not reason about EthLib's algorithms directly.
It reasons about a model of leanSPHINCS: a functional description of key generation, signing and verification, with every hash a query to the random oracle.
The model is generic over a class of parameters.
They are the height of the key, its layers, the shape of the FORS forest and the cap on signatures.
The configuration that the proof uses has three layers of heights 10, 8 and 8, and a FORS forest of 24 trees of height 10.

`SphincsSecurity/Scheme.lean` defines the model.
Its hash inputs are byte lists, and its hash outputs are 256-bit vectors.
Its oracle world is a uniform sampler together with a hash oracle from byte lists to 256-bit outputs.
`SphincsSecurity/Statement.lean` defines the model's unforgeability game, and what it means for that game to have a given number of bits of classical security.
The files in `SphincsSecurity/Scheme/` prove facts about the model.
These facts cover the byte layout of its hash inputs, the encoding of digests and the recovery of public values from a signature.
They also cover correctness, the search for a valid encoding and the cost of a verification.

The files in `SphincsSecurity/Base/` prove probability bounds that do not mention the scheme.
They bound potentials of independent disclosures, and they bound tails with Chernoff and Poisson estimates.
`Base/Prelude.lean` holds generic lemmas about counted queries and uniform tables.

The files in `SphincsSecurity/Seed/` prepare the step that removes the hidden key seed from the game.
`Seed/Model.lean` describes the hash outputs that key generation derives from the seed, and the cache that programs them.
`Seed/Coupling.lean` proves that sampling these outputs and programming them into the cache before a computation leaves its distribution unchanged.

The other directories hold the first files of the later steps.
`Classification/` starts the description of what an accepted forgery must contain.
`ScanSigner/`, `GraphView/` and `LazyRun/` start the analysis of the signer's hash calls, their cost, and a run whose hidden values are sampled only when read.
`Reduction/` starts to move the oracle and the seed out of the game.
`CoverBound/` and `CoverPotential/` start the bound on the chance that a forgery covers every FORS tree.
`Configurations.lean` proves, for the configuration of the proof, the size of a serialized signature and the cost of a verification.

A later part will bridge the model to EthLib's leanSPHINCS, in `EthLib/Cryptography/Sphincs/`.
Some hash calls are made by EthLib and not by the model, or the other way round.
The bridge will treat them as calls answered from the oracle's cache.

## Source

The proof is adapted from [leanEthereum/leanVM](https://github.com/leanEthereum/leanVM) at commit [`1753fde3ee06e534db39487c88a13e29d4ed05bf`](https://github.com/leanEthereum/leanVM/tree/1753fde3ee06e534db39487c88a13e29d4ed05bf/formal/lean_sphincs), directory `formal/lean_sphincs/`.

## License

These files are under CC0, like the rest of EthLib (`LICENSE` at the root).
leanVM ships them under MIT or Apache-2.0, and their copyright holder, leanEthereum, releases them to EthLib under CC0.

## What changed here

leanVM builds the proof with Lean v4.31.0, Mathlib `fabf563a` and VCVio `cbd4144b`.
EthLib builds with Lean v4.35.0, VCVio `bbf05eee` and the Mathlib that this VCVio uses.
The changes that follow from this are:

- VCVio now gives the distribution of a computation as a Mathlib measure, not as a sub-probability mass function.
  So a statement that two computations have the same distribution now says that they are equal in distribution.
  This means that every event has the same probability under both.
  The lemmas about uniform samples, events and sums of point masses use the new names of VCVio.
- VCVio's query cache is now a structure, not a function, so a cache is built and read through its constructor and its lookup.
- The modules use Lean's module system, as all of EthLib does.
  VCVio's tracing handler is not exposed to importers.
  So two statements about the hash trace of a computation are proved by simplification, not by definitional unfolding.
- On Lean v4.35.0 the simplifier does not read the length of a byte encoding of a fixed-width digest through the width's arithmetic.
  `Scheme/Bytes.lean` gains lemmas for the lengths of the byte widths that the model uses.
  Some files set the option that lets definitional unfolding cross reducibility boundaries, each with a comment that says why.
- `Scheme/Uniform.lean` gains a lemma: the first coordinate of a uniform pair is uniform.
- The Mathlib that EthLib uses has no uniform probability mass function of a finite type.
  So `Base/Prelude.lean` states its lemmas about uniform products and uniform tables for uniform samples, as equalities in distribution.
- The fixed-function worlds of the reduction answer hash queries from a fixed function and make private draws.
  leanVM runs them in Mathlib's probability mass functions, and the Mathlib that EthLib uses has no uniform one of a finite type.
  Here they are probabilistic computations, and a private draw is a query to the uniform oracle.
  Two of their lemmas then hold as equalities of computations, which is stronger than the equalities of distributions of the source.
- `Base/Prelude.lean` gains a lemma: two independent draws have the same joint distribution in either order.
- `Base/Domination.lean` and `Base/Virtual.lean` import the parts of Mathlib that they use instead of all of Mathlib.
  A file that imports all of Mathlib needs more memory than EthLib's limit per file.
- `LazyRun/Reveal.lean` states that revealing a coordinate commutes with sampling the rest of a uniform table as an equality in distribution.
- `lake exe check-decls` rejects `opaque` declarations, so the sampling instance of `Seed/Model.lean` is an irreducible definition instead.
- No file raises the heartbeat limit.
- Arguments that the simplifier does not use, deprecated lemma names and unused section variables are removed, so the files build without warnings.

The other changes are names and documentation:

- The root namespace `FORS` is renamed `SphincsSecurity`, because in EthLib FORS names a part of the scheme, not the whole proof.
- The Lean documentation follows EthLib's rules for doc comments: one sentence per line, at most 100 characters, no declaration names, and ASCII math.
