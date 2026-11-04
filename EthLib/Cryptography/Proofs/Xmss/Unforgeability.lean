module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Queries

/-!
# Proofs: leanXMSS as EthLib computes it is unforgeable

Source: the leanXMSS specification draft, section "Security".

The theorem holds in the random oracle model.

Take an adversary whose experiment makes at most `q >= 1` hash calls.

It forges a signature with probability at most `q / 2^127`.

`q` counts every hash call of the experiment, the signer's and key generation's included.

Key generation alone makes about `2^23.7` calls.

A signing request can make more than `2^33`, when its randomizer trials keep missing.

So the bound is never below about `2^-103.3`, and each signing request adds more than `2^-94`.

With all `2^32` leaf indices signed, `q` exceeds `2^65`, and the bound exceeds `2^-62`.

The same bound is restated with the adversary's hash queries `qH` and signing requests `qS` apart.

It is at most `(qH + 8,630,239,199 * qS + 13,435,265) / 2^127`.

A signing request is charged the most hash calls the signer can make, about `2^33.007`.

The game runs EthLib's key generation, signing and verification.

Their hash `H` is a query to the oracle.

The security proof in `Security/` reasons over EthLib's algorithms too.

It compares them with a model of the scheme with precomputed keys, its own game-hopping device:

- EthLib's bytes, addresses and codewords are the model's.
- Each hashing routine of EthLib is the model's, call for call.
- EthLib's adversary is one of the model's.
- EthLib's game wins as often as the real game of the proof.

EthLib's signer gets the seed `S_0` and re-derives `S` and `P` with two hash calls.

Key generation made those calls first, so they return cached answers and change nothing.

They still count toward the budget `q`, so the bound holds as stated.
-/

@[expose] public section

/-! The build fails if the theorem ever depends on more than Lean's three standard axioms. -/

/--
info: 'EthLib.Cryptography.Xmss.Unforgeability.unforgeable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EthLib.Cryptography.Xmss.Unforgeability.unforgeable

/--
info: 'EthLib.Cryptography.Xmss.Unforgeability.unforgeable_queries' depends on axioms:
    [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EthLib.Cryptography.Xmss.Unforgeability.unforgeable_queries
