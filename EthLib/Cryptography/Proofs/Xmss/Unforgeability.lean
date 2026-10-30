import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Game

/-!
# Proofs: leanXMSS as EthLib computes it is unforgeable

Source: the leanXMSS specification draft, section "Security".

`Unforgeability.unforgeable` holds in the random oracle model.

Take an adversary whose experiment makes at most `q >= 1` hash calls.

It forges a signature with probability at most `q / 2^127`.

The game (`Unforgeability/Statement.lean`) runs EthLib's own `keyGenWith`, `signWith` and
`verifyWith`.

Their hash `H` is a query to the oracle.

The security proof in `Security/` reasons over EthLib's algorithms too.

It compares them with a model of the scheme with precomputed keys, its own game-hopping device:

```text
    Bytes, Address, Codeword    EthLib's bytes, addresses and codewords are the model's
    Translate                   each hashing routine of EthLib is the model's, call for call
    Adversary                   EthLib's adversary is one of the model's
    Game                        EthLib's game wins as often as the real game of the proof
```

EthLib's signer gets the seed `S_0` and re-derives `S` and `P` with two hash calls.

Key generation made those calls first, so they return cached answers and change nothing.

They still count toward the budget `q`, so the bound holds as stated.
-/

/-! The build fails if the theorem ever depends on more than Lean's three standard axioms. -/

/--
info: 'EthLib.Cryptography.Xmss.Unforgeability.unforgeable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EthLib.Cryptography.Xmss.Unforgeability.unforgeable
