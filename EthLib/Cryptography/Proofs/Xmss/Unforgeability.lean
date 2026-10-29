import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Game

/-!
# Proofs: leanXMSS as EthLib computes it is unforgeable

Source: the leanXMSS specification draft, section "Security".

`Unforgeability.unforgeable` holds in the random oracle model.

Take an adversary whose experiment makes at most `q >= 1` hash calls.

It forges a signature with probability at most `q / 2^127`.

The game (`Unforgeability/Statement.lean`) runs EthLib's own `keyGenWith`, `signWith` and `verifyWith`.

Their hash `H` is a query to the oracle.

The theorem comes from the security proof in `Security/`, about its own model of the scheme:

```text
    Bytes, Address, Codeword    EthLib's bytes, addresses and codewords are the model's
    Algorithms                  each of EthLib's algorithms is the model's, call for call
    Game                        EthLib's game is the model's, except two cached calls per signature
```

EthLib's signer gets the seed `S_0` and re-derives `S` and `P` with two hash calls.

Key generation made those calls first, so they return cached answers and change nothing.

They still count toward the budget `q`, so the bound holds as stated.
-/
