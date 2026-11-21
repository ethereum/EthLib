module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Security

/-!
# Proofs: the security proof of leanXMSS, over EthLib's algorithms

The proof that the real game of leanXMSS is won with probability at most `q / 2^127`.

```text
    for every q >= 1 and every adversary whose real game makes at most q hash calls:
    Pr[strong forgery] <= q / 2^127
```

Here `q` counts every hash call of the game in the worst run, the signer's included.

With all `2^32` leaf indices signed, `q` exceeds `2^64`, and the bound exceeds `2^-63`.

The real game runs EthLib's own algorithms.

Its signer keeps its key across requests.

The unforgeability module proves that EthLib's game is the real game.

The README of the security proof says where the proof comes from and what changed here.
-/
