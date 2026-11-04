module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Security

/-!
# Proofs: the security proof of leanXMSS, over EthLib's algorithms

The proof that the real game of leanXMSS is won with probability at most `q / 2^127`.

```text
    for every q >= 1 and every adversary whose real game makes at most q hash calls:
    Pr[strong forgery] <= q / 2^127
```

The real game runs EthLib's own algorithms.

Its signer keeps the scheme seed `S` and the parameter `P`.

The unforgeability module carries the bound to EthLib's game, whose signer re-derives `S` and `P`.

The README of the security proof says where the proof comes from and what changed here.
-/
