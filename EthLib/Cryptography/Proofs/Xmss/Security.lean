import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Security

/-!
# Proofs: the security proof of leanXMSS, over EthLib's algorithms

The proof that the real game of leanXMSS is won with probability at most `q / 2^127`.

```text
    for every q >= 1 and every adversary whose real game makes at most q hash calls:
    Pr[strong forgery] <= q / 2^127
```

The real game runs EthLib's own algorithms, with a signer that keeps the scheme seed `S` and the
parameter `P`.

The theorem is `XmssSecurity.Bridge.realGame_security`.

`Unforgeability.lean` carries it to EthLib's game, whose signer re-derives `S` and `P`.

`Security/README.md` says where the proof comes from and what changed here.
-/
