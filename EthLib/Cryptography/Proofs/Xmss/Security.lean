import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity

/-!
# Proofs: leanXMSS security in the random oracle model

The proof that leanXMSS has 127 bits of classical security, as the leanXMSS note states it in its section "Security".

```text
    for every q >= 1 and every adversary whose experiment makes at most q hash calls:
    Pr[strong forgery] <= q / 2^127
```

The theorem is `XmssSecurity.leanXmss_has_127_bits_of_classical_security`, of statement `LeanXmss.LeanXmssSecurityStatement`.

It is about the scheme as the proof writes it, in the namespace `LeanXmss`.

`Security/README.md` says where the proof comes from and what changed here.
-/
