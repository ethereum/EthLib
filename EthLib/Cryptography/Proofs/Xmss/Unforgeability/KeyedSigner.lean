module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Game
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.SignerReplay

/-!
# Strong unforgeability of the keyed leanXMSS signer

The keyed signer has the same forgery probability as the stateless signer.

The stateless security bound therefore applies to EthLib’s signer.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability

/-- **leanXMSS as EthLib computes it is strongly unforgeable in the random oracle model.**

The signer keeps its key across requests, as a real signer does.

Take an adversary whose game with the stateless signer makes at most `q >= 1` hash calls.

It forges with probability at most `q / 2^127`.

`q` counts the calls of key generation and of every signing request too.

A signing request of the stateless signer can make more than `2^33` calls.

So `2^32` requests give `q > 2^65`, and over the key's lifetime the bound is above `2^-62`. -/
theorem unforgeable : HasClassicalSecurityBits 127 := fun q hq adversary hbound =>
  (forgeAdvantage_eq_statelessForgeAdvantage adversary).trans_le
    (statelessForgeAdvantage_le q hq adversary hbound)

end EthLib.Cryptography.Xmss.Unforgeability
