module

public import EthLib.Cryptography.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: the leanXMSS tweakable hash

A hash input determines its public parameter, its address and its payload.

So two calls hash the same bytes only when they are the same call.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- `P | A | M` determines `P`, `A` and `M`. -/
theorem thInput_inj {pp pp' : PublicParam} {a a' : Address} {m m' : ByteArray}
    (h : thInput pp a m = thInput pp' a' m') : pp = pp' ∧ a = a' ∧ m = m' := by
  -- The first 32 bytes are the two fixed-size prefixes, the rest is the payload.
  obtain ⟨hpre, hm⟩ := HashSig.byteArray_append_inj h (by simp)
  obtain ⟨hpp, ha⟩ := HashSig.byteArray_append_inj hpre (by simp)
  exact ⟨packBytes_injective hpp, packBytes_injective ha, hm⟩

end EthLib.Cryptography.Xmss
