import EthLib.Cryptography.Xmss.TweakableHash
import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: `Xmss.TweakableHash`

A hash input determines its public parameter, its address and its payload.

So two calls hash the same bytes only when they are the same call.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- Two concatenations with first parts of the same size agree part by part. -/
theorem byteArray_append_inj {a b c d : ByteArray} (h : a ++ b = c ++ d) (hs : a.size = c.size) :
    a = c ∧ b = d := by
  have := congrArg ByteArray.data h
  simp only [ByteArray.data_append] at this
  obtain ⟨ha, hb⟩ := Array.append_inj this hs
  exact ⟨ByteArray.ext ha, ByteArray.ext hb⟩

/-- `P | A | M` determines `P`, `A` and `M`. -/
theorem thInput_inj {pp pp' : PublicParam} {a a' : Address} {m m' : ByteArray}
    (h : thInput pp a m = thInput pp' a' m') : pp = pp' ∧ a = a' ∧ m = m' := by
  -- The first 32 bytes are the two fixed-size prefixes, the rest is the payload.
  obtain ⟨hpre, hm⟩ := byteArray_append_inj h (by simp)
  obtain ⟨hpp, ha⟩ := byteArray_append_inj hpre (by simp)
  exact ⟨packBytes_injective hpp, packBytes_injective ha, hm⟩

end EthLib.Cryptography.Xmss
