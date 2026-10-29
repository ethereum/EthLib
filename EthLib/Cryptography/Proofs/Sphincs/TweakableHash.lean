import EthLib.Cryptography.Sphincs.TweakableHash
import EthLib.Cryptography.Proofs.Xmss.TweakableHash

/-!
# Proofs: `Sphincs.TweakableHash`

A hash input determines its public parameter, its address and its payload.

So two calls hash the same bytes only when they are the same call.

With the address proofs, distinct call sites of one key never hash the same input.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- `P | A | M` determines `P`, `A` and `M`. -/
theorem thInput_inj {pp pp' : PublicParam} {a a' : Address} {m m' : ByteArray}
    (h : thInput pp a m = thInput pp' a' m') : pp = pp' ∧ a = a' ∧ m = m' := by
  -- The first 32 bytes are the two fixed-size prefixes, the rest is the payload.
  obtain ⟨hpre, hm⟩ := Xmss.byteArray_append_inj h (by simp)
  obtain ⟨hpp, ha⟩ := Xmss.byteArray_append_inj hpre (by simp)
  exact ⟨Xmss.packBytes_injective hpp, Xmss.packBytes_injective ha, hm⟩

/-- The two halves of a hash output, side by side, are the output. -/
theorem halfOf_append (full : HashOutput) : halfOf 0 full ++ halfOf 1 full = full := by
  ext i hi
  simp only [halfOf, Vector.getElem_append, Vector.getElem_ofFn]
  split <;> congr 1 <;> simp only [N] at * <;> omega

end EthLib.Cryptography.Sphincs
