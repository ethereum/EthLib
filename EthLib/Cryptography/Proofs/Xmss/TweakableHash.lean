module

public import EthLib.Cryptography.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: the leanXMSS tweakable hash

A hash input determines its public parameter, its address and its payload.

So two calls hash the same bytes only when they are the same call.

A derivation from the seed with an empty suffix hashes `P | A | S`.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- Byte `i` of a half of a hash value is byte `16 h + i` of the value, for half `h`. -/
theorem getElem_halfOf (half : Fin 2) (full : Vector UInt8 32) (i : Nat) (hi : i < DIGEST_LEN) :
    (halfOf half full)[i] =
      full[16 * half.val + i]'(by have := half.isLt; simp only [DIGEST_LEN] at hi; omega) := by
  simp only [halfOf, Vector.getElem_cast, Vector.getElem_extract]

/-- A half of a hash value is the vector of its 16 bytes, read one by one. -/
theorem halfOf_eq_ofFn (half : Fin 2) (full : Vector UInt8 32) :
    halfOf half full = Vector.ofFn fun i => full[16 * half.val + i.val]'(by
      have := half.isLt
      have := i.isLt
      simp only [DIGEST_LEN] at *
      omega) :=
  Vector.ext fun i hi => by rw [getElem_halfOf _ _ _ hi, Vector.getElem_ofFn]

/-- `P | A | M` determines `P`, `A` and `M`. -/
theorem thInput_inj {pp pp' : PublicParam} {a a' : Address} {m m' : ByteArray}
    (h : thInput pp a m = thInput pp' a' m') : pp = pp' ∧ a = a' ∧ m = m' := by
  -- The first 32 bytes are the two fixed-size prefixes, the rest is the payload.
  obtain ⟨hpre, hm⟩ := HashSig.byteArray_append_inj h (by simp)
  obtain ⟨hpp, ha⟩ := HashSig.byteArray_append_inj hpre (by simp)
  exact ⟨packBytes_injective hpp, packBytes_injective ha, hm⟩

/-- A derivation with an empty suffix hashes `P | A | S`.

The public parameter and the chain starts are halves of such derivations. -/
theorem seedPrf_empty {m : Type → Type} (H : ByteArray → m (Vector UInt8 32)) (s : Seed)
    (pp : PublicParam) (address : Address) :
    seedPrf H s pp address .empty = H (thInput pp address (packBytes s)) := by
  simp only [seedPrf, ByteArray.append_empty]

end EthLib.Cryptography.Xmss
