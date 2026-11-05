module

public import EthLib.Cryptography.Sphincs.TweakableHash
public import EthLib.Cryptography.Proofs.HashSig

/-!
# Proofs: the leanSPHINCS tweakable hash

A hash input determines its public parameter, its address and its payload.

So two calls hash the same bytes only when they are the same call.

With the address proofs, distinct call sites of one key never hash the same input.

A derivation from the seed with an empty suffix hashes the parameter, the address and the seed.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- `P | A | M` determines `P`, `A` and `M`. -/
theorem thInput_inj {pp pp' : PublicParam} {a a' : Address} {m m' : ByteArray}
    (h : thInput pp a m = thInput pp' a' m') : pp = pp' ∧ a = a' ∧ m = m' := by
  -- The first 32 bytes are the two fixed-size prefixes, the rest is the payload.
  obtain ⟨hpre, hm⟩ := HashSig.byteArray_append_inj h (by simp)
  obtain ⟨hpp, ha⟩ := HashSig.byteArray_append_inj hpre (by simp)
  exact ⟨Base.packBytes_injective hpp, Base.packBytes_injective ha, hm⟩

/-- A derivation with an empty suffix hashes `P' | A | S`.

The public parameter, the chain starts and the FORS secrets are such derivations. -/
theorem seedPrf_empty {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32)) (s : Seed)
    (pp : PublicParam) (address : Address) :
    seedPrf H s pp address .empty = thFull H pp address (packBytes s) := by
  simp only [seedPrf, ByteArray.append_empty]

/-- The two halves of a hash output, side by side, are the output. -/
theorem halfOf_append (full : HashOutput) : halfOf 0 full ++ halfOf 1 full = full := by
  ext i hi
  simp only [halfOf, Vector.getElem_append, Vector.getElem_ofFn]
  split <;> congr 1 <;> simp only [N] at * <;> omega

end EthLib.Cryptography.Sphincs
