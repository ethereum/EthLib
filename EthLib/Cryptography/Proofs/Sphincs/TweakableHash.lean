module

public import EthLib.Cryptography.Sphincs.TweakableHash
public import EthLib.Cryptography.Proofs.HashSig

/-!
# Proofs: the leanSPHINCS tweakable hash

A hash input determines its `PK.seed`, its address and its payload.

So two calls hash the same bytes only when they are the same call.

With the address proofs, distinct call sites of one key never hash the same input.

`Trunc_n` keeps the first `n` bytes of the hash, in order.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- `PK.seed | ADRS | M` determines `PK.seed`, `ADRS` and `M`. -/
theorem thInput_inj {pkSeed pkSeed' : PkSeed} {a a' : Adrs} {m m' : ByteArray}
    (h : thInput pkSeed a m = thInput pkSeed' a' m') : pkSeed = pkSeed' ∧ a = a' ∧ m = m' := by
  -- The first 48 bytes are the two fixed-size prefixes, the rest is the payload.
  obtain ⟨hpre, hm⟩ := HashSig.byteArray_append_inj h (by simp)
  obtain ⟨hseed, ha⟩ := HashSig.byteArray_append_inj hpre (by simp)
  exact ⟨Base.packBytes_injective hseed, Base.packBytes_injective ha, hm⟩

/-- A hash input has the 48 bytes of `PK.seed | ADRS`, then the payload. -/
@[simp] theorem size_thInput (pkSeed : PkSeed) (a : Adrs) (m : ByteArray) :
    (thInput pkSeed a m).size = PREFIX_LEN + m.size := by
  simp only [thInput, ByteArray.size_append, Base.size_packBytes, PREFIX_LEN]

/-- A `PRF` input is `PK.seed | ADRS | SK.seed`, 80 bytes. -/
theorem size_thInput_seed (pkSeed : PkSeed) (a : Adrs) (skSeed : Seed) :
    (thInput pkSeed a (packBytes skSeed)).size = 80 := by
  rw [size_thInput, Base.size_packBytes]
  rfl

/-- Byte `i` of `Trunc_r(x)` is byte `i` of `x`. -/
@[simp] theorem getElem_trunc {k r : Nat} (x : Vector UInt8 k) (h : r ≤ k) (i : Nat) (hi : i < r) :
    (trunc r x h)[i] = x[i] := by
  simp [trunc]

/-- `Trunc_r(x)` is the first `r` bytes of `x`. -/
theorem toList_trunc {k r : Nat} (x : Vector UInt8 k) (h : r ≤ k) :
    (trunc r x h).toList = x.toList.take r := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i hi _
    simp

end EthLib.Cryptography.Sphincs
