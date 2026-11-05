module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Lemmas

/-!
# Byte encodings

The `n`-byte little-endian encoding of a bit vector is injective and has length `n`.

The 16 address bytes of a hash call determine all the fields of the address.
-/

@[expose] public section

namespace SphincsSecurity

variable [Params]

omit [Params] in
/-- Two bit vectors with the same little-endian bytes are equal. -/
theorem bytesLE_injective {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

omit [Params] in
theorem bytesLE_length (n : Nat) (x : BitVec (8 * n)) : (bytesLE n x).length = n := by
  simp [bytesLE]

omit [Params] in
@[simp] theorem bytesLE_length_1 (x : BitVec 8) : (bytesLE 1 x).length = 1 :=
  bytesLE_length 1 x

omit [Params] in
@[simp] theorem bytesLE_length_3 (x : BitVec 24) : (bytesLE 3 x).length = 3 :=
  bytesLE_length 3 x

omit [Params] in
@[simp] theorem bytesLE_length_4 (x : BitVec 32) : (bytesLE 4 x).length = 4 :=
  bytesLE_length 4 x

omit [Params] in
@[simp] theorem bytesLE_length_16 (x : BitVec 128) : (bytesLE 16 x).length = 16 :=
  bytesLE_length 16 x

omit [Params] in
@[simp] theorem bytesLE_length_32 (x : BitVec 256) : (bytesLE 32 x).length = 32 :=
  bytesLE_length 32 x

omit [Params] in
/-- Two naturals below `2^w` with the same `w`-bit vector are equal. -/
theorem ofNat_inj_of_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

omit [Params] in
/-- A concatenation determines its two halves. -/
theorem bitVec_append_inj {n m : Nat} {a a' : BitVec n} {b b' : BitVec m}
    (h : a ++ b = a' ++ b') : a = a' ∧ b = b' := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v : BitVec (n + m) => v.getLsbD (m + i)) h
    simpa [BitVec.getLsbD_append] using this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v : BitVec (n + m) => v.getLsbD i) h
    simpa [BitVec.getLsbD_append, hi] using this

omit [Params] in
/-- The 16 address bytes determine the type, the step, the layer, the tree and the two fields. -/
theorem fieldBytes_injective {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) :
    t1 = t2 := by
  obtain ⟨tag1, step1, layer1, tree1, hi1, lo1⟩ := t1
  obtain ⟨tag2, step2, layer2, tree2, hi2, lo2⟩ := t2
  simp only [fieldBytes] at h
  obtain ⟨h, _⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, htree⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hlayer⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, htag⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hlo, hhi⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hstep, htag⟩ := bitVec_append_inj (bytesLE_injective htag)
  simp only [bytesLE_injective hlo, bytesLE_injective hhi, bytesLE_injective hlayer,
    bytesLE_injective htree, hstep, htag]

end SphincsSecurity
