module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Lemmas

/-!
# Byte encodings

The `n`-byte little-endian and big-endian encodings of a bit vector are injective.

Both have length `n`, and this file gives the lengths of the payloads and hash inputs.

The 32 address bytes of a hash call determine every word of the address.
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
@[simp] theorem bytesLE_length_digest (x : Digest) : (bytesLE 16 x).length = 16 :=
  bytesLE_length 16 x

omit [Params] in
@[simp] theorem bytesLE_length_parameter (x : PublicParameter) : (bytesLE 16 x).length = 16 :=
  bytesLE_length 16 x

omit [Params] in
@[simp] theorem bytesLE_length_hashOutput (x : HashOutput) : (bytesLE 32 x).length = 32 :=
  bytesLE_length 32 x

omit [Params] in
@[simp] theorem bytesLE_length_message (x : Message) : (bytesLE 32 x).length = 32 :=
  bytesLE_length 32 x

omit [Params] in
/-- Two naturals below `2^w` with the same `w`-bit vector are equal. -/
theorem ofNat_inj_of_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

omit [Params] in
theorem bytesBE_length (n : Nat) (x : BitVec (8 * n)) : (bytesBE n x).length = n := by
  simp [bytesBE]

omit [Params] in
@[simp] theorem bytesBE_length_4 (x : BitVec 32) : (bytesBE 4 x).length = 4 :=
  bytesBE_length 4 x

omit [Params] in
@[simp] theorem bytesBE_length_12 (x : BitVec 96) : (bytesBE 12 x).length = 12 :=
  bytesBE_length 12 x

omit [Params] in
@[simp] theorem bytesBE_length_counter (x : Counter) : (bytesBE 4 x).length = 4 :=
  bytesBE_length 4 x

omit [Params] in
/-- Two bit vectors with the same big-endian bytes are equal. -/
theorem bytesBE_injective {n : Nat} {x y : BitVec (8 * n)} (h : bytesBE n x = bytesBE n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : n - 1 - i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨n - 1 - i / 8, hj⟩
  have hidx : n - 1 - (n - 1 - i / 8) = i / 8 := by omega
  simp only [hidx] at hbyte
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

omit [Params] in
theorem flatMap_bytesLE_length' (values : List (BitVec (8 * 16))) :
    (values.flatMap (bytesLE 16)).length = 16 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]
      ring

omit [Params] in
theorem flatMap_bytesLE_length (values : List Digest) :
    (values.flatMap (bytesLE 16)).length = 16 * values.length :=
  flatMap_bytesLE_length' values

omit [Params] in
theorem ofFn_flatMap_bytesLE_length {n : Nat} (values : Fin n → Digest) :
    ((List.ofFn values).flatMap (bytesLE 16)).length = 16 * n := by
  rw [flatMap_bytesLE_length, List.length_ofFn]

omit [Params] in
theorem nodePayload_length (left right : Digest) :
    (Concrete.nodePayload left right).length = 32 := by
  simp [Concrete.nodePayload]

omit [Params] in
theorem leafPayload_length (endpoints : ChainIndex → Digest) :
    (Concrete.leafPayload endpoints).length = 1024 := by
  rw [Concrete.leafPayload, ofFn_flatMap_bytesLE_length]
  rfl

theorem rootsPayload_length (roots : ForsKey) :
    (Concrete.rootsPayload roots).length = 16 * forsTrees := by
  rw [Concrete.rootsPayload, ofFn_flatMap_bytesLE_length]

omit [Params] in
theorem rootPayload_length (root : Digest) : (Concrete.rootPayload root).length = 16 :=
  bytesLE_length 16 root

theorem tweakableHashInput_length (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (tweakableHashInput parameter domain payload).length = 48 + payload.length := by
  simp [tweakableHashInput, tweakBytes, fieldBytes]
  omega

theorem keygenHashInput_length (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : (keygenHashInput parameter domain seed).length = 80 := by
  simp [keygenHashInput, fieldBytes]

omit [Params] in
/-- The 32 address bytes determine every word of the address. -/
theorem fieldBytes_injective {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) :
    t1 = t2 := by
  obtain ⟨layer1, tree1, tag1, key1, height1, index1⟩ := t1
  obtain ⟨layer2, tree2, tag2, key2, height2, index2⟩ := t2
  simp only [fieldBytes] at h
  obtain ⟨h, hindex⟩ := List.append_inj' h (by simp [bytesBE_length])
  obtain ⟨h, hheight⟩ := List.append_inj' h (by simp [bytesBE_length])
  obtain ⟨h, hkey⟩ := List.append_inj' h (by simp [bytesBE_length])
  obtain ⟨h, htag⟩ := List.append_inj' h (by simp [bytesBE_length])
  obtain ⟨hlayer, htree⟩ := List.append_inj' h (by simp [bytesBE_length])
  simp only [bytesBE_injective hlayer, bytesBE_injective htree, bytesBE_injective htag,
    bytesBE_injective hkey, bytesBE_injective hheight, bytesBE_injective hindex]

end SphincsSecurity
