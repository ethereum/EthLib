module

public import EthLib.Serialization.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Class

/-!
# Proofs: basic typed SSZ values are lawful

Booleans, the unsigned integers and fixed byte vectors convert to SSZ values and back.

An integer type holds exactly the numbers below its bound, so its conversions are inverse.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType

/-- An integer read back at a width is a number below the width's bound, made into a value. -/
theorem SszType.ofUint_ok {α : Type} {width : Nat} {make : Nat → α} {value : Value} {a : α} :
    ofUint width make value = .ok a ↔ ∃ n, value = .uint n ∧ n < 2 ^ (8 * width) ∧ make n = a := by
  cases value with
  | uint n => by_cases below : n < 2 ^ (8 * width) <;> simp [ofUint, below]
  | _ => simp [ofUint]

/-- An integer read straight from its bytes is the one the untyped decoder reads. -/
theorem SszType.decodeUint_eq {α : Type} (width : Nat) (make : Nat → α) (data : ByteArray) :
    decodeUint width make data =
      (do ofUint width make (← Ssz.deserialize (.uint width) data.data)) := by
  unfold decodeUint
  by_cases size : data.size = width
  · have below := readUint_lt data.data 0 width
    simp [Ssz.deserialize, ByteArray.size_data, size, readUintBytes_eq, ofUint, below]
  · simp [Ssz.deserialize, ByteArray.size_data, size]
    rfl

/-- The bytes pushed for an integer are its little-endian bytes, after the bytes so far. -/
theorem SszType.data_pushUintBytes (width n : Nat) (out : ByteArray) :
    (pushUintBytes width n out).data = out.data ++ uintBytes width n := by
  induction width generalizing n out with
  | zero => simp [pushUintBytes, uintBytes_zero]
  | succ width ih =>
    rw [pushUintBytes, ih, uintBytes_succ, ← Array.append_assoc, ByteArray.data_push,
      ← UInt8.ofNat_mod_size (x := n)]
    rfl

/-- An integer that fits its width, written straight to bytes, gives the untyped encoder's bytes. -/
theorem SszType.encodeUint_eq (width n : Nat) (below : n < 2 ^ (8 * width)) :
    encodeUint width n = (do return ⟨← Ssz.serialize (.uint width) (.uint n)⟩) := by
  have bytes : pushUintBytes width n (ByteArray.emptyWithCapacity width) = ⟨uintBytes width n⟩ := by
    cases h : pushUintBytes width n (ByteArray.emptyWithCapacity width) with
    | mk data =>
      have := data_pushUintBytes width n (ByteArray.emptyWithCapacity width)
      rw [h] at this
      simp only at this
      rw [this, show (ByteArray.emptyWithCapacity width).data = #[] from rfl, Array.empty_append]
  simp [encodeUint, bytes, Ssz.serialize, below, bind, Except.bind, pure, Except.pure]

/--
An integer type is lawful when its numbers are exactly those below the bound of its width.

The width must be one of the six that SSZ defines.

The root, the bytes and the decoding must be the untyped ones.
-/
theorem LawfulSszType.ofUint {α : Type} [SszType α] {width : Nat} (toNat : α → Nat)
    (ofNat : Nat → α) (declared : desc α = .uint width)
    (sized : [1, 2, 4, 8, 16, 32].contains width = true)
    (written : ∀ a, toValue a = .uint (toNat a)) (read : ofValue (α := α) = ofUint width ofNat)
    (bounded : ∀ a, toNat a < 2 ^ (8 * width)) (left : ∀ a, ofNat (toNat a) = a)
    (right : ∀ n, n < 2 ^ (8 * width) → toNat (ofNat n) = n)
    (rooted : ∀ a : α, SszType.root a = Ssz.hashTreeRoot (desc α) (toValue a) := by intro; rfl)
    (encoded : ∀ a : α, SszType.encode a = (do return ⟨← Ssz.serialize (desc α) (toValue a)⟩) := by
      intro; rfl)
    (decoded : ∀ data : ByteArray,
      SszType.decode data = (do ofValue (α := α) (← Ssz.deserialize (desc α) data.data)) := by
      intro; rfl) :
    LawfulSszType α where
  wellFormed := by simp only [declared, Desc.wellFormed, sized, ↓reduceIte]
  fits a := by rw [declared, written]; exact .uint (bounded a)
  ofValue_toValue a := by rw [read, written, ofUint_ok]; exact ⟨_, rfl, bounded a, left a⟩
  toValue_of_ofValue {value a} made := by
    rw [read, ofUint_ok] at made
    obtain ⟨n, rfl, below, rfl⟩ := made
    rw [written, right n below]
  ofValue_ne_error {value fault} fits made := by
    rw [declared] at fits
    cases fits with
    | uint bound =>
      rw [read] at made
      simp [SszType.ofUint, bound] at made
  root_eq := rooted
  encode_eq := encoded
  decode_eq := decoded

instance : LawfulSszType Bool where
  wellFormed := rfl
  fits b := .bool b
  ofValue_toValue _ := rfl
  toValue_of_ofValue {value _} made := by
    cases value <;> cases made <;> rfl
  ofValue_ne_error {value fault} fits made := by
    cases fits
    simp [ofValue] at made
  decode_eq data := by
    have get : data[0]? = data.data[0]? := by
      by_cases h : 0 < data.size
      · simp [h, ByteArray.size_data]
        rfl
      · simp [h, ByteArray.size_data]
    have kind : SszType.desc Bool = .bool := rfl
    by_cases size : data.size = 1
    · simp only [decode, kind, Ssz.deserialize, ByteArray.size_data, get, size, bne_self_eq_false,
        Bool.false_eq_true, ite_false]
      split <;> split <;> simp_all [ofValue] <;> rfl
    · simp [decode, kind, Ssz.deserialize, ByteArray.size_data, size]
      rfl

instance : LawfulSszType UInt8 :=
  .ofUint UInt8.toNat UInt8.ofNat rfl rfl (fun _ => rfl) rfl UInt8.toNat_lt
    (fun _ => UInt8.ofNat_toNat) (fun _ below => UInt8.toNat_ofNat_of_lt' below)
    (encoded := fun a => encodeUint_eq 1 a.toNat (by simpa using a.toNat_lt))
    (decoded := decodeUint_eq 1 UInt8.ofNat)

instance : LawfulSszType UInt16 :=
  .ofUint UInt16.toNat UInt16.ofNat rfl rfl (fun _ => rfl) rfl UInt16.toNat_lt
    (fun _ => UInt16.ofNat_toNat) (fun _ below => UInt16.toNat_ofNat_of_lt' below)
    (encoded := fun a => encodeUint_eq 2 a.toNat (by simpa using a.toNat_lt))
    (decoded := decodeUint_eq 2 UInt16.ofNat)

instance : LawfulSszType UInt32 :=
  .ofUint UInt32.toNat UInt32.ofNat rfl rfl (fun _ => rfl) rfl UInt32.toNat_lt
    (fun _ => UInt32.ofNat_toNat) (fun _ below => UInt32.toNat_ofNat_of_lt' below)
    (encoded := fun a => encodeUint_eq 4 a.toNat (by simpa using a.toNat_lt))
    (decoded := decodeUint_eq 4 UInt32.ofNat)

instance : LawfulSszType UInt64 :=
  .ofUint UInt64.toNat UInt64.ofNat rfl rfl (fun _ => rfl) rfl UInt64.toNat_lt
    (fun _ => UInt64.ofNat_toNat) (fun _ below => UInt64.toNat_ofNat_of_lt' below)
    (encoded := fun a => encodeUint_eq 8 a.toNat (by simpa using a.toNat_lt))
    (decoded := decodeUint_eq 8 UInt64.ofNat)

instance : LawfulSszType (BitVec 128) :=
  .ofUint BitVec.toNat (BitVec.ofNat 128) rfl rfl (fun _ => rfl) rfl BitVec.isLt
    (fun _ => by simp) (fun _ below => Nat.mod_eq_of_lt below)
    (encoded := fun a => encodeUint_eq 16 a.toNat a.isLt)
    (decoded := decodeUint_eq 16 (BitVec.ofNat 128))

instance : LawfulSszType Base.U256 :=
  .ofUint BitVec.toNat (BitVec.ofNat 256) rfl rfl (fun _ => rfl) rfl BitVec.isLt
    (fun _ => by simp) (fun _ below => Nat.mod_eq_of_lt below)
    (encoded := fun a => encodeUint_eq 32 a.toNat a.isLt)
    (decoded := decodeUint_eq 32 (BitVec.ofNat 256))

instance {n : Nat} [NeZero n] : LawfulSszType (Vector UInt8 n) where
  wellFormed := by simp [desc, Desc.wellFormed, NeZero.ne n]
  fits v := .byteVector v.size_toArray
  ofValue_toValue v := by simp [toValue, ofValue, v.size_toArray]
  toValue_of_ofValue {value _} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    -- Only bytes of the declared count read back, as the vector that holds them.
    rename_i data
    by_cases exact : data.size = n
    · simp only [exact, dite_true, Except.ok.injEq] at made
      subst made
      rfl
    · simp [exact] at made
  ofValue_ne_error {value fault} fits made := by
    cases fits with
    | byteVector exact => simp [ofValue, exact] at made
  encode_eq v := by
    by_cases wide : n ≥ 2 ^ (8 * bytesPerOffset)
    · simp [encode, desc, toValue, Ssz.serialize, wide, v.size_toArray, bind, Except.bind, throw,
        throwThe, MonadExceptOf.throw]
    · simp [encode, desc, toValue, Ssz.serialize, wide, v.size_toArray, bind, Except.bind, pure,
        Except.pure]

end EthLib.Serialization.Ssz
