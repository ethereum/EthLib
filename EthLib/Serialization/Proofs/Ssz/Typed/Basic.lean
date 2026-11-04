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

/--
An integer type is lawful when its numbers are exactly those below the bound of its width.

The width must be one of the six that SSZ defines.
-/
theorem LawfulSszType.ofUint {α : Type} [SszType α] {width : Nat} (toNat : α → Nat)
    (ofNat : Nat → α) (declared : desc α = .uint width)
    (sized : [1, 2, 4, 8, 16, 32].contains width = true)
    (written : ∀ a, toValue a = .uint (toNat a)) (read : ofValue (α := α) = ofUint width ofNat)
    (bounded : ∀ a, toNat a < 2 ^ (8 * width)) (left : ∀ a, ofNat (toNat a) = a)
    (right : ∀ n, n < 2 ^ (8 * width) → toNat (ofNat n) = n) : LawfulSszType α where
  wellFormed := by simp only [declared, Desc.wellFormed, sized, ↓reduceIte]
  fits a := by rw [declared, written]; exact .uint (bounded a)
  ofValue_toValue a := by rw [read, written, ofUint_ok]; exact ⟨_, rfl, bounded a, left a⟩
  toValue_of_ofValue {value a} made := by
    rw [read, ofUint_ok] at made
    obtain ⟨n, rfl, below, rfl⟩ := made
    rw [written, right n below]

instance : LawfulSszType Bool where
  wellFormed := rfl
  fits b := .bool b
  ofValue_toValue _ := rfl
  toValue_of_ofValue {value _} made := by
    cases value <;> cases made <;> rfl

instance : LawfulSszType UInt8 :=
  .ofUint UInt8.toNat UInt8.ofNat rfl rfl (fun _ => rfl) rfl UInt8.toNat_lt
    (fun _ => UInt8.ofNat_toNat) (fun _ below => UInt8.toNat_ofNat_of_lt' below)

instance : LawfulSszType UInt16 :=
  .ofUint UInt16.toNat UInt16.ofNat rfl rfl (fun _ => rfl) rfl UInt16.toNat_lt
    (fun _ => UInt16.ofNat_toNat) (fun _ below => UInt16.toNat_ofNat_of_lt' below)

instance : LawfulSszType UInt32 :=
  .ofUint UInt32.toNat UInt32.ofNat rfl rfl (fun _ => rfl) rfl UInt32.toNat_lt
    (fun _ => UInt32.ofNat_toNat) (fun _ below => UInt32.toNat_ofNat_of_lt' below)

instance : LawfulSszType UInt64 :=
  .ofUint UInt64.toNat UInt64.ofNat rfl rfl (fun _ => rfl) rfl UInt64.toNat_lt
    (fun _ => UInt64.ofNat_toNat) (fun _ below => UInt64.toNat_ofNat_of_lt' below)

instance : LawfulSszType Base.U256 :=
  .ofUint BitVec.toNat (BitVec.ofNat 256) rfl rfl (fun _ => rfl) rfl BitVec.isLt
    (fun _ => by simp) (fun _ below => Nat.mod_eq_of_lt below)

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

end EthLib.Serialization.Ssz
