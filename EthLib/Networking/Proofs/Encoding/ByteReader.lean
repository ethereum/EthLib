module

public import EthLib.Networking.Encoding.ByteReader
public import EthLib.Base.Proofs.ByteOrder
public import EthLib.Base.Proofs.Bytes

/-!
# Proofs: readers of byte fields

Each reader recovers its field and preserves arbitrary trailing bytes.
-/

@[expose] public section

namespace EthLib.Networking.Encoding.ByteReader

open EthLib.Base

/-- Reading as many bytes as a field holds returns that field and the bytes after it. -/
@[simp] theorem bytes_append {ε : Type} (truncated : Nat → ε) (field rest : List UInt8) :
    bytes truncated field.length (field ++ rest) = .ok (field, rest) := by
  simp [bytes]

/-- Reading as many bytes as an object holds returns that object and the bytes after it. -/
@[simp] theorem vector_append {ε : Type} (truncated : Nat → ε) {n : Nat} (value : Vector UInt8 n)
    (rest : List UInt8) : vector truncated n (value.toList ++ rest) = .ok (value, rest) := by
  have length : value.toList.length = n := by simp
  simp only [vector, ← length, bytes_append, bind, StateT.bind, Except.bind, StateT.lift,
    Vector.toArray_toList, exactArray_toArray]
  rfl

/-- Reading a written integer returns it modulo the field width, and the bytes after it. -/
@[simp] theorem uint_encode {ε : Type} (truncated : Nat → ε) (n value : Nat) (rest : List UInt8) :
    uint truncated n ((ByteOrder.toBE n value).toList ++ rest) = .ok (value % 256 ^ n, rest) := by
  simp [uint, bytes, ByteOrder.ofBE_toBE,
    StateT.bind, StateT.pure, bind, Except.bind, pure, Except.pure]

/-- A condition that holds consumes nothing. -/
@[simp] theorem require_true {ε : Type} (condition : Prop) [Decidable condition]
    (holds : condition) (error : ε) (rest : List UInt8) :
    require condition error rest = .ok ((), rest) := by
  simp [require, holds]

/-- A successful byte read consumes exactly the returned field. -/
theorem bytes_ok_iff {ε : Type} (truncated : Nat → ε) (n : Nat)
    (input field rest : List UInt8) :
    bytes truncated n input = .ok (field, rest) ↔
      field.length = n ∧ input = field ++ rest := by
  constructor
  · intro accepted
    dsimp only [bytes] at accepted
    split at accepted
    · cases accepted
      exact ⟨by assumption, (List.take_append_drop n input).symm⟩
    · contradiction
  · rintro ⟨rfl, rfl⟩
    exact bytes_append truncated field rest

/-- A byte read fails exactly when the input is shorter than the field.

The error is then the one built from the count of bytes left. -/
theorem bytes_error_iff {ε : Type} (truncated : Nat → ε) (n : Nat) (input : List UInt8)
    (error : ε) :
    bytes truncated n input = .error error ↔ input.length < n ∧ error = truncated input.length := by
  simp only [bytes, List.length_take]
  split
  -- A field that is all there gives no error.
  · simp only [reduceCtorEq, false_iff, not_and]
    intro short
    omega
  -- A field cut short gives the error of the bytes left.
  · constructor
    · intro h
      cases h
      exact ⟨by omega, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl

/-- An object read succeeds exactly when the input is the bytes of the object, then the rest. -/
theorem vector_ok_iff {ε : Type} (truncated : Nat → ε) {n : Nat} (input rest : List UInt8)
    (value : Vector UInt8 n) :
    vector truncated n input = .ok (value, rest) ↔ input = value.toList ++ rest := by
  constructor
  · intro accepted
    cases read : bytes truncated n input with
    | error error => simp [vector, read, StateT.bind, bind, Except.bind] at accepted
    | ok result =>
      obtain ⟨field, trailing⟩ := result
      obtain ⟨length, rfl⟩ := (bytes_ok_iff truncated n input field trailing).mp read
      have made : exactArray field.length field.toArray truncated =
          .ok ⟨field.toArray, by simp⟩ := exactArray_of_size_eq _ (by simp)
      subst length
      simp [vector, read, made, StateT.bind, StateT.lift, bind, Except.bind] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      simp
  · rintro rfl
    exact vector_append truncated value rest

/-- A successful integer read consumes its unique encoding at the given width. -/
theorem uint_ok_iff {ε : Type} (truncated : Nat → ε) (n value : Nat)
    (input rest : List UInt8) :
    uint truncated n input = .ok (value, rest) ↔
      value < 256 ^ n ∧ input = (ByteOrder.toBE n value).toList ++ rest := by
  constructor
  · intro accepted
    unfold uint at accepted
    cases read : bytes truncated n input with
    | error error => simp [read, StateT.bind, bind, Except.bind] at accepted
    | ok result =>
      rcases result with ⟨field, trailing⟩
      simp [read, StateT.bind, StateT.pure, bind, Except.bind, pure, Except.pure] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      obtain ⟨length, split⟩ := (bytes_ok_iff truncated n input field trailing).mp read
      constructor
      · simpa [← length] using ByteOrder.ofBE_lt field
      · rwa [ByteOrder.toList_toBE_ofBE_of_length length]
  · rintro ⟨bound, rfl⟩
    simp [uint_encode, Nat.mod_eq_of_lt bound]

/-- A successful condition check consumes no input and establishes its condition. -/
theorem require_ok_iff {ε : Type} (condition : Prop) [Decidable condition]
    (error : ε) (input rest : List UInt8) :
    require condition error input = .ok ((), rest) ↔ condition ∧ input = rest := by
  by_cases holds : condition <;> simp [require, holds]

end EthLib.Networking.Encoding.ByteReader
