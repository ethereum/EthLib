module

public import EthLib.Base.Exports.PyValue
import all Init.Data.Nat.ToString

/-!
# Proofs: `Base.Exports.PyValue`

Reading back the Python value of a value gives that value, for each type that crosses the boundary.

So an export never sends two different results as one value of this type.

A type built from these types by pairs, options, lists and arrays inherits the law.

An option inherits it only when no value inside becomes `None`, so an option of an option does not.

Lean writes a large `int` as lower-case digits in base 16, and reading them back gives the number.

Python writes the same digits for the same number, and the C layer passes them on.
-/

public section

namespace EthLib.Exports

private theorem fromPyBelow_int {bound n : Nat} (h : n < bound) :
    fromPyBelow bound (.int n) = .ok ⟨n, h⟩ := by
  simp only [fromPyBelow]
  show dite _ _ _ = _
  simp only [h, ↓reduceDIte]
  rfl

instance : LawfulPy PyValue where
  fromPy_toPy := fun _ => rfl

instance : LawfulPy Unit where
  fromPy_toPy := fun _ => rfl

instance : LawfulPy Bool where
  fromPy_toPy := by intro b; cases b <;> rfl

instance : PlainPy Bool where
  isPlain_toPy := by intro b; cases b <;> rfl

instance : LawfulPy Nat where
  fromPy_toPy := fun _ => rfl

instance : PlainPy Nat where
  isPlain_toPy := fun _ => rfl

instance : LawfulPy UInt8 where
  fromPy_toPy := by
    intro a
    show (do return UInt8.ofNatLT _ (← fromPyBelow UInt8.size (.int a.toNat)).2) = _
    rw [fromPyBelow_int a.toNat_lt]
    exact congrArg Except.ok (UInt8.ofNatLT_toNat ..)

instance : PlainPy UInt8 where
  isPlain_toPy := fun _ => rfl

instance : LawfulPy UInt16 where
  fromPy_toPy := by
    intro a
    show (do return UInt16.ofNatLT _ (← fromPyBelow UInt16.size (.int a.toNat)).2) = _
    rw [fromPyBelow_int a.toNat_lt]
    exact congrArg Except.ok (UInt16.ofNatLT_toNat ..)

instance : PlainPy UInt16 where
  isPlain_toPy := fun _ => rfl

instance : LawfulPy UInt32 where
  fromPy_toPy := by
    intro a
    show (do return UInt32.ofNatLT _ (← fromPyBelow UInt32.size (.int a.toNat)).2) = _
    rw [fromPyBelow_int a.toNat_lt]
    exact congrArg Except.ok (UInt32.ofNatLT_toNat ..)

instance : PlainPy UInt32 where
  isPlain_toPy := fun _ => rfl

instance : LawfulPy UInt64 where
  fromPy_toPy := by
    intro a
    show (do return UInt64.ofNatLT _ (← fromPyBelow UInt64.size (.int a.toNat)).2) = _
    rw [fromPyBelow_int a.toNat_lt]
    exact congrArg Except.ok (UInt64.ofNatLT_toNat ..)

instance : PlainPy UInt64 where
  isPlain_toPy := fun _ => rfl

instance : LawfulPy ByteArray where
  fromPy_toPy := fun _ => rfl

instance : PlainPy ByteArray where
  isPlain_toPy := fun _ => rfl

instance {n : Nat} : LawfulPy (Vector UInt8 n) where
  fromPy_toPy := by
    intro v
    show dite _ _ _ = _
    simp only [v.size_toArray, ↓reduceDIte]
    rfl

instance {n : Nat} : PlainPy (Vector UInt8 n) where
  isPlain_toPy := fun _ => rfl

instance : LawfulPy String where
  fromPy_toPy := fun _ => rfl

instance : PlainPy String where
  isPlain_toPy := fun _ => rfl

/-- An option is `None` or its value, so the value must never be `None` itself. -/
instance {α : Type} [ToPy α] [FromPy α] [LawfulPy α] [PlainPy α] : LawfulPy (Option α) where
  fromPy_toPy := by
    intro o
    cases o with
    | none => rfl
    | some a =>
      have hp := PlainPy.isPlain_toPy a
      have key : fromPy (α := Option α) (toPy a) = some <$> fromPy (toPy a) := by
        cases h : toPy a <;> simp_all [fromPy, PyValue.isPlain]
      show fromPy (α := Option α) (toPy a) = _
      rw [key, LawfulPy.fromPy_toPy]
      rfl

instance {α : Type} [ToPy α] [FromPy α] [LawfulPy α] : LawfulPy (Array α) where
  fromPy_toPy := by
    intro xs
    show Array.mapM fromPy (xs.map toPy) = _
    rw [Array.mapM_map]
    have h : (fromPy ∘ toPy : α → Except String α) = fun a => pure (id a) :=
      funext LawfulPy.fromPy_toPy
    rw [h, Array.mapM_pure]
    simp; rfl

instance {α : Type} [ToPy α] : PlainPy (Array α) where
  isPlain_toPy := fun _ => rfl

instance {α : Type} [ToPy α] [FromPy α] [LawfulPy α] : LawfulPy (List α) where
  fromPy_toPy := by
    intro xs
    show List.mapM fromPy (xs.map toPy).toArray.toList = _
    rw [List.toList_toArray, List.mapM_map]
    have h : (fromPy ∘ toPy : α → Except String α) = fun a => pure (id a) :=
      funext LawfulPy.fromPy_toPy
    rw [h, List.mapM_pure]
    simp; rfl

instance {α : Type} [ToPy α] : PlainPy (List α) where
  isPlain_toPy := fun _ => rfl

/-- A value that is not a pair is one item. -/
instance (priority := low) {α : Type} [ToPy α] [FromPy α] [LawfulPy α] : LawfulPyItems α where
  ofItems_items := fun a => LawfulPy.fromPy_toPy a

instance {α β : Type} [ToPy α] [FromPy α] [LawfulPy α] [ToPyItems β] [FromPyItems β]
    [LawfulPyItems β] : LawfulPyItems (α × β) where
  ofItems_items := by
    rintro ⟨a, b⟩
    show (do return (← fromPy (toPy a), ← FromPyItems.ofItems (ToPyItems.items b))) = _
    rw [LawfulPy.fromPy_toPy, LawfulPyItems.ofItems_items]
    rfl

instance {α β : Type} [ToPy α] [FromPy α] [LawfulPy α] [ToPyItems β] [FromPyItems β]
    [LawfulPyItems β] : LawfulPy (α × β) where
  fromPy_toPy := by
    rintro ⟨a, b⟩
    show FromPyItems.ofItems (ToPyItems.items (a, b)).toArray.toList = _
    rw [List.toList_toArray]
    exact LawfulPyItems.ofItems_items (a, b)

instance {α β : Type} [ToPy α] [ToPyItems β] : PlainPy (α × β) where
  isPlain_toPy := fun _ => rfl

/-- A value that is never `None` nor an error is never an error. -/
instance (priority := low) {α : Type} [ToPy α] [PlainPy α] : NoFailurePy α where
  isFailure_toPy a := by
    have hp := PlainPy.isPlain_toPy a
    cases h : toPy a <;> simp_all [PyValue.isPlain, PyValue.isFailure]

/-- An option is `None` or its value, and neither is an error. -/
instance {α : Type} [ToPy α] [NoFailurePy α] : NoFailurePy (Option α) where
  isFailure_toPy
    | none => rfl
    | some a => NoFailurePy.isFailure_toPy a

/-- A result is a failure or its value, so the value must never be a failure itself. -/
instance {α : Type} [ToPy α] [FromPy α] [LawfulPy α] [NoFailurePy α] :
    LawfulPy (Except (UInt32 × String) α) where
  fromPy_toPy := by
    intro r
    cases r with
    | error e => rfl
    | ok a =>
      have hp := NoFailurePy.isFailure_toPy a
      have key : fromPy (α := Except (UInt32 × String) α) (toPy a) =
          .ok <$> fromPy (toPy a) := by
        cases h : toPy a <;> simp_all [fromPy, PyValue.isFailure]
      show fromPy (α := Except (UInt32 × String) α) (toPy a) = _
      rw [key, LawfulPy.fromPy_toPy]
      rfl

/-- An export runs its function on the arguments that the items of a value write. -/
theorem pyExport_items {α β : Type} [ToPyItems α] [FromPyItems α] [LawfulPyItems α] [ToPy β]
    [FromPy β] [LawfulPy β] (f : α → Result β) (a : α) :
    pyExport f (.tuple (ToPyItems.items a).toArray) = toPy <$> f a := by
  simp [pyExport, LawfulPyItems.ofItems_items, Except.mapError]
  rfl

/-- Reading the digits of a number in base 16 gives the number. -/
theorem natOfHex_natToHex (n : Nat) : natOfHex (natToHex n) = n := by
  have hd : ∀ m : Fin 16, hexDigit (Nat.digitChar m) = m := by
    rintro ⟨m, hm⟩
    have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
        m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp [hexDigit, Nat.digitChar, Char.isDigit]
  have key : ∀ n : Nat, (Nat.toDigits 16 n).foldl (fun n c => 16 * n + hexDigit c) 0 = n := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      by_cases h : n < 16
      · rw [Nat.toDigits_of_lt_base h]
        simpa using hd ⟨n, h⟩
      · rw [Nat.toDigits_eq_ite (by omega)]
        simp only [h, ↓reduceIte, List.foldl_append]
        have h2 := hd ⟨n % 16, Nat.mod_lt _ (by omega)⟩
        simp only [ih (n / 16) (by omega), List.foldl_cons, List.foldl_nil] at h2 ⊢
        omega
  unfold natOfHex natToHex
  rw [String.foldl_eq_foldl_toList, String.toList_ofList]
  exact key n

end EthLib.Exports
