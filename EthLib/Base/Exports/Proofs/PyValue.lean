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

instance {w : Nat} : LawfulPy (BitVec w) where
  fromPy_toPy := by
    intro a
    show (do return BitVec.ofNatLT _ (← fromPyBelow (2 ^ w) (.int a.toNat)).2) = _
    rw [fromPyBelow_int a.isLt]
    exact congrArg Except.ok (BitVec.ofNatLT_toNat ..)

instance {w : Nat} : PlainPy (BitVec w) where
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

/-- The digit that a value below 16 writes reads back as that value. -/
theorem hexDigit_digitChar (m : Nat) (h : m < 16) : hexDigit (Nat.digitChar m) = m := by
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
      m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp [hexDigit, Nat.digitChar, Char.isDigit]

/-- Reading digits after a value shifts that value by one place per digit. -/
theorem foldl_hexDigit (a : Nat) (cs : List Char) :
    cs.foldl (fun n c => 16 * n + hexDigit c) a =
      a * 16 ^ cs.length + cs.foldl (fun n c => 16 * n + hexDigit c) 0 := by
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (16 * 0 + hexDigit c), Nat.pow_succ]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_mul]
    rw [Nat.mul_comm 16 a, Nat.mul_assoc, Nat.mul_comm 16]
    omega

/-- Reading the digits by halves gives the number that reading them one by one gives. -/
theorem natOfHexDigits_eq_foldl (cs : List Char) :
    natOfHexDigits cs = cs.foldl (fun n c => 16 * n + hexDigit c) 0 := by
  induction cs using natOfHexDigits.induct with
  | case1 cs h =>
    rw [natOfHexDigits]
    simp only [h, ↓reduceIte]
  | case2 cs h ih1 ih2 =>
    rw [natOfHexDigits]
    simp only [h, ↓reduceIte]
    rw [ih1, ih2, Nat.shiftLeft_eq]
    conv => rhs; rw [← List.take_append_drop (cs.length - cs.length / 2) cs, List.foldl_append,
      foldl_hexDigit (List.foldl _ 0 _), List.length_drop]
    have hk : cs.length - (cs.length - cs.length / 2) = cs.length / 2 := by omega
    rw [hk, Nat.pow_mul]

/-- The padded digits of a number are `m` digits, and they write its remainder by `16 ^ m`. -/
theorem hexDigitsPadded_spec (m n : Nat) :
    (hexDigitsPadded m n).length = m ∧
      (hexDigitsPadded m n).foldl (fun n c => 16 * n + hexDigit c) 0 = n % 16 ^ m := by
  induction m, n using hexDigitsPadded.induct with
  | case1 m n h =>
    rw [hexDigitsPadded]
    simp only [h, ↓reduceIte]
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · simp [Nat.mod_one]
    · simp [hexDigit_digitChar _ (Nat.mod_lt n (by omega))]
  | case2 m n h ih1 ih2 =>
    rw [hexDigitsPadded]
    simp only [h, ↓reduceIte]
    rw [List.length_append, List.foldl_append, ih1.1, ih2.1,
      foldl_hexDigit (List.foldl _ 0 _), ih1.2, ih2.1, ih2.2]
    refine ⟨by omega, ?_⟩
    have hm : 16 ^ m = 16 ^ (m / 2) * 16 ^ (m - m / 2) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h16 : (2 : Nat) ^ (4 * (m / 2)) = 16 ^ (m / 2) := by rw [Nat.pow_mul]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, h16, hm, Nat.mod_mul,
      Nat.mod_mod]
    ac_rfl

/-- Each padded digit of a number is a digit of base 16. -/
theorem hexDigitsPadded_digits (m n : Nat) :
    ∀ c ∈ hexDigitsPadded m n, ∃ d, d < 16 ∧ c = Nat.digitChar d := by
  induction m, n using hexDigitsPadded.induct with
  | case1 m n h =>
    rw [hexDigitsPadded]
    simp only [h, ↓reduceIte]
    intro c hc
    exact ⟨n % 16, Nat.mod_lt n (by omega), (List.eq_of_mem_replicate hc)⟩
  | case2 m n h ih1 ih2 =>
    rw [hexDigitsPadded]
    simp only [h, ↓reduceIte]
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ih1 c hc
    · exact ih2 c hc

/-- The digits of a number are digits of base 16, in lower case, so the C layer can read them. -/
theorem natToHex_digits (n : Nat) :
    ∀ c ∈ (natToHex n).toList, ∃ d, d < 16 ∧ c = Nat.digitChar d := by
  unfold natToHex
  rw [String.toList_ofList]
  exact hexDigitsPadded_digits _ n

/-- Reading the digits of a number in base 16 gives the number. -/
theorem natOfHex_natToHex (n : Nat) : natOfHex (natToHex n) = n := by
  unfold natOfHex natToHex
  rw [String.toList_ofList, natOfHexDigits_eq_foldl, (hexDigitsPadded_spec _ n).2]
  apply Nat.mod_eq_of_lt
  calc n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
    _ ≤ 2 ^ (4 * (n.log2 / 4 + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 16 ^ (n.log2 / 4 + 1) := by rw [Nat.pow_mul]

end EthLib.Exports
