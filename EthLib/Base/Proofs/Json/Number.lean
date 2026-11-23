module

public import EthLib.Base.Proofs.Json.Text

/-!
# Proofs: the decimal digits of a JSON number

The decimal digits of a natural number are digits of the grammar of RFC 8259 §6.

They read back as that number, and a positive number has no leading zero.

So the reader takes exactly those digits as the integer part of a number.
-/

@[expose] public section

namespace EthLib.Base.Json

/-- A decimal digit of a natural number is a digit of the grammar. -/
theorem digit_of_mem_toDigits {c : Char} {n : Nat} (h : c ∈ Nat.toDigits 10 n) :
    digit c = true := by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  simp only [Char.isDigit, digit, Bool.and_eq_true, decide_eq_true_eq] at this ⊢
  exact this

/-- The decimal digits of a natural number have that number as their value. -/
theorem foldl_digitStep_toDigits (n : Nat) : (Nat.toDigits 10 n).foldl digitStep 0 = n := by
  have key : ∀ (l : List Char), (∀ c ∈ l, digit c = true) → ∀ init,
      l.foldl digitStep init = Nat.ofDigitChars 10 l init := by
    intro l
    induction l with
    | nil => simp
    | cons c l ih =>
      intro h init
      have hc := h c (by simp)
      simp only [digit, Bool.and_eq_true, decide_eq_true_eq] at hc
      have : '0'.toNat ≤ c.toNat := hc.1
      rw [List.foldl_cons, Nat.ofDigitChars_cons, digitStep, Nat.add_sub_assoc this]
      exact ih (fun d hd => h d (by simp [hd])) _
  rw [key _ (fun c h => digit_of_mem_toDigits h), Nat.ofDigitChars_ten_toDigits]

/-- A positive natural number has no leading zero among its decimal digits. -/
theorem head_toDigits_ne_zero (n : Nat) (hn : 0 < n) :
    (Nat.toDigits 10 n).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · simp; omega
    · have h := ih (n / 10) (by omega) (by omega)
      rw [List.head?_append]
      cases hd : Nat.toDigits 10 (n / 10) with
      | nil => exact absurd hd Nat.toDigits_ne_nil
      | cons d ds => simpa [hd] using h

/-- The decimal digits of a natural number are the run of digits that a non-digit ends. -/
theorem takeWhile_toDigits (n : Nat) (X : List Char) (hX : ∀ c ∈ X.head?, digit c = false) :
    (Nat.toDigits 10 n ++ X).takeWhile digit = Nat.toDigits 10 n := by
  rw [List.takeWhile_append_of_pos (fun c h => digit_of_mem_toDigits h)]
  rcases X with _ | ⟨c, X⟩
  · simp
  · simp [List.takeWhile_cons_of_neg (by simpa using hX c rfl)]

/-- The characters left after the decimal digits of a natural number start at the non-digit. -/
theorem dropWhile_toDigits (n : Nat) (X : List Char) (hX : ∀ c ∈ X.head?, digit c = false) :
    (Nat.toDigits 10 n ++ X).dropWhile digit = X := by
  rw [List.dropWhile_append_of_pos (fun c h => digit_of_mem_toDigits h)]
  rcases X with _ | ⟨c, X⟩
  · simp
  · simp [List.dropWhile_cons_of_neg (by simpa using hX c rfl)]

end EthLib.Base.Json
