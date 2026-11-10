module

/-!
# `Base.Proofs.List`

Facts about lists that Lean core does not prove and that several layers use.

Removing the duplicates of a list leaves each element once.

A bound on each term of a sum bounds the sum by the count times that bound.

Bounds on each term of a sum bound it by the sum of those bounds.

A factor of every term comes out of the sum.

The quotients of the terms sum to at most the quotient of the sum.

Dropping the front where a test holds keeps each member that fails the test.

Numbering the front of a list gives the front of the numbered list.
-/

@[expose] public section

namespace EthLib.Base

/-- Removing the duplicates of a list leaves a list in which each element comes once. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  -- The recursion removes the head from the tail, so it runs on the length.
  suffices ∀ n, ∀ l : List α, l.length ≤ n → l.eraseDups.Nodup from this _ l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l short
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp short)]
    exact List.nodup_nil
  | succ n ih =>
    intro l short
    cases l with
    | nil => exact List.nodup_nil
    | cons head tail =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨fun mem => ?_, ih _ ?_⟩
      · rw [List.mem_eraseDups, List.mem_filter] at mem
        simp at mem
      · exact Nat.le_trans (List.length_filter_le _ _) (by simpa using short)

/-- Each term at least `low` makes the sum at least the count times `low`. -/
theorem le_sum_map {α : Type} {f : α → Nat} {low : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, low ≤ f x) → xs.length * low ≤ (xs.map f).sum
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have := le_sum_map (xs := xs) fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    omega

/-- Each term at most `high` makes the sum at most the count times `high`. -/
theorem sum_map_le {α : Type} {f : α → Nat} {high : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x ≤ high) → (xs.map f).sum ≤ xs.length * high
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have := sum_map_le (xs := xs) fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    omega

/-- Bounds on each term of a sum bound it by the sum of those bounds. -/
theorem sum_map_le_sum_map {α : Type} {f g : α → Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x ≤ g x) → (xs.map f).sum ≤ (xs.map g).sum
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have := sum_map_le_sum_map (xs := xs) fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A factor on the left of every term comes out of the sum. -/
theorem sum_map_mul_left {α : Type} (factor : Nat) (f : α → Nat) :
    ∀ xs : List α, (xs.map fun x => factor * f x).sum = factor * (xs.map f).sum
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, Nat.mul_add, sum_map_mul_left factor f xs]

/-- A factor on the right of every term comes out of the sum. -/
theorem sum_map_mul_right {α : Type} (f : α → Nat) (factor : Nat) :
    ∀ xs : List α, (xs.map fun x => f x * factor).sum = (xs.map f).sum * factor
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, Nat.add_mul, sum_map_mul_right f factor xs]

/-- The quotients of the terms sum to at most the quotient of the sum. -/
theorem sum_map_div_le {α : Type} (f : α → Nat) (divisor : Nat) :
    ∀ xs : List α, (xs.map fun x => f x / divisor).sum ≤ (xs.map f).sum / divisor
  | [] => by simp
  | x :: xs => by
    have rest := sum_map_div_le f divisor xs
    simp only [List.map_cons, List.sum_cons]
    rcases Nat.eq_zero_or_pos divisor with zero | positive
    · subst zero
      simp only [Nat.div_zero] at rest ⊢
      omega
    · refine (Nat.le_div_iff_mul_le positive).mpr ?_
      have first := Nat.div_mul_le_self (f x) divisor
      have second := Nat.div_mul_le_self (xs.map f).sum divisor
      have kept := Nat.mul_le_mul_right divisor rest
      rw [Nat.add_mul]
      omega

/-- Dropping the front where a test holds keeps each member that fails the test. -/
theorem mem_dropWhile_of_eq_false {α : Type} {test : α → Bool} {member : α}
    (failed : test member = false) {list : List α} (found : member ∈ list) :
    member ∈ list.dropWhile test := by
  rw [← List.takeWhile_append_dropWhile (p := test) (l := list), List.mem_append] at found
  rcases found with taken | kept
  · have passed := List.all_eq_true.mp List.all_takeWhile member taken
    rw [failed] at passed
    cases passed
  · exact kept

/-- Numbering the first `i` elements of a list gives the first `i` elements of the numbered list. -/
theorem zipIdx_take {α : Type} (l : List α) (i : Nat) : (l.take i).zipIdx = l.zipIdx.take i := by
  apply List.ext_getElem?
  intro n
  simp only [List.getElem?_zipIdx, List.getElem?_take]
  split <;> simp

end EthLib.Base
