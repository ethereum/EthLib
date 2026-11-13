module

/-!
# `Base.Proofs.List`

Facts about lists that Lean core does not prove and that several layers use.

Removing the duplicates of a list leaves each element once.

A bound on each term of a sum bounds the sum by the count times that bound.

Bounds on each term of a sum bound it by the sum of those bounds.

A factor of every term comes out of the sum.

The quotients of the terms sum to at most the quotient of the sum.

Two lists of distinct elements that each hold every element with a nonzero term give the same sum.

A change of one term of a sum over distinct elements changes the sum by the same amount.

A sum of a value where a test holds, and zero elsewhere, is its sum over the passing entries.

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

/-- Dropping the terms that are 0 keeps a sum. -/
theorem sum_map_filter_ne_zero {α : Type} (f : α → Nat) :
    ∀ xs : List α, ((xs.filter fun x => f x ≠ 0).map f).sum = (xs.map f).sum
  | [] => rfl
  | x :: xs => by
    have ih := sum_map_filter_ne_zero f xs
    by_cases hx : f x = 0 <;> simp_all

/-- Two lists without repeats that each hold every element with a nonzero term give the same sum. -/
theorem sum_map_eq_of_nodup {α : Type} {f : α → Nat} {xs ys : List α} (dx : xs.Nodup)
    (dy : ys.Nodup) (hx : ∀ a, f a ≠ 0 → a ∈ xs) (hy : ∀ a, f a ≠ 0 → a ∈ ys) :
    (xs.map f).sum = (ys.map f).sum := by
  rw [← sum_map_filter_ne_zero f xs, ← sum_map_filter_ne_zero f ys]
  refine List.Perm.sum_nat (List.Perm.map f ?_)
  refine (List.perm_ext_iff_of_nodup (dx.filter _) (dy.filter _)).mpr fun a => ?_
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => ⟨hy a h.2, h.2⟩, fun h => ⟨hx a h.2, h.2⟩⟩

/-- A change of one term of a sum over distinct elements changes the sum by the same amount.

The two functions agree at every element other than `a`, which the list holds. -/
theorem sum_map_add_eq_of_eq_off {α : Type} {f g : α → Nat} {a : α}
    (h : ∀ x, x ≠ a → g x = f x) :
    ∀ {xs : List α}, xs.Nodup → a ∈ xs → (xs.map g).sum + f a = (xs.map f).sum + g a
  | [], _, ha => absurd ha List.not_mem_nil
  | x :: xs, d, ha => by
    obtain ⟨hx, d⟩ := List.nodup_cons.mp d
    simp only [List.map_cons, List.sum_cons]
    by_cases hxa : x = a
    · subst hxa
      have hrest : xs.map g = xs.map f :=
        List.map_congr_left fun y hy => h y fun e => hx (e ▸ hy)
      rw [hrest]
      omega
    · have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with e | e
        · exact absurd e.symm hxa
        · exact e
      have := sum_map_add_eq_of_eq_off h d ha'
      rw [h x hxa]
      omega

/-- A sum of a value where a test holds, and zero elsewhere, is its sum over the passing entries. -/
theorem sum_map_ite_eq_sum_filter {α : Type} (test : α → Prop) [DecidablePred test]
    (value : α → Nat) (entries : List α) :
    (entries.map fun entry => if test entry then value entry else 0).sum =
      ((entries.filter fun entry => test entry).map value).sum := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => by_cases passes : test entry <;> simp [passes, ih]

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
