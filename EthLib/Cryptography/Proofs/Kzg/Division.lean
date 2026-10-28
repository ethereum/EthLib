import EthLib.Cryptography.Proofs.Kzg.Polynomials
import EthLib.Cryptography.Proofs.Bls.FrZMod
import Mathlib.Tactic

/-!
# Proofs: polynomial long division

The code divides two coefficient arrays the way the specification does.

Each step cancels the current leading coefficient of the dividend.

The proofs track one fact through both loops:

```text
    a(x) = q(x) * b(x) + r(x)      at every evaluation point x
```

At the end the remainder has degree below the divisor.
-/

namespace EthLib.Cryptography.Kzg
open Bls (Fr)
open scoped EthLib.Cryptography.Bls.Fr

private theorem getElem_set_bounded (a : Array Fr) (i j : Nat) (v : Fr) (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  simp [Array.set!, getElem!_pos, hj, Array.getElem_setIfInBounds]


private theorem set_top_identity {R : Type*} [CommRing R] (e v a p : R) :
    (e + 0) + v * p = (e + a * p) + (v - a) * p := by ring

private theorem evalAux_set (a : PolynomialCoeff) (x v : Fr) (i n : Nat)
    (hi : i < a.size) (hn : n ≤ a.size) :
    evalCoeffPolyAux (a.set! i v) x n = evalCoeffPolyAux a x n +
      (if i < n then (v - a[i]!) * Fr.powNat x i else 0) := by
  induction n with
  | zero => simp [evalCoeffPolyAux, Fr.zero]
  | succ n ih =>
    rw [evalCoeffPolyAux, evalCoeffPolyAux, ih (by omega),
      getElem_set_bounded a i n v (by omega)]
    by_cases h : i = n
    · subst i
      simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]
      exact set_top_identity (evalCoeffPolyAux a x n) v a[n]! (Fr.powNat x n)
    · by_cases hin : i < n
      · simp only [h, hin, Nat.lt_trans hin (Nat.lt_succ_self n), ↓reduceIte]
        exact add_right_comm _ _ _
      · have hnot : ¬ i < n + 1 := by omega
        simp only [h, hin, hnot, ↓reduceIte]
        exact add_right_comm _ _ _

/-- Changing one coefficient changes evaluation by exactly its monomial. -/
theorem evalPolyAt_set (a : PolynomialCoeff) (x v : Fr) (i : Nat)
    (hi : i < a.size) :
    evalPolyAt (a.set! i v) x = evalPolyAt a x +
      (v - a[i]!) * Fr.powNat x i := by
  unfold evalPolyAt evalCoeffPoly
  rw [show (a.set! i v).size = a.size by simp [Array.set!], evalAux_set a x v i a.size hi (Nat.le_refl _), ite_eq_left hi]


private def divisionSubtract (a b : PolynomialCoeff) (shift : Nat) (quot : Fr)
    (count : Nat) : PolynomialCoeff :=
  (List.range count).foldl
    (fun r i => r.set! (shift + i) (r[shift + i]! - b[i]! * quot)) a

private theorem divisionSubtract_succ (a b : PolynomialCoeff) (shift : Nat)
    (quot : Fr) (count : Nat) :
    divisionSubtract a b shift quot (count + 1) =
      (divisionSubtract a b shift quot count).set! (shift + count)
        ((divisionSubtract a b shift quot count)[shift + count]! - b[count]! * quot) := by
  simp [divisionSubtract, List.range_succ, List.foldl_append]

private theorem size_divisionSubtract (a b : PolynomialCoeff) (shift : Nat)
    (quot : Fr) (count : Nat) :
    (divisionSubtract a b shift quot count).size = a.size := by
  induction count with
  | zero => rfl
  | succ n ih => simp [divisionSubtract_succ, Array.set!, ih]

private theorem subtract_step_identity {R : Type*} [CommRing R]
    (e s q t c r u : R) :
    (e - s * q * t) + ((r - c * q) - r) * (t * u) =
      e - (s + c * u) * q * t := by ring

private theorem eval_divisionSubtract (a b : PolynomialCoeff) (x quot : Fr)
    (shift count : Nat) (hfit : shift + count ≤ a.size) :
    evalPolyAt (divisionSubtract a b shift quot count) x =
      evalPolyAt a x - evalCoeffPolyAux b x count * quot * Fr.powNat x shift := by
  induction count with
  | zero =>
    change evalPolyAt a x = evalPolyAt a x - Fr.zero * quot * Fr.powNat x shift
    exact (sub_zero _).symm.trans (congrArg (fun z => evalPolyAt a x - z)
      (by simp only [Fr.zero_def, Fin.zero_mul])).symm
  | succ n ih =>
    rw [divisionSubtract_succ, evalPolyAt_set _ _ _ _ (by rw [size_divisionSubtract]; omega),
      ih (by omega), Fr.powNat_add, evalCoeffPolyAux]
    exact subtract_step_identity _ _ _ _ _ _ _

/-- The actual coefficient-update loop used by long division subtracts exactly
`quot * X^shift * b(X)`. The fit condition ensures no `set!` is out of bounds. -/
theorem dividePolynomialcoeff_inner_eval (a b : PolynomialCoeff) (x quot : Fr)
    (shift : Nat) (hfit : shift + b.size ≤ a.size) :
    evalPolyAt ((Array.range b.size).foldl
      (fun r i => r.set! (shift + i) (r[shift + i]! - b[i]! * quot)) a) x =
      evalPolyAt a x - evalPolyAt b x * quot * Fr.powNat x shift := by
  rw [← Array.foldl_toList, Array.toList_range]
  exact eval_divisionSubtract a b x quot shift b.size hfit


private theorem divisionSubtract_get (a b : PolynomialCoeff) (quot : Fr)
    (shift count j : Nat) (hj : j < a.size) :
    (divisionSubtract a b shift quot count)[j]! =
      if shift ≤ j ∧ j < shift + count then a[j]! - b[j - shift]! * quot else a[j]! := by
  induction count with
  | zero => simp [divisionSubtract]
  | succ n ih =>
    rw [divisionSubtract_succ, getElem_set_bounded _ _ _ _
      (by rw [size_divisionSubtract]; exact hj)]
    by_cases heq : shift + n = j
    · subst j
      rw [ite_eq_left rfl, ih, ite_eq_right (by omega), ite_eq_left (by omega)]
      simp
    · rw [ite_eq_right heq, ih]
      have hc : (shift ≤ j ∧ j < shift + (n + 1)) ↔ (shift ≤ j ∧ j < shift + n) := by omega
      simp only [hc]

private theorem cancel_leading_identity {R : Type*} [Field R] (c b : R)
    (hb : b ≠ 0) : c - b * (c * b⁻¹) = 0 := by
  rw [← mul_assoc, mul_comm b c, mul_assoc, mul_inv_cancel₀ hb, mul_one, sub_self]

/-- A division subtraction with the selected quotient eliminates its leading
coefficient; every index touched is in bounds. -/
theorem dividePolynomialcoeff_inner_leading_zero (a b : PolynomialCoeff)
    (shift : Nat) (hb : 0 < b.size) (hfit : shift + b.size ≤ a.size)
    (hlead : b[b.size - 1]! ≠ 0) :
    let top := shift + b.size - 1
    let quot := a[top]! * b[b.size - 1]!.inverse
    ((Array.range b.size).foldl
      (fun r i => r.set! (shift + i) (r[shift + i]! - b[i]! * quot)) a)[top]! = 0 := by
  dsimp only
  rw [← Array.foldl_toList, Array.toList_range]
  change (divisionSubtract a b shift (a[shift + b.size - 1]! * b[b.size - 1]!.inverse) b.size)[shift + b.size - 1]! = 0
  rw [divisionSubtract_get a b _ shift b.size _ (by omega), ite_eq_left (by omega)]
  have hindex : shift + b.size - 1 - shift = b.size - 1 := by omega
  rw [hindex, Fr.inverse_eq_inv]
  exact cancel_leading_identity _ _ hlead


private theorem prepend_zero_identity {R : Type*} [CommRing R] (q x : R) :
    0 + q * 1 = q + x * 0 := by ring

private theorem prepend_step_identity {R : Type*} [CommRing R]
    (q x e c p : R) : (q + x * e) + c * (x * p) = q + x * (e + c * p) := by ring

private theorem evalAux_prepend (q : Fr) (a : PolynomialCoeff) (x : Fr) (n : Nat)
    (hn : n ≤ a.size) :
    evalCoeffPolyAux (#[q] ++ a) x (n+1) = q + x * evalCoeffPolyAux a x n := by
  induction n with
  | zero =>
    simp only [evalCoeffPolyAux, Fr.powNat_zero, Fr.zero_def, Fr.one_def]
    rw [getElem!_pos _ 0 (by simp), Array.getElem_append_left (by simp)]
    change 0 + q * 1 = q + x * 0
    exact prepend_zero_identity q x
  | succ n ih =>
    rw [evalCoeffPolyAux, ih (by omega), evalCoeffPolyAux]
    have hget : (#[q] ++ a)[n+1]! = a[n]! := by
      rw [getElem!_pos _ _ (by simp; omega), Array.getElem_append_right (by simp), getElem!_pos _ _ (by omega)]
      simp
    rw [hget, Fr.powNat_succ]
    exact prepend_step_identity _ _ _ _ _

private theorem eval_prepend (q : Fr) (a : PolynomialCoeff) (x : Fr) :
    evalPolyAt (#[q] ++ a) x = q + x * evalPolyAt a x := by
  unfold evalPolyAt evalCoeffPoly
  have hs : (#[q] ++ a).size = a.size + 1 := by simp; omega
  rw [hs, evalAux_prepend q a x a.size (Nat.le_refl _)]


/-- The state of the executable long-division loop after `count` iterations.
This proof-only name unfolds to the original loop, without changing it. -/
def divisionLoopState (a b : PolynomialCoeff) (count : Nat) :
    PolynomialCoeff × PolynomialCoeff :=
  (List.range count).foldl (init := (a, #[])) fun (r, out) t =>
    let apos := r.size - 1 - t
    let shift := apos - (b.size - 1)
    let quot := r[apos]! * b[b.size - 1]!.inverse
    (divisionSubtract r b shift quot b.size, #[quot] ++ out)

private theorem divisionLoopState_succ (a b : PolynomialCoeff) (n : Nat) :
    divisionLoopState a b (n+1) =
      let st := divisionLoopState a b n
      let apos := st.1.size - 1 - n
      let shift := apos - (b.size - 1)
      let quot := st.1[apos]! * b[b.size - 1]!.inverse
      (divisionSubtract st.1 b shift quot b.size, #[quot] ++ st.2) := by
  simp [divisionLoopState, List.range_succ, List.foldl_append]

private theorem divisionLoopState_size (a b : PolynomialCoeff) (n : Nat) :
    (divisionLoopState a b n).1.size = a.size := by
  induction n with
  | zero => rfl
  | succ n ih => simp [divisionLoopState_succ, size_divisionSubtract, ih]

private theorem outer_step_identity {R : Type*} [CommRing R]
    (r b q o x p : R) :
    (r - b*q*p) + (q+x*o)*b*p = r + o*b*(x*p) := by ring

private theorem outer_zero_identity {R : Type*} [CommRing R] (a b p : R) :
    a + 0*b*p = a := by ring

/-- The actual long-division state preserves the dividend evaluation. At an
intermediate stage, the accumulated quotient still needs `steps-count`
leading zero coefficients. -/
theorem dividePolynomialcoeff_loop_invariant (a b : PolynomialCoeff) (x : Fr)
    (hb : 0 < b.size) (hab : b.size ≤ a.size) (count : Nat)
    (hc : count ≤ a.size + 1 - b.size) :
    evalPolyAt (divisionLoopState a b count).1 x +
      evalPolyAt (divisionLoopState a b count).2 x * evalPolyAt b x *
        Fr.powNat x (a.size + 1 - b.size - count) = evalPolyAt a x := by
  induction count with
  | zero =>
    change evalPolyAt a x + Fr.zero * evalPolyAt b x *
      Fr.powNat x (a.size + 1 - b.size - 0) = evalPolyAt a x
    exact outer_zero_identity _ _ _
  | succ n ih =>
    rw [divisionLoopState_succ]
    dsimp only
    rw [divisionLoopState_size]
    have hshift : a.size - 1 - n - (b.size - 1) = a.size + 1 - b.size - (n+1) := by omega
    have hfit : a.size - 1 - n - (b.size - 1) + b.size ≤
        (divisionLoopState a b n).1.size := by rw [divisionLoopState_size]; omega
    rw [eval_divisionSubtract _ _ _ _ _ _ hfit, eval_prepend, hshift]
    change (_ - evalPolyAt b x * _ * _) + _ = _
    have hremain : a.size + 1 - b.size - n = (a.size + 1 - b.size - (n+1)) + 1 := by omega
    have hi := ih (by omega)
    rw [hremain, Fr.powNat_succ] at hi
    exact (outer_step_identity
      (evalPolyAt (divisionLoopState a b n).1 x)
      (evalPolyAt b x)
      ((divisionLoopState a b n).1[a.size - 1 - n]! * b[b.size - 1]!.inverse)
      (evalPolyAt (divisionLoopState a b n).2 x)
      x (Fr.powNat x (a.size + 1 - b.size - (n+1)))).trans hi


private theorem dividePolynomialcoeff_eq_loop (a b : PolynomialCoeff)
    (hb : 0 < b.size) (hab : b.size ≤ a.size)
    (hlead : b[b.size-1]!.isZero = false) :
    dividePolynomialcoeff a b =
      .ok (divisionLoopState a b (a.size + 1 - b.size)).2 := by
  have hb0 : ¬ b.size = 0 := by omega
  have hnotlt : ¬ a.size < b.size := by omega
  have hmax : max b.size 1 = b.size := by omega
  simp only [dividePolynomialcoeff, hb0, hnotlt, hlead, ↓reduceIte,
    Bool.false_eq_true, pure, Except.pure,
    hmax, divisionLoopState, divisionSubtract,
    ← Array.foldl_toList, Array.toList_range]
  rfl

private theorem final_identity {R : Type*} [CommRing R] (r q b a : R)
    (h : r + q*b*1 = a) : a = q*b+r := by linear_combination -h

/-- Successful long division satisfies the quotient/remainder evaluation
identity, with the remainder equal to the actual final mutable dividend.
The degree bound for that remainder is a separate property. -/
theorem dividePolynomialcoeff_eval_identity {a b q : PolynomialCoeff}
    (hb : 0 < b.size) (hab : b.size ≤ a.size)
    (h : dividePolynomialcoeff a b = .ok q) (x : Fr) :
    evalPolyAt a x = evalPolyAt q x * evalPolyAt b x +
      evalPolyAt (divisionLoopState a b (a.size + 1 - b.size)).1 x := by
  have hlead : b[b.size-1]!.isZero = false := by
    cases hz : b[b.size-1]!.isZero with
    | false => rfl
    | true =>
      have he := dividePolynomialcoeff_zero_divisor a b (Or.inr ⟨hab, hz⟩)
      rw [he] at h
      cases h
  rw [dividePolynomialcoeff_eq_loop a b hb hab hlead] at h
  have hq := Except.ok.inj h
  have hi := dividePolynomialcoeff_loop_invariant a b x hb hab
    (a.size + 1 - b.size) (Nat.le_refl _)
  rw [Nat.sub_self, Fr.powNat_zero, hq] at hi
  exact final_identity _ _ _ _ hi


private theorem divisionSubtract_leading_zero (a b : PolynomialCoeff)
    (shift : Nat) (hb : 0 < b.size) (hfit : shift + b.size ≤ a.size)
    (hlead : b[b.size-1]! ≠ 0) :
    (divisionSubtract a b shift
      (a[shift+b.size-1]! * b[b.size-1]!.inverse) b.size)[shift+b.size-1]! = 0 := by
  have h := dividePolynomialcoeff_inner_leading_zero a b shift hb hfit hlead
  dsimp only at h
  rw [← Array.foldl_toList, Array.toList_range] at h
  exact h

/-- Each outer iteration clears its highest remaining coefficient, preserving
all higher coefficients already cleared. -/
theorem dividePolynomialcoeff_loop_high_zero (a b : PolynomialCoeff)
    (hb : 0 < b.size) (hab : b.size ≤ a.size) (hlead : b[b.size-1]! ≠ 0)
    (count : Nat) (hc : count ≤ a.size+1-b.size) :
    ∀ j, j < a.size → a.size-count ≤ j →
      (divisionLoopState a b count).1[j]! = 0 := by
  induction count with
  | zero => intro j hj hhigh; omega
  | succ n ih =>
    intro j hj hhigh
    rw [divisionLoopState_succ]
    dsimp only
    rw [divisionLoopState_size]
    let shift := a.size - 1 - n - (b.size-1)
    have hfit : shift + b.size ≤ (divisionLoopState a b n).1.size := by
      rw [divisionLoopState_size]
      dsimp [shift]
      omega
    have htop : shift + b.size - 1 = a.size - 1 - n := by dsimp [shift]; omega
    by_cases heq : j = a.size - 1 - n
    · subst j
      rw [← htop]
      have hshift0 : shift + b.size - 1 - (b.size - 1) = shift := by omega
      rw [hshift0]
      exact divisionSubtract_leading_zero _ b shift hb hfit hlead
    · change (divisionSubtract (divisionLoopState a b n).1 b shift
        ((divisionLoopState a b n).1[a.size-1-n]! * b[b.size-1]!.inverse) b.size)[j]! = 0
      rw [divisionSubtract_get _ _ _ _ _ _ (by rw [divisionLoopState_size]; exact hj)]
      rw [ite_eq_right (by dsimp [shift]; omega)]
      exact ih (by omega) j hj (by omega)

/-- The final mutable dividend has no coefficients at or above the divisor's
leading index. This is the long-division remainder degree bound, stated
without imposing a normalized array representation. -/
theorem dividePolynomialcoeff_remainder_degree_bound (a b : PolynomialCoeff)
    (hb : 0 < b.size) (hab : b.size ≤ a.size) (hlead : b[b.size-1]! ≠ 0)
    (j : Nat) (hj : b.size-1 ≤ j) :
    (divisionLoopState a b (a.size+1-b.size)).1[j]! = 0 := by
  by_cases hja : j < a.size
  · exact dividePolynomialcoeff_loop_high_zero a b hb hab hlead _ (Nat.le_refl _)
      j hja (by omega)
  · rw [getElem!_neg _ _ (by rw [divisionLoopState_size]; exact hja)]
    rfl


private theorem empty_quotient_identity {R : Type*} [CommRing R] (a b : R) :
    a = 0*b+a := by ring

/-- For a nonempty divisor with nonzero leading coefficient, a successful
quotient has a remainder of strictly smaller coefficient degree and satisfies
the evaluation identity at every field point. The witness is the final loop
state (or the unchanged dividend when division has no iterations). -/
theorem dividePolynomialcoeff_quotient_remainder_spec {a b q : PolynomialCoeff}
    (hb : 0 < b.size) (hlead : b[b.size-1]! ≠ 0)
    (h : dividePolynomialcoeff a b = .ok q) :
    ∃ r : PolynomialCoeff,
      (∀ x, evalPolyAt a x = evalPolyAt q x * evalPolyAt b x + evalPolyAt r x) ∧
      (∀ j, b.size-1 ≤ j → r[j]! = 0) := by
  by_cases hab : b.size ≤ a.size
  · refine ⟨(divisionLoopState a b (a.size+1-b.size)).1, ?_, ?_⟩
    · exact fun x => dividePolynomialcoeff_eval_identity hb hab h x
    · exact fun j hj => dividePolynomialcoeff_remainder_degree_bound a b hb hab hlead j hj
  · have hlt : a.size < b.size := by omega
    rw [dividePolynomialcoeff_lt_size hlt] at h
    have hq : q = #[] := (Except.ok.inj h).symm
    subst q
    refine ⟨a, ?_, ?_⟩
    · intro x
      change evalPolyAt a x = Fr.zero * evalPolyAt b x + evalPolyAt a x
      exact empty_quotient_identity _ _
    · intro j hj
      rw [getElem!_neg _ _ (by omega)]
      rfl

end EthLib.Cryptography.Kzg
