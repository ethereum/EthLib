module

public import EthLib.Cryptography.Proofs.MillerReciprocity
public import EthLib.Cryptography.Proofs.MillerUnique

/-!
# Proofs: linearity of an ate-type pairing

An ate-type pairing evaluates a quotient of products of lines, built from `Q`, at a point `P`.

The final exponentiation then raises the value to a fixed power `N`.

Let `σ` be the map `z -> z^q` of the field, and let it fix the coefficients of the curve.

Let `pi` be the map `(x, y) -> (σ x, σ y)` on the points of the curve.

The quotient for `Q` has the divisor `sum_j c_j ((pi^j Q) - (O))`, for fixed integers `c_j`.

Let `n = sum_j c_j q^j`, and let `z^(N n)` be 1 for every nonzero `z`.

Let `Q` lie in a group that `pi` maps into itself, where `pi` fixes only `O`.

Let `P` be fixed by `pi`.

Then the power `N` of the value is linear in `Q`, and also in `P` when `N` is even.

In `P`, Weil reciprocity with the function `g_{P₁,P₂}` leaves the factor `g_{P₁,P₂}(Q)^n`.

In `Q`, the quotients for `Q₁`, `Q₂` and `Q₁ + Q₂` differ by a product of functions `g`.

That product takes the value `g_{Q₁,Q₂}(P)^n`.

Both factors become 1 after the final exponentiation.

So does the sign of Weil reciprocity, when `N` is even.

The proof does not go through the Tate pairing.

See Miller, "The Weil Pairing, and Its Efficient Calculation", J. Cryptology 17 (2004).

Its Proposition 7, in Section 4.2, proves linearity of the Weil pairing with Weil reciprocity.

See [Vercauteren](https://eprint.iacr.org/2008/096), "Optimal pairings", Section 2.2.

There, `pi` fixes the first group of an ate pairing, and acts as `q` on the second.
-/

@[expose] public section

namespace EthLib.Cryptography.Miller

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K] {W : WeierstrassCurve.Affine K}

/-! ## The map of points -/

section Frobenius

variable (σ : K →+* K) (hW : W.map σ = W)

include hW

omit [DecidableEq K] in
/-- The image of a nonsingular point is nonsingular. -/
theorem nonsingular_map {x y : K} (h : W.Nonsingular x y) : W.Nonsingular (σ x) (σ y) := by
  have h' := (W.map_nonsingular σ.injective x y).mpr h
  rwa [hW] at h'

omit [DecidableEq K] in
/-- The map `σ` commutes with the negation of `y`. -/
theorem negY_map (x y : K) : W.negY (σ x) (σ y) = σ (W.negY x y) := by
  have h := map_negY (W' := W) σ x y
  rwa [hW] at h

/-- The map `σ` commutes with the slope. -/
theorem slope_map (x₁ x₂ y₁ y₂ : K) :
    W.slope (σ x₁) (σ x₂) (σ y₁) (σ y₂) = σ (W.slope x₁ x₂ y₁ y₂) := by
  have h := map_slope (W := W) σ x₁ x₂ y₁ y₂
  rwa [hW] at h

omit [DecidableEq K] in
/-- The map `σ` commutes with the `x` of a sum. -/
theorem addX_map (x₁ x₂ ℓ : K) : W.addX (σ x₁) (σ x₂) (σ ℓ) = σ (W.addX x₁ x₂ ℓ) := by
  have h := map_addX (W' := W) σ x₁ x₂ ℓ
  rwa [hW] at h

omit [DecidableEq K] in
/-- The map `σ` commutes with the `y` of a sum. -/
theorem addY_map (x₁ x₂ y₁ ℓ : K) :
    W.addY (σ x₁) (σ x₂) (σ y₁) (σ ℓ) = σ (W.addY x₁ x₂ y₁ ℓ) := by
  have h := map_addY (W' := W) σ (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (ℓ := ℓ)
  rwa [hW] at h

omit [DecidableEq K] in
/-- Two images are opposite exactly when the two points are. -/
theorem opposite_map_iff {x₁ y₁ x₂ y₂ : K} :
    (σ x₁ = σ x₂ ∧ σ y₁ = W.negY (σ x₂) (σ y₂)) ↔ (x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
  rw [negY_map σ hW, σ.injective.eq_iff, σ.injective.eq_iff]

/-- The map `(x, y) -> (σ x, σ y)` on the points of the curve, with `O` to `O`. -/
noncomputable def mapPointFun : W.Point → W.Point
  | .zero => .zero
  | .some x y h => .some (σ x) (σ y) (nonsingular_map σ hW h)

/-- The map of points preserves addition, since `σ` preserves the slope and the formulas. -/
theorem mapPointFun_add (P Q : W.Point) :
    mapPointFun σ hW (P + Q) = mapPointFun σ hW P + mapPointFun σ hW Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    simp only [mapPointFun]
    rw [Point.add_of_Y_eq ((opposite_map_iff σ hW).mpr hxy).1 ((opposite_map_iff σ hW).mpr hxy).2]
    rfl
  · rw [Point.add_some hxy]
    simp only [mapPointFun]
    rw [Point.add_some (fun h => hxy ((opposite_map_iff σ hW).mp h)), Point.some.injEq,
      slope_map σ hW, addX_map σ hW, addY_map σ hW]
    exact ⟨rfl, rfl⟩

/-- The map `(x, y) -> (σ x, σ y)` on the points of the curve, a group homomorphism. -/
noncomputable def mapPoint : W.Point →+ W.Point where
  toFun := mapPointFun σ hW
  map_zero' := rfl
  map_add' := mapPointFun_add σ hW

/-- The map of points on a finite point. -/
theorem mapPoint_some {x y : K} (h : W.Nonsingular x y) :
    mapPoint σ hW (.some x y h) = .some (σ x) (σ y) (nonsingular_map σ hW h) := rfl

/-- The line through two images, at an image, takes the image of the value. -/
theorem line_mapPoint (T S : W.Point) (x y : K) :
    line W (mapPoint σ hW T) (mapPoint σ hW S) (σ x) (σ y) = σ (line W T S x y) := by
  rcases T with _ | ⟨x₁, y₁, h₁⟩ <;> rcases S with _ | ⟨x₂, y₂, h₂⟩
  · exact (map_one σ).symm
  · exact (map_sub σ x x₂).symm
  · exact (map_sub σ x x₁).symm
  · simp only [mapPoint_some, line, opposite_map_iff σ hW]
    split_ifs <;> simp [slope_map σ hW]

/-- The same holds at `O`, where every line is 1. -/
theorem lineAt_mapPoint (l : W.Point × W.Point) (R : W.Point) :
    lineAt (mapPoint σ hW l.1, mapPoint σ hW l.2) (mapPoint σ hW R) = σ (lineAt l R) := by
  rcases R with _ | ⟨x, y, h⟩
  · exact (map_one σ).symm
  · exact line_mapPoint σ hW l.1 l.2 x y

/-- The same holds for the `j`-th iterate. -/
theorem lineAt_iterate_mapPoint (l : W.Point × W.Point) (R : W.Point) (j : ℕ) :
    lineAt ((mapPoint σ hW)^[j] l.1, (mapPoint σ hW)^[j] l.2) ((mapPoint σ hW)^[j] R) =
      σ^[j] (lineAt l R) := by
  induction j generalizing l R with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply]
    exact (ih (mapPoint σ hW l.1, mapPoint σ hW l.2) (mapPoint σ hW R)).trans
      (congrArg _ (lineAt_mapPoint σ hW l R))

/-- The map of points is injective, since `σ` is. -/
theorem mapPoint_injective : Function.Injective (mapPoint σ hW) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · cases h
  · cases h
  · obtain ⟨hx, hy⟩ := Point.some.inj h
    obtain rfl := σ.injective hx
    obtain rfl := σ.injective hy
    rfl

end Frobenius

/-! ## Quotients of products of lines -/

variable (W) in
/-- A quotient of two products of lines: the lines of the numerator, then of the denominator. -/
abbrev LineRatio : Type _ := Multiset (W.Point × W.Point) × Multiset (W.Point × W.Point)

/-- The value of a quotient of products of lines at a point of the curve, with 1 at `O`. -/
noncomputable def ratioAt (M : LineRatio W) (R : W.Point) : K := linesAt M.1 R / linesAt M.2 R

/-- The divisor of a quotient of products of lines. -/
noncomputable def ratioDivisor (M : LineRatio W) : W.Point →₀ ℤ :=
  linesDivisor W M.1 - linesDivisor W M.2

/-- Every quotient is 1 at `O`. -/
@[simp] theorem ratioAt_zero (M : LineRatio W) : ratioAt M 0 = 1 := by simp [ratioAt]

/-- The value of a union of lines is the product of the values. -/
theorem linesAt_add (A B : Multiset (W.Point × W.Point)) (R : W.Point) :
    linesAt (A + B) R = linesAt A R * linesAt B R := by
  rw [linesAt, Multiset.map_add, Multiset.prod_add, linesAt, linesAt]

/-- Taking each line `n` times raises the value to the power `n`. -/
theorem linesAt_nsmul (n : ℕ) (A : Multiset (W.Point × W.Point)) (R : W.Point) :
    linesAt (n • A) R = linesAt A R ^ n := by
  rw [linesAt, Multiset.map_nsmul, Multiset.prod_nsmul, linesAt]

/-- Taking each line `n` times adds no zero. -/
theorem linesZeros_nsmul_subset (n : ℕ) (A : Multiset (W.Point × W.Point)) :
    ∀ R ∈ linesZeros (n • A), R ∈ linesZeros A := by
  intro R hR
  induction n with
  | zero => simp [linesZeros] at hR
  | succ n ih =>
    rw [succ_nsmul, linesZeros_add, Multiset.mem_add] at hR
    exact hR.elim ih id

/-- The product of two quotients has the product of their values. -/
theorem ratioAt_add (M M' : LineRatio W) (R : W.Point) :
    ratioAt (M + M') R = ratioAt M R * ratioAt M' R := by
  simp only [ratioAt, Prod.fst_add, Prod.snd_add, linesAt_add, mul_div_mul_comm]

/-- The product of two quotients has the sum of their divisors. -/
theorem ratioDivisor_add (M M' : LineRatio W) :
    ratioDivisor (M + M') = ratioDivisor M + ratioDivisor M' := by
  simp only [ratioDivisor, Prod.fst_add, Prod.snd_add, linesDivisor_add]
  abel

/-- The empty quotient has the divisor 0. -/
@[simp] theorem ratioDivisor_zero : ratioDivisor (0 : LineRatio W) = 0 := by
  simp [ratioDivisor, linesDivisor]

/-- The quotient to the power `c`: the lines repeated `|c|` times, and swapped when `c < 0`. -/
noncomputable def zpowRatio (M : LineRatio W) (c : ℤ) : LineRatio W :=
  if 0 ≤ c then (c.toNat • M.1, c.toNat • M.2) else ((-c).toNat • M.2, (-c).toNat • M.1)

/-- The quotient to the power `c` has the value to the power `c`. -/
theorem ratioAt_zpowRatio (M : LineRatio W) (c : ℤ) (R : W.Point) :
    ratioAt (zpowRatio M c) R = ratioAt M R ^ c := by
  unfold zpowRatio ratioAt
  split_ifs with hc
  · rw [linesAt_nsmul, linesAt_nsmul, ← div_pow, ← zpow_natCast, Int.toNat_of_nonneg hc]
  · rw [linesAt_nsmul, linesAt_nsmul, ← div_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega), ← inv_div, inv_zpow', neg_neg]

/-- The quotient to the power `c` has `c` times the divisor. -/
theorem ratioDivisor_zpowRatio (M : LineRatio W) (c : ℤ) :
    ratioDivisor (zpowRatio M c) = c • ratioDivisor M := by
  unfold zpowRatio ratioDivisor
  split_ifs with hc
  · simp only [linesDivisor_nsmul, ← smul_sub, ← natCast_zsmul, Int.toNat_of_nonneg hc]
  · simp only [linesDivisor_nsmul, ← natCast_zsmul, Int.toNat_of_nonneg (by omega : 0 ≤ -c),
      neg_smul, smul_sub]
    abel

/-- The quotient to the power `c` adds no zero. -/
theorem linesZeros_zpowRatio (M : LineRatio W) (c : ℤ) :
    ∀ R ∈ linesZeros ((zpowRatio M c).1 + (zpowRatio M c).2), R ∈ linesZeros (M.1 + M.2) := by
  intro R hR
  unfold zpowRatio at hR
  rw [linesZeros_add] at hR ⊢
  split_ifs at hR <;> simp only [Multiset.mem_add] at hR ⊢
  · exact hR.imp (linesZeros_nsmul_subset _ _ R) (linesZeros_nsmul_subset _ _ R)
  · exact (hR.imp (linesZeros_nsmul_subset _ _ R) (linesZeros_nsmul_subset _ _ R)).symm

/-- A product of lines does not vanish at `O`, nor away from the zeros of its lines. -/
theorem linesAt_ne_zero {A : Multiset (W.Point × W.Point)} {R : W.Point}
    (h : R ∈ linesZeros A → R = 0) : linesAt A R ≠ 0 := fun h0 => by
  have hR := h (mem_linesZeros_of_linesAt_eq_zero h0)
  rw [hR, linesAt_zero] at h0
  exact one_ne_zero h0

/-- A quotient does not vanish at `O`, nor away from the zeros of its lines. -/
theorem ratioAt_ne_zero {M : LineRatio W} {R : W.Point}
    (h : R ∈ linesZeros (M.1 + M.2) → R = 0) : ratioAt M R ≠ 0 := by
  rw [linesZeros_add] at h
  exact div_ne_zero (linesAt_ne_zero fun hR => h (Multiset.mem_add.mpr (.inl hR)))
    (linesAt_ne_zero fun hR => h (Multiset.mem_add.mpr (.inr hR)))

/-- Two quotients with the same divisor take the same value at a point.

The point is not a zero of the denominators.

The two quotients are the same function, with no constant left, since every line is normalized.
-/
theorem ratioAt_eq_of_ratioDivisor {M₁ M₂ : LineRatio W} (h : ratioDivisor M₁ = ratioDivisor M₂)
    {R : W.Point} (h₁ : linesAt M₁.2 R ≠ 0) (h₂ : linesAt M₂.2 R ≠ 0) :
    ratioAt M₁ R = ratioAt M₂ R := by
  rcases R with _ | ⟨x, y, hR⟩
  · exact (ratioAt_zero M₁).trans (ratioAt_zero M₂).symm
  have he := congrArg (evalAt W hR.1) (linesElem_mul_eq_of_linesDivisor h)
  simp only [map_mul, evalAt_linesElem] at he
  rw [ratioAt, ratioAt, div_eq_div_iff h₁ h₂]
  exact he

/-! ## The function `g` through two points -/

/-- The function `g_{A,B}`: the line through `A` and `B`, over the vertical through `A + B`. -/
def chordRatio (A B : W.Point) : LineRatio W := ({(A, B)}, {(A + B, -(A + B))})

/-- The function `g_{A,B}` has the divisor `(A) + (B) - (A + B) - (O)`. -/
theorem ratioDivisor_chordRatio (A B : W.Point) :
    ratioDivisor (chordRatio A B) =
      Finsupp.single A 1 + Finsupp.single B 1 - Finsupp.single (A + B) 1 - Finsupp.single 0 1 := by
  rw [ratioDivisor, chordRatio, linesDivisor_singleton, linesDivisor_singleton]
  exact lineDivisor_sub_add A B

/-! ## Lines through a group of points -/

/-- Every line of the quotient passes through two points of the group `G`. -/
def LinesIn (G : AddSubgroup W.Point) (M : LineRatio W) : Prop :=
  ∀ l ∈ M.1 + M.2, l.1 ∈ G ∧ l.2 ∈ G

/-- If its lines pass through points of `G`, the quotient vanishes only at points of `G`. -/
theorem LinesIn.mem {G : AddSubgroup W.Point} {M : LineRatio W} (hM : LinesIn G M) :
    ∀ R ∈ linesZeros (M.1 + M.2), R ∈ G := by
  intro R hR
  obtain ⟨l, hl, hR⟩ := Multiset.mem_bind.mp hR
  obtain ⟨h1, h2⟩ := hM l hl
  simp only [lineZeros, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hR
  rcases hR with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact G.neg_mem (G.add_mem h1 h2)

/-- A product of two quotients through `G` is through `G`. -/
theorem LinesIn.add {G : AddSubgroup W.Point} {M M' : LineRatio W} (hM : LinesIn G M)
    (hM' : LinesIn G M') : LinesIn G (M + M') := by
  intro l hl
  simp only [Prod.fst_add, Prod.snd_add, Multiset.mem_add] at hl
  rcases hl with (hl | hl) | hl | hl
  · exact hM l (Multiset.mem_add.mpr (.inl hl))
  · exact hM' l (Multiset.mem_add.mpr (.inl hl))
  · exact hM l (Multiset.mem_add.mpr (.inr hl))
  · exact hM' l (Multiset.mem_add.mpr (.inr hl))

/-- A power of a quotient through `G` is through `G`. -/
theorem LinesIn.zpowRatio {G : AddSubgroup W.Point} {M : LineRatio W} (hM : LinesIn G M)
    (c : ℤ) : LinesIn G (zpowRatio M c) := by
  intro l hl
  apply hM l
  unfold Miller.zpowRatio at hl
  split_ifs at hl <;> simp only [Multiset.mem_add] at hl ⊢
  · exact hl.imp Multiset.mem_of_mem_nsmul Multiset.mem_of_mem_nsmul
  · exact (hl.imp Multiset.mem_of_mem_nsmul Multiset.mem_of_mem_nsmul).symm

/-- The function `g` through two points of `G` is through `G`. -/
theorem LinesIn.chordRatio {G : AddSubgroup W.Point} {A B : W.Point} (hA : A ∈ G) (hB : B ∈ G) :
    LinesIn G (chordRatio A B) := by
  intro l hl
  simp only [Miller.chordRatio, Multiset.mem_add, Multiset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact ⟨hA, hB⟩
  · exact ⟨G.add_mem hA hB, G.neg_mem (G.add_mem hA hB)⟩

/-! ## Values at divisors -/

/-- The value at a sum of divisors is the product of the values.

The function must not vanish on the supports of the two divisors. -/
theorem evalDivisor_add {φ : W.Point → K} {D E : W.Point →₀ ℤ}
    (h : ∀ R ∈ D.support ∪ E.support, φ R ≠ 0) :
    evalDivisor φ (D + E) = evalDivisor φ D * evalDivisor φ E :=
  Finsupp.prod_add_index (fun _ _ => zpow_zero _) fun R hR _ _ => zpow_add₀ (h R hR) _ _

omit [DecidableEq K] in
/-- The value at `n (R)` is the value at `R` to the power `n`. -/
theorem evalDivisor_single (φ : W.Point → K) (R : W.Point) (n : ℤ) :
    evalDivisor φ (Finsupp.single R n) = φ R ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

/-- The value at `c ((A) - (O))` of a function worth 1 at `O` and not zero at `A`. -/
private theorem evalDivisor_smul_sub {φ : W.Point → K} (h0 : φ 0 = 1) {A : W.Point}
    (hA : φ A ≠ 0) (c : ℤ) :
    evalDivisor φ (c • (Finsupp.single A 1 - Finsupp.single 0 1)) = φ A ^ c := by
  rw [smul_sub, Finsupp.smul_single_one, Finsupp.smul_single_one, sub_eq_add_neg,
    ← Finsupp.single_neg, evalDivisor_add, evalDivisor_single, evalDivisor_single, h0, one_zpow,
    mul_one]
  intro R hR
  rcases Finset.mem_union.mp hR with hR | hR <;>
    rcases Finset.mem_singleton.mp (Finsupp.support_single_subset hR) with rfl
  · exact hA
  · rw [h0]
    exact one_ne_zero

/-! ## Divisors of ate-type functions -/

/-- The divisor `sum_j c_j ((pi^j Q) - (O))`, for the list of the pairs `(j, c_j)`. -/
noncomputable def ateDivisor (π : W.Point → W.Point) (Q : W.Point) (L : List (ℕ × ℤ)) :
    W.Point →₀ ℤ :=
  (L.map fun jc => jc.2 • (Finsupp.single (π^[jc.1] Q) 1 - Finsupp.single 0 1)).sum

/-- The exponent `sum_j c_j q^j`, for the list of the pairs `(j, c_j)`. -/
def ateExponent (q : ℕ) (L : List (ℕ × ℤ)) : ℤ := (L.map fun jc => jc.2 * (q : ℤ) ^ jc.1).sum

/-- The product of the powers `g_{pi^j Q₁, pi^j Q₂}^(c_j)`, for the list of the pairs `(j, c_j)`.
-/
noncomputable def ateChords (π : W.Point → W.Point) (Q₁ Q₂ : W.Point) (L : List (ℕ × ℤ)) :
    LineRatio W :=
  (L.map fun jc => zpowRatio (chordRatio (π^[jc.1] Q₁) (π^[jc.1] Q₂)) jc.2).sum

/-- Take a function worth 1 at `O`, with `φ(pi^j Q) = φ(Q)^(q^j)` and `φ(Q) ≠ 0`.

At the divisor `sum_j c_j ((pi^j Q) - (O))`, it takes the value `φ(Q)^(sum_j c_j q^j)`. -/
theorem evalDivisor_ateDivisor {π : W.Point → W.Point} {Q : W.Point} {q : ℕ} {φ : W.Point → K}
    (h0 : φ 0 = 1) (hπ : ∀ j, φ (π^[j] Q) = φ Q ^ q ^ j) (hQ : φ Q ≠ 0) (L : List (ℕ × ℤ)) :
    evalDivisor φ (ateDivisor π Q L) = φ Q ^ ateExponent q L := by
  have hne : ∀ j, φ (π^[j] Q) ≠ 0 := fun j => by
    rw [hπ]
    exact pow_ne_zero _ hQ
  -- Every point of the support is `O` or some `pi^j Q`, where the function does not vanish.
  have hsupp : ∀ L : List (ℕ × ℤ), ∀ R ∈ (ateDivisor π Q L).support, φ R ≠ 0 := by
    intro L
    induction L with
    | nil => simp [ateDivisor]
    | cons jc L ih =>
      intro R hR
      rw [ateDivisor, List.map_cons, List.sum_cons] at hR
      rcases Finset.mem_union.mp (Finsupp.support_add hR) with hR | hR
      · rw [smul_sub, Finsupp.smul_single_one, Finsupp.smul_single_one] at hR
        rcases Finset.mem_union.mp (Finsupp.support_sub hR) with hR | hR <;>
          rcases Finset.mem_singleton.mp (Finsupp.support_single_subset hR) with rfl
        · exact hne _
        · rw [h0]
          exact one_ne_zero
      · exact ih R hR
  induction L with
  | nil => simp [ateDivisor, ateExponent, evalDivisor]
  | cons jc L ih =>
    have hR : ∀ R ∈ (jc.2 • (Finsupp.single (π^[jc.1] Q) (1 : ℤ) - Finsupp.single 0 1)).support,
        φ R ≠ 0 := fun R h => hsupp [jc] R (by simpa [ateDivisor] using h)
    rw [ateDivisor, List.map_cons, List.sum_cons, evalDivisor_add, evalDivisor_smul_sub h0 (hne _),
      ← ateDivisor, ih, hπ, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hQ]
    · congr 1
      simp only [ateExponent, List.map_cons, List.sum_cons]
      push_cast
      ring
    · intro R hR'
      rcases Finset.mem_union.mp hR' with h | h
      · exact hR R h
      · exact hsupp L R h

/-- That product has the divisor `D(Q₁) + D(Q₂) - D(Q₁ + Q₂)`.

Here `D(Q)` is the divisor `sum_j c_j ((pi^j Q) - (O))`, and `pi` is additive. -/
theorem ratioDivisor_ateChords (π : W.Point →+ W.Point) (Q₁ Q₂ : W.Point) (L : List (ℕ × ℤ)) :
    ratioDivisor (ateChords π Q₁ Q₂ L) =
      ateDivisor π Q₁ L + ateDivisor π Q₂ L - ateDivisor π (Q₁ + Q₂) L := by
  induction L with
  | nil => simp [ateChords, ateDivisor]
  | cons jc L ih =>
    rw [ateChords, List.map_cons, List.sum_cons, ratioDivisor_add, ← ateChords, ih,
      ratioDivisor_zpowRatio, ratioDivisor_chordRatio, ← iterate_map_add]
    simp only [ateDivisor, List.map_cons, List.sum_cons, smul_sub, smul_add]
    abel

/-- The empty quotient is through every group. -/
theorem LinesIn.zero (G : AddSubgroup W.Point) : LinesIn G (0 : LineRatio W) := by
  intro l hl
  simp at hl

/-- If `pi` maps `G` into itself, the product of the powers of `g` is through `G`. -/
theorem LinesIn.ateChords {G : AddSubgroup W.Point} {π : W.Point →+ W.Point}
    (hGπ : ∀ R ∈ G, π R ∈ G) {Q₁ Q₂ : W.Point} (h₁ : Q₁ ∈ G) (h₂ : Q₂ ∈ G)
    (L : List (ℕ × ℤ)) : LinesIn G (ateChords π Q₁ Q₂ L) := by
  have hit : ∀ (j : ℕ), ∀ R ∈ G, π^[j] R ∈ G := by
    intro j
    induction j with
    | zero => exact fun R hR => hR
    | succ j ih =>
      intro R hR
      rw [Function.iterate_succ_apply]
      exact ih _ (hGπ R hR)
  induction L with
  | nil => exact LinesIn.zero G
  | cons jc L ih =>
    rw [Miller.ateChords, List.map_cons, List.sum_cons]
    exact ((LinesIn.chordRatio (hit _ _ h₁) (hit _ _ h₂)).zpowRatio _).add ih

/-- A quotient is through `G` when its numerator and its denominator are. -/
theorem LinesIn.of_mem {G : AddSubgroup W.Point} {M : LineRatio W}
    (h₁ : ∀ l ∈ M.1, l.1 ∈ G ∧ l.2 ∈ G) (h₂ : ∀ l ∈ M.2, l.1 ∈ G ∧ l.2 ∈ G) : LinesIn G M :=
  fun l hl => (Multiset.mem_add.mp hl).elim (h₁ l) (h₂ l)

/-- The lines of Miller's algorithm for a point of `G` pass through points of `G`.

They pass through multiples of that point. -/
theorem LinesIn.lines {G : AddSubgroup W.Point} {Q : W.Point} (hQ : Q ∈ G) (s : ℕ) :
    LinesIn G (lines W s Q) := by
  have key : ∀ (n : ℕ) (T : W.Point) (M : LineRatio W), T ∈ G → LinesIn G M →
      LinesIn G (lineSteps W s Q n T M) := by
    intro n
    induction n with
    | zero => exact fun _ _ _ hM => hM
    | succ n ih =>
      intro T M hT hM
      have h2 := G.add_mem hT hT
      have h3 := G.add_mem h2 hQ
      have hM₁ : ∀ l ∈ 2 • M.1, l.1 ∈ G ∧ l.2 ∈ G := fun l hl =>
        hM l (Multiset.mem_add.mpr (.inl (Multiset.mem_of_mem_nsmul hl)))
      have hM₂ : ∀ l ∈ 2 • M.2, l.1 ∈ G ∧ l.2 ∈ G := fun l hl =>
        hM l (Multiset.mem_add.mpr (.inr (Multiset.mem_of_mem_nsmul hl)))
      rw [lineSteps]
      split_ifs
      · refine ih _ _ h3 (LinesIn.of_mem (fun l hl => ?_) fun l hl => ?_)
        · rcases Multiset.mem_add.mp hl with hl | hl
          · exact hM₁ l hl
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hl
          rcases hl with rfl | rfl
          · exact ⟨hT, hT⟩
          · exact ⟨h2, hQ⟩
        · rcases Multiset.mem_add.mp hl with hl | hl
          · exact hM₂ l hl
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hl
          rcases hl with rfl | rfl
          · exact ⟨h2, G.neg_mem h2⟩
          · exact ⟨h3, G.neg_mem h3⟩
      · refine ih _ _ h2 (LinesIn.of_mem (fun l hl => ?_) fun l hl => ?_)
        · rcases Multiset.mem_add.mp hl with hl | hl
          · exact hM₁ l hl
          rw [Multiset.mem_singleton] at hl
          subst hl
          exact ⟨hT, hT⟩
        · rcases Multiset.mem_add.mp hl with hl | hl
          · exact hM₂ l hl
          rw [Multiset.mem_singleton] at hl
          subst hl
          exact ⟨h2, G.neg_mem h2⟩
  exact key _ _ _ hQ (LinesIn.zero G)

/-- The denominator of a quotient through `G` vanishes only at points of `G`. -/
theorem LinesIn.linesAt_snd_ne_zero {G : AddSubgroup W.Point} {M : LineRatio W}
    (hM : LinesIn G M) {R : W.Point} (hR : R ∈ G → R = 0) : linesAt M.2 R ≠ 0 :=
  linesAt_ne_zero fun h => hR (hM.mem R (by
    rw [linesZeros_add]
    exact Multiset.mem_add.mpr (.inr h)))

/-- A quotient through `G` vanishes only at points of `G`. -/
theorem LinesIn.ratioAt_ne_zero {G : AddSubgroup W.Point} {M : LineRatio W}
    (hM : LinesIn G M) {R : W.Point} (hR : R ∈ G → R = 0) : ratioAt M R ≠ 0 :=
  Miller.ratioAt_ne_zero fun h => hR (hM.mem R h)

/-- The value of `g_{A,B}`: the line through `A` and `B`, over the vertical through `A + B`. -/
theorem ratioAt_chordRatio (A B R : W.Point) :
    ratioAt (chordRatio A B) R = lineAt (A, B) R / lineAt (A + B, -(A + B)) R := by
  simp [ratioAt, chordRatio, linesAt]

section Frobenius

variable {σ : K →+* K} {hW : W.map σ = W}

omit [DecidableEq K] in
/-- If `σ` is the map `z -> z^q`, its `j`-th iterate is the map `z -> z^(q^j)`. -/
theorem iterate_eq_pow {q : ℕ} (hσ : ∀ z, σ z = z ^ q) (j : ℕ) (z : K) :
    σ^[j] z = z ^ q ^ j := by
  induction j generalizing z with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply, ih, hσ, ← pow_mul, pow_succ']

/-- The function `g` through `pi^j A` and `pi^j B`, at `pi^j R`, is `g_{A,B}(R)^(q^j)`. -/
theorem ratioAt_chordRatio_iterate {q : ℕ} (hσ : ∀ z, σ z = z ^ q) (A B R : W.Point) (j : ℕ) :
    ratioAt (chordRatio ((mapPoint σ hW)^[j] A) ((mapPoint σ hW)^[j] B))
        ((mapPoint σ hW)^[j] R) =
      ratioAt (chordRatio A B) R ^ q ^ j := by
  rw [ratioAt_chordRatio, ratioAt_chordRatio, ← iterate_map_add, ← iterate_map_neg]
  rw [lineAt_iterate_mapPoint σ hW (A, B), lineAt_iterate_mapPoint σ hW (A + B, -(A + B)),
    iterate_eq_pow hσ, iterate_eq_pow hσ, div_pow]

/-- Take the product of the powers `g_{pi^j Q₁, pi^j Q₂}^(c_j)`, at a point `P` fixed by `pi`.

Its value is `g_{Q₁,Q₂}(P)^(sum_j c_j q^j)`. -/
theorem ratioAt_ateChords {q : ℕ} (hσ : ∀ z, σ z = z ^ q) (Q₁ Q₂ : W.Point) {P : W.Point}
    (hP : mapPoint σ hW P = P) (hy : ratioAt (chordRatio Q₁ Q₂) P ≠ 0) (L : List (ℕ × ℤ)) :
    ratioAt (ateChords (mapPoint σ hW) Q₁ Q₂ L) P =
      ratioAt (chordRatio Q₁ Q₂) P ^ ateExponent q L := by
  induction L with
  | nil => simp [ateChords, ateExponent, ratioAt, linesAt]
  | cons jc L ih =>
    have hj := ratioAt_chordRatio_iterate (hW := hW) hσ Q₁ Q₂ P jc.1
    rw [Function.iterate_fixed hP] at hj
    rw [ateChords, List.map_cons, List.sum_cons, ratioAt_add, ← ateChords, ih,
      ratioAt_zpowRatio, hj, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hy]
    congr 1
    simp only [ateExponent, List.map_cons, List.sum_cons]
    push_cast
    ring

/-- The function `g` through two points fixed by `pi` does not vanish on `G`.

In `G`, only `O` is fixed by `pi`, and `g` is 1 there. -/
theorem ratioAt_chordRatio_ne_zero {G : AddSubgroup W.Point}
    (hG : ∀ R ∈ G, mapPoint σ hW R = R → R = 0) {Q : W.Point} (hQ : Q ∈ G) {P₁ P₂ : W.Point}
    (hP₁ : mapPoint σ hW P₁ = P₁) (hP₂ : mapPoint σ hW P₂ = P₂) :
    ratioAt (chordRatio P₁ P₂) Q ≠ 0 := by
  by_cases hQ0 : Q = 0
  · rw [hQ0, ratioAt_zero]
    exact one_ne_zero
  refine (LinesIn.chordRatio (G := AddMonoidHom.eqLocus (mapPoint σ hW) (AddMonoidHom.id _))
    hP₁ hP₂).ratioAt_ne_zero fun h => absurd (hG Q hQ h) hQ0

/-! ## Linearity -/

/-- Linearity in `Q`, before the final exponentiation.

Let `pi` map the group `G` into itself, and fix no point of `G` but `O`.

Take three quotients through `G`, with the divisors `sum_j c_j ((pi^j Q) - (O))`.

Here `Q` is `Q₁`, `Q₂` and `Q₁ + Q₂`.

At a point `P` fixed by `pi`, the values differ by `g_{Q₁,Q₂}(P)` to the power `sum_j c_j q^j`.
-/
theorem ratioAt_mul_ratioAt_right {q : ℕ} (hσ : ∀ z, σ z = z ^ q) {G : AddSubgroup W.Point}
    (hGπ : ∀ R ∈ G, mapPoint σ hW R ∈ G) (hG : ∀ R ∈ G, mapPoint σ hW R = R → R = 0)
    {Q₁ Q₂ : W.Point} (h₁ : Q₁ ∈ G) (h₂ : Q₂ ∈ G) {L : List (ℕ × ℤ)} {M₁ M₂ M₃ : LineRatio W}
    (hM₁ : LinesIn G M₁) (hM₂ : LinesIn G M₂) (hM₃ : LinesIn G M₃)
    (hd₁ : ratioDivisor M₁ = ateDivisor (mapPoint σ hW) Q₁ L)
    (hd₂ : ratioDivisor M₂ = ateDivisor (mapPoint σ hW) Q₂ L)
    (hd₃ : ratioDivisor M₃ = ateDivisor (mapPoint σ hW) (Q₁ + Q₂) L)
    {P : W.Point} (hP : mapPoint σ hW P = P) :
    ratioAt M₁ P * ratioAt M₂ P =
      ratioAt M₃ P * ratioAt (chordRatio Q₁ Q₂) P ^ ateExponent q L := by
  have hPG : P ∈ G → P = 0 := fun h => hG P h hP
  have hC := LinesIn.ateChords hGπ h₁ h₂ L
  have hd : ratioDivisor (M₁ + M₂) =
      ratioDivisor (M₃ + ateChords (mapPoint σ hW) Q₁ Q₂ L) := by
    rw [ratioDivisor_add, ratioDivisor_add, hd₁, hd₂, hd₃, ratioDivisor_ateChords]
    abel
  have he := ratioAt_eq_of_ratioDivisor hd ((hM₁.add hM₂).linesAt_snd_ne_zero hPG)
    ((hM₃.add hC).linesAt_snd_ne_zero hPG)
  rwa [ratioAt_add, ratioAt_add, ratioAt_ateChords hσ Q₁ Q₂ hP
    ((LinesIn.chordRatio h₁ h₂).ratioAt_ne_zero hPG)] at he

/-- Linearity in `P`, before the final exponentiation.

Let `pi` fix no point of the group `G` but `O`, and let `Q` be in `G`.

Take a quotient through `G`, with the divisor `sum_j c_j ((pi^j Q) - (O))`.

Let `P₁` and `P₂` be fixed by `pi`.

The product of the values at `P₁` and `P₂` is the value at `P₁ + P₂`, times two factors.

One is a sign, and the other is `g_{P₁,P₂}(Q)` to the power `sum_j c_j q^j`.

The proof is Weil reciprocity for the quotient and `g_{P₁,P₂}`. -/
theorem ratioAt_mul_ratioAt_left {q : ℕ} (hσ : ∀ z, σ z = z ^ q) {G : AddSubgroup W.Point}
    (hG : ∀ R ∈ G, mapPoint σ hW R = R → R = 0) {Q : W.Point} (hQ : Q ∈ G)
    {L : List (ℕ × ℤ)} {M : LineRatio W} (hM : LinesIn G M)
    (hd : ratioDivisor M = ateDivisor (mapPoint σ hW) Q L)
    {P₁ P₂ : W.Point} (hP₁ : mapPoint σ hW P₁ = P₁) (hP₂ : mapPoint σ hW P₂ = P₂) :
    ratioAt M P₁ * ratioAt M P₂ =
      (-1) ^ (ratioDivisor M 0 * ratioDivisor (chordRatio P₁ P₂) 0) * ratioAt M (P₁ + P₂) *
        ratioAt (chordRatio P₁ P₂) Q ^ ateExponent q L := by
  set Fix := AddMonoidHom.eqLocus (mapPoint σ hW) (AddMonoidHom.id W.Point)
  have hFix : ∀ R, R ∈ Fix ↔ mapPoint σ hW R = R := fun _ => Iff.rfl
  have hC : LinesIn Fix (chordRatio P₁ P₂) :=
    LinesIn.chordRatio ((hFix _).mpr hP₁) ((hFix _).mpr hP₂)
  -- The function does not vanish at fixed points.
  have hne : ∀ R ∈ Fix, ratioAt M R ≠ 0 := fun R hR => hM.ratioAt_ne_zero fun h =>
    hG R h ((hFix R).mp hR)
  have hQ0 := ratioAt_chordRatio_ne_zero hG hQ hP₁ hP₂
  have hπ : ∀ j, ratioAt (chordRatio P₁ P₂) ((mapPoint σ hW)^[j] Q) =
      ratioAt (chordRatio P₁ P₂) Q ^ q ^ j := fun j => by
    have := ratioAt_chordRatio_iterate (hW := hW) hσ P₁ P₂ Q j
    rwa [Function.iterate_fixed hP₁, Function.iterate_fixed hP₂] at this
  have hw := weil_reciprocity (W := W) (N₁ := M.1) (D₁ := M.2) (N₂ := (chordRatio P₁ P₂).1)
    (D₂ := (chordRatio P₁ P₂).2) (fun R h₁ h₂ => hG R (hM.mem R h₁) ((hFix R).mp
      (hC.mem R h₂)))
  change evalDivisor (ratioAt M) (ratioDivisor (chordRatio P₁ P₂)) =
    (-1) ^ (ratioDivisor M 0 * ratioDivisor (chordRatio P₁ P₂) 0) *
      evalDivisor (ratioAt (chordRatio P₁ P₂)) (ratioDivisor M) at hw
  generalize ratioDivisor M 0 * ratioDivisor (chordRatio P₁ P₂) 0 = k at hw ⊢
  rw [hd, evalDivisor_ateDivisor (ratioAt_zero _) hπ hQ0, ratioDivisor,
    evalDivisor_sub_linesDivisor (ratioAt_zero M) fun R hR => hne R (hC.mem R
      (by rwa [linesZeros_add]))] at hw
  have h12 : P₁ + P₂ ∈ Fix := Fix.add_mem ((hFix _).mpr hP₁) ((hFix _).mpr hP₂)
  have a₁ := hne P₁ ((hFix _).mpr hP₁)
  have a₂ := hne P₂ ((hFix _).mpr hP₂)
  have a₃ := hne _ h12
  have a₄ := hne _ (Fix.neg_mem h12)
  simp only [chordRatio, linesZeros, Multiset.singleton_bind, lineZeros, add_neg_cancel,
    neg_zero, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, ratioAt_zero] at hw
  field_simp at hw
  rw [hw, chordRatio]
  ring

/-- Linearity in `P`, after the final exponentiation `z -> z^N`.

`N` is even, and `z^(N n)` is 1 for every nonzero `z`, with `n = sum_j c_j q^j`. -/
theorem pow_ratioAt_add_left {q : ℕ} (hσ : ∀ z, σ z = z ^ q) {G : AddSubgroup W.Point}
    (hG : ∀ R ∈ G, mapPoint σ hW R = R → R = 0) {Q : W.Point} (hQ : Q ∈ G)
    {L : List (ℕ × ℤ)} {M : LineRatio W} (hM : LinesIn G M)
    (hd : ratioDivisor M = ateDivisor (mapPoint σ hW) Q L)
    {P₁ P₂ : W.Point} (hP₁ : mapPoint σ hW P₁ = P₁) (hP₂ : mapPoint σ hW P₂ = P₂)
    {N : ℕ} (hN : Even N) (hkill : ∀ z : K, z ≠ 0 → z ^ ((N : ℤ) * ateExponent q L) = 1) :
    ratioAt M (P₁ + P₂) ^ N = ratioAt M P₁ ^ N * ratioAt M P₂ ^ N := by
  have h := congrArg (· ^ N) (ratioAt_mul_ratioAt_left hσ hG hQ hM hd hP₁ hP₂)
  simp only [mul_pow] at h
  have hε : ∀ k : ℤ, ((-1 : K) ^ k) ^ N = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hN.neg_one_pow, one_zpow]
  have hy : (ratioAt (chordRatio P₁ P₂) Q ^ ateExponent q L) ^ N = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    exact hkill _ (ratioAt_chordRatio_ne_zero hG hQ hP₁ hP₂)
  rw [h, hε, hy, one_mul, mul_one]

/-- Linearity in `Q`, after the final exponentiation `z -> z^N`.

`z^(N n)` is 1 for every nonzero `z`, with `n = sum_j c_j q^j`. -/
theorem pow_ratioAt_add_right {q : ℕ} (hσ : ∀ z, σ z = z ^ q) {G : AddSubgroup W.Point}
    (hGπ : ∀ R ∈ G, mapPoint σ hW R ∈ G) (hG : ∀ R ∈ G, mapPoint σ hW R = R → R = 0)
    {Q₁ Q₂ : W.Point} (h₁ : Q₁ ∈ G) (h₂ : Q₂ ∈ G) {L : List (ℕ × ℤ)} {M₁ M₂ M₃ : LineRatio W}
    (hM₁ : LinesIn G M₁) (hM₂ : LinesIn G M₂) (hM₃ : LinesIn G M₃)
    (hd₁ : ratioDivisor M₁ = ateDivisor (mapPoint σ hW) Q₁ L)
    (hd₂ : ratioDivisor M₂ = ateDivisor (mapPoint σ hW) Q₂ L)
    (hd₃ : ratioDivisor M₃ = ateDivisor (mapPoint σ hW) (Q₁ + Q₂) L)
    {P : W.Point} (hP : mapPoint σ hW P = P)
    {N : ℕ} (hkill : ∀ z : K, z ≠ 0 → z ^ ((N : ℤ) * ateExponent q L) = 1) :
    ratioAt M₃ P ^ N = ratioAt M₁ P ^ N * ratioAt M₂ P ^ N := by
  have h := congrArg (· ^ N)
    (ratioAt_mul_ratioAt_right hσ hGπ hG h₁ h₂ hM₁ hM₂ hM₃ hd₁ hd₂ hd₃ hP)
  simp only [mul_pow] at h
  have hy : (ratioAt (chordRatio Q₁ Q₂) P ^ ateExponent q L) ^ N = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    exact hkill _ ((LinesIn.chordRatio h₁ h₂).ratioAt_ne_zero fun h => hG P h hP)
  rw [h, hy, mul_one]

end Frobenius

end EthLib.Cryptography.Miller
