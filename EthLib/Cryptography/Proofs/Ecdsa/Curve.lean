module

public import EthLib.Base.Proofs.Nat
public import EthLib.Cryptography.Ecdsa.Curve
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

/-!
# Proofs: ECDSA over a short Weierstrass curve

A signature from the signing operation of SEC 1 v2 §4.1.3 verifies.

A valid signature has `r` and `s` in `[1, n - 1]`, under a key on the curve other than `O`.

`(r, s)` and `(r, n - s)` are valid together.

When `p <= r + n`, they are the only valid signatures with that `r`, key and hash.

Verification is exactly the range checks, the key checks and the check of `R`, in the group.

Each fact is proved once, from the laws that each curve proves of its points.
-/

@[expose] public section

namespace EthLib.Cryptography.Ecdsa

open ShortWeierstrass Rfc6979 Fin.CommRing

namespace Curve

variable {p n : Nat} [NeZero p] [NeZero n] [Params (Fin p)]

/-- What the proofs need of a curve: its points form a group in which `Fin n` acts as `ZMod n`.

`toPoint` sends a point to its group element, and `toZMod` reads a scalar in `ZMod n`.

The base point is on the curve and is not `O`, and the products and the inverse are exact. -/
structure Laws (C : Curve p n) {E : Type*} [AddCommGroup E] [Module (ZMod n) E]
    (toPoint : Point (Fin p) → E) (toZMod : Fin n ≃+* ZMod n) : Prop where
  /-- The base point is on the curve. -/
  isOnCurve_generator : C.generator.isOnCurve = true
  /-- The base point is not `O`. -/
  toPoint_generator_ne_zero : toPoint C.generator ≠ 0
  /-- A product of a point on the curve is on the curve. -/
  isOnCurve_mul : ∀ (k : Fin n) {P : Point (Fin p)}, P.isOnCurve = true →
    (C.mul k P).isOnCurve = true
  /-- The product is `k P` in the group. -/
  toPoint_mul : ∀ (k : Fin n) {P : Point (Fin p)}, P.isOnCurve = true →
    toPoint (C.mul k P) = toZMod k • toPoint P
  /-- The double product is the sum of the two products. -/
  mulAdd_eq : ∀ (k l : Fin n) {P Q : Point (Fin p)}, P.isOnCurve = true → Q.isOnCurve = true →
    C.mulAdd k P l Q = C.mul k P + C.mul l Q
  /-- A sum of points on the curve is on the curve. -/
  isOnCurve_add : ∀ {P Q : Point (Fin p)}, P.isOnCurve = true → Q.isOnCurve = true →
    (P + Q).isOnCurve = true
  /-- The sum is the group's. -/
  toPoint_add : ∀ {P Q : Point (Fin p)}, P.isOnCurve = true → Q.isOnCurve = true →
    toPoint (P + Q) = toPoint P + toPoint Q
  /-- The negative of a point on the curve is on the curve. -/
  isOnCurve_neg : ∀ {P : Point (Fin p)}, P.isOnCurve = true → (-P).isOnCurve = true
  /-- The negative is the group's. -/
  toPoint_neg : ∀ {P : Point (Fin p)}, P.isOnCurve = true → toPoint (-P) = -toPoint P
  /-- Points on the curve with one group element are equal. -/
  toPoint_inj : ∀ {P Q : Point (Fin p)}, P.isOnCurve = true → Q.isOnCurve = true →
    (toPoint P = toPoint Q ↔ P = Q)
  /-- `O` is the zero of the group. -/
  toPoint_infinity : toPoint .infinity = 0
  /-- Two points on the curve with the same `x` have opposite or equal `y`. -/
  y_eq_or_eq_neg : ∀ {x y y' : Fin p}, (Point.affine x y).isOnCurve = true →
    (Point.affine x y').isOnCurve = true → y' = y ∨ y' = -y
  /-- The inverse is the inverse of `ZMod n`. -/
  toZMod_inv : ∀ k : Fin n, toZMod (C.inv k) = (toZMod k)⁻¹

/-! ## Facts without the group -/

omit [NeZero p] [Params (Fin p)] in
/-- A scalar read from a natural number is that number in `ZMod n`, under any ring isomorphism. -/
theorem toZMod_ofNat (toZMod : Fin n ≃+* ZMod n) (e : Nat) :
    toZMod (Fin.ofNat _ e) = (e : ZMod n) := by
  rw [Fin.ofNat_eq_cast]
  exact map_natCast toZMod e

variable (C : Curve p n)

/-- A valid signature has `r` and `s` in `[1, n - 1]`. -/
theorem verify_range {q : Point (Fin p)} {e r s : Nat} (h : C.verify q e r s = true) :
    (0 < r ∧ r < n) ∧ (0 < s ∧ s < n) := by
  unfold verify at h
  split at h
  · split at h
    · exact ⟨by assumption, by assumption⟩
    · cases h
  · cases h

/-- The point at infinity is no public key, and verifies nothing. -/
theorem verify_infinity (e r s : Nat) : C.verify .infinity e r s = false := by
  unfold verify
  split
  · split
    · simp
    · rfl
  · rfl

/-- A point off the curve is no public key, and verifies nothing. -/
theorem verify_of_not_isOnCurve {q : Point (Fin p)} (hq : q.isOnCurve = false) (e r s : Nat) :
    C.verify q e r s = false := by
  unfold verify
  split
  · split
    · simp [hq]
    · rfl
  · rfl

omit [NeZero p] [Params (Fin p)] in
/-- What a successful run of the signing loop returns: SEC 1 v2 §4.1.3 for some nonce `k`. -/
theorem signWith_spec {d e r s : Fin n} {x y : Fin p} :
    ∀ {fuel : Nat} {state : NonceState}, C.signWith d e fuel state = some (r, s, x, y) →
      ∃ k : Fin n, k ≠ 0 ∧ C.mul k C.generator = .affine x y ∧
        r = Fin.ofNat _ x.val ∧ r ≠ 0 ∧ s = C.inv k * (e + r * d) ∧ s ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro state h; cases h
  | succ fuel ih =>
    intro state h
    unfold signWith at h
    dsimp only at h
    split at h
    · rename_i ht
      split at h
      · exact ih h
      · rename_i x' y' hR
        split at h
        · exact ih h
        · rename_i hrs
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          refine ⟨⟨_, ht.2⟩, fun h0 => ?_, hR, rfl, fun h => hrs (Or.inl h), rfl,
            fun h => hrs (Or.inr h)⟩
          have := congrArg Fin.val h0
          simp at this
          omega
    · exact ih h

/-! ## Facts in the group -/

variable {E : Type*} [AddCommGroup E] [Module (ZMod n) E]
  {toPoint : Point (Fin p) → E} {toZMod : Fin n ≃+* ZMod n}

variable {C}

namespace Laws

variable (hC : C.Laws toPoint toZMod)
include hC

omit [NeZero n] in
/-- A point on the curve is `O` exactly when its group element is zero. -/
theorem toPoint_eq_zero {P : Point (Fin p)} (hP : P.isOnCurve = true) :
    toPoint P = 0 ↔ P = .infinity := by
  rw [← hC.toPoint_infinity]
  exact hC.toPoint_inj hP rfl

/-- A nonzero key gives a public key other than `O`, since `G` has prime order `n`. -/
theorem mul_generator_ne_infinity [Fact n.Prime] {d : Fin n} (hd : d ≠ 0) :
    C.mul d C.generator ≠ .infinity := by
  intro h
  have h0 := congrArg toPoint h
  rw [hC.toPoint_mul d hC.isOnCurve_generator, hC.toPoint_infinity, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact hd (toZMod.injective (h0.trans (map_zero _).symm))
  · exact hC.toPoint_generator_ne_zero h0

omit [NeZero n] in
/-- The point the verifier rebuilds, in the group: `u1 G + u2 Q`. -/
theorem toPoint_rebuilt (u1 u2 : Fin n) {q : Point (Fin p)} (hq : q.isOnCurve = true) :
    toPoint (C.mul u1 C.generator + C.mul u2 q)
      = toZMod u1 • toPoint C.generator + toZMod u2 • toPoint q := by
  rw [hC.toPoint_add (hC.isOnCurve_mul _ hC.isOnCurve_generator) (hC.isOnCurve_mul _ hq),
    hC.toPoint_mul _ hC.isOnCurve_generator, hC.toPoint_mul _ hq]

/-- A product `k^(-1) a` that is not zero has a nonzero `k`, since the inverse of zero is zero. -/
theorem ne_zero_of_inv_mul_ne_zero [Fact n.Prime] {k a : Fin n} (h : C.inv k * a ≠ 0) : k ≠ 0 := by
  rintro rfl
  apply h
  apply toZMod.injective
  rw [map_mul, hC.toZMod_inv, map_zero, inv_zero, zero_mul]

/-- Completeness: a signature from the signing operation of SEC 1 v2 §4.1.3 verifies.

The signer has a nonzero private key `d` and the nonce `k`.

`R = k G` has coordinate `x`, `r = x mod n`, and `s = k^(-1) (e + r d)`.

Neither `r` nor `s` is zero. -/
theorem verify_sign [Fact n.Prime] (d k : Fin n) (e : Nat) (hd : d ≠ 0) {x y : Fin p}
    (hR : C.mul k C.generator = .affine x y) (hr : x.val % n ≠ 0)
    (hs : C.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % n) * d) ≠ 0) :
    C.verify (C.mul d C.generator) e (x.val % n)
      (C.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % n) * d)).val = true := by
  set sig := C.inv k * (Fin.ofNat _ e + Fin.ofNat _ (x.val % n) * d) with hsig
  have hk : k ≠ 0 := hC.ne_zero_of_inv_mul_ne_zero hs
  have hrr : 0 < x.val % n ∧ x.val % n < n :=
    ⟨Nat.pos_of_ne_zero hr, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
  have hss : 0 < sig.val ∧ sig.val < n :=
    ⟨Nat.pos_of_ne_zero (fun h => hs (Fin.ext h)), sig.isLt⟩
  have hG := hC.isOnCurve_generator
  -- The key `d G` is valid: `d` is nonzero and `G` has order `n`.
  have hQ : C.mul d C.generator ≠ .infinity ∧ (C.mul d C.generator).isOnCurve = true :=
    ⟨hC.mul_generator_ne_infinity hd, hC.isOnCurve_mul d hG⟩
  rw [verify, dite_eq_left hrr, dite_eq_left hss, ite_eq_left hQ]
  dsimp only
  rw [hC.mulAdd_eq _ _ hG hQ.2]
  -- The verifier rebuilds `R`: `u1 G + u2 (d G) = s^(-1) (e + r d) G = k G`.
  have hrebuilt : toPoint (C.mul (Fin.ofNat _ e * C.inv ⟨sig.val, hss.2⟩) C.generator
      + C.mul ((⟨x.val % n, hrr.2⟩ : Fin n) * C.inv ⟨sig.val, hss.2⟩) (C.mul d C.generator))
      = toPoint (.affine x y) := by
    rw [hC.toPoint_rebuilt _ _ hQ.2, hC.toPoint_mul d hG, ← hR, hC.toPoint_mul k hG, smul_smul,
      ← add_smul]
    refine congrArg (· • toPoint C.generator) ?_
    have hk' : toZMod k ≠ 0 := fun h => hk (toZMod.injective (h.trans (map_zero _).symm))
    have hs' : toZMod sig ≠ 0 := fun h => hs (toZMod.injective (h.trans (map_zero _).symm))
    have hr' : ((⟨x.val % n, hrr.2⟩ : Fin n) : Fin n) = Fin.ofNat _ (x.val % n) :=
      Fin.ext (Nat.mod_eq_of_lt hrr.2).symm
    have hsig' : toZMod sig = (toZMod k)⁻¹ * (toZMod (Fin.ofNat _ e)
        + toZMod (Fin.ofNat _ (x.val % n)) * toZMod d) := by
      rw [hsig, map_mul, hC.toZMod_inv, map_add, map_mul]
    rw [Fin.eta sig hss.2, hr', map_mul, map_mul, hC.toZMod_inv]
    rw [hsig'] at hs' ⊢
    have he : toZMod (Fin.ofNat _ e) + toZMod (Fin.ofNat _ (x.val % n)) * toZMod d ≠ 0 :=
      fun h => hs' (by rw [h, mul_zero])
    field_simp
  split
  · rename_i heq
    rw [heq, hC.toPoint_infinity] at hrebuilt
    exact absurd ((hC.toPoint_eq_zero (hC.isOnCurve_mul k hG)).mp (hR ▸ hrebuilt.symm))
      (by rw [hR]; simp)
  · rename_i x' y' heq
    rw [heq] at hrebuilt
    have := (hC.toPoint_inj (heq ▸ hC.isOnCurve_add (hC.isOnCurve_mul _ hG)
      (hC.isOnCurve_mul _ hQ.2)) (hR ▸ hC.isOnCurve_mul k hG)).mp hrebuilt
    cases this
    simp

/-- `(r, s)` and `(r, n - s)` are valid together: `n - s` rebuilds `-R`, which has the same `x`. -/
theorem verify_neg_s [Fact n.Prime] (q : Point (Fin p)) (e r : Nat) {s : Nat} (hs : 0 < s ∧ s < n) :
    C.verify q e r (n - s) = C.verify q e r s := by
  have hs' : 0 < n - s ∧ n - s < n := by omega
  by_cases hr : 0 < r ∧ r < n
  · by_cases hq : q ≠ .infinity ∧ q.isOnCurve = true
    · rw [verify, verify, dite_eq_left hr, dite_eq_left hr, dite_eq_left hs, dite_eq_left hs',
        ite_eq_left hq, ite_eq_left hq]
      dsimp only
      have hG := hC.isOnCurve_generator
      rw [hC.mulAdd_eq _ _ hG hq.2, hC.mulAdd_eq _ _ hG hq.2]
      -- `n - s` is `-s` mod `n`, so `u1`, `u2` and the rebuilt point change sign.
      have hneg : (⟨n - s, hs'.2⟩ : Fin n) = -⟨s, hs.2⟩ :=
        Fin.ext (by simp only [Fin.neg_def]; exact (Nat.mod_eq_of_lt hs'.2).symm)
      rw [hneg]
      generalize hR : C.mul (Fin.ofNat _ e * C.inv ⟨s, hs.2⟩) C.generator
        + C.mul ((⟨r, hr.2⟩ : Fin n) * C.inv ⟨s, hs.2⟩) q = R
      have hRc : R.isOnCurve = true :=
        hR ▸ hC.isOnCurve_add (hC.isOnCurve_mul _ hG) (hC.isOnCurve_mul _ hq.2)
      have hR' : C.mul (Fin.ofNat _ e * C.inv (-⟨s, hs.2⟩)) C.generator
          + C.mul ((⟨r, hr.2⟩ : Fin n) * C.inv (-⟨s, hs.2⟩)) q = -R := by
        apply (hC.toPoint_inj (hC.isOnCurve_add (hC.isOnCurve_mul _ hG)
          (hC.isOnCurve_mul _ hq.2)) (hC.isOnCurve_neg hRc)).mp
        rw [hC.toPoint_neg hRc, ← hR, hC.toPoint_rebuilt _ _ hq.2, hC.toPoint_rebuilt _ _ hq.2]
        simp only [map_mul, hC.toZMod_inv, map_neg, inv_neg, mul_neg, neg_smul, neg_add]
      rw [hR']
      cases R <;> rfl
    · have hq' : q = .infinity ∨ q.isOnCurve = false := by
        by_cases h : q = .infinity
        · exact Or.inl h
        · exact Or.inr (by simpa [h] using hq)
      rcases hq' with rfl | hq'
      · rw [verify_infinity, verify_infinity]
      · rw [verify_of_not_isOnCurve _ hq', verify_of_not_isOnCurve _ hq']
  · simp only [verify, dite_eq_right hr]

/-- What a valid signature gives: the ranges, a valid key, and the rebuilt point `R`.

That point has `x_R mod n = r`. -/
theorem verify_rebuilt {q : Point (Fin p)} {e r s : Nat} (hv : C.verify q e r s = true) :
    ∃ (hr : 0 < r ∧ r < n) (hs : 0 < s ∧ s < n), q ≠ .infinity ∧ q.isOnCurve = true ∧
      ∃ x y : Fin p, C.mul (Fin.ofNat _ e * C.inv ⟨s, hs.2⟩) C.generator
        + C.mul ((⟨r, hr.2⟩ : Fin n) * C.inv ⟨s, hs.2⟩) q = .affine x y ∧ x.val % n = r := by
  obtain ⟨hr, hs⟩ := C.verify_range hv
  have hq : q ≠ .infinity ∧ q.isOnCurve = true := by
    by_cases hi : q = .infinity
    · subst hi; rw [verify_infinity] at hv; cases hv
    · cases hc : q.isOnCurve
      · rw [verify_of_not_isOnCurve _ hc] at hv; cases hv
      · exact ⟨hi, rfl⟩
  refine ⟨hr, hs, hq.1, hq.2, ?_⟩
  rw [verify, dite_eq_left hr, dite_eq_left hs, ite_eq_left hq] at hv
  dsimp only at hv
  rw [hC.mulAdd_eq _ _ hC.isOnCurve_generator hq.2] at hv
  split at hv
  · cases hv
  · rename_i x y hR
    exact ⟨x, y, hR, by simpa using hv⟩

/-- Two signatures with the same `r`, key and hash verify only if their `s` agree up to sign.

The bound `p <= r + n` makes both rebuilt points have `x = r`, so they are equal or opposite. -/
theorem verify_s_eq_or_neg [Fact n.Prime] {q : Point (Fin p)} {e r s s' : Nat}
    (hv : C.verify q e r s = true) (hv' : C.verify q e r s' = true) (hp : p ≤ r + n) :
    s' = s ∨ s' = n - s := by
  obtain ⟨hr, hs, -, hqc, x, y, hR, hx⟩ := hC.verify_rebuilt hv
  obtain ⟨hr', hs', -, -, x', y', hR', hx'⟩ := hC.verify_rebuilt hv'
  -- Both rebuilt points have `x = r`.
  obtain rfl : x' = x := Fin.ext ((Base.eq_of_mod_eq_of_lt hx' x'.isLt hp).trans
    (Base.eq_of_mod_eq_of_lt hx x.isLt hp).symm)
  have hG := hC.isOnCurve_generator
  have hc : (Point.affine x' y).isOnCurve = true :=
    hR ▸ hC.isOnCurve_add (hC.isOnCurve_mul _ hG) (hC.isOnCurve_mul _ hqc)
  have hc' : (Point.affine x' y').isOnCurve = true :=
    hR' ▸ hC.isOnCurve_add (hC.isOnCurve_mul _ hG) (hC.isOnCurve_mul _ hqc)
  -- Each point is `s^(-1) X` for the same `X = e G + r Q`, and `X` is not `O`.
  set X := toZMod (Fin.ofNat _ e) • toPoint C.generator + toZMod ⟨r, hr.2⟩ • toPoint q
  have hP : toPoint (Point.affine x' y) = (toZMod ⟨s, hs.2⟩)⁻¹ • X := by
    rw [← hR, hC.toPoint_rebuilt _ _ hqc]
    simp only [X, map_mul, hC.toZMod_inv, smul_add, smul_smul, mul_comm]
  have hP' : toPoint (Point.affine x' y') = (toZMod ⟨s', hs'.2⟩)⁻¹ • X := by
    rw [← hR', hC.toPoint_rebuilt _ _ hqc]
    simp only [X, map_mul, hC.toZMod_inv, smul_add, smul_smul, mul_comm]
  have hX : X ≠ 0 := fun h0 => by
    rw [h0, smul_zero, hC.toPoint_eq_zero hc] at hP
    cases hP
  -- The two `y` agree up to sign.
  rcases hC.y_eq_or_eq_neg hc hc' with rfl | rfl
  · -- The same point: `s'^(-1) X = s^(-1) X`, so `s' = s`.
    have h0 : ((toZMod ⟨s', hs'.2⟩)⁻¹ - (toZMod ⟨s, hs.2⟩)⁻¹) • X = 0 := by
      rw [sub_smul, ← hP, ← hP', sub_self]
    have heq := inv_injective (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hX))
    exact Or.inl (congrArg Fin.val (toZMod.injective heq))
  · -- Opposite points: `s'^(-1) X = -(s^(-1) X)`, so `s' = -s`.
    have hneg : toPoint (Point.affine x' (-y)) = -toPoint (Point.affine x' y) :=
      hC.toPoint_neg (P := Point.affine x' y) hc
    have h0 : ((toZMod ⟨s', hs'.2⟩)⁻¹ + (toZMod ⟨s, hs.2⟩)⁻¹) • X = 0 := by
      rw [add_smul, ← hP, ← hP', hneg, neg_add_cancel]
    have heq : toZMod ⟨s', hs'.2⟩ = -toZMod ⟨s, hs.2⟩ := by
      rw [← inv_inj, inv_neg]
      exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp h0).resolve_right hX)
    have hv := congrArg Fin.val (toZMod.injective (heq.trans (map_neg toZMod _).symm))
    simp only [Fin.neg_def] at hv
    exact Or.inr (hv.trans (Nat.mod_eq_of_lt (by omega)))

/-- Let `(r, s)` be a valid signature under a key and a hash, with `p <= r + n`.

Then `(r, s')` is valid under the same key and hash exactly when `s'` is `s` or `n - s`.

Below that bound, the rebuilt point `R` may also have `x = r + n`.

Then up to four values of `s` may verify. -/
theorem verify_iff_s_eq_or_neg [Fact n.Prime] {q : Point (Fin p)} {e r s s' : Nat}
    (hv : C.verify q e r s = true) (hp : p ≤ r + n) :
    C.verify q e r s' = true ↔ s' = s ∨ s' = n - s := by
  refine ⟨fun hv' => hC.verify_s_eq_or_neg hv hv' hp, ?_⟩
  rintro (rfl | rfl)
  · exact hv
  · obtain ⟨-, hs⟩ := C.verify_range hv
    rw [hC.verify_neg_s q e r hs, hv]

/-- The scalars `e / s` and `r / s` that the verifier computes, in `ZMod n`. -/
theorem toZMod_scalars [Fact n.Prime] (e r s : Nat) (hr : r < n) (hs : s < n) :
    toZMod (Fin.ofNat _ e * C.inv ⟨s, hs⟩) = (e : ZMod n) / (s : ZMod n) ∧
      toZMod ((⟨r, hr⟩ : Fin n) * C.inv ⟨s, hs⟩) = (r : ZMod n) / (s : ZMod n) := by
  have hs' : (⟨s, hs⟩ : Fin n) = Fin.ofNat _ s := Fin.ext (Nat.mod_eq_of_lt hs).symm
  have hr' : (⟨r, hr⟩ : Fin n) = Fin.ofNat _ r := Fin.ext (Nat.mod_eq_of_lt hr).symm
  rw [map_mul, map_mul, hC.toZMod_inv, hs', hr', toZMod_ofNat, toZMod_ofNat,
    toZMod_ofNat, div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨rfl, rfl⟩

/-- Verification is the verifying operation of SEC 1 v2 §4.1.4, read in the group of the curve.

A signature `(r, s)` is valid exactly when these hold:

- `r` and `s` lie in `[1, n - 1]`;
- the key `Q` lies on the curve and is not `O`;
- `R = (e / s) G + (r / s) Q` is a point `(x, y)` other than `O`, with `x mod n = r`.

The scalars `e / s` and `r / s` are taken modulo `n`, and `e` is any natural number. -/
theorem verify_eq_true_iff [Fact n.Prime] {q : Point (Fin p)} {e r s : Nat} :
    C.verify q e r s = true ↔
      (0 < r ∧ r < n) ∧ (0 < s ∧ s < n) ∧ q ≠ .infinity ∧ q.isOnCurve = true ∧
        ∃ x y : Fin p, (Point.affine x y).isOnCurve = true ∧
          toPoint (.affine x y) = ((e : ZMod n) / (s : ZMod n)) • toPoint C.generator
            + ((r : ZMod n) / (s : ZMod n)) • toPoint q ∧
          x.val % n = r := by
  have hG := hC.isOnCurve_generator
  constructor
  · intro hv
    obtain ⟨hr, hs, hqi, hqc, x, y, hR, hx⟩ := hC.verify_rebuilt hv
    obtain ⟨h1, h2⟩ := hC.toZMod_scalars e r s hr.2 hs.2
    have hc : (Point.affine x y).isOnCurve = true :=
      hR ▸ hC.isOnCurve_add (hC.isOnCurve_mul _ hG) (hC.isOnCurve_mul _ hqc)
    refine ⟨hr, hs, hqi, hqc, x, y, hc, ?_, hx⟩
    rw [← hR, hC.toPoint_rebuilt _ _ hqc, h1, h2]
  · rintro ⟨hr, hs, hqi, hqc, x, y, hc, hR, hx⟩
    obtain ⟨h1, h2⟩ := hC.toZMod_scalars e r s hr.2 hs.2
    rw [verify, dite_eq_left hr, dite_eq_left hs, ite_eq_left ⟨hqi, hqc⟩]
    dsimp only
    rw [hC.mulAdd_eq _ _ hG hqc]
    -- The point that the verifier rebuilds is `(x, y)`, since both have one image in the group.
    have heq : C.mul (Fin.ofNat _ e * C.inv ⟨s, hs.2⟩) C.generator
        + C.mul ((⟨r, hr.2⟩ : Fin n) * C.inv ⟨s, hs.2⟩) q = .affine x y := by
      apply (hC.toPoint_inj (hC.isOnCurve_add (hC.isOnCurve_mul _ hG)
        (hC.isOnCurve_mul _ hqc)) hc).mp
      rw [hC.toPoint_rebuilt _ _ hqc, h1, h2, hR]
    rw [heq]
    simp [hx]

end Laws

end Curve

end EthLib.Cryptography.Ecdsa
