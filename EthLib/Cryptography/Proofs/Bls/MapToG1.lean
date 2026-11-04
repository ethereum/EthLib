module

public import EthLib.Cryptography.Bls.MapToCurve
public import EthLib.Cryptography.Proofs.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.HashToCurve

/-!
# Proofs: the map to `G1` reaches the curve

Sources: RFC 9380 §6.6.2, §6.6.3 and Appendix E.2.

The SSWU map always finds a square root, so it never fails.

Its output lies on `E' : y^2 = x^3 + A' * x + B'`.

The 11-isogeny sends a point of `E'` to a valid point of `E : y^2 = x^3 + 4`, the curve of `G1`.

A polynomial identity of degree 63 shows this, and the kernel checks it on the coefficient lists.

At a pole of the isogeny, the map returns the identity point, which is valid too.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.MapToCurve

open EthLib.Cryptography.Bls
open scoped EthLib.Cryptography.Bls.Fp

local notation "F" => ZMod Fp.modulus

/-- A field element of the specification, seen in Mathlib's `ZMod p`. -/
private def toF (a : Fp) : F := a

/-! ## The SSWU map onto `E'` -/

/-- The right-hand side `g(x) = x^3 + A' * x + B'` of `E'`. -/
private def g (x : Fp) : Fp := x * x * x + Aprime * x + Bprime

/-- The first candidate `x1` of the SSWU map. -/
private def x1 (u : Fp) : Fp :=
  if (Z * (u * u) * (Z * (u * u)) + Z * (u * u)).isZero then Bprime / (Z * Aprime)
  else (-Bprime / Aprime) * (Fp.one + (Z * (u * u) * (Z * (u * u)) + Z * (u * u)).inverse)

/-- A square root of `-Z = -11`. -/
private def sqrtNegZ : Fp :=
  Fp.ofNat (0x4610e003bd3ac94dfa9246c390d7a78942602029175a4ca * 2 ^ 192 +
    0x366d601f33f3946e3ed39794735c38315d874bc1d70637c3)

private theorem sqrtNegZ_sq : toF sqrtNegZ * toF sqrtNegZ = -toF Z := by decide

private theorem aprime_ne_zero : toF Aprime ≠ 0 := by decide

-- At the exceptional `u`, the map takes `x1 = B' / (Z * A')`, and `g(x1)` is a square.
private theorem sqrt_exceptional_ok : (Fp.sqrt (g (Bprime / (Z * Aprime)))).isOk = true := by
  decide +kernel

/-- `g(t * x1) = t^3 * g(x1)` when `x1 = (-B' / A') * (1 + 1 / (t^2 + t))`. -/
private theorem g_mul (t : F) (ht : t * t + t ≠ 0) :
    let x := (-toF Bprime * (toF Aprime)⁻¹) * (1 + (t * t + t)⁻¹)
    (t * x) * (t * x) * (t * x) + toF Aprime * (t * x) + toF Bprime =
      t * t * t * (x * x * x + toF Aprime * x + toF Bprime) := by
  intro x
  have hd : (t * t + t) * (t * t + t)⁻¹ = 1 := mul_inv_cancel₀ ht
  have ha : toF Aprime * (toF Aprime)⁻¹ = 1 := mul_inv_cancel₀ aprime_ne_zero
  linear_combination
    toF Bprime * toF Aprime * (toF Aprime)⁻¹ * (t - 1) * hd + toF Bprime * (t * t * t - 1) * ha

-- With `c^2 = -z` and `s^2 = -g`, the product `c * z * u^3 * s` squares to `(z * u^2)^3 * g`.
private theorem sq_witness {c z u s gx : F} (hc : c * c = -z) (hs : s * s = -gx) :
    (c * z * (u * u * u) * s) * (c * z * (u * u * u) * s) =
      (z * (u * u)) * (z * (u * u)) * (z * (u * u)) * gx := by
  linear_combination z ^ 2 * u ^ 6 * s ^ 2 * hc - z ^ 3 * u ^ 6 * hs

/-- `g(x1)` or `g(Z * u^2 * x1)` is a square, so the map takes a square root of one of them. -/
private theorem sqrt_ok (u : Fp) :
    ∃ c, Fp.sqrt (g (if (Fp.sqrt (g (x1 u))).isOk then x1 u else Z * (u * u) * x1 u)) = .ok c := by
  by_cases hok : (Fp.sqrt (g (x1 u))).isOk = true
  · rw [ite_eq_left hok]
    cases hs : Fp.sqrt (g (x1 u)) with
    | ok c => exact ⟨c, rfl⟩
    | error e => rw [hs] at hok; cases hok
  rw [ite_eq_right hok]
  have hden : (Z * (u * u) * (Z * (u * u)) + Z * (u * u)).isZero = false := by
    apply Bool.eq_false_iff.mpr
    intro hz
    apply hok
    rw [x1, ite_eq_left hz]
    exact sqrt_exceptional_ok
  -- `g(x1)` is not a square, so `-g(x1)` is one.
  rcases HashToCurve.sq_or_neg_sq (g (x1 u)) with hs | hs
  · exact absurd (by rw [Fp.sqrt_complete hs]; rfl) hok
  have hne : toF (Z * (u * u)) * toF (Z * (u * u)) + toF (Z * (u * u)) ≠ 0 := fun h => by
    rw [(G1.isZero_iff (a := Z * (u * u) * (Z * (u * u)) + Z * (u * u))).mpr h] at hden
    cases hden
  have hx1 : x1 u = (-Bprime / Aprime) *
      (Fp.one + (Z * (u * u) * (Z * (u * u)) + Z * (u * u)).inverse) := by
    rw [x1, ite_eq_right (by rw [hden]; decide)]
  have hg : toF (g (Z * (u * u) * x1 u)) =
      toF (Z * (u * u)) * toF (Z * (u * u)) * toF (Z * (u * u)) * toF (g (x1 u)) := by
    rw [hx1, Fp.div_eq_mul_inv', Fp.inverse_eq_inv]
    exact g_mul (toF (Z * (u * u))) hne
  refine ⟨_, Fp.sqrt_complete (b := sqrtNegZ * Z * (u * u * u) *
    Fp.powNat (g (x1 u)) ((Fp.modulus + 1) / 4)) ?_⟩
  exact (sq_witness (c := toF sqrtNegZ) (z := toF Z) (u := toF u)
    (s := toF (Fp.powNat (g (x1 u)) ((Fp.modulus + 1) / 4))) (gx := toF (g (x1 u)))
    sqrtNegZ_sq hs).trans hg.symm

/-- The SSWU map succeeds on every input (RFC 9380 §6.6.2). -/
theorem simpleSwuG1_ok (u : Fp) : ∃ p, simpleSwuG1 u = .ok p := by
  have h := sqrt_ok u
  revert h
  unfold simpleSwuG1 g x1
  generalize Fp.sqrt = sqrtFn
  rintro ⟨c, hc⟩
  dsimp only
  rw [hc]
  exact ⟨_, rfl⟩

-- The last step of the map: a square root `y` of `g(x)` gives `(x, ±y)` on `E'`.
private theorem curve_of_bind {s : Except BlsError Fp} {x : Fp} {f : Fp → Fp} {p : Fp × Fp}
    (hf : ∀ y, f y * f y = y * y) (hs : ∀ c, s = .ok c → c * c = x * x * x + Aprime * x + Bprime)
    (h : (s >>= fun y => pure (x, f y)) = Except.ok p) :
    p.2 * p.2 = p.1 * p.1 * p.1 + Aprime * p.1 + Bprime := by
  cases s with
  | error e => cases h
  | ok c =>
    cases h
    exact (hf c).trans (hs c rfl)

/-- Every output `(x, y)` of the SSWU map lies on `E' : y^2 = x^3 + A' * x + B'`. -/
theorem simpleSwuG1_curve_eq {u : Fp} {p : Fp × Fp} (h : simpleSwuG1 u = .ok p) :
    p.2 * p.2 = p.1 * p.1 * p.1 + Aprime * p.1 + Bprime := by
  have hsqrt : ∀ {a c : Fp}, Fp.sqrt a = .ok c → c * c = a := fun hs => Fp.sqrt_ok hs
  revert h
  unfold simpleSwuG1
  generalize Fp.sqrt = sqrtFn at hsqrt ⊢
  intro h
  refine curve_of_bind (fun y => ?_) (fun c hc => hsqrt hc) h
  split
  · rfl
  · exact neg_mul_neg y y

/-! ## Polynomials as coefficient lists, lowest degree first

These lists serve only to check the isogeny identity, over any commutative ring.
-/

namespace ListPoly

variable {R : Type*} [CommRing R]

/-- The value at `x` of the polynomial with coefficients `l`, by Horner's rule. -/
private def eval (l : List R) (x : R) : R := l.foldr (fun c acc => c + x * acc) 0

/-- The sum of two polynomials. -/
private def add : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- The product of two polynomials. -/
private def mul : List R → List R → List R
  | [], _ => []
  | a :: p, q => add (q.map (a * ·)) (0 :: mul p q)

@[simp] private theorem eval_nil (x : R) : eval [] x = 0 := rfl

@[simp] private theorem eval_cons (a : R) (l : List R) (x : R) :
    eval (a :: l) x = a + x * eval l x := rfl

private theorem eval_add (p q : List R) (x : R) : eval (add p q) x = eval p x + eval q x := by
  induction p, q using add.induct with
  | case1 q => simp [add]
  | case2 p hp => cases p <;> simp_all [add]
  | case3 a p b q ih => rw [add, eval_cons, ih, eval_cons, eval_cons]; ring

private theorem eval_map_mul (a : R) (q : List R) (x : R) :
    eval (q.map (a * ·)) x = a * eval q x := by
  induction q with
  | nil => simp
  | cons b q ih => rw [List.map_cons, eval_cons, ih, eval_cons]; ring

private theorem eval_mul (p q : List R) (x : R) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => rw [mul, eval_add, eval_map_mul, eval_cons, ih, eval_cons]; ring

private theorem eval_append (p q : List R) (x : R) :
    eval (p ++ q) x = eval p x + x ^ p.length * eval q x := by
  induction p with
  | nil => simp
  | cons a p ih => rw [List.cons_append, eval_cons, ih, eval_cons, List.length_cons]; ring

end ListPoly

open ListPoly

/-! ## The isogeny identity -/

/-- A coefficient list of the specification, seen in Mathlib's `ZMod p`. -/
private def toFs (l : List Fp) : List F := l

-- The kernel multiplies the coefficient lists: about 5 s and 1.5 GB.
private theorem coefficients_eq :
    mul [toF Bprime, toF Aprime, 0, 1]
        (mul (mul (toFs K3) (toFs K3))
          (mul (toFs K2 ++ [1]) (mul (toFs K2 ++ [1]) (toFs K2 ++ [1])))) =
      add (mul (mul (toFs K1) (mul (toFs K1) (toFs K1)))
          (mul (toFs K4 ++ [1]) (toFs K4 ++ [1])))
        (mul [4] (mul (mul (toFs K2 ++ [1]) (mul (toFs K2 ++ [1]) (toFs K2 ++ [1])))
          (mul (toFs K4 ++ [1]) (toFs K4 ++ [1])))) :=
  of_decide_eq_true (inst := instDecidableEqList _ _) (by decide +kernel)

private theorem eval_monic (l : List F) (x : F) :
    eval (l ++ [1]) x = eval l x + x ^ l.length := by
  rw [eval_append, eval_cons, eval_nil]
  ring

/-- `g(x) * y_num^2 * x_den^3 = x_num^3 * y_den^2 + 4 * x_den^3 * y_den^2` for every `x`.

With `y^2 = g(x)`, it is the equation of `E` at the image point. -/
private theorem isogeny_identity (x : F) :
    (x * x * x + toF Aprime * x + toF Bprime) * eval (toFs K3) x ^ 2 *
        (eval (toFs K2) x + x ^ 10) ^ 3 =
      eval (toFs K1) x ^ 3 * (eval (toFs K4) x + x ^ 15) ^ 2 +
        4 * (eval (toFs K2) x + x ^ 10) ^ 3 * (eval (toFs K4) x + x ^ 15) ^ 2 := by
  have hk2 : (toFs K2).length = 10 := rfl
  have hk4 : (toFs K4).length = 15 := rfl
  have hl := congrArg (fun l => eval l x) coefficients_eq
  simp only [eval_mul, eval_add, eval_monic, hk2, hk4, eval_cons, eval_nil] at hl
  linear_combination hl

/-! ## Validity -/

-- Off the poles, the image `(x_num / x_den, y * y_num / y_den)` satisfies `Y^2 = X^3 + 4`.
private theorem image_equation {x y : F}
    (hc : y * y = x * x * x + toF Aprime * x + toF Bprime)
    (hxd : eval (toFs K2) x + x ^ 10 ≠ 0) (hyd : eval (toFs K4) x + x ^ 15 ≠ 0) :
    (y * eval (toFs K3) x * (eval (toFs K4) x + x ^ 15)⁻¹) *
        (y * eval (toFs K3) x * (eval (toFs K4) x + x ^ 15)⁻¹) =
      eval (toFs K1) x * (eval (toFs K2) x + x ^ 10)⁻¹ *
        (eval (toFs K1) x * (eval (toFs K2) x + x ^ 10)⁻¹) *
        (eval (toFs K1) x * (eval (toFs K2) x + x ^ 10)⁻¹) + 4 := by
  field_simp
  linear_combination
    eval (toFs K3) x ^ 2 * (eval (toFs K2) x + x ^ 10) ^ 3 * hc + isogeny_identity x

/-- The isogeny sends every point of `E' : y^2 = x^3 + A' * x + B'` to a valid point of `G1`. -/
theorem isoMapG1_valid {x y : Fp} (h : y * y = x * x * x + Aprime * x + Bprime) :
    G1.Valid (isoMapG1 x y) := by
  unfold isoMapG1
  dsimp only
  by_cases hd : ((evaluate K2 x + Fp.powNat x 10).isZero ||
      (evaluate K4 x + Fp.powNat x 15).isZero) = true
  · rw [ite_eq_left hd]
    exact G1.valid_zero
  · rw [ite_eq_right hd]
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hd
    have hxd : evaluate K2 x + Fp.powNat x 10 ≠ 0 := fun h0 => by
      rw [G1.isZero_iff.mpr h0] at hd
      exact Bool.noConfusion hd.1
    have hyd : evaluate K4 x + Fp.powNat x 15 ≠ 0 := fun h0 => by
      rw [G1.isZero_iff.mpr h0] at hd
      exact Bool.noConfusion hd.2
    rw [Fp.powNat_eq_pow] at hxd hyd
    apply G1.valid_of_affine_eq
    rw [Fp.div_eq_mul_inv', Fp.div_eq_mul_inv', Fp.powNat_eq_pow, Fp.powNat_eq_pow]
    exact image_equation h hxd hyd

end EthLib.Cryptography.Bls.MapToCurve
