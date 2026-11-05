module

public import EthLib.Cryptography.Proofs.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.G1Order

/-!
# Proofs: a kernel check that a point of `G1` has order dividing `r`

A point `P` of `G1` lies in the subgroup of order `r` when `[r] P` is the point at infinity.

The kernel can check this for a concrete point by running double and add.

The check writes `r` as `z^4 - z^2 + 1`, with the BLS parameter `z`.

It computes `[r] P` as `[z^2] ([z^2] P - P) + P`.

The products by `|z|` need about as many doublings as one product by `r`, but far fewer additions.

Here the coordinates are naturals below `p`, and each field operation is one product or sum mod `p`.

These operations take the same values as the field operations of `Fp`.

The kernel runs them several times faster, since it skips the structure of `Fin`.

The check reads only the `x` coordinate of a point with `z = 1`.

It computes a square root `y` of `x^3 + 4`, and checks `[r] (x, y, 1) = 0`.

The other root `-y` gives the opposite point, which then also has order dividing `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1.TorsionCheck

open WeierstrassCurve.Jacobian

/-- Jacobian coordinates as naturals. -/
abbrev Coords := Nat × Nat × Nat

/-- The coordinates of a point, as naturals below `p`. -/
def coords (q : G1) : Coords := (q.x.val, q.y.val, q.z.val)

/-- Sum mod `p`, with the value of the sum in `Fp`. -/
def fadd (a b : Nat) : Nat := (a + b) % Fp.modulus

/-- Difference mod `p`, with the value of the difference in `Fp`. -/
def fsub (a b : Nat) : Nat := (Fp.modulus - b + a) % Fp.modulus

/-- Product mod `p`, with the value of the product in `Fp`. -/
def fmul (a b : Nat) : Nat := a * b % Fp.modulus

/-- The coordinates of the point at infinity. -/
def zero : Coords := (1, 1, 0)

/-- Doubling, by the formulas of the doubling of `G1`. -/
def double (q : Coords) : Coords :=
  bif Nat.beq q.2.2 0 then q else
    let A := fmul q.1 q.1
    let B := fmul q.2.1 q.2.1
    let C := fmul B B
    let t := fsub (fsub (fmul (fadd q.1 B) (fadd q.1 B)) A) C
    let D := fadd t t
    let E := fadd (fadd A A) A
    let F := fmul E E
    let x' := fsub F (fadd D D)
    let C2 := fadd C C
    let C4 := fadd C2 C2
    let y' := fsub (fmul E (fsub D x')) (fadd C4 C4)
    let z' := fmul (fadd q.2.1 q.2.1) q.2.2
    (x', y', z')

/-- Addition with `z = 1` for the second point, by the formulas of the mixed addition. -/
def addMixed (p q : Coords) : Coords :=
  let z1z1 := fmul p.2.2 p.2.2
  let u2 := fmul q.1 z1z1
  let s2 := fmul (fmul q.2.1 p.2.2) z1z1
  bif Nat.beq p.1 u2 then
    bif Nat.beq p.2.1 s2 then double p else zero
  else
    let h := fsub u2 p.1
    let h2 := fadd h h
    let i := fmul h2 h2
    let j := fmul h i
    let r := fadd (fsub s2 p.2.1) (fsub s2 p.2.1)
    let v := fmul p.1 i
    let x' := fsub (fsub (fmul r r) j) (fadd v v)
    let y' := fsub (fmul r (fsub v x')) (fmul (fadd p.2.1 p.2.1) j)
    let z' := fmul (fadd p.2.2 p.2.2) h
    (x', y', z')

/-- Addition of two finite points, by the formulas of the general addition. -/
def addGeneral (p q : Coords) : Coords :=
  let z1z1 := fmul p.2.2 p.2.2
  let z2z2 := fmul q.2.2 q.2.2
  let u1 := fmul p.1 z2z2
  let u2 := fmul q.1 z1z1
  let s1 := fmul (fmul p.2.1 q.2.2) z2z2
  let s2 := fmul (fmul q.2.1 p.2.2) z1z1
  bif Nat.beq u1 u2 then
    bif Nat.beq s1 s2 then double p else zero
  else
    let h := fsub u2 u1
    let h2 := fadd h h
    let i := fmul h2 h2
    let j := fmul h i
    let r := fadd (fsub s2 s1) (fsub s2 s1)
    let v := fmul u1 i
    let x' := fsub (fsub (fmul r r) j) (fadd v v)
    let y' := fsub (fmul r (fsub v x')) (fmul (fadd s1 s1) j)
    let z' := fmul (fsub (fsub (fmul (fadd p.2.2 q.2.2) (fadd p.2.2 q.2.2)) z1z1) z2z2) h
    (x', y', z')

/-- Addition, by the case split of the addition of `G1`. -/
def add (p q : Coords) : Coords :=
  bif Nat.beq p.2.2 0 then q else
  bif Nat.beq q.2.2 0 then p else
  bif Nat.beq q.2.2 1 then addMixed p q else addGeneral p q

/-- Double and add with fuel, as the scalar product of `G1` runs it. -/
def mulNatAux : Nat → Coords → Nat → Coords
  | 0, _, _ => zero
  | fuel + 1, p, k =>
    bif Nat.beq k 0 then zero
    else
      let half := mulNatAux fuel (double p) (k / 2)
      bif Nat.beq (k % 2) 1 then add p half else half

/-! ## The values agree with `Fp` -/

/-- The kernel evaluates the equality test of naturals directly, and the spec writes `==`. -/
private theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.mpr (by simp)

theorem coords_double (q : G1) : coords (G1.double q) = double (coords q) := by
  unfold G1.double double
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show ((coords q).2.2 == 0) = q.z.isZero from rfl]
  by_cases h : q.z.isZero = true <;> simp only [h, ↓reduceIte]
  rfl

theorem coords_addMixed (p q : G1) : coords (G1.addMixed p q) = addMixed (coords p) (coords q) := by
  unfold G1.addMixed addMixed
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show ((coords p).1 == fmul (coords q).1 (fmul (coords p).2.2 (coords p).2.2)) =
      p.x.beq (q.x * (p.z * p.z)) from rfl,
    show ((coords p).2.1 == fmul (fmul (coords q).2.1 (coords p).2.2)
      (fmul (coords p).2.2 (coords p).2.2)) = p.y.beq (q.y * p.z * (p.z * p.z)) from rfl]
  by_cases h₁ : p.x.beq (q.x * (p.z * p.z)) = true
  · by_cases h₂ : p.y.beq (q.y * p.z * (p.z * p.z)) = true
    · simp only [h₁, h₂, ↓reduceIte, coords_double]
    · simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
      rfl
  · simp only [h₁, ↓reduceIte, Bool.false_eq_true]
    rfl

theorem coords_addGeneral (p q : G1) :
    coords (G1.addGeneral p q) = addGeneral (coords p) (coords q) := by
  unfold G1.addGeneral addGeneral
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show (fmul (coords p).1 (fmul (coords q).2.2 (coords q).2.2) ==
      fmul (coords q).1 (fmul (coords p).2.2 (coords p).2.2)) =
      (p.x * (q.z * q.z)).beq (q.x * (p.z * p.z)) from rfl,
    show (fmul (fmul (coords p).2.1 (coords q).2.2) (fmul (coords q).2.2 (coords q).2.2) ==
      fmul (fmul (coords q).2.1 (coords p).2.2) (fmul (coords p).2.2 (coords p).2.2)) =
      (p.y * q.z * (q.z * q.z)).beq (q.y * p.z * (p.z * p.z)) from rfl]
  by_cases h₁ : (p.x * (q.z * q.z)).beq (q.x * (p.z * p.z)) = true
  · by_cases h₂ : (p.y * q.z * (q.z * q.z)).beq (q.y * p.z * (p.z * p.z)) = true
    · simp only [h₁, h₂, ↓reduceIte, coords_double]
    · simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
      rfl
  · simp only [h₁, ↓reduceIte, Bool.false_eq_true]
    rfl

theorem coords_add (p q : G1) : coords (G1.add p q) = add (coords p) (coords q) := by
  unfold G1.add add
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show ((coords p).2.2 == 0) = p.z.isZero from rfl,
    show ((coords q).2.2 == 0) = q.z.isZero from rfl,
    show ((coords q).2.2 == 1) = q.z.beq Fp.one from rfl]
  by_cases h₁ : p.z.isZero = true
  · simp only [h₁, ↓reduceIte]
  by_cases h₂ : q.z.isZero = true
  · simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
  by_cases h₃ : q.z.beq Fp.one = true
  · simp only [h₁, h₂, h₃, ↓reduceIte, Bool.false_eq_true, coords_addMixed]
  · simp only [h₁, h₂, h₃, ↓reduceIte, Bool.false_eq_true, coords_addGeneral]

theorem coords_mulNatAux (fuel : Nat) (q : G1) (k : Nat) :
    coords (G1.mulNatAux fuel q k) = mulNatAux fuel (coords q) k := by
  induction fuel generalizing q k with
  | zero => rfl
  | succ fuel ih =>
    rw [G1.mulNatAux, mulNatAux]
    simp only [beq_eq, Bool.cond_eq_ite, beq_iff_eq]
    by_cases h0 : k = 0
    · simp only [h0, ↓reduceIte]
      rfl
    simp only [h0, ↓reduceIte]
    by_cases h1 : k % 2 = 1
    · simp only [h1, ↓reduceIte, coords_add, ih, coords_double]
    · simp only [h1, ↓reduceIte, ih, coords_double]

/-! ## The check -/

/-- Square and multiply mod `p`, with fuel. -/
def powMod : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | fuel + 1, b, e =>
    bif Nat.beq e 0 then 1
    else
      let half := powMod fuel (fmul b b) (e / 2)
      bif Nat.beq (e % 2) 1 then fmul b half else half

/-- The absolute value of the BLS parameter `z = -0xd201000000010000`. -/
def zAbs : Nat := 0xd201000000010000

/-- The order `r` of `G1` is `z^4 - z^2 + 1`. -/
theorem modulus_eq : Fr.modulus = zAbs ^ 4 - zAbs ^ 2 + 1 := by decide

/-- Negation, as the negation of `G1` computes it. -/
def neg (q : Coords) : Coords := (q.1, (Fp.modulus - q.2.1) % Fp.modulus, q.2.2)

/-- `[r] q`, computed as `[z^2] ([z^2] q - q) + q`.

Double and add takes one doubling for each bit of the scalar.

It also takes one addition for each set bit.

`|z|` has 64 bits, six of them set, so the four products by `|z|` take 256 doublings.

They take 24 additions, and the chain adds two more.

`r` has 255 bits, 134 of them set. -/
def mulModulus (q : Coords) : Coords :=
  let a := mulNatAux 64 (mulNatAux 64 q zAbs) zAbs
  add (mulNatAux 64 (mulNatAux 64 (add a (neg q)) zAbs) zAbs) q

/-- The candidate root of `x^3 + 4`, as `Fp.sqrt` computes it. -/
def rootCandidate (x : Nat) : Nat :=
  powMod 384 (fadd (fmul (fmul x x) x) (4 % Fp.modulus)) ((Fp.modulus + 1) / 4) % Fp.modulus

/-- The check for the `x` coordinate of a point with `z = 1`.

It holds when `x` is below `p`, the candidate `y` squares to `x^3 + 4`, and `[r] (x, y, 1) = 0`. -/
def check (x : Nat) : Bool :=
  let y := rootCandidate x
  decide (x < Fp.modulus) &&
    fmul y y == fadd (fmul (fmul x x) x) (4 % Fp.modulus) &&
    (mulModulus (x, y, 1)).2.2 == 0

theorem coords_neg (q : G1) : coords (G1.neg q) = neg (coords q) := rfl

/-- `[r] q` in `G1`, by the steps of `mulModulus`. -/
def mulModulusG1 (q : G1) : G1 :=
  let a := G1.mulNat (G1.mulNat q zAbs) zAbs
  G1.add (G1.mulNat (G1.mulNat (G1.add a (G1.neg q)) zAbs) zAbs) q

theorem coords_mulModulusG1 (q : G1) : coords (mulModulusG1 q) = mulModulus (coords q) := by
  have hz (p : G1) : G1.mulNat p zAbs = G1.mulNatAux 64 p zAbs :=
    (mulNatAux_eq 64 p zAbs (by decide)).symm
  simp only [mulModulusG1, mulModulus, hz, coords_add, coords_mulNatAux, coords_neg]

theorem toPoint_mulModulusG1 {q : G1} (h : Valid q) :
    toPoint (mulModulusG1 q) = Fr.modulus • toPoint q := by
  have h₁ := valid_mulNat (valid_mulNat h zAbs) zAbs
  have h₂ := valid_add h₁ (valid_neg h)
  have h₃ := valid_mulNat (valid_mulNat h₂ zAbs) zAbs
  simp only [mulModulusG1, toPoint_add h₃ h, toPoint_mulNat (valid_mulNat h₂ zAbs),
    toPoint_mulNat h₂, toPoint_add h₁ (valid_neg h), toPoint_mulNat (valid_mulNat h zAbs),
    toPoint_mulNat h, toPoint_neg h]
  have hle : zAbs ^ 2 ≤ zAbs ^ 4 := Nat.pow_le_pow_right (by decide) (by decide)
  rw [modulus_eq, add_smul, one_smul, sub_nsmul _ hle]
  simp only [smul_smul, ← pow_two]
  rw [nsmul_add, neg_nsmul, smul_smul, ← pow_add]

/-- A point `(x, y, 1)` of the curve whose `x` passes the check has order dividing `r`. -/
theorem modulus_smul_eq_zero {x y : Fp} (hc : check x.val = true)
    (hy : (y : ZMod Fp.modulus) * y = x * x * x + Fp.ofNat 4) :
    Fr.modulus • toPoint ⟨x, y, Fp.one⟩ = 0 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨-, hsq⟩, hz⟩ := hc
  let y₀ : Fp := ⟨rootCandidate x.val, Nat.mod_lt _ Fp.modulus_pos⟩
  have hy₀ : (y₀ : ZMod Fp.modulus) * y₀ = x * x * x + Fp.ofNat 4 := Fin.ext hsq
  have hv : Valid ⟨x, y₀, Fp.one⟩ := valid_of_affine_eq hy₀
  -- The chain reaches the point at infinity, so `[r] (x, y₀, 1) = 0`.
  have hr : Fr.modulus • toPoint ⟨x, y₀, Fp.one⟩ = 0 := by
    rw [← toPoint_mulModulusG1 hv]
    refine Point.toAffine_of_Z_eq_zero (isZero_iff.mp ?_)
    rw [rep_z]
    have hc : coords ⟨x, y₀, Fp.one⟩ = (x.val, rootCandidate x.val, 1) := rfl
    have h := congrArg (fun c : Coords => c.2.2) (coords_mulModulusG1 ⟨x, y₀, Fp.one⟩)
    rw [hc, hz] at h
    generalize mulModulusG1 ⟨x, y₀, Fp.one⟩ = X at h ⊢
    exact beq_iff_eq.mpr h
  rcases sqrt_pm (hy.trans hy₀.symm) with h | h
  · rw [show y = y₀ from h]
    exact hr
  · rw [show (⟨x, y, Fp.one⟩ : G1) = G1.neg ⟨x, y₀, Fp.one⟩ by rw [show y = -y₀ from h]; rfl,
      toPoint_neg hv, neg_nsmul, hr, neg_zero]

end EthLib.Cryptography.Bls.G1.TorsionCheck
