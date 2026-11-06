module

public import EthLib.Cryptography.Proofs.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.G1Order
public import EthLib.Cryptography.Proofs.Bls.FpModel
public import EthLib.Cryptography.Proofs.Bls.CurveMap

/-!
# Proofs: a kernel check that a point of `G1` has order dividing `r`

A point `P` of `G1` lies in the subgroup of order `r` when `[r] P` is the point at infinity.

The kernel can check this for a concrete point by running double and add.

The BLS parameter is `t = -0xd201000000010000`, and `r = t^4 - t^2 + 1`.

So the check computes `[r] P` as `[t^2] ([t^2] P - P) + P`.

Each `[t^2]` is two products by `|t|`, since `t^2 = |t|^2`.

These take about as many doublings as one product by `r`, but far fewer additions.

Here the coordinates are naturals below `p`, and each field operation is one product or sum mod `p`.

These operations take the same values as the field operations of `Fp`.

The kernel runs them several times faster, since it skips the structure of `Fin`.

They call `Nat.add`, `Nat.sub`, `Nat.mul` and `Nat.mod` directly, not through `+`, `-`, `*` and `%`.

The kernel then computes each one at once, without first unfolding the instances of the notation.

On a run of doublings, that takes about half the time and half the memory.

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
def fadd (a b : Nat) : Nat := Nat.mod (Nat.add a b) Fp.modulus

/-- Difference mod `p`, with the value of the difference in `Fp`. -/
def fsub (a b : Nat) : Nat := Nat.mod (Nat.add (Nat.sub Fp.modulus b) a) Fp.modulus

/-- Product mod `p`, with the value of the product in `Fp`. -/
def fmul (a b : Nat) : Nat := Nat.mod (Nat.mul a b) Fp.modulus

/-- The sum in the notation of `Fin`, for proofs. -/
private theorem fadd_eq (a b : Nat) : fadd a b = (a + b) % Fp.modulus := rfl

/-- The product in the notation of `Fin`, for proofs. -/
private theorem fmul_eq (a b : Nat) : fmul a b = a * b % Fp.modulus := rfl

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

/-- Negation `(x, p - y, z)` mod `p`, as the negation of `G1` computes it. -/
def neg (q : Coords) : Coords := (q.1, (Fp.modulus - q.2.1) % Fp.modulus, q.2.2)

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

/-- The coordinates of a point over the model of the kernel, as naturals below `p`. -/
private def modelCoords (q : G1 Fp.Model) : Coords := (q.x.val, q.y.val, q.z.val)

/-- A point and its image in the model have the same coordinates. -/
private theorem coords_eq (q : G1) : coords q = modelCoords (G1.map Fp.toModel q) := by
  simp only [coords, modelCoords, G1.map, Fp.val_toModel]

private theorem modelCoords_double (q : G1 Fp.Model) :
    modelCoords (G1.double q) = double (modelCoords q) := by
  unfold G1.double double
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show ((modelCoords q).2.2 == 0) = BaseField.isZero q.z from rfl]
  by_cases h : BaseField.isZero q.z = true <;> simp only [h, ↓reduceIte]
  rfl

private theorem modelCoords_addMixed (p q : G1 Fp.Model) :
    modelCoords (G1.addMixed p q) = addMixed (modelCoords p) (modelCoords q) := by
  unfold G1.addMixed addMixed
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show ((modelCoords p).1 == fmul (modelCoords q).1
      (fmul (modelCoords p).2.2 (modelCoords p).2.2)) =
      BaseField.beq p.x (q.x * (p.z * p.z)) from rfl,
    show ((modelCoords p).2.1 == fmul (fmul (modelCoords q).2.1 (modelCoords p).2.2)
      (fmul (modelCoords p).2.2 (modelCoords p).2.2)) =
      BaseField.beq p.y (q.y * p.z * (p.z * p.z)) from rfl]
  by_cases h₁ : BaseField.beq p.x (q.x * (p.z * p.z)) = true
  · by_cases h₂ : BaseField.beq p.y (q.y * p.z * (p.z * p.z)) = true
    · simp only [h₁, h₂, ↓reduceIte, modelCoords_double]
    · simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
      rfl
  · simp only [h₁, ↓reduceIte, Bool.false_eq_true]
    rfl

private theorem modelCoords_addGeneral (p q : G1 Fp.Model) :
    modelCoords (G1.addGeneral p q) = addGeneral (modelCoords p) (modelCoords q) := by
  unfold G1.addGeneral addGeneral
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show (fmul (modelCoords p).1 (fmul (modelCoords q).2.2 (modelCoords q).2.2) ==
      fmul (modelCoords q).1 (fmul (modelCoords p).2.2 (modelCoords p).2.2)) =
      BaseField.beq (p.x * (q.z * q.z)) (q.x * (p.z * p.z)) from rfl,
    show (fmul (fmul (modelCoords p).2.1 (modelCoords q).2.2)
      (fmul (modelCoords q).2.2 (modelCoords q).2.2) ==
      fmul (fmul (modelCoords q).2.1 (modelCoords p).2.2)
        (fmul (modelCoords p).2.2 (modelCoords p).2.2)) =
      BaseField.beq (p.y * q.z * (q.z * q.z)) (q.y * p.z * (p.z * p.z)) from rfl]
  by_cases h₁ : BaseField.beq (p.x * (q.z * q.z)) (q.x * (p.z * p.z)) = true
  · by_cases h₂ : BaseField.beq (p.y * q.z * (q.z * q.z)) (q.y * p.z * (p.z * p.z)) = true
    · simp only [h₁, h₂, ↓reduceIte, modelCoords_double]
    · simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
      rfl
  · simp only [h₁, ↓reduceIte, Bool.false_eq_true]
    rfl

private theorem modelCoords_add (p q : G1 Fp.Model) :
    modelCoords (G1.add p q) = add (modelCoords p) (modelCoords q) := by
  unfold G1.add add
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show ((modelCoords p).2.2 == 0) = BaseField.isZero p.z from rfl,
    show ((modelCoords q).2.2 == 0) = BaseField.isZero q.z from rfl,
    show ((modelCoords q).2.2 == 1) = BaseField.beq q.z BaseField.one from rfl]
  by_cases h₁ : BaseField.isZero p.z = true
  · simp only [h₁, ↓reduceIte]
  by_cases h₂ : BaseField.isZero q.z = true
  · simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
  by_cases h₃ : BaseField.beq q.z BaseField.one = true
  · simp only [h₁, h₂, h₃, ↓reduceIte, Bool.false_eq_true, modelCoords_addMixed]
  · simp only [h₁, h₂, h₃, ↓reduceIte, Bool.false_eq_true, modelCoords_addGeneral]

theorem coords_double (q : G1) : coords (G1.double q) = double (coords q) := by
  rw [coords_eq, G1.map_double, modelCoords_double, ← coords_eq]

theorem coords_addMixed (p q : G1) : coords (G1.addMixed p q) = addMixed (coords p) (coords q) := by
  rw [coords_eq, G1.map_addMixed, modelCoords_addMixed, ← coords_eq, ← coords_eq]

theorem coords_addGeneral (p q : G1) :
    coords (G1.addGeneral p q) = addGeneral (coords p) (coords q) := by
  rw [coords_eq, G1.map_addGeneral, modelCoords_addGeneral, ← coords_eq, ← coords_eq]

theorem coords_add (p q : G1) : coords (G1.add p q) = add (coords p) (coords q) := by
  have h := G1.map_add Fp.toModel p q
  rw [coords_eq, show G1.map Fp.toModel (G1.add p q) = G1.add (G1.map Fp.toModel p)
    (G1.map Fp.toModel q) from h, modelCoords_add, ← coords_eq, ← coords_eq]

theorem coords_neg (q : G1) : coords (G1.neg q) = neg (coords q) := by
  simp only [coords, neg, G1.neg, Fp.val_neg]

theorem coords_zero : coords (G1.zero : G1) = zero := by
  rw [coords_eq, G1.map_zero]
  rfl

theorem coords_mulNatAux (fuel : Nat) (q : G1) (k : Nat) :
    coords (G1.mulNatAux fuel q k) = mulNatAux fuel (coords q) k := by
  induction fuel generalizing q k with
  | zero => exact coords_zero
  | succ fuel ih =>
    rw [G1.mulNatAux, mulNatAux]
    simp only [beq_eq, Bool.cond_eq_ite, beq_iff_eq]
    by_cases h0 : k = 0
    · simp only [h0, ↓reduceIte]
      exact coords_zero
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

/-- The subgroup order `r` is `|t|^4 - |t|^2 + 1`, for the BLS parameter `t`. -/
private theorem modulus_eq_blsX : Fr.modulus = blsX ^ 4 - blsX ^ 2 + 1 := by decide

/-- The chain `[t^2] ([t^2] q - q) + q`, which is `[r] q` for a valid point `q`.

Double and add takes at most one doubling for each bit of the scalar.

It takes at most one addition for each set bit.

`|t|` has 64 bits, six of them set, so the four products by `|t|` take at most 256 doublings.

The four products take at most 24 additions, and the chain adds two more.

One product by `r` would take up to 255 doublings and 134 additions. -/
def mulModulus (q : Coords) : Coords :=
  let a := mulNatAux 64 (mulNatAux 64 q blsX) blsX
  add (mulNatAux 64 (mulNatAux 64 (add a (neg q)) blsX) blsX) q

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

/-- The chain `[t^2] ([t^2] q - q) + q` in `G1`, step for step as the check runs it. -/
private def mulModulusChain (q : G1) : G1 :=
  let a := G1.mulNat (G1.mulNat q blsX) blsX
  G1.add (G1.mulNat (G1.mulNat (G1.add a (G1.neg q)) blsX) blsX) q

/-- The check computes the coordinates of the chain. -/
private theorem coords_mulModulusChain (q : G1) :
    coords (mulModulusChain q) = mulModulus (coords q) := by
  have hz (p : G1) : G1.mulNat p blsX = G1.mulNatAux 64 p blsX :=
    (mulNatAux_eq 64 p blsX (by decide)).symm
  simp only [mulModulusChain, mulModulus, hz, coords_add, coords_mulNatAux, coords_neg]

/-- For a valid point `q`, the chain represents `[r] q`. -/
private theorem toPoint_mulModulusChain {q : G1} (h : Valid q) :
    toPoint (mulModulusChain q) = Fr.modulus • toPoint q := by
  have h₁ := valid_mulNat (valid_mulNat h blsX) blsX
  have h₂ := valid_add h₁ (valid_neg h)
  have h₃ := valid_mulNat (valid_mulNat h₂ blsX) blsX
  simp only [mulModulusChain, toPoint_add h₃ h, toPoint_mulNat (valid_mulNat h₂ blsX),
    toPoint_mulNat h₂, toPoint_add h₁ (valid_neg h), toPoint_mulNat (valid_mulNat h blsX),
    toPoint_mulNat h, toPoint_neg h]
  have hle : blsX ^ 2 ≤ blsX ^ 4 := Nat.pow_le_pow_right (by decide) (by decide)
  rw [modulus_eq_blsX, add_smul, one_smul, sub_nsmul _ hle]
  simp only [smul_smul, ← pow_two]
  rw [nsmul_add, neg_nsmul, smul_smul, ← pow_add]

/-- A point `(x, y, 1)` of the curve whose `x` passes the check has order dividing `r`. -/
theorem modulus_smul_eq_zero {x y : Fp} (hc : check x.val = true)
    (hy : y * y = x * x * x + Fp.ofNat 4) :
    Fr.modulus • toPoint ⟨x, y, Fp.one⟩ = 0 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, fadd_eq, fmul_eq] at hc
  obtain ⟨⟨-, hsq⟩, hz⟩ := hc
  -- The candidate root, as an element of `Fp`.
  obtain ⟨y₀, hy₀v⟩ : ∃ y₀ : Fp, y₀.val = rootCandidate x.val :=
    ⟨_, Fp.val_ofNat_of_lt (Nat.mod_lt _ Fp.modulus_pos)⟩
  have hy₀ : y₀ * y₀ = x * x * x + Fp.ofNat 4 := by
    apply Fp.ext
    rw [Fp.val_mul, Fp.val_add, Fp.val_mul, Fp.val_mul, Fp.val_ofNat, hy₀v]
    exact hsq
  have hv : Valid ⟨x, y₀, Fp.one⟩ := valid_of_affine_eq hy₀
  -- The chain reaches the point at infinity, so `[r] (x, y₀, 1) = 0`.
  have hr : Fr.modulus • toPoint ⟨x, y₀, Fp.one⟩ = 0 := by
    rw [← toPoint_mulModulusChain hv]
    have hc : coords ⟨x, y₀, Fp.one⟩ = (x.val, rootCandidate x.val, 1) := by
      simp only [coords, hy₀v, Fp.one_def, Fp.val_one]
    have h := congrArg (fun c : Coords => c.2.2) (coords_mulModulusChain ⟨x, y₀, Fp.one⟩)
    rw [hc, hz] at h
    generalize mulModulusChain ⟨x, y₀, Fp.one⟩ = X at h ⊢
    apply Point.toAffine_of_Z_eq_zero
    rw [rep_z]
    apply (isZero_iff (a := X.z)).mp
    rw [Fp.isZero_eq]
    exact beq_iff_eq.mpr h
  have hsq' : Fp.toZMod y * Fp.toZMod y = Fp.toZMod y₀ * Fp.toZMod y₀ := by
    rw [← Fp.toZMod_mul, ← Fp.toZMod_mul, hy, hy₀]
  rcases sqrt_pm hsq' with h | h
  · rw [Fp.toZMod_inj.mp h]
    exact hr
  · have hn : y = -y₀ := Fp.toZMod.injective (by rw [h, Fp.toZMod_neg])
    rw [show (⟨x, y, Fp.one⟩ : G1) = G1.neg ⟨x, y₀, Fp.one⟩ by rw [hn]; rfl,
      toPoint_neg hv, neg_nsmul, hr, neg_zero]

end EthLib.Cryptography.Bls.G1.TorsionCheck
