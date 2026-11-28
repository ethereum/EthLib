module

public import EthLib.Cryptography.Bls.Constants

/-!
# Proofs: the torsion check of `G1`, on naturals

These definitions run double and add on Jacobian coordinates held as naturals below `p`.

They read only the modulus `p` and the BLS parameter, so their kernel checks import nothing else.

The proofs that they agree with `G1` are in the module of the torsion check.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1.TorsionCheck

/-- Jacobian coordinates as naturals. -/
abbrev Coords := Nat × Nat × Nat

-- Here the coordinates are naturals below `p`.
--
-- Each field operation is one product or sum mod `p`.
--
-- These operations take the same values as the field operations of `Fp`.
--
-- The kernel runs them several times faster, since it skips the structure of `Fin`.
--
-- They call `Nat.add`, `Nat.sub`, `Nat.mul` and `Nat.mod` directly.
--
-- They do not go through `+`, `-`, `*` and `%`.
--
-- The kernel then computes each one at once, without first unfolding the instances of the notation.
--
-- On a run of doublings, that takes about half the time and half the memory.
/-- Sum mod `p`, with the value of the sum in `Fp`. -/
def fadd (a b : Nat) : Nat := Nat.mod (Nat.add a b) Fp.modulus

/-- Difference mod `p`, with the value of the difference in `Fp`. -/
def fsub (a b : Nat) : Nat := Nat.mod (Nat.add (Nat.sub Fp.modulus b) a) Fp.modulus

/-- Product mod `p`, with the value of the product in `Fp`. -/
def fmul (a b : Nat) : Nat := Nat.mod (Nat.mul a b) Fp.modulus

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

/-! ## The check -/

/-- Square and multiply mod `p`, with fuel. -/
def powMod : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | fuel + 1, b, e =>
    bif Nat.beq e 0 then 1
    else
      let half := powMod fuel (fmul b b) (e / 2)
      bif Nat.beq (e % 2) 1 then fmul b half else half

/-- The chain `[t^2] ([t^2] q - q) + q`, which is `[r] q` for a valid point `q`. -/
def mulModulus (q : Coords) : Coords :=
  -- Each `[t^2]` is two products by `|t|`, since `t^2 = |t|^2`.
  --
  -- These take about as many doublings as one product by `r`, but far fewer additions.
  --
  -- Double and add takes at most one doubling for each bit of the scalar.
  --
  -- It takes at most one addition for each set bit.
  --
  -- `|t|` has 64 bits, six of them set, so the four products by `|t|` take at most 256 doublings.
  --
  -- The four products take at most 24 additions, and the chain adds two more.
  --
  -- One product by `r` would take up to 255 doublings and 134 additions.
  let a := mulNatAux 64 (mulNatAux 64 q blsX) blsX
  add (mulNatAux 64 (mulNatAux 64 (add a (neg q)) blsX) blsX) q

/-- The candidate root of `x^3 + 4`, as `Fp.sqrt` computes it. -/
def rootCandidate (x : Nat) : Nat :=
  powMod 384 (fadd (fmul (fmul x x) x) (4 % Fp.modulus)) ((Fp.modulus + 1) / 4) % Fp.modulus

/-- The check for the `x` coordinate of a point with `z = 1`.

It holds when `x` is below `p`, the candidate `y` squares to `x^3 + 4`, and `[r] (x, y, 1) = 0`. -/
def check (x : Nat) : Bool :=
  -- The check reads only the `x` coordinate of a point with `z = 1`.
  --
  -- It computes a square root `y` of `x^3 + 4`, and checks `[r] (x, y, 1) = 0`.
  --
  -- The other root `-y` gives the opposite point, which then also has order dividing `r`.
  let y := rootCandidate x
  decide (x < Fp.modulus) &&
    fmul y y == fadd (fmul (fmul x x) x) (4 % Fp.modulus) &&
    (mulModulus (x, y, 1)).2.2 == 0

end EthLib.Cryptography.Bls.G1.TorsionCheck
