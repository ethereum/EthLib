module

public import EthLib.Cryptography.Kzg.FftHalves
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Checker

/-!
# Proofs: the kernel checks of the Lagrange points of the embedded setup

The inverse transform of the 4096 monomial points runs in three rounds of transforms of size 16.

The checks read tables of affine points, and compare each transform of size 16 with them.

They run on naturals below `p` and `r`, with the operations of the torsion check.

The file also declares the commands that state the checks against the tables.

Its imports read only the constants of BLS12-381 and the halves of a vector.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G1
open EthLib.Cryptography.Bls.G1.TorsionCheck (Coords fadd fmul)
open EthLib.Cryptography.Kzg.SetupTorsion (hexBytes xOf)

/-! ## The roots and scalars of the rounds -/

/-- The value of `ζ`. -/
def zetaNat : Nat :=
  25829815649260311651249373569448671287036547786131478959351418120540316250978

/-- The value of `u = ζ^256`. -/
def rootNat : Nat :=
  26753076894533791554649012143113393549300550745003194222677083919072199473480

/-- The value of `4096⁻¹`. -/
def scaleNat : Nat :=
  52423073447788513186850219087163459498374710080483563692275874603576291491841

/-- The value of `u^i`; the rounds read it for `i < 16`. -/
def rootPowNat (i : Nat) : Nat := Nat.powMod rootNat i Fr.modulus

/-- The value of `ζ^e`; the rounds read it for `e < 4096`. -/
def zetaPowNat (e : Nat) : Nat := Nat.powMod zetaNat e Fr.modulus

/-- The value of `4096⁻¹ ζ^(16 j2 k1)`, the scalar of the second round. -/
def scalarB (k1 j2 : Nat) : Nat := scaleNat * zetaPowNat (16 * j2 * k1) % Fr.modulus

/-- The value of `ζ^(j3 (k1 + 16 k2))`, the scalar of the third round. -/
def scalarC (k1 k2 j3 : Nat) : Nat := zetaPowNat (j3 * (k1 + 16 * k2))

/-! ## Points as naturals -/

/-- The cube root of unity `β'` of `Fp`, as a natural. -/
def cubeRootNat : Nat :=
  0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac

/-- The right side `x^3 + 4` of the curve equation, mod `p`. -/
def rhs (x : Nat) : Nat := fadd (fmul (fmul x x) x) (4 % Fp.modulus)

/-- The sign of `y`, as the encoding defines it: `y` is greater than `p - y`. -/
def signBit (y : Nat) : Bool := y > Fp.modulus - y

/-- The bytes encode the affine point `(x, y)`.

The infinity flag is clear, `x` is the value of the bytes, and `y` is below `p`.

The pair satisfies the curve equation, and the sign flag is the sign of `y`. -/
def encodesBytes (x y : Nat) : List Nat → Bool
  | [] => false
  | h :: t =>
    Nat.land (h % 256) 0x40 == 0 && xOf (h :: t) == x && Nat.blt y Fp.modulus &&
      fmul y y == rhs x && signBit y == (Nat.land (h % 256) 0x20 != 0)

/-- The list of digit codes encodes the affine point `(x, y)`.

A string of 96 hexadecimal digits encodes `(x, y)` under three conditions.

The value is `x`, `y^2 = x^3 + 4`, and the sign flag is the sign of `y`. -/
def encodes (ns : List Nat) (x y : Nat) : Bool :=
  match hexBytes ns with
  | some l => encodesBytes x y l
  | none => false

/-- The pair is below `p`, and it satisfies the curve equation. -/
def onCurve (x y : Nat) : Bool :=
  Nat.blt x Fp.modulus && Nat.blt y Fp.modulus && fmul y y == rhs x

/-- `(X, Y, Z)` with `Z ≠ 0`, `X = x Z^2` and `Y = y Z^3`, mod `p`. -/
def sameAffine (q : Coords) (x y : Nat) : Bool :=
  let z2 := fmul q.2.2 q.2.2
  q.2.2 != 0 && q.1 == fmul x z2 && q.2.1 == fmul y (fmul z2 q.2.2)

/-! ## Products that split the scalar in two halves -/

/-- The scalar `λ = z^2 - 1`, where `z` is the BLS parameter.

Then `λ^2 + λ + 1 = r`, so `λ` is a cube root of unity mod `r`. -/
def eigenvalue : Nat := blsX ^ 2 - 1

/-- The map `(x, y) ↦ (β' x, y)` on coordinates. -/
def endoNat (q : Coords) : Coords := (fmul cubeRootNat q.1, q.2.1, q.2.2)

/-- The two products in one run, on coordinates. -/
def jointNat : Nat → Coords → Coords → Coords → Nat → Nat → Coords
  | 0, _, _, _, _, _ => TorsionCheck.zero
  | fuel + 1, p, q, t, a, b =>
    bif Nat.beq a 0 && Nat.beq b 0 then TorsionCheck.zero
    else
      let h := TorsionCheck.double (jointNat fuel p q t (a / 2) (b / 2))
      bif Nat.beq (a % 2) 1 then
        (bif Nat.beq (b % 2) 1 then TorsionCheck.add h t else TorsionCheck.add h p)
      else (bif Nat.beq (b % 2) 1 then TorsionCheck.add h q else h)

/-- The split product, on coordinates. -/
def glvNat (p : Coords) (s : Nat) : Coords :=
  let e := endoNat p
  jointNat 128 p e (TorsionCheck.add p e) (s % eigenvalue) (s / eigenvalue)

/-! ## The check of one transform -/

/-- The FFT of `G1` on coordinates, with the products split in two halves. -/
def fftNat : (k : Nat) → Vector Coords (2 ^ k) → Vector Nat (2 ^ k) → Vector Coords (2 ^ k)
  | 0, vals, _ => vals
  | k + 1, vals, roots =>
    let halfRoots := everyOther roots 0
    let l := fftNat k (everyOther vals 0) halfRoots
    let r := fftNat k (everyOther vals 1) halfRoots
    -- Each product by a root splits the root in two halves of 128 bits, as in the GLV product.
    let t := Vector.ofFn (n := 2 ^ k) fun i => glvNat r[i] (roots[i.val]'(by
      have hlt := i.isLt
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
      omega))
    Vector.ofFn fun i =>
      if h : i.val < 2 ^ k then G1.TorsionCheck.add l[i.val] t[i.val]
      else
        have hi : i.val - 2 ^ k < 2 ^ k := by
          have hlt := i.isLt
          have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
          omega
        G1.TorsionCheck.add l[i.val - 2 ^ k] (G1.TorsionCheck.neg t[i.val - 2 ^ k])

/-- The check of one transform: each pair is on the curve, and each output matches.

The check takes affine inputs, a scalar for each input, the roots, and affine outputs.

Input `i` is first multiplied by its scalar `tw[i]`. -/
def dftCheck {k : Nat} (ins : Vector (Nat × Nat) (2 ^ k)) (tw roots : Vector Nat (2 ^ k))
    (outs : Vector (Nat × Nat) (2 ^ k)) : Bool :=
  -- Multiply each input by its scalar, then run the transform.
  let res := fftNat k
    (Vector.ofFn fun (i : Fin (2 ^ k)) => glvNat (ins[i].1, ins[i].2, 1) tw[i]) roots
  ins.toList.all (fun q => onCurve q.1 q.2) && outs.toList.all (fun q => onCurve q.1 q.2) &&
    -- Compare the results with the outputs.
    --
    -- The comparison is projective, so the check never inverts a coordinate.
    (Vector.ofFn fun (i : Fin (2 ^ k)) => sameAffine res[i] outs[i].1 outs[i].2).toList.all id

/-! ## The checks of the setup -/

/-- A table of 4096 affine points, as pairs of naturals read by index.

Four tables hold the points.

- Table `M` holds the decoded monomial points, and table `L` the decoded Lagrange points.
- Tables `A` and `B` hold the results of the first two rounds. -/
abbrev Table := Nat → Nat × Nat

/-- Each list of digit codes encodes its entry of the table, from entry `a` on. -/
def decodeCheck (t : Table) : Nat → List (List Nat) → Bool
  | _, [] => true
  | a, c :: cs => encodes c (t a).1 (t a).2 && decodeCheck t (a + 1) cs

/-- The roots `u^i` of the transforms of size 16. -/
def roots16 : Vector Nat (2 ^ 4) := Vector.ofFn fun i => rootPowNat i.val

/-- The first round at `(j2, j3)`, from `M(256 j1 + 16 j2 + j3)` to `A(256 k1 + 16 j2 + j3)`. -/
def checkA (tM tA : Table) (j2 j3 : Nat) : Bool :=
  dftCheck (k := 4) (Vector.ofFn fun i => tM (256 * i.val + 16 * j2 + j3))
    (Vector.ofFn fun _ => 1) roots16 (Vector.ofFn fun k1 => tA (256 * k1.val + 16 * j2 + j3))

/-- The second round at `(k1, j3)`, from `A(256 k1 + 16 j2 + j3)` to `B(256 k1 + 16 k2 + j3)`. -/
def checkB (tA tB : Table) (k1 j3 : Nat) : Bool :=
  dftCheck (k := 4) (Vector.ofFn fun i => tA (256 * k1 + 16 * i.val + j3))
    (Vector.ofFn fun i => scalarB k1 i.val) roots16
    (Vector.ofFn fun k2 => tB (256 * k1 + 16 * k2.val + j3))

/-- The third round at `(k1, k2)`, from `B(256 k1 + 16 k2 + j3)` to `L(k1 + 16 k2 + 256 k3)`. -/
def checkC (tB tL : Table) (k1 k2 : Nat) : Bool :=
  dftCheck (k := 4) (Vector.ofFn fun i => tB (256 * k1 + 16 * k2 + i.val))
    (Vector.ofFn fun i => scalarC k1 k2 i.val) roots16
    (Vector.ofFn fun k3 => tL (k1 + 16 * k2 + 256 * k3.val))

/-- Entry `n` of a table in rows of 64 entries. -/
def entryAt (rows : Array (Array (Nat × Nat))) (n : Nat) : Nat × Nat :=
  (rows.getD (n / 64) #[]).getD (n % 64) (0, 0)

/-! ## Declaring the checks -/

open Lean Elab Command in
/-- Declares the checks of the chunks `a` to `b - 1` of the strings `xs`.

Chunk `k` holds the 16 strings from index `16 * k`.

Its check is the theorem `name_k`: these strings encode the entries of table `t` from that index.

A kernel check closes it. -/
elab "decode_checks " name:ident t:ident xs:ident a:num b:num : command => do
  for k in [a.getNat:b.getNat] do
    let id := mkIdent (name.getId.appendAfter s!"_{k}")
    let start := Syntax.mkNumLit (toString (16 * k))
    elabCommand (← `(command|
      theorem $id:ident :
          decodeCheck $t $start
            (((($xs).toList.map SetupTorsion.codes).drop $start).take 16) = true := by
        rw [codes_chunk% $xs $start 16]
        decide +kernel))

open Lean Elab Command in
/-- Declares the 16 checks of a round of transforms at the index `i`, from table `t` to `u`.

The check at the second index `k` is the theorem `name_i_k`, where `name` is the check itself.

A kernel check closes it. -/
elab "round_checks " name:ident t:ident u:ident i:num : command => do
  for k in [0:16] do
    let id := mkIdent (name.getId.appendAfter s!"_{i.getNat}_{k}")
    elabCommand (← `(command|
      theorem $id:ident : $name $t $u $i $(Syntax.mkNumLit (toString k)) = true := by
        decide +kernel))

end EthLib.Cryptography.Kzg.SetupLagrange
