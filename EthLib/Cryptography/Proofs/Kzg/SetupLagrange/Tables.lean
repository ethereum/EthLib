module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Rounds
public meta import Lean.Elab.Term
meta import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Roots
meta import EthLib.Cryptography.Kzg.Fft
meta import EthLib.Cryptography.Kzg.TrustedSetup

/-!
# Proofs: the four tables of the setup check, computed when the file is built

The checks of the three rounds read four tables of affine points.

- `M` holds the decoded monomial points, and `L` the decoded Lagrange points in file order.
- `A` and `B` hold the outputs of the first two rounds.

The repository holds no copy of the tables.

Elaborators compute them each time this file is built, with the compiled specification.

Each table, and each quarter of table `B`, is its own definition with its own elaborator.

Each elaborator thus stays within the default limit of heartbeats.

An elaborator reads the table of the previous round from the definition that holds it.

The proofs do not trust the tables: a wrong entry only makes a kernel check fail.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls (Fp Fr G1)

/-! ## The computation -/

/-- The affine coordinates of a point, as naturals. -/
meta def affineNat (p : G1) : Nat × Nat :=
  let a := p.toAffine
  (a.1.val, a.2.val)

/-- The point with affine coordinates `x` and `y`. -/
meta def pointNat (p : Nat × Nat) : G1 :=
  ⟨Fp.ofNat p.1, Fp.ofNat p.2, Fp.one⟩

/-- The 16th roots of unity of the transforms. -/
meta def rootsFr : Vector Fr 16 :=
  Vector.ofFn fun i => Fr.ofNat (rootPowNat i.val)

/-- The embedded setup, decoded. -/
meta def decodedSetup : Except String TrustedSetup :=
  match TrustedSetup.ofHex with
  | .ok s => .ok s
  | .error _ => .error "the embedded setup does not decode"

/-- Table `M`: the decoded monomial points. -/
meta def tableMNat : Except String (Array (Nat × Nat)) := do
  let s ← decodedSetup
  return s.g1Monomial.toArray.map affineNat

/-- Table `L`: the decoded Lagrange points, in file order. -/
meta def tableLNat : Except String (Array (Nat × Nat)) := do
  let s ← decodedSetup
  let n := Constants.FIELD_ELEMENTS_PER_BLOB
  return (Array.range n).map fun k =>
    affineNat s.g1LagrangeBrp.toArray[BitReversal.reverseBits k n]!

/-- Table `A` from table `M`: entry `256 k1 + 16 j2 + j3`. -/
meta def tableANat (tM : Array (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := Array.replicate 4096 (0, 0)
  for j2 in [0:16] do
    for j3 in [0:16] do
      let vals : Vector G1 16 := Vector.ofFn fun j1 =>
        pointNat tM[256 * j1.val + 16 * j2 + j3]!
      let ys := fftG1Vector 4 vals rootsFr
      for k1 in [0:16] do
        out := out.set! (256 * k1 + 16 * j2 + j3) (affineNat ys[k1]!)
  return out

/-- The product `s p`, as the first output of the transform of size 2 of `(0, p)` with root `s`.

The elaborators run interpreted, and a call to the curve code here would run interpreted too.

The transform is compiled with the specification, so the product runs as compiled code. -/
meta def mulCompiled (p : G1) (s : Fr) : G1 :=
  (fftG1Vector 1 #v[G1.zero, p] #v[s, s])[0]

/-- Quarter `q` of table `B` from table `A`: entry `256 k1 + 16 k2 + j3` for `k1 / 4 = q`.

Entry `n` of the table is entry `n % 1024` of quarter `n / 1024`. -/
meta def tableBNat (tA : Array (Nat × Nat)) (q : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := Array.replicate 1024 (0, 0)
  for i in [0:4] do
    let k1 := 4 * q + i
    for j3 in [0:16] do
      let vals : Vector G1 16 := Vector.ofFn fun j2 =>
        mulCompiled (pointNat tA[256 * k1 + 16 * j2.val + j3]!) (Fr.ofNat (scalarB k1 j2.val))
      let ys := fftG1Vector 4 vals rootsFr
      for k2 in [0:16] do
        out := out.set! (256 * i + 16 * k2 + j3) (affineNat ys[k2]!)
  return out

open Lean Meta Elab Term

/-- A table as a literal, in rows of 64 entries. -/
meta def tableLit (t : Array (Nat × Nat)) : MetaM Expr := do
  let nat := Lean.mkConst ``Nat
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) nat nat
  let rowTy := mkApp (Lean.mkConst ``Array [.zero]) pairTy
  let pair (p : Nat × Nat) : Expr :=
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) nat nat (mkNatLit p.1) (mkNatLit p.2)
  let rows ← (List.range (t.size / 64)).mapM fun r =>
    mkArrayLit pairTy ((List.range 64).map fun c => pair t[64 * r + c]!)
  mkArrayLit rowTy rows

/-- The entries of a table literal, if `e` is one. -/
meta def tableOfLit? (e : Expr) : Option (Array (Nat × Nat)) := do
  let (_, rows) ← e.arrayLit?
  let mut out := #[]
  for row in rows do
    let (_, pairs) ← row.arrayLit?
    for p in pairs do
      guard (p.isAppOfArity ``Prod.mk 4)
      out := out.push (← p.appFn!.appArg!.nat?, ← p.appArg!.nat?)
  return out

/-- The entries of the table literal that the definition `c` holds. -/
meta def readTable (c : Name) : MetaM (Array (Nat × Nat)) := do
  let some (.defnInfo d) := (← getEnv).find? c
    | throwError "{c} is not a definition"
  let some t := tableOfLit? d.value
    | throwError "{c} does not hold a table literal"
  return t

/-- Table `M`, as a literal. -/
elab "setup_table_m%" : term => do
  match tableMNat with
  | .ok t => tableLit t
  | .error e => throwError e

/-- Table `L`, as a literal. -/
elab "setup_table_l%" : term => do
  match tableLNat with
  | .ok t => tableLit t
  | .error e => throwError e

/-- Table `A`, as a literal, from table `M` in the definition `c`. -/
elab "setup_table_a%" c:ident : term => do
  tableLit (tableANat (← readTable (← realizeGlobalConstNoOverloadWithInfo c)))

/-- Quarter `q` of table `B`, as a literal, from table `A` in the definition `c`. -/
elab "setup_table_b%" c:ident q:num : term => do
  tableLit (tableBNat (← readTable (← realizeGlobalConstNoOverloadWithInfo c)) q.getNat)

/-! ## The tables -/

/-- Entry `n` of a table in rows of 64 entries. -/
def entryAt (rows : Array (Array (Nat × Nat))) (n : Nat) : Nat × Nat :=
  (rows.getD (n / 64) #[]).getD (n % 64) (0, 0)

/-- The decoded monomial points, in rows of 64. -/
noncomputable def tableMData : Array (Array (Nat × Nat)) := setup_table_m%

/-- The decoded Lagrange points in file order, in rows of 64. -/
noncomputable def tableLData : Array (Array (Nat × Nat)) := setup_table_l%

/-- The outputs of the first round, in rows of 64. -/
noncomputable def tableAData : Array (Array (Nat × Nat)) := setup_table_a% tableMData

/-- The first quarter of the outputs of the second round, in rows of 64. -/
noncomputable def tableBData0 : Array (Array (Nat × Nat)) := setup_table_b% tableAData 0

/-- The second quarter of the outputs of the second round, in rows of 64. -/
noncomputable def tableBData1 : Array (Array (Nat × Nat)) := setup_table_b% tableAData 1

/-- The third quarter of the outputs of the second round, in rows of 64. -/
noncomputable def tableBData2 : Array (Array (Nat × Nat)) := setup_table_b% tableAData 2

/-- The last quarter of the outputs of the second round, in rows of 64. -/
noncomputable def tableBData3 : Array (Array (Nat × Nat)) := setup_table_b% tableAData 3

/-- The decoded monomial points. -/
noncomputable def tableM : Table := entryAt tableMData

/-- The outputs of the first round. -/
noncomputable def tableA : Table := entryAt tableAData

/-- The outputs of the second round. -/
noncomputable def tableB : Table := fun n =>
  entryAt (#[tableBData0, tableBData1, tableBData2, tableBData3].getD (n / 1024) #[]) (n % 1024)

/-- The decoded Lagrange points, in file order. -/
noncomputable def tableL : Table := entryAt tableLData

end EthLib.Cryptography.Kzg.SetupLagrange
