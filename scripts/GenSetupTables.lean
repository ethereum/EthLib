module

import EthLib.Cryptography.Kzg.Fft
import EthLib.Cryptography.Kzg.TrustedSetup
import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checker

/-!
# The tables of the setup check, as Lean modules

Write the four tables of affine points that the kernel checks of the Lagrange setup read.

The program computes them with the compiled specification, from the embedded setup.

The proofs do not trust the tables: a wrong entry only makes a kernel check fail.

With `--check`, it writes nothing, and fails when a file differs from what it would write.
-/

open EthLib.Cryptography
open EthLib.Cryptography.Bls (Fp Fr G1)
open EthLib.Cryptography.Kzg

namespace GenSetupTables

/-- The directory of the generated modules. -/
def dir : System.FilePath := "EthLib/Cryptography/Proofs/Kzg/SetupLagrange/Data"

/-- The affine coordinates of a point, as naturals. -/
def affineNat (p : G1) : Nat × Nat :=
  let a := p.toAffine
  (a.1.val, a.2.val)

/-- The point with affine coordinates `x` and `y`. -/
def pointNat (p : Nat × Nat) : G1 :=
  ⟨Fp.ofNat p.1, Fp.ofNat p.2, Fp.one⟩

/-- The 16th roots of unity of the transforms. -/
def rootsFr : Vector Fr 16 :=
  Vector.ofFn fun i => Fr.ofNat (SetupLagrange.rootPowNat i.val)

/-- Table `M`: the decoded monomial points. -/
def tableM (s : TrustedSetup) : Array (Nat × Nat) :=
  s.g1Monomial.toArray.map affineNat

/-- Table `L`: the decoded Lagrange points, in file order. -/
def tableL (s : TrustedSetup) : Array (Nat × Nat) :=
  let n := Constants.FIELD_ELEMENTS_PER_BLOB
  (Array.range n).map fun k =>
    affineNat (s.g1LagrangeBrp.toArray.getD (BitReversal.reverseBits k n) G1.zero)

/-- Table `A` from table `M`: entry `256 k1 + 16 j2 + j3`. -/
def tableA (tM : Array (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := Array.replicate 4096 (0, 0)
  for j2 in [0:16] do
    for j3 in [0:16] do
      let vals : Vector G1 16 := Vector.ofFn fun j1 =>
        pointNat (tM.getD (256 * j1.val + 16 * j2 + j3) (0, 0))
      let ys := fftG1Vector 4 vals rootsFr
      for k1 in [0:16] do
        out := out.set! (256 * k1 + 16 * j2 + j3) (affineNat (ys.toArray.getD k1 G1.zero))
  return out

/-- Table `B` from table `A`: entry `256 k1 + 16 k2 + j3`. -/
def tableB (tA : Array (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := Array.replicate 4096 (0, 0)
  for k1 in [0:16] do
    for j3 in [0:16] do
      let vals : Vector G1 16 := Vector.ofFn fun j2 =>
        G1.mul (pointNat (tA.getD (256 * k1 + 16 * j2.val + j3) (0, 0)))
          (Fr.ofNat (SetupLagrange.scalarB k1 j2.val))
      let ys := fftG1Vector 4 vals rootsFr
      for k2 in [0:16] do
        out := out.set! (256 * k1 + 16 * k2 + j3) (affineNat (ys.toArray.getD k2 G1.zero))
  return out

/-- A natural below `2^384` in hexadecimal, with no indentation, so that a line fits 100 columns. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Entries `a` to `a + n - 1` of a table, in rows of 64, as a Lean array literal. -/
def rowsLit (t : Array (Nat × Nat)) (a n : Nat) : String :=
  let row (r : Nat) : String :=
    let entries := (List.range 64).map fun c =>
      let (x, y) := t.getD (a + 64 * r + c) (0, 0)
      s!"({hex x},\n{hex y})"
    "#[\n" ++ ",\n".intercalate entries ++ "\n]"
  "#[\n" ++ ",\n".intercalate ((List.range (n / 64)).map row) ++ "]"

/-- One generated module: its file name, the title of its header, the docstring and the name. -/
structure Module where
  file : String
  title : String
  doc : String
  name : String
  table : Array (Nat × Nat)
  start : Nat
  size : Nat

/-- The text of a generated module. -/
def Module.text (m : Module) : String :=
  s!"module

/-!
# Proofs: {m.title}

`lake exe gen-setup-tables` writes this file from the embedded setup.

The proofs do not trust it: a wrong entry only makes a kernel check fail.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

/-- {m.doc} -/
noncomputable def {m.name} : Array (Array (Nat × Nat)) := {rowsLit m.table m.start m.size}

end EthLib.Cryptography.Kzg.SetupLagrange
"

/-- The generated modules, from the decoded setup. -/
def modules (s : TrustedSetup) : List Module :=
  let tM := tableM s
  let tA := tableA tM
  let tB := tableB tA
  let quarter (q : Nat) (word : String) : Module :=
    { file := s!"TableB{q}.lean", title := s!"the {word} quarter of table `B` of the setup check"
      doc := s!"The {word} quarter of the outputs of the second round, in rows of 64."
      name := s!"tableBData{q}", table := tB, start := 1024 * q, size := 1024 }
  [{ file := "TableM.lean", title := "table `M` of the setup check"
     doc := "The decoded monomial points, in rows of 64.", name := "tableMData", table := tM
     start := 0, size := 4096 },
   { file := "TableL.lean", title := "table `L` of the setup check"
     doc := "The decoded Lagrange points in file order, in rows of 64.", name := "tableLData"
     table := tableL s, start := 0, size := 4096 },
   { file := "TableA.lean", title := "table `A` of the setup check"
     doc := "The outputs of the first round, in rows of 64.", name := "tableAData", table := tA
     start := 0, size := 4096 },
   quarter 0 "first", quarter 1 "second", quarter 2 "third", quarter 3 "last"]

/-- Write the modules, or with `--check` compare them with the files. -/
def run (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let .ok s := TrustedSetup.ofHex | throw (IO.userError "the embedded setup does not decode")
  let mut stale := 0
  for m in modules s do
    let path := dir / m.file
    if check then
      let current ← (IO.FS.readFile path).toBaseIO
      if current.toOption != some m.text then
        IO.eprintln s!"{path} is stale; run `lake exe gen-setup-tables`"
        stale := stale + 1
    else
      IO.FS.writeFile path m.text
  return if stale = 0 then 0 else 1

end GenSetupTables

public def main (args : List String) : IO UInt32 := GenSetupTables.run args
