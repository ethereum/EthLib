module

public import EthLib.Cryptography.Proofs.Bls.G1NatCheck
public meta import Lean.Elab.Command

/-!
# Proofs: the kernel check of the points of the embedded setup

The embedded setup holds each point as a string of 96 hexadecimal digits.

The check reads the digit codes of such a string, decodes them to 48 bytes, and keeps `x`.

Then it runs the torsion check of `G1` on that `x`, on naturals.

The file also declares the checks of many strings, one theorem each.

It imports only the checks on naturals, which read only the constants of BLS12-381.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

open EthLib.Cryptography.Bls

/-! ## Decoding digit codes -/

/-- The value of the hexadecimal digit with character code `n`, in either case. -/
def digit (n : Nat) : Option Nat :=
  if 0x30 ≤ n ∧ n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n ∧ n ≤ 0x66 then some (n - 0x57)
  else if 0x41 ≤ n ∧ n ≤ 0x46 then some (n - 0x37)
  else none

/-- Decode pairs of digit codes to byte values.

An odd number of codes, or a code that is not a digit, gives `none`. -/
def hexBytes : List Nat → Option (List Nat)
  | [] => some []
  | [_] => none
  | hi :: lo :: rest => do
    let h ← digit hi
    let l ← digit lo
    let r ← hexBytes rest
    return (h * 16 + l) :: r

/-- The character codes of a string. -/
def codes (s : String) : List Nat := s.toList.map Char.toNat

/-- The `x` coordinate that 48 bytes encode, without the three flag bits of the first byte. -/
def xOf : List Nat → Nat
  | [] => 0
  | h :: t => t.foldl (fun acc u => (acc <<< 8) ||| u % 256) (h % 256 &&& 31)

/-- The check of one string: it decodes, and its `x` passes the check of `G1`. -/
def checkCodes (ns : List Nat) : Bool :=
  match hexBytes ns with
  -- The check of `G1` finds `y` with `y^2 = x^3 + 4`, and tests `[r] (x, y, 1) = 0`.
  | some l => G1.TorsionCheck.check (xOf l)
  | none => false

/-! ## Reading the literals

The kernel decodes a string slowly, since it reads its UTF-8 bytes one at a time.

So a proof first replaces each string by the list of its codes.

The kernel checks that step by unfolding the literal, which is cheap. -/

open Lean Meta in
/-- The codes of a literal `s`, written out as `ns`, and the equation `codes s = ns`.

The right side keeps the form `List.map Char.toNat (List.map Char.ofNat ns)`.

Its proof reads `s` as the string of the characters `Char.ofNat ns`.

The kernel checks that reading by unfolding the literal, without decoding UTF-8. -/
meta def codesEq (str : String) : MetaM (Expr × Expr × Expr) := do
  let nat := mkConst ``Nat
  let char := mkConst ``Char
  let ns ← mkListLit nat (str.toList.map fun c => mkNatLit c.toNat)
  let chars := mkApp4 (mkConst ``List.map [.zero, .zero]) nat char (mkConst ``Char.ofNat) ns
  let toNat := mkApp3 (mkConst ``List.map [.zero, .zero]) char nat (mkConst ``Char.toNat)
  let lhs := mkApp (mkConst ``codes) (mkStrLit str)
  let rhs := mkApp toNat chars
  let proof := mkApp6 (mkConst ``congrArg [.one, .one]) (mkApp (mkConst ``List [.zero]) char)
    (mkApp (mkConst ``List [.zero]) nat)
    (mkApp (mkConst ``String.toList) (mkApp (mkConst ``String.ofList) chars)) chars toNat
    (mkApp (mkConst ``String.toList_ofList) chars)
  return (lhs, rhs, ← mkExpectedTypeHint proof (← mkEq lhs rhs))

open Lean Meta Elab Term in
open Lean (mkConst) in
/-- The term writes out the codes of the strings `a` to `a + n - 1` of the array `xs`.

It proves the equation between the chunk of codes and the written lists.

The kernel checks the choice of the strings by evaluating the list.

It checks each list of codes as the equation of one literal says. -/
elab "codes_chunk% " xs:ident a:num n:num : term => do
  let name ← realizeGlobalConstNoOverload xs
  let some value := (← getEnv).find? name |>.bind (·.value?)
    | throwError "{name} has no value"
  -- Read the string literals of the array, in order.
  let mut list ← whnfCore value
  let some (_, l) := list.app2? ``List.toArray | throwError "{name} is not an array literal"
  list ← whnfCore l
  let mut strs : Array String := #[]
  repeat
    match list.app3? ``List.cons with
    | some (_, .lit (.strVal str), tl) =>
      strs := strs.push str
      list ← whnfCore tl
    | _ => break
  let chunk := (strs.extract a.getNat (a.getNat + n.getNat)).toList
  let eqs ← chunk.mapM fun str => (codesEq str : MetaM _)
  let listNat := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
  let listLits ← mkListLit listNat (eqs.map (·.1))
  -- The chunk of the codes, as the kernel evaluates it, is the list of `codes` of the literals.
  let codesList := mkApp4 (mkConst ``List.map [.zero, .zero]) (mkConst ``String) listNat
    (mkConst ``codes)
    (mkApp2 (mkConst ``Array.toList [.zero]) (mkConst ``String) (mkConst name))
  let lhs := mkApp3 (mkConst ``List.take [.zero]) listNat (mkNatLit n.getNat)
    (mkApp3 (mkConst ``List.drop [.zero]) listNat (mkNatLit a.getNat) codesList)
  let select ← mkExpectedTypeHint (← mkEqRefl listLits) (← mkEq lhs listLits)
  -- Rewrite each element with its equation, from the last one.
  let cons := mkApp (mkConst ``List.cons [.zero]) listNat
  let mut proof ← mkEqRefl (mkApp (mkConst ``List.nil [.zero]) listNat)
  let mut accL := mkApp (mkConst ``List.nil [.zero]) listNat
  let mut accR := accL
  for (l, r, h) in eqs.reverse do
    let hHead := mkApp6 (mkConst ``congrArg [.one, .one]) listNat
      (← mkArrow (mkApp (mkConst ``List [.zero]) listNat) (mkApp (mkConst ``List [.zero]) listNat))
      l r cons h
    proof := mkAppN (mkConst ``congr [.one, .one])
      #[mkApp (mkConst ``List [.zero]) listNat, mkApp (mkConst ``List [.zero]) listNat,
        mkApp cons l, mkApp cons r, accL, accR, hHead, proof]
    accL := mkApp2 cons l accL
    accR := mkApp2 cons r accR
  mkEqTrans select proof

/-! ## Declaring the checks -/

open Lean Elab Command in
/-- Declares the checks of the chunks `a` to `b - 1` of the strings `xs`.

Chunk `k` holds the 16 strings from index `16 * k`.

Its check is the theorem `name_k`, closed by a kernel check. -/
elab "torsion_checks " name:ident xs:ident a:num b:num : command => do
  for k in [a.getNat:b.getNat] do
    let id := mkIdent (name.getId.appendAfter s!"_{k}")
    let start := Syntax.mkNumLit (toString (16 * k))
    elabCommand (← `(command|
      theorem $id:ident :
          (((($xs).toList.map codes).drop $start).take 16).all checkCodes = true := by
        rw [codes_chunk% $xs $start 16]
        decide +kernel))

end EthLib.Cryptography.Kzg.SetupTorsion
