module

public import EthLib.Cryptography.Kzg.TrustedSetup
public import EthLib.Cryptography.Proofs.Bls.G1TorsionCheck
public meta import Lean.Elab.Term

/-!
# Proofs: the check that reads one point of the embedded setup

The embedded setup holds each point as a string of 96 hexadecimal digits.

The check reads the digit codes of such a string, decodes them to 48 bytes, and keeps `x`.

Then it runs the kernel check of `G1` on that `x`.

That check finds `y` with `y^2 = x^3 + 4`, and tests `[r] (x, y, 1) = 0`.

If the check passes, every point that the string decodes to has order dividing `r`.

The kernel decodes a string slowly, since it reads its UTF-8 bytes one at a time.

So a proof first replaces each string by the list of its codes.

The kernel checks that step by unfolding the literal, which is cheap.
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
  | some l => G1.TorsionCheck.check (xOf l)
  | none => false

theorem nibble?_eq (c : Char) : TrustedSetup.nibble? c = (digit c.toNat).map UInt8.ofNat := by
  unfold TrustedSetup.nibble? digit
  dsimp only
  split_ifs <;> rfl

theorem digit_lt {n d : Nat} (h : digit n = some d) : d < 16 := by
  unfold digit at h
  split_ifs at h <;> cases h <;> omega

private theorem byte_eq_aux :
    ∀ a b : Fin 16,
      (UInt8.ofNat a.val <<< 4 ||| UInt8.ofNat b.val) = UInt8.ofNat (a.val * 16 + b.val) := by
  decide

/-- Two digits make one byte, as the decoder of the setup combines them. -/
theorem byte_eq {a b : Nat} (ha : a < 16) (hb : b < 16) :
    (UInt8.ofNat a <<< 4 ||| UInt8.ofNat b) = UInt8.ofNat (a * 16 + b) :=
  byte_eq_aux ⟨a, ha⟩ ⟨b, hb⟩

/-- The decoder of the setup reads the bytes that the digit codes give. -/
theorem hexToBytesAux_eq : ∀ (cs : List Char) (acc : ByteArray),
    TrustedSetup.hexToBytesAux cs acc =
      (hexBytes (cs.map Char.toNat)).map fun l => ⟨acc.data ++ (l.map UInt8.ofNat).toArray⟩
  | [], acc => by simp [TrustedSetup.hexToBytesAux, hexBytes]
  | [_], acc => by simp [TrustedSetup.hexToBytesAux, hexBytes]
  | hi :: lo :: rest, acc => by
    rw [TrustedSetup.hexToBytesAux, List.map_cons, List.map_cons, hexBytes, nibble?_eq,
      nibble?_eq]
    cases hh : digit hi.toNat with
    | none => rfl
    | some h =>
      cases hl : digit lo.toNat with
      | none => rfl
      | some l =>
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, hexToBytesAux_eq rest,
          byte_eq (digit_lt hh) (digit_lt hl)]
        cases hexBytes (rest.map Char.toNat) with
        | none => rfl
        | some r =>
          simp only [Option.map_some, Option.bind_some, Option.pure_def, Option.some.injEq,
            ByteArray.push, List.map_cons]
          congr 1
          rw [← Array.toList_inj]
          simp

/-- The decoder of `G1` reads from the bytes `l` the same `x` coordinate as the check. -/
theorem fromBytesBE_eq {l : List Nat} {x : Fp}
    (h : Fp.fromBytesBE ((⟨(l.map UInt8.ofNat).toArray⟩ : ByteArray).set! 0
      ((⟨(l.map UInt8.ofNat).toArray⟩ : ByteArray).get! 0 &&& 0x1f)) = .ok x) :
    x.val = xOf l := by
  unfold Fp.fromBytesBE at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · cases Except.ok.inj h
    show Fp.bytesBEToNat _ = _
    rw [Fp.bytesBEToNat_eq_list]
    cases l with
    | nil => rfl
    | cons a t =>
      simp [ByteArray.set!, ByteArray.get!, xOf, List.foldl_map]
  · cases h

/-! ## The check is sound -/

/-- If the check of a string passes, each point that it decodes to has order dividing `r`. -/
theorem modulus_smul_eq_zero {s : String} {b : ByteArray} {q : G1}
    (hc : checkCodes (codes s) = true) (hb : TrustedSetup.hexToBytes? s = some b)
    (hq : G1.uncompress b = .ok q) : Fr.modulus • G1.toPoint q = 0 := by
  unfold checkCodes codes at hc
  rw [TrustedSetup.hexToBytes?, hexToBytesAux_eq] at hb
  cases hl : hexBytes (s.toList.map Char.toNat) with
  | none => rw [hl] at hc; cases hc
  | some l =>
    rw [hl] at hc
    rw [hl, Option.map_some, Option.some.injEq] at hb
    subst hb
    rcases G1.uncompress_eq_zero_or hq with rfl | ⟨x, y, hx, hy, rfl⟩
    · rw [G1.toPoint_zero, nsmul_zero]
    · have he : ByteArray.empty.data ++ (l.map UInt8.ofNat).toArray =
          (l.map UInt8.ofNat).toArray := Array.empty_append
      rw [he] at hx
      exact G1.TorsionCheck.modulus_smul_eq_zero ((fromBytesBE_eq hx).symm ▸ hc) hy

/-! ## Reading the literals -/

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

/-! ## Checking a list in chunks -/

/-- A list passes a test when each chunk of `c` elements passes it. -/
theorem all_of_chunks {α : Type} (p : α → Bool) (c : Nat) :
    ∀ (n : Nat) (L : List α), L.length ≤ c * n →
      (∀ k < n, ((L.drop (c * k)).take c).all p = true) → L.all p = true
  | 0, L, hlen, _ => by
    rw [List.eq_nil_of_length_eq_zero (by omega : L.length = 0)]
    rfl
  | n + 1, L, hlen, h => by
    rw [← List.take_append_drop c L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_chunks p c n (L.drop c) ?_ fun k hk => ?_⟩
    · rw [List.length_drop]
      rw [Nat.mul_succ] at hlen
      omega
    · rw [List.drop_drop, show c + c * k = c * (k + 1) by rw [Nat.mul_succ, Nat.add_comm]]
      exact h (k + 1) (by omega)

end EthLib.Cryptography.Kzg.SetupTorsion
