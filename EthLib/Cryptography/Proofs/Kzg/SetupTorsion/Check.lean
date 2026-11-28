module

public import EthLib.Cryptography.Kzg.TrustedSetup
public import EthLib.Cryptography.Proofs.Bls.G1TorsionCheck
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Checker
public import EthLib.Cryptography.Proofs.Kzg.TrustedSetup

/-!
# Proofs: the check that reads one point of the embedded setup is sound

If the check of a string passes, every point that the string decodes to has order dividing `r`.

The file also declares a term that gathers the checks of many strings.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

open EthLib.Cryptography.Bls

/-- The hex reader of Base reads a digit as the decoder of its code does. -/
theorem hexValue?_eq (c : Char) : Base.hexValue? c = (digit c.toNat).map UInt8.ofNat := by
  have e0 : ('0' : Char).val.toNat = 48 := rfl
  have e9 : ('9' : Char).val.toNat = 57 := rfl
  have ea : ('a' : Char).val.toNat = 97 := rfl
  have ef : ('f' : Char).val.toNat = 102 := rfl
  have eA : ('A' : Char).val.toNat = 65 := rfl
  have eF : ('F' : Char).val.toNat = 70 := rfl
  unfold Base.hexValue? digit
  simp only [Char.le_def, Char.toNat, UInt32.le_iff_toNat_le, e0, e9, ea, ef, eA, eF, true_and]
  split_ifs <;> simp only [Option.map_some, Option.map_none, Nat.toUInt8_eq]
  all_goals (congr 2; omega)

theorem digit_lt {n d : Nat} (h : digit n = some d) : d < 16 := by
  unfold digit at h
  split_ifs at h <;> cases h <;> omega

/-- Two digits make one byte, as the hex reader of Base combines them.

Byte arithmetic is modulo 256, so the equation holds for any two numbers. -/
theorem byte_eq (a b : Nat) : 16 * UInt8.ofNat a + UInt8.ofNat b = UInt8.ofNat (a * 16 + b) := by
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_add, UInt8.toNat_mul, UInt8.toNat_ofNat]
  omega

/-- The hex reader of Base reads the bytes that the digit codes give. -/
theorem hexBytesFrom?_eq : ∀ (cs : List Char) (acc : ByteArray),
    Base.hexBytesFrom? cs acc =
      (hexBytes (cs.map Char.toNat)).map fun l => ⟨acc.data ++ (l.map UInt8.ofNat).toArray⟩
  | [], acc => by simp [Base.hexBytesFrom?, hexBytes]
  | [_], acc => by simp [Base.hexBytesFrom?, hexBytes]
  | hi :: lo :: rest, acc => by
    rw [Base.hexBytesFrom?, List.map_cons, List.map_cons, hexBytes, hexValue?_eq, hexValue?_eq]
    cases hh : digit hi.toNat with
    | none => rfl
    | some h =>
      cases hl : digit lo.toNat with
      | none => rfl
      | some l =>
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
        rw [byte_eq]
        rw [hexBytesFrom?_eq rest]
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
  rw [Fp.val_of_fromBytesBE h]
  cases l with
  | nil => rfl
  | cons a t =>
    simp [ByteArray.set!, ByteArray.get!, xOf]
    -- Both sides fold over the same bytes: a byte `u` maps `acc` to `256 acc + (u mod 256)`.
    rw [Base.ByteOrder.ofBE_eq_foldl, List.foldl_cons, List.foldl_map]
    refine congrArg₂ (fun f i => List.foldl f i t) ?_ ?_
    · funext acc u
      rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt u (by decide) : u % 256 < 2 ^ 8),
        Nat.shiftLeft_eq, UInt8.toNat_ofNat']
      omega
    · simp [UInt8.toNat_and]

/-! ## The check is sound -/

/-- If the check of a string passes, each point that it decodes to has order dividing `r`. -/
theorem modulus_smul_eq_zero {s : String} {b : ByteArray} {q : G1}
    (hc : checkCodes (codes s) = true) (hb : Base.hexBytes? s.toList = some b)
    (hq : TrustedSetup.decodeG1 b = .ok q) : Fr.modulus • G1.toPoint q = 0 := by
  unfold checkCodes codes at hc
  rw [Base.hexBytes?, hexBytesFrom?_eq] at hb
  cases hl : hexBytes (s.toList.map Char.toNat) with
  | none => rw [hl] at hc; cases hc
  | some l =>
    rw [hl] at hc
    rw [hl, Option.map_some, Option.some.injEq] at hb
    subst hb
    obtain ⟨v, hv, hq⟩ := TrustedSetup.decodeG1_eq_ok.mp hq
    rcases G1.uncompress_eq_zero_or_bytes hv hq with rfl | ⟨x, y, hx, hy, rfl⟩
    · rw [G1.toPoint_zero, nsmul_zero]
    · have he : ByteArray.empty.data ++ (l.map UInt8.ofNat).toArray =
          (l.map UInt8.ofNat).toArray := Array.empty_append
      rw [he] at hx
      exact G1.TorsionCheck.modulus_smul_eq_zero ((fromBytesBE_eq hx).symm ▸ hc) hy

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

/-! ## Gathering the checks -/

/-- A predicate holds below `a + b` if it holds below `a`, and at `a + k` for each `k` below `b`. -/
theorem forall_lt_add {p : Nat → Prop} {a b : Nat} (ha : ∀ k < a, p k)
    (hb : ∀ k < b, p (a + k)) : ∀ k < a + b, p k := fun k hk =>
  if h : k < a then ha k h else Nat.add_sub_cancel' (Nat.le_of_not_lt h) ▸ hb (k - a) (by omega)

/-- A predicate holds below 1 if it holds at 0. -/
theorem forall_lt_one {p : Nat → Prop} (h : p 0) : ∀ k < 1, p k := fun _ hk =>
  Nat.lt_one_iff.mp hk ▸ h

open Lean in
/-- A proof of `∀ k < n, p (lo + k)` from the theorems for `lo` to `lo + n - 1`.

It splits the range in halves, so the proof has depth logarithmic in `n`. -/
meta def checksBelow (leaf : Nat → MacroM Term) (lo n : Nat) : MacroM Term :=
  if n = 0 then `(fun _ h => absurd h (Nat.not_lt_zero _))
  else if n = 1 then do `(forall_lt_one $(← leaf lo))
  else do
    `(forall_lt_add (a := $(quote (n / 2))) (b := $(quote (n - n / 2)))
      $(← checksBelow leaf lo (n / 2)) $(← checksBelow leaf (lo + n / 2) (n - n / 2)))
termination_by n
decreasing_by all_goals omega

open Lean in
/-- A proof of `∀ k < n, p k` from the theorems `name_0` to `name_(n - 1)`.

With two bounds `n m`, it proves `∀ k < n, ∀ l < m, p k l` from the theorems `name_k_l`. -/
macro "checks_of% " name:ident bounds:num+ : term => do
  let rec go (pre : Name) : List Nat → MacroM Term
    | [] => return mkIdent pre
    | n :: rest => checksBelow (fun k => go (pre.appendAfter s!"_{k}") rest) 0 n
  go name.getId (bounds.map (·.getNat)).toList

end EthLib.Cryptography.Kzg.SetupTorsion
