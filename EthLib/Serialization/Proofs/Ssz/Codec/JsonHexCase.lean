module

public import EthLib.Serialization.Ssz.Codec.Json

/-!
# Proofs: hex reads the same in either case

A hex digit reads the same in uppercase, so a hex string does too.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- A lowercase letter is 32 below the code of its uppercase letter. -/
private theorem toUpper_val_of_lower {c : Char} (low : 'a'.val.toNat ≤ c.val.toNat)
    (high : c.val.toNat ≤ 'z'.val.toNat) : c.toUpper.val.toNat + 32 = c.val.toNat := by
  have h : 'a'.val ≤ c.val ∧ c.val ≤ 'z'.val := by
    simp only [UInt32.le_iff_toNat_le]
    exact ⟨low, high⟩
  simp only [Char.toUpper, h, and_self, ↓reduceDIte, UInt32.toNat_add, UInt32.toNat_sub]
  have ea : 'a'.val.toNat = 97 := rfl
  have eA : 'A'.val.toNat = 65 := rfl
  have ez : 'z'.val.toNat = 122 := rfl
  omega

/-- The code of any other character is kept in uppercase. -/
private theorem toUpper_of_not_lower {c : Char} (h : ¬ ('a'.val.toNat ≤ c.val.toNat ∧
    c.val.toNat ≤ 'z'.val.toNat)) : c.toUpper = c := by
  have h' : ¬ ('a'.val ≤ c.val ∧ c.val ≤ 'z'.val) := by
    simpa only [UInt32.le_iff_toNat_le] using h
  unfold Char.toUpper
  simp only [h', ↓reduceDIte]

/-- A hex digit reads the same in uppercase. -/
theorem hexDigit_toUpper (c : Char) : hexDigit c.toUpper = hexDigit c := by
  by_cases h : 'a'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ 'z'.val.toNat
  · have key := toUpper_val_of_lower h.1 h.2
    unfold hexDigit
    simp only [Char.le_def, Char.toNat, UInt32.le_iff_toNat_le]
    generalize c.toUpper = d at *
    have e0 : '0'.val.toNat = 48 := rfl
    have e9 : '9'.val.toNat = 57 := rfl
    have ea : 'a'.val.toNat = 97 := rfl
    have ef : 'f'.val.toNat = 102 := rfl
    have ez : 'z'.val.toNat = 122 := rfl
    have eA : 'A'.val.toNat = 65 := rfl
    have eF : 'F'.val.toNat = 70 := rfl
    simp only [e0, e9, ea, ef, ez, eA, eF, Bool.and_eq_true, decide_eq_true_eq] at *
    repeat' split
    all_goals first | rfl | (exfalso; omega) | (congr 1; omega)
  · rw [toUpper_of_not_lower h]

/-- Pairs of digits read the same in uppercase. -/
theorem hexBytesFrom_map_toUpper :
    ∀ (digits : List Char) (out : Bytes),
      hexBytesFrom (digits.map Char.toUpper) out = hexBytesFrom digits out
  | [], _ => rfl
  | [_], _ => rfl
  | high :: low :: rest, out => by
    simp only [List.map_cons, hexBytesFrom, hexDigit_toUpper, hexBytesFrom_map_toUpper rest]

/-- Hex reads the same with its digits in uppercase. -/
theorem ofHex_uppercase (digits : String) :
    ofHex ("0x" ++ digits.map Char.toUpper) = ofHex ("0x" ++ digits) := by
  simp only [ofHex, String.toList_append, String.toList_map]
  have marker : "0x".toList = ['0', 'x'] := by decide
  simp only [marker, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact hexBytesFrom_map_toUpper digits.toList #[]

end EthLib.Serialization.Ssz
