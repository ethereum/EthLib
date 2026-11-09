module

public import EthLib.Cryptography.Bls.KeyPath

import Init.Data.Nat.ToString
import Init.Data.String.Lemmas.Pattern.Split.Char

/-!
# Proofs: ERC-2334 key paths

Paths have the required purpose and at least four child indices.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.KeyPath

/-- Every path includes purpose, coin type, account and use. -/
theorem four_le_length_indices (path : Path) : 4 ≤ path.indices.length := by
  simp [Path.indices]

/-- The withdrawal path uses Ethereum coin type 3600 and use zero. -/
theorem withdrawalPath_indices (index : UInt32) :
    (withdrawalPath index).indices = [12381, 3600, index, 0] := rfl

/-- The signing path is child zero of the withdrawal path. -/
theorem signingPath_indices (index : UInt32) :
    (signingPath index).indices = (withdrawalPath index).indices ++ [0] := rfl

private theorem decimalValue_utf8Encode (cs : List Char) (init : Nat)
    (h : ∀ c ∈ cs, c.isDigit = true) :
    decimalValue cs.utf8Encode.data.toList init = some (Nat.ofDigitChars 10 cs init) := by
  induction cs generalizing init with
  | nil => simp [List.utf8Encode_nil, decimalValue]
  | cons c cs ih =>
    have hc := h c (by simp)
    have hc' : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := Char.isDigit_iff_toNat.mp hc
    -- Decimal characters use a single UTF-8 byte.
    have hb : c.utf8Size = 1 := by
      unfold Char.utf8Size
      have hh : c.val ≤ 127 := UInt32.le_iff_toNat_le.mpr (by change c.toNat ≤ 127; omega)
      simp [hh]
    rw [List.utf8Encode_cons, List.utf8Encode_singleton,
      String.utf8EncodeChar_eq_singleton hb]
    simp only [ByteArray.data_append, Array.toList_append]
    have hval : c.toUInt8.toNat = c.toNat := by
      change c.val.toNat % 2 ^ 8 = c.val.toNat
      exact Nat.mod_eq_of_lt (by change c.toNat < 256; omega)
    have ht : ∀ x ∈ cs, x.isDigit = true := fun x hx => h x (by simp [hx])
    simpa [decimalValue, Nat.ofDigitChars_cons, hval, UInt8.le_iff_toNat_le,
      hc'.1, hc'.2] using ih (10 * init + (c.toNat - 48)) ht

private theorem parseIndex_toString (index : UInt32) :
    parseIndex (toString index.toNat) = .ok index := by
  have hd : decimalValue (Nat.toDigits 10 index.toNat).utf8Encode.data.toList 0 =
      some index.toNat := by
    simpa using decimalValue_utf8Encode (Nat.toDigits 10 index.toNat) 0
      (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
  have hn : ¬(Nat.toDigits 10 index.toNat).utf8Encode.data.toList.isEmpty := by
    simp only [List.isEmpty_iff, Array.toList_eq_nil_iff]
    intro hh
    have he : (Nat.toDigits 10 index.toNat).utf8Encode = ByteArray.empty := by
      exact ByteArray.ext hh
    exact Nat.toDigits_ne_nil (List.utf8Encode_eq_empty.mp he)
  rw [Nat.toString_eq_ofList_toDigits]
  unfold parseIndex
  simp only [String.toByteArray_ofList, hn, Bool.false_eq_true, ↓reduceIte]
  have hr : index.toNat < 4294967296 := UInt32.toNat_lt index
  simp [hd, hr]
  rfl

private theorem slash_not_mem_toString (n : Nat) : '/' ∉ (toString n).toList := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  intro hc
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  contradiction

/-- Parsing the decimal form of a path recovers every index, including deeper indices. -/
theorem parsePath_toString (path : Path) : parsePath path.toString = .ok path := by
  -- Include the master node in the intercalation to use the split inverse.
  have hf : path.toString = "/".intercalate ("m" ::
      path.indices.map (fun index => toString index.toNat)) := by
    simp [Path.toString, Path.indices, String.append_assoc]
  have hs : (path.toString.split '/').toList.map String.Slice.copy =
      "m" :: path.indices.map (fun index => toString index.toNat) := by
    rw [hf]
    have hnone : ∀ s ∈ "m" :: path.indices.map (fun index => toString index.toNat),
        '/' ∉ s.toList := by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · decide
      · obtain ⟨index, _, rfl⟩ := List.mem_map.mp hs
        exact slash_not_mem_toString index.toNat
    simpa using String.toList_split_intercalate (c := '/') hnone
  unfold parsePath
  rw [hs]
  simp only [Path.indices, List.map_cons]
  simp only [parseIndex_toString]
  simp only [List.mapM_map, Function.comp_def, parseIndex_toString]
  simp only [Bind.bind, Except.bind]
  have hm : (path.subpath.mapM fun x => (Except.ok x : Except KeyPathError UInt32)) =
      .ok path.subpath := by
    change path.subpath.mapM pure = pure path.subpath
    simpa using (List.mapM_pure (m := Except KeyPathError) (l := path.subpath) (f := id))
  rw [hm]
  rfl

end EthLib.Cryptography.Bls.KeyPath
