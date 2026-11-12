module

public import EthLib.Cryptography.Bls.KeyPath

public import Mathlib.Data.List.Forall2

import Batteries.Data.String.Lemmas
import EthLib.Base.Except
import EthLib.Base.Proofs.Forall2
import Init.Data.Nat.ToString
import Init.Data.String.Lemmas.Pattern.Split.Char

/-!
# Proofs: ERC-2334 key paths

Paths have the required purpose and at least four child indices.

Parsing the written form of a path gives back the same path, at any depth.

An index is accepted exactly when it is a non-empty run of decimal digits with a value below 2^32.

A path is accepted exactly when it is `m` and at least four such indices, the first of them 12381.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.KeyPath

/-- Path error codes start at 101, so they never meet a BLS error code. -/
theorem KeyPathError.code_ge (e : KeyPathError) : 101 ≤ e.code := by
  cases e <;> simp [KeyPathError.code]

/-- Every path includes purpose, coin type, account and use. -/
theorem four_le_length_indices (path : Path) : 4 ≤ path.indices.length := by
  simp [Path.indices]

/-- The withdrawal path uses Ethereum coin type 3600 and use zero. -/
theorem withdrawalPath_indices (index : UInt32) :
    (withdrawalPath index).indices = [12381, 3600, index, 0] := rfl

/-- The signing path is child zero of the withdrawal path. -/
theorem signingPath_indices (index : UInt32) :
    (signingPath index).indices = (withdrawalPath index).indices ++ [0] := rfl

/-- An OR with a byte of 58 or more gives no decimal digit. -/
private theorem not_digit_or {a b : UInt8} (hb : 58 ≤ b.toNat) :
    ¬ (48 ≤ (a ||| b) && (a ||| b) ≤ 57) = true := by
  intro h
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, UInt8.toNat_or] at h
  have : b.toNat ≤ a.toNat ||| b.toNat := Nat.or_comm b.toNat a.toNat ▸ Nat.left_le_or
  simp at h
  omega

/-- The first byte of a character that is no decimal digit is no decimal digit either. -/
private theorem decimalValue_utf8EncodeChar_append {c : Char} (hc : c.isDigit = false)
    (rest : List UInt8) (init : Nat) :
    decimalValue (String.utf8EncodeChar c ++ rest) init = none := by
  have hpos := Char.utf8Size_pos c
  have hle := Char.utf8Size_le_four c
  by_cases h1 : c.utf8Size = 1
  · rw [String.utf8EncodeChar_eq_singleton h1]
    have hlt : c.toNat ≤ 127 := by
      simpa [UInt32.le_iff_toNat_le] using (Char.utf8Size_eq_one_iff).mp h1
    have hval : c.val.toUInt8.toNat = c.toNat := by
      change c.val.toNat % 2 ^ 8 = c.val.toNat
      exact Nat.mod_eq_of_lt (by change c.toNat < 256; omega)
    have hnd : ¬ (48 ≤ c.val.toUInt8 && c.val.toUInt8 ≤ 57) = true := by
      intro hb
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, hval] at hb
      have : c.isDigit = true := Char.isDigit_iff_toNat.mpr hb
      simp_all
    simp only [List.singleton_append, decimalValue, hnd, Bool.false_eq_true, ↓reduceIte]
  · by_cases h2 : c.utf8Size = 2
    · rw [String.utf8EncodeChar_eq_cons_cons h2]
      simp [decimalValue, not_digit_or (a := (c.val >>> 6).toUInt8 &&& 0x1f) (b := 0xc0)
        (by decide)]
    · by_cases h3 : c.utf8Size = 3
      · rw [String.utf8EncodeChar_eq_cons_cons_cons h3]
        simp [decimalValue, not_digit_or (a := (c.val >>> 12).toUInt8 &&& 0x0f) (b := 0xe0)
          (by decide)]
      · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons (by omega)]
        simp [decimalValue, not_digit_or (a := (c.val >>> 18).toUInt8 &&& 0x07) (b := 0xf0)
          (by decide)]

/-- The digit reader succeeds on the bytes of some characters exactly when each is a decimal digit.

Its value is then the number that the digits write in base ten after the accumulator. -/
private theorem decimalValue_utf8Encode_eq_some_iff (cs : List Char) (init n : Nat) :
    decimalValue cs.utf8Encode.data.toList init = some n ↔
      (∀ c ∈ cs, c.isDigit = true) ∧ n = Nat.ofDigitChars 10 cs init := by
  induction cs generalizing init with
  | nil =>
    rw [show ([] : List Char).utf8Encode.data.toList = [] from rfl]
    simp only [decimalValue, Nat.ofDigitChars_nil, Option.some.injEq, List.not_mem_nil,
      false_implies, implies_true, true_and]
    exact eq_comm
  | cons c cs ih =>
    rw [List.utf8Encode_cons, List.utf8Encode_singleton]
    simp only [ByteArray.data_append, Array.toList_append, List.toList_data_toByteArray]
    cases hc : c.isDigit with
    | false =>
      rw [decimalValue_utf8EncodeChar_append hc]
      simp [hc]
    | true =>
      have hc' : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := Char.isDigit_iff_toNat.mp hc
      have hb : c.utf8Size = 1 := by
        unfold Char.utf8Size
        have hh : c.val ≤ 127 := UInt32.le_iff_toNat_le.mpr (by change c.toNat ≤ 127; omega)
        simp [hh]
      rw [String.utf8EncodeChar_eq_singleton hb]
      have hval : c.val.toUInt8.toNat = c.toNat := by
        change c.val.toNat % 2 ^ 8 = c.val.toNat
        exact Nat.mod_eq_of_lt (by change c.toNat < 256; omega)
      have hdig : (48 ≤ c.val.toUInt8 && c.val.toUInt8 ≤ 57) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, hval]
        exact hc'
      simp only [List.singleton_append, decimalValue, hdig, ↓reduceIte, hval]
      rw [ih]
      simp [Nat.ofDigitChars_cons, hc]

/-- A character lies between `0` and `9` exactly when it is a decimal digit. -/
private theorem le_and_le_iff_isDigit (c : Char) : ('0' ≤ c ∧ c ≤ '9') ↔ c.isDigit = true := by
  rw [Char.isDigit_iff_toNat]
  simp only [Char.le_def, UInt32.le_iff_toNat_le]
  rfl

/-- A segment is an index exactly when it is a non-empty run of the decimal digits `0` to `9`.

The index is the number that those digits write in base ten, which must lie below 2^32.

So leading zeros are accepted, and a sign, a space or an apostrophe is not. -/
theorem parseIndex_eq_ok_iff {segment : String} {index : UInt32} :
    parseIndex segment = .ok index ↔
      segment ≠ "" ∧ (∀ c ∈ segment.toList, '0' ≤ c ∧ c ≤ '9') ∧
        index.toNat = Nat.ofDigitChars 10 segment.toList 0 := by
  obtain ⟨cs, rfl⟩ : ∃ cs, segment = String.ofList cs := ⟨segment.toList, by simp⟩
  simp only [String.toList_ofList, le_and_le_iff_isDigit]
  unfold parseIndex
  rw [String.toByteArray_ofList]
  by_cases he : cs = []
  · subst he
    simp only [ne_eq, String.ofList_nil, not_true_eq_false, false_and, iff_false]
    nofun
  · have hn : ¬(cs.utf8Encode.data.toList.isEmpty) := by
      simp only [List.isEmpty_iff, Array.toList_eq_nil_iff]
      intro hh
      exact he (List.utf8Encode_eq_empty.mp (ByteArray.ext hh))
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    have hne : String.ofList cs ≠ "" := by
      intro h
      exact he (by simpa using congrArg String.toList h)
    have hlt := UInt32.toNat_lt index
    cases hv : decimalValue cs.utf8Encode.data.toList 0 with
    | none =>
      simp only
      refine ⟨nofun, ?_⟩
      rintro ⟨_, hd, _⟩
      rw [(decimalValue_utf8Encode_eq_some_iff cs 0 _).mpr ⟨hd, rfl⟩] at hv
      cases hv
    | some v =>
      obtain ⟨hd, rfl⟩ := (decimalValue_utf8Encode_eq_some_iff cs 0 v).mp hv
      simp only
      by_cases hr : Nat.ofDigitChars 10 cs 0 < 2 ^ 32
      · simp only [hr, ↓reduceIte]
        constructor
        · intro h
          have h' : UInt32.ofNat (Nat.ofDigitChars 10 cs 0) = index := by injection h
          subst h'
          exact ⟨hne, hd, by simp [Nat.mod_eq_of_lt hr]⟩
        · rintro ⟨_, _, h⟩
          show Except.ok _ = Except.ok index
          congr 1
          apply UInt32.toNat_inj.mp
          rw [h]
          simp [Nat.mod_eq_of_lt hr]
      · simp only [hr, ↓reduceIte]
        refine ⟨nofun, ?_⟩
        rintro ⟨_, _, h⟩
        omega

/-- Parsing the decimal form of an index gives back the index. -/
theorem parseIndex_toString (index : UInt32) :
    parseIndex (toString index.toNat) = .ok index := by
  rw [Nat.toString_eq_ofList_toDigits]
  refine parseIndex_eq_ok_iff.mpr ⟨?_, ?_, ?_⟩
  · -- The decimal form of a number has at least one digit.
    intro h
    simpa using congrArg String.toList h
  · intro c hc
    rw [String.toList_ofList] at hc
    exact (le_and_le_iff_isDigit c).mpr (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
  · simp [Nat.ofDigitChars_ten_toDigits]

private theorem slash_not_mem_toString (n : Nat) : '/' ∉ (toString n).toList := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  intro hc
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  contradiction

/-- Parsing the written form of a path gives back the same path, at any depth. -/
theorem parsePath_toString (path : Path) : parsePath path.toString = .ok path := by
  -- Write `m` as the first segment, so that splitting at `/` undoes the join.
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
  rw [String.splitToList_of_valid, ← List.splitOn_eq_splitOnP,
    ← String.toList_split_char, hs]
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

/-- An index is written with decimal digits alone, so it holds no `/`. -/
private theorem slash_not_mem_of_parseIndex {segment : String} {index : UInt32}
    (h : parseIndex segment = .ok index) : '/' ∉ segment.toList := by
  intro hm
  have := (parseIndex_eq_ok_iff.mp h).2.1 '/' hm
  revert this
  decide

/-- Joining the segments of a text at `/` gives back the text. -/
private theorem intercalate_splitToList (text : String) :
    "/".intercalate (text.splitToList (· == '/')) = text := by
  rw [String.splitToList_of_valid, ← List.splitOn_eq_splitOnP]
  apply String.toList_inj.mp
  simp [String.toList_intercalate, Function.comp_def, List.intercalate_splitOn]

/-- A text is a path exactly when it is `m` and then at least four indices, each after a `/`.

The first index is the purpose 12381, and the coin type, the account and the use follow it.

Any deeper indices are the subpath, in order.

Each index is written as a single index is, so no index has a hardened marker or a space.

The coin type may be any index, as ERC-2334, Coin Type, fixes none. -/
theorem parsePath_eq_ok_iff {text : String} {path : Path} :
    parsePath text = .ok path ↔
      ∃ purpose segments, text = "/".intercalate ("m" :: purpose :: segments) ∧
        parseIndex purpose = .ok 12381 ∧
        List.Forall₂ (fun segment index => parseIndex segment = .ok index) segments
          (path.coinType :: path.account :: path.use :: path.subpath) := by
  constructor
  · intro h
    have ht := intercalate_splitToList text
    unfold parsePath at h
    generalize text.splitToList (· == '/') = parts at h ht
    subst ht
    rcases parts with _ | ⟨root, _ | ⟨p, _ | ⟨c, _ | ⟨a, _ | ⟨u, sub⟩⟩⟩⟩⟩
    rotate_left 5
    · by_cases hr : root = "m"
      · subst hr
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
        simp only [EthLib.Base.bind_ok_iff] at h
        obtain ⟨pv, hpv, h⟩ := h
        by_cases hpp : pv = PURPOSE
        · subst hpp
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
            EthLib.Base.bind_ok_iff] at h
          obtain ⟨cv, hc, av, ha, uv, hu, sv, hsv, h⟩ := h
          cases h
          exact ⟨p, c :: a :: u :: sub, rfl, hpv,
            .cons hc (.cons ha (.cons hu (EthLib.Base.forall₂_of_mapM_ok hsv)))⟩
        · simp [hpp, throw, throwThe, MonadExceptOf.throw] at h
          exact nomatch h
      · simp [hr, throw, throwThe, MonadExceptOf.throw] at h
        exact nomatch h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    all_goals
      by_cases hr : root = "m" <;>
        simp [hr, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · rintro ⟨purpose, segments, rfl, hp, hs⟩
    rcases hs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hu, hsub⟩⟩⟩
    rename_i coinType account use subpath
    have hnone : ∀ s ∈ "m" :: purpose :: coinType :: account :: use :: subpath, '/' ∉ s.toList := by
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | hs
      · decide
      · exact slash_not_mem_of_parseIndex hp
      · exact slash_not_mem_of_parseIndex hc
      · exact slash_not_mem_of_parseIndex ha
      · exact slash_not_mem_of_parseIndex hu
      · obtain ⟨_, _, h⟩ := EthLib.Base.exists_mem_of_forall₂ hsub hs
        exact slash_not_mem_of_parseIndex h
    have hs : ("/".intercalate ("m" :: purpose :: coinType :: account :: use :: subpath)
        |>.splitToList (· == '/')) = "m" :: purpose :: coinType :: account :: use :: subpath := by
      rw [String.splitToList_of_valid, ← List.splitOn_eq_splitOnP, ← String.toList_split_char]
      simpa using String.toList_split_intercalate (c := '/') hnone
    unfold parsePath
    rw [hs]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hp, hc, ha, hu,
      EthLib.Base.mapM_ok_of_forall₂ hsub]
    rfl

end EthLib.Cryptography.Bls.KeyPath
