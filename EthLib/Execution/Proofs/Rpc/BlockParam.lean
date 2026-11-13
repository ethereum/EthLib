module

public import EthLib.Execution.Rpc.BlockParam
public import EthLib.Serialization.Proofs.JsonRpc

/-!
# Proofs: the block parameter

Each reader of a block parameter reads back what the writer writes.

A tag, and a hash in the object of EIP-1898, read back.

A number reads back when its text is no hash, which holds for every number below `2^252`.

A number with 64 hex digits reads as a hash, as the official fixtures read it.

A range rejects the tag `pending`.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc

/-- No tag name starts with `0x`. -/
private theorem name_ne_hex (t : BlockTag) (l : List Char) : t.name.toList ≠ '0' :: 'x' :: l := by
  cases t <;> simp [BlockTag.name]

/-- A tag name is not the text of a quantity. -/
private theorem uint_name (what : String) (t : BlockTag) (v : Nat) :
    uint what (.str t.name) ≠ .ok v := by
  intro h
  rw [uint_eq_ok_iff] at h
  unfold quantityJson at h
  have h := congrArg String.toList (Lean.Json.str.inj h)
  rw [String.toList_append] at h
  exact name_ne_hex t _ h

/-- A tag name is not the text of a hash. -/
private theorem hash32_name (what : String) (t : BlockTag) (h : Hash32) :
    hash32 what (.str t.name) ≠ .ok h := by
  intro he
  unfold hash32 at he
  rw [fixed_false_eq_ok_iff] at he
  have he := congrArg String.toList (Lean.Json.str.inj he)
  rw [toList_hexString] at he
  exact name_ne_hex t _ he

/-- The reader of tags reads back the name of a tag. -/
private theorem blockTag_name (what : String) (t : BlockTag) :
    blockTag what (.str t.name) = .ok t := by
  cases t <;> rfl

/-- A name that is a tag is the name of that tag. -/
private theorem ofName_eq (s : String) (t : BlockTag) (h : BlockTag.ofName? s = some t) :
    s = t.name := by
  unfold BlockTag.ofName? at h
  split at h <;> first | (obtain rfl := Option.some.inj h; rfl) | cases h

/-- The reader of tags rejects the text of a quantity. -/
private theorem blockTag_quantity (what : String) (n : Nat) :
    (blockTag what (quantityJson n)).toOption = none := by
  unfold quantityJson blockTag
  simp only
  cases h : BlockTag.ofName? ("0x" ++ String.ofList (Nat.toDigits 16 n)) with
  | none => rfl
  | some t =>
    exfalso
    have := congrArg String.toList (ofName_eq _ _ h)
    rw [String.toList_append] at this
    exact name_ne_hex t _ this.symm

/-- The reader of numbers rejects a tag name. -/
private theorem uint_name_none (what : String) (t : BlockTag) :
    (uint what (.str t.name)).toOption = none := by
  cases h : uint what (.str t.name) with
  | error e => rfl
  | ok v => exact absurd h (uint_name what t v)

/-- The reader of hashes rejects a tag name. -/
private theorem hash32_name_none (what : String) (t : BlockTag) :
    (hash32 what (.str t.name)).toOption = none := by
  cases h : hash32 what (.str t.name) with
  | error e => rfl
  | ok v => exact absurd h (hash32_name what t v)

/-- A number or a tag reads back a number. -/
theorem blockNumberOrTag_number (what : String) (n : Nat) :
    blockNumberOrTag what (blockParamJson (.number n)) = .ok (.number n) := by
  unfold blockNumberOrTag
  rcases hb : blockTag what (blockParamJson (.number n)) with e | t
  · simp [blockParamJson, uint_quantityJson, bind, Except.bind, pure, Except.pure]
  · have h := blockTag_quantity what n
    simp only [blockParamJson] at hb
    rw [hb] at h
    cases h

/-- A number or a tag reads back a tag. -/
theorem blockNumberOrTag_tag (what : String) (t : BlockTag) :
    blockNumberOrTag what (blockParamJson (.tag t)) = .ok (.tag t) := by
  unfold blockNumberOrTag
  rw [blockParamJson, blockTag_name]
  rfl

/-- A number or a tag of a range reads back a number. -/
theorem blockNumberOrTagForRange_number (what : String) (n : Nat) :
    blockNumberOrTagForRange what (blockParamJson (.number n)) = .ok (.number n) := by
  unfold blockNumberOrTagForRange
  rw [blockNumberOrTag_number]
  rfl

/-- A number or a tag of a range reads back every tag but `pending`. -/
theorem blockNumberOrTagForRange_tag (what : String) {t : BlockTag} (ht : t ≠ .pending) :
    blockNumberOrTagForRange what (blockParamJson (.tag t)) = .ok (.tag t) := by
  unfold blockNumberOrTagForRange
  rw [blockNumberOrTag_tag]
  cases t <;> first | rfl | exact absurd rfl ht

/-- A number or a tag of a range rejects the tag `pending`. -/
theorem blockNumberOrTagForRange_pending (what : String) :
    (blockNumberOrTagForRange what (blockParamJson (.tag .pending))).toOption = none := by
  unfold blockNumberOrTagForRange
  rw [blockNumberOrTag_tag]
  rfl

/-- A number, a tag or a hash reads back a tag. -/
theorem blockNumberOrTagOrHash_tag (what : String) (t : BlockTag) :
    blockNumberOrTagOrHash what (blockParamJson (.tag t)) = .ok (.tag t) := by
  have h1 := hash32_name_none what t
  have h2 := uint_name_none what t
  unfold blockNumberOrTagOrHash
  rw [blockParamJson, blockTag_name]
  rcases e1 : hash32 what (.str t.name) with _ | _
  · rcases e2 : uint what (.str t.name) with _ | _
    · rfl
    · rw [e2] at h2
      cases h2
  · rw [e1] at h1
    cases h1

/-- A number, a tag or a hash reads back a hash with its flag. -/
theorem blockNumberOrTagOrHash_hash (what : String) (h : Hash32) (c : Bool) :
    blockNumberOrTagOrHash what (blockParamJson (.hash h c)) = .ok (.hash h c) := by
  obtain ⟨kvs, hobj, hlen, hmem, hd⟩ := toList_mkObj (pairs := [
    ("blockHash", dataJson h.toList), ("requireCanonical", .bool c)]) (by simp)
  have hnone : kvs.toList.lookup "blockNumber" = none := by
    have : ∀ p ∈ kvs.toList, p.1 ≠ "blockNumber" := by
      intro p hp
      have := (hmem p).mp hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl <;> simp
    generalize kvs.toList = l at this
    induction l with
    | nil => rfl
    | cons q l ih =>
      simp only [List.lookup]
      have hq := this q (by simp)
      have hb : ("blockNumber" == q.1) = false := by simpa using Ne.symm hq
      rw [hb]
      exact ih fun p hp => this p (by simp [hp])
  have hh := lookup_of_mem hd ((hmem ("blockHash", dataJson h.toList)).mpr (by simp))
  have hc := lookup_of_mem hd ((hmem ("requireCanonical", .bool c)).mpr (by simp))
  have hall : (kvs.toList.all fun (k, _) => k == "blockHash" || k == "requireCanonical") =
      true := by
    refine List.all_eq_true.mpr fun p hp => ?_
    have := (hmem p).mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl <;> simp
  have hx : hash32 what (dataJson h.toList) = .ok h := fixed_hexString what 32 h false
  unfold blockNumberOrTagOrHash
  rw [blockParamJson, hobj]
  simp only [hnone, hh, hc, hall, requireCanonical, hx]
  rfl

/-- The text of a number below `2^252` has fewer than 64 digits, so it is no hash. -/
theorem hash32_quantityJson_of_lt (what : String) {n : Nat} (hn : n < 2 ^ 252) :
    (hash32 what (quantityJson n)).toOption = none := by
  cases h : hash32 what (quantityJson n) with
  | error e => rfl
  | ok v =>
    exfalso
    unfold hash32 at h
    rw [fixed_false_eq_ok_iff] at h
    have h := congrArg String.toList (Lean.Json.str.inj h)
    unfold quantityJson at h
    rw [String.toList_append, toList_hexString, String.toList_ofList] at h
    have h := congrArg List.length (List.append_cancel_left (as := ['0', 'x']) h)
    have hl : ∀ l : List UInt8, (l.flatMap byteHexDigits).length = 2 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons b l ih =>
        simp only [List.flatMap_cons, List.length_append, ih]
        simp [byteHexDigits]
        omega
    have hv := hl v.toList
    have hs : v.toList.length = 32 := by simp
    simp only [← List.flatMap_def] at h
    have hd := (Nat.length_toDigits_le_iff (b := 16) (n := n) (k := 63) (by omega)
      (by omega)).mpr (by
        have : (16 : Nat) ^ 63 = 2 ^ 252 := by decide
        omega)
    simp only [String.toList_ofList] at h
    omega

/-- A number, a tag or a hash reads back a number whose text is no hash. -/
theorem blockNumberOrTagOrHash_number (what : String) {n : Nat}
    (hn : (hash32 what (quantityJson n)).toOption = none) :
    blockNumberOrTagOrHash what (blockParamJson (.number n)) = .ok (.number n) := by
  have hu := uint_quantityJson what n
  unfold blockNumberOrTagOrHash
  rw [blockParamJson]
  unfold quantityJson at *
  rcases e : hash32 what (.str ("0x" ++ String.ofList (Nat.toDigits 16 n))) with _ | _
  · rw [hu]
    rfl
  · rw [e] at hn
    cases hn

/-- A hash written as a bare string reads as that hash, without the flag. -/
theorem blockNumberOrTagOrHash_hashString (what : String) (h : Hash32) :
    blockNumberOrTagOrHash what (dataJson h.toList) = .ok (.hash h false) := by
  have hx : hash32 what (.str (hexString h.toList)) = .ok h := fixed_hexString what 32 h false
  unfold blockNumberOrTagOrHash
  simp only [dataJson]
  rw [hx]
  split <;> simp_all [pure, Except.pure]

end EthLib.Execution.Rpc
