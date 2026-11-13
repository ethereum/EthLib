module

public import EthLib.Execution.Rpc.BlockParam
public import EthLib.Serialization.Proofs.JsonRpc

/-!
# Proofs: the block parameter

Each reader of a block parameter reads back what the writer writes.

A tag, and a hash in the object of EIP-1898, read back as their only reading.

A number reads back as its first reading.

It may have one more, as a hash, when its quantity has exactly 64 digits.

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

/-- Mapping over a rejected reading leaves it rejected. -/
private theorem toOption_map_none {α β : Type} (f : α → β) (r : Read α) (h : r.toOption = none) :
    (f <$> r).toOption = none := by
  cases r <;> simp_all [Functor.map, Except.map, Except.toOption]

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

/-- A number, a tag or a hash reads back a tag, as its only reading. -/
theorem blockNumberOrTagOrHash_tag (what : String) (t : BlockTag) :
    blockNumberOrTagOrHash what (blockParamJson (.tag t)) = .ok [.tag t] := by
  unfold blockNumberOrTagOrHash
  simp only [blockParamJson, List.filterMap_cons, List.filterMap_nil,
    toOption_map_none _ _ (uint_name_none what t),
    toOption_map_none _ _ (hash32_name_none what t), blockTag_name]
  rfl

/-- A number, a tag or a hash reads back a hash with its flag, as its only reading. -/
theorem blockNumberOrTagOrHash_hash (what : String) (h : Hash32) (c : Bool) :
    blockNumberOrTagOrHash what (blockParamJson (.hash h c)) = .ok [.hash h c] := by
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

/-- A number, a tag or a hash reads back a number, as its first reading.

Every other reading is a hash without the flag. -/
theorem blockNumberOrTagOrHash_number (what : String) (n : Nat) :
    ∃ rest, blockNumberOrTagOrHash what (blockParamJson (.number n)) = .ok (.number n :: rest) ∧
      ∀ q ∈ rest, ∃ h, q = .hash h false := by
  have hu : uint what (quantityJson n) = .ok n := uint_quantityJson what n
  obtain ⟨e, he⟩ : ∃ e, blockTag what (quantityJson n) = .error e := by
    cases h : blockTag what (quantityJson n) with
    | error e => exact ⟨e, rfl⟩
    | ok t =>
      have := blockTag_quantity what n
      rw [h] at this
      cases this
  cases hh : hash32 what (quantityJson n) with
  | error e' =>
    refine ⟨[], ?_, by simp⟩
    unfold blockNumberOrTagOrHash
    simp [blockParamJson, hu, he, hh, Functor.map, Except.map, Except.toOption, pure, Except.pure]
    unfold quantityJson
    rfl
  | ok v =>
    refine ⟨[.hash v false], ?_, by simp⟩
    unfold blockNumberOrTagOrHash
    simp [blockParamJson, hu, he, hh, Functor.map, Except.map, Except.toOption, pure, Except.pure]
    unfold quantityJson
    rfl

end EthLib.Execution.Rpc
