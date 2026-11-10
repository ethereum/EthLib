module

public import EthLib.Execution.Trie.Range
public import EthLib.Execution.Proofs.Trie.Proof

/-!
# Proofs: the range check of a trie

The codes of the range errors, the order of the paths, and where a subtree lies against the range.

Then the nodes that the check reads, and the checks it makes before the proof.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-- Two errors with one code come from one constructor. -/
theorem RangeError.code_injective (e₁ e₂ : RangeError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [RangeError.code] at h; exact absurd h (by decide))

/-- Every code of the range check is at least 201. -/
theorem RangeError.le_code (e : RangeError) : 201 ≤ e.code.toNat := by
  cases e <;> simp only [RangeError.code] <;> decide

/-- A range error never has the code of a trie error, so one Python class carries both. -/
theorem RangeError.code_ne_trie (e : RangeError) (r : TrieError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [RangeError.code, TrieError.code] <;> decide

/-- A range error never has the code of a proof error, so one Python class carries both. -/
theorem RangeError.code_ne_proof (e : RangeError) (r : ProofError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [RangeError.code, ProofError.code] <;> decide

/-! ## Paths in order -/

/-- A path below another stays below every extension of it. -/
theorem lt_append_right : {r a : List Nibble} → (c : List Nibble) → r < a → r < a ++ c
  | _, _, _, .nil => .nil
  | _, _, _, .rel h => .rel h
  | _, _, c, .cons h => .cons (lt_append_right c h)

/-- A path below another, and no prefix of it, keeps every extension of itself below it. -/
theorem append_lt_of_not_prefix : (a b c : List Nibble) → a < b → ¬a <+: b → a ++ c < b
  | [], b, _, _, hprefix => absurd (List.nil_prefix (l := b)) hprefix
  | _ :: _, [], _, hlt, _ => absurd hlt (by simp)
  | x :: a, y :: b, c, hlt, hprefix => by
    rcases List.cons_lt_cons_iff.mp hlt with hxy | ⟨rfl, hab⟩
    · exact List.cons_lt_cons_iff.mpr (.inl hxy)
    · refine List.cons_lt_cons_iff.mpr (.inr ⟨rfl, append_lt_of_not_prefix a b c hab ?_⟩)
      exact fun h => hprefix (List.prefix_cons_inj x |>.mpr h)

/-- Paths are in strictly increasing order exactly when each is below every later path. -/
theorem strictlyIncreasing_iff_pairwise :
    (keys : List (List Nibble)) → (strictlyIncreasing keys = true ↔ keys.Pairwise (· < ·))
  | [] => iff_of_true rfl .nil
  | [_] => iff_of_true rfl (List.pairwise_singleton _ _)
  | a :: b :: rest => by
    have hrest := strictlyIncreasing_iff_pairwise (b :: rest)
    simp only [strictlyIncreasing, List.tail_cons, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true, decide_eq_true_eq] at hrest ⊢
    rw [hrest]
    constructor
    · rintro ⟨hab, hrest⟩
      refine .cons ?_ hrest
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact List.lt_trans hab (List.rel_of_pairwise_cons hrest hx)
    · intro h
      exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, List.Pairwise.of_cons h⟩

/-- Paths in strictly increasing order have no repeat. -/
theorem nodup_of_strictlyIncreasing {keys : List (List Nibble)}
    (h : strictlyIncreasing keys = true) : keys.Nodup :=
  ((strictlyIncreasing_iff_pairwise keys).mp h).imp fun {a b} (hlt : a < b) (heq : a = b) =>
    List.lt_irrefl a (by rwa [← heq] at hlt)

/-- Every path that extends a subtree before the range is below the first end. -/
theorem append_lt_of_rangePlace_before {left pre : List Nibble}
    {right : Option (List Nibble)} (h : rangePlace left right pre = .before) (c : List Nibble) :
    pre ++ c < left := by
  unfold rangePlace at h
  by_cases hboundary : (pre.isPrefixOf left || right.any pre.isPrefixOf) = true
  · simp only [hboundary, ↓reduceIte, reduceCtorEq] at h
  · by_cases hlt : pre < left
    · refine append_lt_of_not_prefix pre left c hlt fun hprefix => hboundary ?_
      simp [List.isPrefixOf_iff_prefix.mpr hprefix]
    · simp only [hboundary, hlt, Bool.false_eq_true, ↓reduceIte] at h
      split at h <;> cases h

/-- Every path that extends a subtree after the range is above the last end. -/
theorem lt_append_of_rangePlace_after {left pre : List Nibble}
    {right : Option (List Nibble)} (h : rangePlace left right pre = .after) (c : List Nibble) :
    ∃ last, right = some last ∧ last < pre ++ c := by
  unfold rangePlace at h
  by_cases hboundary : (pre.isPrefixOf left || right.any pre.isPrefixOf) = true
  · simp only [hboundary, ↓reduceIte, reduceCtorEq] at h
  · by_cases hlt : pre < left
    · simp only [hboundary, hlt, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    · simp only [hboundary, hlt, Bool.false_eq_true, ↓reduceIte] at h
      cases right with
      | none => simp at h
      | some last =>
        have hafter : last < pre := by
          by_cases hafter : last < pre
          · exact hafter
          · simp [hafter] at h
        exact ⟨last, rfl, lt_append_right c hafter⟩

/-- Every path that extends a subtree inside the range lies strictly between its two ends. -/
theorem between_of_rangePlace_inside {left pre : List Nibble}
    {right : Option (List Nibble)} (h : rangePlace left right pre = .inside) (c : List Nibble) :
    left < pre ++ c ∧ ∀ last, right = some last → pre ++ c < last := by
  unfold rangePlace at h
  by_cases hboundary : (pre.isPrefixOf left || right.any pre.isPrefixOf) = true
  · simp only [hboundary, ↓reduceIte, reduceCtorEq] at h
  · by_cases hlt : pre < left
    · simp only [hboundary, hlt, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hboundary
      -- The subtree is above the first end, and no prefix of it.
      have hleft : left < pre ++ c := by
        rcases Std.lt_trichotomy pre left with hlt' | heq | hgt
        · exact absurd hlt' hlt
        · subst heq
          simp [List.isPrefixOf_iff_prefix.mpr (List.prefix_refl pre)] at hboundary
        · exact lt_append_right c hgt
      refine ⟨hleft, ?_⟩
      rintro last rfl
      have hafter : ¬last < pre := by
        intro hafter
        simp [hboundary, hlt, hafter] at h
      have hprefix : ¬pre <+: last := fun hp => by
        simp [List.isPrefixOf_iff_prefix.mpr hp] at hboundary
      have hpre : pre < last := by
        rcases Std.lt_trichotomy pre last with hlt' | heq | hgt
        · exact hlt'
        · exact absurd (heq ▸ List.prefix_refl pre) hprefix
        · exact absurd hgt hafter
      exact append_lt_of_not_prefix pre last c hpre hprefix

/-- A subtree on the path of an end has a path that is a prefix of that end. -/
theorem exists_end_of_rangePlace_boundary {left pre : List Nibble}
    {right : Option (List Nibble)} (h : rangePlace left right pre = .boundary) :
    ∃ path, (path = left ∨ right = some path) ∧ pre.isPrefixOf path = true := by
  unfold rangePlace at h
  by_cases hboundary : (pre.isPrefixOf left || right.any pre.isPrefixOf) = true
  · rcases Bool.or_eq_true_iff.mp hboundary with hl | hr
    · exact ⟨left, .inl rfl, hl⟩
    · cases hright : right with
      | none => simp [hright] at hr
      | some last =>
        rw [hright, Option.any_some] at hr
        exact ⟨last, .inr rfl, hr⟩
  · simp only [hboundary, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h <;> cases h

/-- Hash keys whose paths are in strictly increasing order are distinct byte strings. -/
theorem nodup_toArray_of_strictlyIncreasing {data : List (Hash32 × ByteArray)}
    (h : strictlyIncreasing (data.map fun entry => bytesToNibbleList ⟨entry.1.toArray⟩) = true) :
    ((data.map fun entry => ((⟨entry.1.toArray⟩ : ByteArray), entry.2)).map Prod.fst).Nodup := by
  have hpaths := nodup_of_strictlyIncreasing h
  rw [show (data.map fun entry => bytesToNibbleList ⟨entry.1.toArray⟩) =
      ((data.map fun entry => ((⟨entry.1.toArray⟩ : ByteArray), entry.2)).map Prod.fst).map
        bytesToNibbleList by simp [List.map_map, Function.comp_def]] at hpaths
  exact nodup_of_map bytesToNibbleList hpaths

/-! ## The nodes that the check reads -/

/-- A node held inside its parent is read from the parent. -/
theorem lookupNode_unencoded (nodes : List (Hash32 × ByteArray))
    (node : Option InternalNode) : lookupNode nodes (unencoded node) = .ok (unencoded node) := by
  rcases unencoded_shape node with ⟨items, h⟩ | h <;> rw [h]
  · rfl
  · simp [lookupNode, ByteArray.size_empty]

/-- A node held by hash is read from the proof, when it is the only node there with its hash. -/
theorem lookupNode_hash (hash : ByteArray → Hash32) {proof : List ByteArray}
    {node : Option InternalNode} {encoded : ByteArray}
    (hencode : encode (unencoded node) = .ok encoded) (hmem : encoded ∈ proof)
    (hcoll : ∀ x ∈ proof, hash x = hash encoded → x = encoded) :
    lookupNode (proof.map fun encoded => (hash encoded, encoded))
      (.bytes ⟨(hash encoded).toArray⟩) = .ok (unencoded node) := by
  have hdecode : decode encoded = .ok (unencoded node) := (decode_eq_ok_iff _ _).mpr hencode
  simp only [lookupNode, size_hashBytes]
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  cases hfind : (proof.map fun encoded => (hash encoded, encoded)).find?
      (fun x => x.1.toList == (hash encoded).toArray.toList) with
  | none =>
    have := List.find?_eq_none.mp hfind (hash encoded, encoded) (List.mem_map_of_mem hmem)
    simp [Vector.toList] at this
  | some found =>
    obtain ⟨digest, other⟩ := found
    have hmatch := List.find?_some hfind
    obtain ⟨other', hother, heq⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [beq_iff_eq, Vector.toList] at hmatch
    have hsame : hash other' = hash encoded := Vector.toArray_inj.mp (Array.toList_inj.mp hmatch)
    rw [hcoll _ hother hsame]
    simp [hdecode, Except.mapError]

/-! ## The checks before the proof -/

/-- Sorted keys from the start on, with no empty value, reduce the check to its last step. -/
theorem verifyRange_eq (hash : ByteArray → Hash32) (root start : Hash32)
    (entries : List (Hash32 × ByteArray)) (proof : List ByteArray)
    (hsorted : strictlyIncreasing (entries.map fun entry =>
      bytesToNibbleList ⟨entry.1.toArray⟩) = true)
    (hstart : ∀ entry ∈ entries,
      bytesToNibbleList ⟨start.toArray⟩ ≤ bytesToNibbleList ⟨entry.1.toArray⟩)
    (hfull : ∀ entry ∈ entries, entry.2.size ≠ 0) :
    verifyRange hash root start entries proof =
      if proof.isEmpty then
        match Trie.root hash ⟨false, entries.map fun (key, value) => (⟨key.toArray⟩, value)⟩ with
        | .ok built => if built = root then .ok false else .error .mismatch
        | .error (.rlp error) => .error (.rlp error)
        | .error .emptyValue => .error .emptyValue
      else
        checkSubtree hash (proof.map fun encoded => (hash encoded, encoded))
          (bytesToNibbleList ⟨start.toArray⟩)
          ((entries.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)).getLast?.map
            Prod.fst)
          ((bytesToNibbleList ⟨start.toArray⟩).length + 2) (.bytes ⟨root.toArray⟩) []
          (entries.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)) := by
  have hbefore : ((entries.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)).any
      fun x => decide (x.fst < bytesToNibbleList ⟨start.toArray⟩)) = false := by
    simp only [List.any_map, List.any_eq_false, Function.comp_apply, decide_eq_true_eq]
    exact fun entry hmem => List.not_lt.mpr (hstart entry hmem)
  have hzero : ((entries.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)).any
      fun x => decide (x.snd.size = 0)) = false := by
    simp only [List.any_map, List.any_eq_false, Function.comp_apply, decide_eq_true_eq]
    exact hfull
  unfold verifyRange
  have hsorted' : strictlyIncreasing ((entries.map fun entry =>
      (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)).map Prod.fst) = true := by
    rwa [List.map_map]
  simp only [hsorted', hbefore, hzero, Bool.false_eq_true, ↓reduceIte]
  rfl

end EthLib.Execution.Trie
