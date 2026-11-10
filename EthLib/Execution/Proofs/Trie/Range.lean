module

public import EthLib.Execution.Trie.Range
public import EthLib.Execution.Proofs.Trie.Proof

/-!
# Proofs: the range check of a trie

Two errors of the range check with one code come from one constructor.

Every code is at least 201, and differs from every code of a trie or proof error.

So one Python class carries all three.

Paths in strictly increasing order are distinct, and each is below every later path.

A subtree before the range lies wholly below its first end, and one after it wholly above its last.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base

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

/-- Paths in strictly increasing order are each below every later path. -/
theorem pairwise_of_strictlyIncreasing :
    (keys : List (List Nibble)) → strictlyIncreasing keys = true → keys.Pairwise (· < ·)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [strictlyIncreasing, List.tail_cons, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true, decide_eq_true_eq] at h
    have hrest := pairwise_of_strictlyIncreasing (b :: rest) h.2
    refine .cons ?_ hrest
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact List.lt_trans h.1 (List.rel_of_pairwise_cons hrest hx)

/-- Paths in strictly increasing order have no repeat. -/
theorem nodup_of_strictlyIncreasing {keys : List (List Nibble)}
    (h : strictlyIncreasing keys = true) : keys.Nodup :=
  (pairwise_of_strictlyIncreasing keys h).imp fun {a b} (hlt : a < b) (heq : a = b) =>
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

/-- Hash keys whose paths are in strictly increasing order are distinct byte strings. -/
theorem nodup_toArray_of_strictlyIncreasing {data : List (Hash32 × ByteArray)}
    (h : strictlyIncreasing (data.map fun entry => bytesToNibbleList ⟨entry.1.toArray⟩) = true) :
    ((data.map fun entry => ((⟨entry.1.toArray⟩ : ByteArray), entry.2)).map Prod.fst).Nodup := by
  have hpaths := nodup_of_strictlyIncreasing h
  rw [show (data.map fun entry => bytesToNibbleList ⟨entry.1.toArray⟩) =
      ((data.map fun entry => ((⟨entry.1.toArray⟩ : ByteArray), entry.2)).map Prod.fst).map
        bytesToNibbleList by simp [List.map_map, Function.comp_def]] at hpaths
  exact nodup_of_map bytesToNibbleList hpaths

end EthLib.Execution.Trie
