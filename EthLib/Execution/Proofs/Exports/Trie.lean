module

public import EthLib.Execution.Exports.Trie
import all EthLib.Execution.Exports.Trie
import all EthLib.Base.Exports.Result
import EthLib.Base.Proofs.List
import EthLib.Execution.Proofs.Trie.Root
import Std.Data.HashMap.Lemmas

/-!
# Proofs: `Execution.Exports.Trie`

The root export returns the root of the trie that sets the decoded pairs in order.

So the binding and soundness theorems for such tries apply to its output.

-/

@[expose] public section

namespace EthLib.Execution.Trie.Exports

open EthLib.Base
open EthLib.Serialization.Rlp (Item)

/-- One step of the table sets the key as the trie does, and keeps each place on its key. -/
private theorem step_setPairs {secured : Bool} {data : List (ByteArray × ByteArray)}
    {log : Array ByteArray} {table : Std.HashMap ByteArray (Nat × ByteArray)}
    (key value : ByteArray)
    (ha : data = logEntries log table)
    (hb : ∀ k p v, table[k]? = some (p, v) → ∃ h : p < log.size, log[p] = k) :
    let st := setPairStep (log, table) (key, value)
    (trieSet ⟨secured, data⟩ key value).data = logEntries st.1 st.2 ∧
      ∀ k p v, st.2[k]? = some (p, v) → ∃ h : p < st.1.size, st.1[p] = k := by
  intro st
  by_cases h0 : value.size = 0
  -- An empty value drops the key from the trie and from the table.
  · subst ha
    simp only [st, setPairStep, logEntries, h0, ↓reduceIte, trieSet]
    refine ⟨?_, fun k p v h => ?_⟩
    · rw [List.filter_filterMap]
      refine filterMap_congr ?_
      rintro ⟨k, i⟩ -
      by_cases hk : k = key
      · subst hk
        simp
        split <;> simp [sameBytes_iff]
      · simp [Std.HashMap.getElem?_erase, Ne.symm hk]
        split <;> (try split) <;> simp [Option.filter, sameBytes_iff, hk]
    · simp only [Std.HashMap.getElem?_erase] at h
      split at h
      · cases h
      · exact hb _ _ _ h
  · cases hk : table[key]? with
    -- A key in the table is in the trie, at its place, and takes the new value.
    | some e =>
      obtain ⟨place, old⟩ := e
      simp only [st, setPairStep, h0, ↓reduceIte, hk, trieSet]
      obtain ⟨hp, hlog⟩ := hb _ _ _ hk
      split
      · subst ha
        simp only [logEntries]
        refine ⟨?_, fun k p v h => ?_⟩
        · rw [List.map_filterMap]
          refine filterMap_congr ?_
          rintro ⟨k, i⟩ -
          by_cases hk' : k = key
          · subst hk'
            simp [hk]
            split <;> simp [sameBytes_iff]
          · simp [Std.HashMap.getElem?_insert, Ne.symm hk']
            split <;> (try split) <;> simp [sameBytes_iff, hk']
        · rw [Std.HashMap.getElem?_insert] at h
          split at h
          · cases h
            rename_i hkey
            rw [← eq_of_beq hkey]
            exact ⟨hp, hlog⟩
          · exact hb _ _ _ h
      · rename_i hn
        subst ha
        simp only [logEntries] at hn
        refine absurd ?_ hn
        rw [List.any_eq_true]
        refine ⟨(key, old), List.mem_filterMap.2 ⟨(key, place), ?_, by simp [hk]⟩, ?_⟩
        · rw [List.mem_zipIdx_iff_getElem?]
          simp [hp, hlog]
        · simp [sameBytes_iff]
    -- A key not in the table is not in the trie, and goes last in both.
    | none =>
      simp only [st, setPairStep, h0, ↓reduceIte, hk, trieSet]
      split
      · rename_i hany
        subst ha
        simp only [logEntries] at hany
        exfalso
        rw [List.any_eq_true] at hany
        obtain ⟨⟨k, v⟩, hmem, hs⟩ := hany
        rw [sameBytes_iff] at hs
        subst hs
        obtain ⟨⟨k', i⟩, -, hf⟩ := List.mem_filterMap.1 hmem
        split at hf <;> simp_all
      · subst ha
        simp only [logEntries]
        refine ⟨?_, fun k p v h => ?_⟩
        · rw [Array.toList_push, List.zipIdx_append, List.filterMap_append]
          congr 1
          · refine filterMap_congr ?_
            rintro ⟨k, i⟩ hm
            have hi : i < log.size := by
              rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff] at hm
              obtain ⟨hlt, -⟩ := hm
              simpa using hlt
            by_cases hk' : k = key
            · subst hk'
              simp [hk, Nat.ne_of_gt hi]
            · simp [Std.HashMap.getElem?_insert, Ne.symm hk']
          · simp
        · rw [Std.HashMap.getElem?_insert] at h
          split at h
          · cases h
            rename_i hkey
            rw [← eq_of_beq hkey]
            simp
          · obtain ⟨hp, hl⟩ := hb _ _ _ h
            exact ⟨by simp; omega, by simp [Array.getElem_push_lt hp, hl]⟩

/-- Folding the table gives the same entries as setting the pairs one by one.

It holds from entries that the table lists, with each place pointing to its key in the log. -/
private theorem foldl_setPairs (secured : Bool) (pairs : List (ByteArray × ByteArray)) :
    ∀ (data : List (ByteArray × ByteArray))
      (st : Array ByteArray × Std.HashMap ByteArray (Nat × ByteArray)),
      data = logEntries st.1 st.2 →
      (∀ k p v, st.2[k]? = some (p, v) → ∃ h : p < st.1.size, st.1[p] = k) →
      let final := pairs.foldl setPairStep st
      pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured, data⟩ =
        ⟨secured, logEntries final.1 final.2⟩ := by
  induction pairs with
  | nil =>
    intro data st ha _
    simp [ha]
  | cons kv pairs ih =>
    intro data st ha hb
    obtain ⟨key, value⟩ := kv
    obtain ⟨log, table⟩ := st
    -- The first pair keeps both facts, so the rest of the fold follows.
    obtain ⟨h₁, h₂⟩ := step_setPairs (secured := secured) key value ha hb
    have h := ih _ _ h₁ h₂
    -- The trie after the first pair keeps its flag.
    have hs := secured_trieSet ⟨secured, data⟩ key value
    simp only [List.foldl_cons]
    generalize trieSet ⟨secured, data⟩ key value = t at hs h ⊢
    obtain ⟨s', d'⟩ := t
    simp only at hs h ⊢
    subst hs
    exact h

/-- Setting the pairs through the table leaves the trie that sets them one by one. -/
theorem setPairs_eq (secured : Bool) (pairs : List (ByteArray × ByteArray)) :
    pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured, []⟩ =
      ⟨secured, setPairs pairs⟩ :=
  foldl_setPairs secured pairs [] (#[], ∅) (by simp [logEntries]) (by intro k p v h; simp at h)

/-- With the pairs decoded, the export is the match on the root of their trie. -/
private theorem rootExport_eq {secured : UInt8} {input : ByteArray} {items : List Item}
    {pairs : List (ByteArray × ByteArray)}
    (hitems : readList input "pairs" = .ok items) (hpairs : items.mapM ofPairItem = .ok pairs) :
    rootExport secured input =
      match root Cryptography.Hash.Keccak.keccak256
          (pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured != 0, []⟩) with
      | .ok hash => return ⟨hash.toArray⟩
      | .error e => throw (e.code, s!"trie has no root: {repr e}") := by
  rw [setPairs_eq]
  simp only [rootExport, hitems, hpairs, bind, Except.bind]
  -- The conversion of an error writes the same code and the same message.
  split <;> simp [*, EthLib.Exports.toResult, Except.mapError, throw, throwThe,
    MonadExceptOf.throw]
  -- The context and the message join into the same text.
  refine ⟨rfl, ?_⟩
  rw [String.append_assoc]
  rfl

/-- A root that the export returns has 32 bytes. -/
theorem size_of_rootExport {secured : UInt8} {input out : ByteArray}
    (h : rootExport secured input = .ok out) : out.size = 32 := by
  unfold rootExport at h
  simp only [bind, Except.bind, EthLib.Exports.rejectArgument, EthLib.Exports.toResult,
    Except.mapError] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
        exact Vector.size_toArray _
      · cases h
    · cases h

/-- The root export returns the root of the trie that sets the decoded pairs in order.

The trie starts empty, and it hashes its keys when the flag is not 0. -/
theorem root_of_rootExport {secured : UInt8} {input out : ByteArray} {items : List Item}
    {pairs : List (ByteArray × ByteArray)}
    (hitems : readList input "pairs" = .ok items) (hpairs : items.mapM ofPairItem = .ok pairs)
    (h : rootExport secured input = .ok out) :
    root Cryptography.Hash.Keccak.keccak256
        (pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured != 0, []⟩) =
      .ok ⟨out.data, size_of_rootExport h⟩ := by
  rw [rootExport_eq hitems hpairs] at h
  split at h
  · rename_i hash hr
    cases h
    rw [hr]
  · cases h

/-- When that trie has a root, the root export returns it. -/
theorem rootExport_of_root {secured : UInt8} {input : ByteArray} {items : List Item}
    {pairs : List (ByteArray × ByteArray)} {hash : Hash32}
    (hitems : readList input "pairs" = .ok items) (hpairs : items.mapM ofPairItem = .ok pairs)
    (hroot : root Cryptography.Hash.Keccak.keccak256
        (pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured != 0, []⟩) =
      .ok hash) :
    rootExport secured input = .ok ⟨hash.toArray⟩ := by
  rw [rootExport_eq hitems hpairs, hroot]
  rfl

end EthLib.Execution.Trie.Exports
