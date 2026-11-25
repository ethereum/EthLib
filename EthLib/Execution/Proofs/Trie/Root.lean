module

public import EthLib.Base.Proofs.ExceptT
public import EthLib.Execution.Trie.Root
import EthLib.Base.Proofs.CodeInjective
import EthLib.Base.Proofs.List
import Std.Data.TreeMap.Lemmas

/-!
# Proofs: `Trie.Root`

The theorems cover the budget of the node composition and the root of each map.

They also say which map setting pairs in order gives.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## The plain-hash instances

The definitions take a hash that may answer in a monad.

With a plain hash they run in the identity monad, and each step reads as a plain computation.
-/

/-- Holding a node, with a plain hash. -/
theorem encodeInternalNode_eq (hash : ByteArray → Hash32) (node : Option InternalNode) :
    encodeInternalNode hash node = do
      let encoded ← encode (unencoded node)
      if encoded.size < 32 then
        return unencoded node
      else
        return .bytes ⟨(hash encoded).toArray⟩ := by
  unfold encodeInternalNode encodeInternalNodeM
  cases encode (unencoded node) <;> rfl

/-- The vector map in the identity monad with errors is the vector map with errors. -/
theorem mapMVector_run {α β ε : Type} (f : α → Except ε β) :
    (xs : List α) → (mapMVector (m := ExceptT ε Id) f xs) = mapMVector f xs
  | [] => rfl
  | x :: rest => by
    have ih := mapMVector_run f rest
    simp only [mapMVector] at *
    rw [exceptT_id_bind, ih]
    congr 1
    funext y
    generalize mapMVector f rest = r
    cases r <;> rfl

/-- No key gives no node. -/
theorem patricializeStep_nil (hash : ByteArray → Hash32)
    (recurse : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode))
    (level : Nat) : patricializeStep hash recurse [] level = .ok none := rfl

/-- One key gives a leaf with the rest of its path. -/
theorem patricializeStep_singleton (hash : ByteArray → Hash32)
    (recurse : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode))
    (key : List Nibble) (value : ByteArray) (level : Nat) :
    patricializeStep hash recurse [(key, value)] level
      = .ok (some (.leaf (key.drop level) value)) :=
  rfl

/-- Two keys or more give an extension over their shared run, or else a branch. -/
theorem patricializeStep_cons_cons (hash : ByteArray → Hash32)
    (recurse : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode))
    (first second : List Nibble × ByteArray) (rest : List (List Nibble × ByteArray)) (level : Nat) :
    patricializeStep hash recurse (first :: second :: rest) level = (do
      let obj := first :: second :: rest
      let substring := first.1.drop level
      let prefixLength :=
        obj.foldl
          (fun length (key, _) => min length (commonPrefixLength substring (key.drop level)))
          substring.length
      if 0 < prefixLength then
        let subnode ← encodeInternalNode hash (← recurse obj (level + prefixLength))
        return some (.extension (substring.take prefixLength) subnode)
      else
        let value :=
          obj.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value)
            .empty
        let subnodes ← mapMVector (fun nibble => do
            encodeInternalNode hash
              (← recurse (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1)))
          (List.finRange 16)
        return some (.branch (subnodes.cast (by simp)) value) : Except RlpError _) := by
  obtain ⟨key, value⟩ := first
  simp only [patricializeStep, patricializeStepM, ExceptT.run, exceptT_id_bind, exceptT_id_pure,
    mapMVector_run, except_bind_eq]
  split <;> rfl

/-- A budget of zero makes every nested call give no node. -/
theorem patricializeAux_zero (hash : ByteArray → Hash32) (obj : List (List Nibble × ByteArray))
    (level : Nat) :
    patricializeAux hash 0 obj level = patricializeStep hash (fun _ _ => .ok none) obj level :=
  rfl

/-- One more unit of budget makes each nested call with the budget left. -/
theorem patricializeAux_add_one (hash : ByteArray → Hash32) (fuel : Nat)
    (obj : List (List Nibble × ByteArray)) (level : Nat) :
    patricializeAux hash (fuel + 1) obj level
      = patricializeStep hash (patricializeAux hash fuel) obj level :=
  rfl

/-- The node composition starts with a budget of one more than the longest path. -/
theorem patricialize_eq (hash : ByteArray → Hash32) (obj : List (List Nibble × ByteArray))
    (level : Nat) :
    patricialize hash obj level = patricializeAux hash (longestPath obj + 1) obj level :=
  rfl

/-- The path of a key, with a plain hash. -/
theorem keyPath_eq (hash : ByteArray → Hash32) (secured : Bool) (key : ByteArray) :
    keyPath hash secured key
      = bytesToNibbleList (if secured then ⟨(hash key).toArray⟩ else key) := by
  cases secured <;> rfl

/-- Preparing the data, with a plain hash. -/
theorem prepareData_eq (hash : ByteArray → Hash32) (data : List (ByteArray × ByteArray))
    (secured : Bool) :
    prepareData hash data secured = data.mapM fun (preimage, value) =>
      if value.size = 0 then .error .emptyValue
      else .ok (keyPath hash secured preimage, value) := by
  induction data with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨preimage, value⟩ := entry
    simp only [prepareData, prepareDataM, List.mapM_cons, ExceptT.run] at ih ⊢
    rw [← ih]
    by_cases hvalue : value.size = 0
    · simp only [hvalue, ↓reduceIte]
      rfl
    · simp only [hvalue, ↓reduceIte, exceptT_id_bind, exceptT_id_lift, exceptT_id_pure,
        except_bind_eq]
      rfl

/-- The root, with a plain hash. -/
theorem root_eq (hash : ByteArray → Hash32) (trie : Trie) :
    root hash trie = do
      let obj ← prepareData hash trie.data trie.secured
      let rootNode ← (patricialize hash obj 0).mapError .rlp
      let encoded ← (encode (unencoded rootNode)).mapError .rlp
      return hash encoded := by
  simp only [root, rootM, ExceptT.run, exceptT_id_bind, exceptT_id_adapt, exceptT_id_monadLift,
    exceptT_id_lift, except_bind_eq]
  rfl

/-! ## The longest path -/

/-- Folding from any start value gives the larger of the start and the longest path. -/
theorem foldl_longestPath (obj : List (List Nibble × ByteArray)) (start : Nat) :
    obj.foldl (fun longest (key, _) => max longest key.length) start = max start (longestPath obj) := by
  induction obj generalizing start with
  | nil => simp [longestPath]
  | cons entry rest ih =>
    -- One step of the fold on both sides, then the induction hypothesis twice.
    simp only [longestPath, List.foldl_cons] at ih ⊢
    rw [ih, ih (max 0 entry.1.length)]
    omega

/-- The longest path is at most `n` exactly when every path is. -/
theorem longestPath_le_iff (obj : List (List Nibble × ByteArray)) (n : Nat) :
    longestPath obj ≤ n ↔ ∀ entry ∈ obj, entry.1.length ≤ n := by
  induction obj with
  | nil => simp [longestPath]
  | cons entry rest ih =>
    have h := foldl_longestPath rest (max 0 entry.1.length)
    simp only [longestPath, List.foldl_cons] at h ih ⊢
    rw [h, List.forall_mem_cons, ← ih]
    omega

/-- Keeping some of the keys keeps the longest path or shortens it. -/
theorem longestPath_filter_le (obj : List (List Nibble × ByteArray)) (p : List Nibble × ByteArray → Bool) :
    longestPath (obj.filter p) ≤ longestPath obj := by
  rw [longestPath_le_iff]
  intro entry h
  exact (longestPath_le_iff obj _).mp (Nat.le_refl _) entry (List.mem_filter.mp h).1

/-! ## One step of `patricialize` -/

/-- `mapMVector` gives the same result for two functions that agree on every entry. -/
theorem mapMVector_congr {α β ε : Type} {f g : α → Except ε β} :
    (xs : List α) → (∀ x ∈ xs, f x = g x) → mapMVector f xs = mapMVector g xs
  | [], _ => rfl
  | x :: rest, h => by
    simp only [mapMVector]
    rw [h x List.mem_cons_self, mapMVector_congr rest fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- A fold that takes minimums ends at most at its start. -/
theorem foldl_min_le (obj : List (List Nibble × ByteArray)) (f : List Nibble × ByteArray → Nat) (start : Nat) :
    obj.foldl (fun length entry => min length (f entry)) start ≤ start := by
  induction obj generalizing start with
  | nil => exact Nat.le_refl _
  | cons entry rest ih => exact Nat.le_trans (ih _) (Nat.min_le_left _ _)

/-- One step gives the same node for two ways of making the nested calls, when they agree on the calls the step makes.

- An extension calls on the same keys, at a level above `level` and at most the longest path.
- A branch calls on the keys of each next nibble, one level down. -/
theorem patricializeStep_congr (hash : ByteArray → Hash32)
    {recurse₁ recurse₂ : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode)}
    {obj : List (List Nibble × ByteArray)} {level : Nat}
    (hextension : ∀ deeper, level < deeper → deeper ≤ longestPath obj → recurse₁ obj deeper = recurse₂ obj deeper)
    (hbranch : ∀ nibble : Nibble,
      recurse₁ (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1)
        = recurse₂ (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1)) :
    patricializeStep hash recurse₁ obj level = patricializeStep hash recurse₂ obj level := by
  match obj, hextension, hbranch with
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | (arbitraryKey, arbitraryValue) :: second :: rest, hextension, hbranch =>
    simp only [patricializeStep_cons_cons]
    -- The run is at most the rest of the first path, so an extension lands at most at its end.
    have hrun := foldl_min_le ((arbitraryKey, arbitraryValue) :: second :: rest)
      (fun entry => commonPrefixLength (arbitraryKey.drop level) (entry.1.drop level)) (arbitraryKey.drop level).length
    have hdrop : (arbitraryKey.drop level).length = arbitraryKey.length - level := List.length_drop
    have hfirst : arbitraryKey.length ≤ longestPath ((arbitraryKey, arbitraryValue) :: second :: rest) :=
      (longestPath_le_iff ((arbitraryKey, arbitraryValue) :: second :: rest) _).mp (Nat.le_refl _)
        (arbitraryKey, arbitraryValue) List.mem_cons_self
    split
    · rename_i hpositive
      rw [hextension _ (by omega) (by omega)]
    · -- Each child is the filter of one nibble, on which the two agree.
      congr 1
      apply mapMVector_congr
      intro nibble _
      rw [hbranch nibble]

/-- With fewer than two keys, a step makes no nested call. -/
theorem patricializeStep_of_length_lt (hash : ByteArray → Hash32)
    (recurse₁ recurse₂ : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode))
    {obj : List (List Nibble × ByteArray)} (hlength : obj.length < 2) (level : Nat) :
    patricializeStep hash recurse₁ obj level = patricializeStep hash recurse₂ obj level := by
  match obj, hlength with
  | [], _ => rfl
  | [_], _ => rfl

/-- A call on no key gives no node, whatever the budget. -/
theorem patricializeAux_nil (hash : ByteArray → Hash32) (fuel level : Nat) :
    patricializeAux hash fuel [] level = .ok none := by
  cases fuel <;> rfl

/-! ## The budget never runs out -/

/-- A budget fits a call when the call has fewer than two keys, or every path ends before `level + fuel`. -/
def Fits (obj : List (List Nibble × ByteArray)) (level fuel : Nat) : Prop :=
  obj.length < 2 ∨ longestPath obj < level + fuel

/-- One more unit of a budget that fits changes nothing. -/
theorem patricializeAux_succ (hash : ByteArray → Hash32) :
    (fuel : Nat) → (obj : List (List Nibble × ByteArray)) → (level : Nat) → Fits obj level fuel →
      patricializeAux hash (fuel + 1) obj level = patricializeAux hash fuel obj level
  | fuel, obj, level, .inl hlength => by
    cases fuel <;> exact patricializeStep_of_length_lt hash _ _ hlength level
  | 0, obj, level, .inr hlongest => by
    -- Every path ends before `level`, so no extension is made and every child has no key.
    apply patricializeStep_congr
    · intro deeper hdeeper hle
      omega
    · intro nibble
      have hempty : (obj.filter fun (key, _) => key[level]? = some nibble) = [] := by
        rw [List.filter_eq_nil_iff]
        intro entry hmem
        have := (longestPath_le_iff obj _).mp (Nat.le_refl _) entry hmem
        simp [List.getElem?_eq_none (show entry.1.length ≤ level by omega)]
      rw [hempty]
      exact patricializeAux_nil hash 0 (level + 1)
  | fuel + 1, obj, level, .inr hlongest => by
    -- Each nested call fits the smaller budget, so the induction hypothesis applies to it.
    apply patricializeStep_congr
    · intro deeper hdeeper hle
      exact patricializeAux_succ hash fuel obj deeper (.inr (by omega))
    · intro nibble
      exact patricializeAux_succ hash fuel _ (level + 1)
        (.inr (Nat.lt_of_le_of_lt (longestPath_filter_le obj _) (by omega)))

/-- Any larger budget than one that fits changes nothing. -/
theorem patricializeAux_add (hash : ByteArray → Hash32) {obj : List (List Nibble × ByteArray)} {level fuel : Nat}
    (hfits : Fits obj level fuel) (extra : Nat) :
    patricializeAux hash (fuel + extra) obj level = patricializeAux hash fuel obj level := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    rw [← Nat.add_assoc, patricializeAux_succ hash _ obj level (hfits.imp_right fun h => by omega), ih]

/-- Every budget that reaches past the longest path gives the node of `patricialize`. -/
theorem patricializeAux_eq_patricialize (hash : ByteArray → Hash32) {obj : List (List Nibble × ByteArray)}
    {level fuel : Nat} (hfuel : longestPath obj < level + fuel) :
    patricializeAux hash fuel obj level = patricialize hash obj level := by
  have hfits : Fits obj level fuel := .inr hfuel
  have hdefault : Fits obj level (longestPath obj + 1) := .inr (by omega)
  -- Both budgets give the node of their sum.
  rw [patricialize_eq, ← patricializeAux_add hash hfits (longestPath obj + 1),
    ← patricializeAux_add hash hdefault fuel, Nat.add_comm]

/-! ## The root -/

/-- The empty map's root is the hash of `0x80`, the encoding of the empty byte string, secured or not. -/
theorem root_empty (hash : ByteArray → Hash32) (secured : Bool) :
    root hash ⟨secured, []⟩ = .ok (hash ⟨#[0x80]⟩) := rfl

/-- A map with an empty value has no root. -/
theorem prepareData_emptyValue (hash : ByteArray → Hash32) (secured : Bool) :
    (data : List (ByteArray × ByteArray)) → (∃ entry ∈ data, entry.2.size = 0) →
      prepareData hash data secured = .error .emptyValue
  | (key, value) :: rest, ⟨entry, hmem, hempty⟩ => by
    by_cases hvalue : value.size = 0
    · simp only [prepareData_eq, List.mapM_cons, hvalue, ↓reduceIte]
      rfl
    · -- The first value is not empty, so the empty one is further on.
      have hrest : ∃ entry ∈ rest, entry.2.size = 0 := by
        rcases List.mem_cons.mp hmem with rfl | h
        · exact absurd hempty hvalue
        · exact ⟨entry, h, hempty⟩
      have hrestError := prepareData_emptyValue hash secured rest hrest
      simp only [prepareData_eq] at hrestError
      simp only [prepareData_eq, List.mapM_cons, hvalue, ↓reduceIte, hrestError]
      rfl

/-- A map with an empty value has no root. -/
theorem root_emptyValue (hash : ByteArray → Hash32) (trie : Trie) (h : ∃ entry ∈ trie.data, entry.2.size = 0) :
    root hash trie = .error .emptyValue := by
  simp only [root_eq, prepareData_emptyValue hash trie.secured trie.data h]
  rfl

/-- With no empty value, each key becomes its path, after hashing in a secured trie, and keeps its value and its place. -/
theorem prepareData_ok (hash : ByteArray → Hash32) (secured : Bool) :
    (data : List (ByteArray × ByteArray)) → (∀ entry ∈ data, entry.2.size ≠ 0) →
      prepareData hash data secured
        = .ok (data.map fun (preimage, value) => (keyPath hash secured preimage, value))
  | [], _ => rfl
  | (key, value) :: rest, h => by
    have hrest := prepareData_ok hash secured rest fun entry hmem => h entry (List.mem_cons_of_mem _ hmem)
    simp only [prepareData_eq] at hrest
    simp only [prepareData_eq, List.mapM_cons, h (key, value) List.mem_cons_self, ↓reduceIte, hrest]
    rfl

/-! ## Getting and setting a key -/

/-- The trie compares two keys by their bytes, so it finds them equal exactly when they are. -/
theorem sameBytes_iff (a b : ByteArray) : sameBytes a b = true ↔ a = b := by
  cases a; cases b
  simp [sameBytes]

/-- The keys of a trie that sets pairs in order are distinct, as Yellow Paper Appendix D assumes.
-/
theorem nodup_keys_setPairs (pairs : List (ByteArray × ByteArray)) :
    ((setPairs pairs).map Prod.fst).Nodup := by
  -- The places of a numbered list increase along it.
  have places : ∀ (l : List ByteArray) (k : Nat),
      (l.zipIdx k).Pairwise fun a b => a.2 < b.2 := by
    intro l
    induction l with
    | nil => intro k; simp
    | cons x l ih =>
      intro k
      refine List.pairwise_cons.2 ⟨fun b hb => ?_, ih (k + 1)⟩
      exact Nat.lt_of_succ_le (List.le_snd_of_mem_zipIdx hb)
  -- An entry kept at a place is the key that the table puts there, so one key has one place.
  simp only [setPairs, logEntries, List.map_filterMap, List.Nodup]
  rw [List.pairwise_filterMap]
  refine (places _ 0).imp ?_
  rintro ⟨k, i⟩ ⟨k', i'⟩ hlt b hb b' hb' heq
  subst heq
  split at hb <;> split at hb' <;> simp_all

/-- Each key of the table has its place in the log, holding that key. -/
private def PlacesKeys (st : Array ByteArray × Std.TreeMap ByteArray (Nat × ByteArray)) : Prop :=
  ∀ k p v, st.2[k]? = some (p, v) → ∃ h : p < st.1.size, st.1[p] = k

/-- One step keeps each key of the table at a place of the log that holds it. -/
private theorem placesKeys_step {st : Array ByteArray × Std.TreeMap ByteArray (Nat × ByteArray)}
    (pair : ByteArray × ByteArray) (hst : PlacesKeys st) : PlacesKeys (setPairStep st pair) := by
  obtain ⟨log, table⟩ := st
  obtain ⟨key, value⟩ := pair
  intro k p v h
  by_cases h0 : value.size = 0
  · -- An empty value only removes a key.
    simp only [setPairStep, h0, ↓reduceIte, Std.TreeMap.getElem?_erase] at h ⊢
    split at h
    · cases h
    · exact hst _ _ _ h
  · cases hk : table[key]? with
    | some e =>
      obtain ⟨place, old⟩ := e
      simp only [setPairStep, h0, ↓reduceIte, hk] at h ⊢
      obtain ⟨hp, hlog⟩ := hst _ _ _ hk
      rw [Std.TreeMap.getElem?_insert] at h
      split at h
      · cases h
        rename_i hkey
        rw [← Std.compare_eq_iff_eq.mp hkey]
        exact ⟨hp, hlog⟩
      · exact hst _ _ _ h
    | none =>
      simp only [setPairStep, h0, ↓reduceIte, hk] at h ⊢
      rw [Std.TreeMap.getElem?_insert] at h
      split at h
      · cases h
        rename_i hkey
        rw [← Std.compare_eq_iff_eq.mp hkey]
        simp
      · obtain ⟨hp, hlog⟩ := hst _ _ _ h
        have hp' : p < log.size := hp
        refine ⟨by simp only [Array.size_push]; omega, ?_⟩
        simp [Array.getElem_push, hp, hlog]

/-- One step sets the value of its key in the table, where an empty value removes it. -/
private theorem value_step (st : Array ByteArray × Std.TreeMap ByteArray (Nat × ByteArray))
    (key value k : ByteArray) :
    ((setPairStep st (key, value)).2[k]?).map Prod.snd =
      if key = k then (some value).filter (fun v => decide (v.size ≠ 0))
      else (st.2[k]?).map Prod.snd := by
  obtain ⟨log, table⟩ := st
  by_cases h0 : value.size = 0
  · simp only [setPairStep, h0, ↓reduceIte, Std.TreeMap.getElem?_erase]
    by_cases hk : key = k
    · subst hk
      simp only [Option.filter_some, h0, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, Std.compare_self, Option.map_none]
    · simp [hk]
  · cases hk : table[key]? with
    | some e =>
      obtain ⟨place, old⟩ := e
      simp only [setPairStep, h0, ↓reduceIte, hk, Std.TreeMap.getElem?_insert]
      by_cases hkk : key = k
      · subst hkk
        simp only [Option.filter_some, h0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
          Std.compare_self, Option.map_some]
      · simp [hkk]
    | none =>
      simp only [setPairStep, h0, ↓reduceIte, hk, Std.TreeMap.getElem?_insert]
      by_cases hkk : key = k
      · subst hkk
        simp only [Option.filter_some, h0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
          Std.compare_self, Option.map_some]
      · simp [hkk]

/-- The fold of the steps keeps the places, and its table holds the last value of each key. -/
private theorem foldl_setPairStep (pairs : List (ByteArray × ByteArray)) :
    PlacesKeys (pairs.foldl setPairStep (#[], ∅)) ∧
      ∀ k, ((pairs.foldl setPairStep (#[], ∅)).2[k]?).map Prod.snd =
        ((pairs.reverse.find? fun pair => pair.1 == k).map Prod.snd).filter
          (fun v => decide (v.size ≠ 0)) := by
  -- Induct on the reversed list, so that the last pair is the head.
  suffices h : ∀ l : List (ByteArray × ByteArray),
      PlacesKeys (l.reverse.foldl setPairStep (#[], ∅)) ∧
        ∀ k, ((l.reverse.foldl setPairStep (#[], ∅)).2[k]?).map Prod.snd =
          ((l.find? fun pair => pair.1 == k).map Prod.snd).filter
            (fun v => decide (v.size ≠ 0)) by
    simpa using h pairs.reverse
  intro l
  induction l with
  | nil => exact ⟨fun k p v h => by simp at h, fun k => by simp⟩
  | cons x l ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨placesKeys_step x ih1, fun k => ?_⟩
    obtain ⟨key, value⟩ := x
    rw [value_step, List.find?_cons]
    by_cases hkk : key = k
    · subst hkk; simp [Option.filter_some]
    · have hf : (key == k) = false := by simpa using hkk
      simp only [hkk, ↓reduceIte]
      rw [ih2]
      simp only [hf]

/-- An entry of the log is a key of the table, with the value that the table gives it. -/
private theorem mem_logEntries {log : Array ByteArray}
    {table : Std.TreeMap ByteArray (Nat × ByteArray)} {e : ByteArray × ByteArray}
    (he : e ∈ logEntries log table) : ∃ p, table[e.1]? = some (p, e.2) := by
  obtain ⟨k, v⟩ := e
  obtain ⟨⟨k', i⟩, -, hk⟩ := List.mem_filterMap.1 he
  simp only at hk
  split at hk
  · rename_i p v' hs
    split at hk
    · cases hk; exact ⟨p, hs⟩
    · cases hk
  · cases hk

/-- The entries of the log are the table's pairs, once its places hold their keys. -/
private theorem trieGet_logEntries (log : Array ByteArray)
    (table : Std.TreeMap ByteArray (Nat × ByteArray))
    (hb : PlacesKeys (log, table)) (key : ByteArray) :
    ((logEntries log table).find? fun (k, _) => sameBytes k key).map Prod.snd =
      (table[key]?).map Prod.snd := by
  -- An entry of the log is a key of the table with the value that the table gives it.
  have hmem := fun e => @mem_logEntries log table e
  cases hk : table[key]? with
  | none =>
    -- No entry has the key.
    have : ((logEntries log table).find? fun (k, _) => sameBytes k key) = none := by
      rw [List.find?_eq_none]
      rintro ⟨k, v⟩ he hsame
      have := sameBytes_iff _ _ |>.1 hsame
      obtain ⟨_, h2⟩ := hmem _ he
      simp only at h2 this
      rw [this, hk] at h2
      cases h2
    rw [this]; rfl
  | some e =>
    obtain ⟨p, v⟩ := e
    obtain ⟨hp, hlog⟩ := hb _ _ _ hk
    -- The key has an entry, at its place.
    have hin : (key, v) ∈ logEntries log table := by
      refine List.mem_filterMap.2 ⟨(key, p), ?_, by simp [hk]⟩
      rw [List.mem_zipIdx_iff_getElem?]
      simp [hp, hlog]
    have hsome : ((logEntries log table).find? fun (k, _) => sameBytes k key).isSome := by
      rw [List.find?_isSome]
      exact ⟨(key, v), hin, by simp [sameBytes_iff]⟩
    obtain ⟨⟨k, v'⟩, hfind⟩ := Option.isSome_iff_exists.1 hsome
    have hmem' := List.mem_of_find?_eq_some hfind
    have hsame := List.find?_some hfind
    obtain ⟨_, h2⟩ := hmem _ hmem'
    have h3 := sameBytes_iff _ _ |>.1 hsame
    simp only at h2 h3
    rw [h3, hk] at h2
    cases h2
    rw [hfind]; rfl

/-- In a trie that sets pairs in order, a key has the value of its last pair.

A key that no pair sets has the empty value, as a key whose last value is empty. -/
theorem trieGet_setPairs (secured : Bool) (pairs : List (ByteArray × ByteArray))
    (key : ByteArray) :
    trieGet ⟨secured, setPairs pairs⟩ key =
      ((pairs.reverse.find? fun pair => pair.1 == key).map Prod.snd).getD .empty := by
  obtain ⟨h1, h2⟩ := foldl_setPairStep pairs
  unfold setPairs trieGet
  -- Read the state of the fold as a log and a table.
  generalize hst : pairs.foldl setPairStep (#[], ∅) = st at h1 h2
  obtain ⟨log, table⟩ := st
  simp only
  rw [trieGet_logEntries log table h1 key]
  have h3 := h2 key
  simp only at h3
  rw [h3]
  -- A last pair with an empty value gives the empty value, as a removed key does.
  cases hf : (pairs.reverse.find? fun pair => pair.1 == key) with
  | none => rfl
  | some pair =>
    simp only [Option.map_some, Option.filter_some]
    by_cases h0 : pair.2.size = 0
    · have : pair.2 = .empty := by simpa using h0
      simp [this]
    · simp [h0]

/-! ## Error codes -/


/-- A trie that sets pairs in order holds no empty value, which its root would reject. -/
theorem size_ne_zero_of_mem_setPairs {pairs : List (ByteArray × ByteArray)}
    {entry : ByteArray × ByteArray} (h : entry ∈ setPairs pairs) : entry.2.size ≠ 0 := by
  obtain ⟨-, hvalues⟩ := foldl_setPairStep pairs
  unfold setPairs at h
  generalize pairs.foldl setPairStep (#[], ∅) = st at h hvalues
  obtain ⟨log, table⟩ := st
  obtain ⟨p, hp⟩ := mem_logEntries h
  -- The table keeps only the values that pass the test of a nonzero size.
  have hv := hvalues entry.1
  simp only [hp, Option.map_some] at hv
  intro h0
  rcases hf : (pairs.reverse.find? fun pair => pair.1 == entry.1) with _ | pair <;>
    simp_all [Option.filter_some]

/-- Two errors with one code come from one constructor. -/
theorem TrieError.code_injective (e₁ e₂ : TrieError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective TrieError.code

end EthLib.Execution.Trie
