module

public import EthLib.Base.Proofs.ExceptT
public import EthLib.Execution.Trie.Root

/-!
# Proofs: `Trie.Root`

- The budget of the node composition never runs out.
  Any budget above the longest path, counted from the level, gives the same node.
- The root of the empty map is the hash of `0x80`, secured or not.
- A map with an empty value has no root.
- The keys and values of every other map reach the composition unchanged, in order.
- A key that is set takes the new value, and every other key keeps its value.
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

/-- A key that was just set has the value it was set to. -/
theorem trieGet_trieSet_self (trie : Trie) (key value : ByteArray) :
    trieGet (trieSet trie key value) key = value := by
  unfold trieSet trieGet
  split
  · -- The key is removed, so it has the default, the empty value it was set to.
    rename_i hempty
    rw [List.find?_filter, List.find?_eq_none.mpr (by simp)]
    exact (ByteArray.size_eq_zero_iff.mp hempty).symm
  · split
    · -- The key is present, and every entry of it now holds the new value.
      rename_i hany
      simp only [List.find?_map, Function.comp_def, apply_ite Prod.fst, ite_self]
      cases hfind : trie.data.find? (fun entry => sameBytes entry.1 key) with
      | none => exact absurd (List.find?_isSome.mpr (List.any_eq_true.mp hany)) (by simp [hfind])
      | some entry =>
        have hkey : sameBytes entry.1 key = true :=
          List.find?_some (p := fun entry : ByteArray × ByteArray => sameBytes entry.1 key) hfind
        simp [hkey]
    · -- The key is absent, so its only entry is the new one at the end.
      rename_i hany
      rw [List.find?_append, List.find?_eq_none.mpr fun entry hmem hsame =>
        hany (List.any_eq_true.mpr ⟨entry, hmem, hsame⟩)]
      simp [(sameBytes_iff key key).mpr rfl]

/-- Setting a key leaves the value of every other key unchanged. -/
theorem trieGet_trieSet_of_ne (trie : Trie) {key other : ByteArray} (value : ByteArray)
    (h : other ≠ key) : trieGet (trieSet trie key value) other = trieGet trie other := by
  unfold trieSet trieGet
  -- An entry of the other key is not an entry of the key that is set.
  have hne : ∀ k, sameBytes k other = true → sameBytes k key = false := by
    intro k hother
    rw [(sameBytes_iff k other).mp hother]
    exact Bool.eq_false_iff.mpr fun hkey => h ((sameBytes_iff other key).mp hkey)
  split
  · -- Removing the key keeps every entry of the other key.
    rw [List.find?_filter]
    congr 3
    funext entry
    cases hother : sameBytes entry.1 other <;> simp [hother, hne]
  · split
    · -- The first entry of the other key keeps its value.
      simp only [List.find?_map, Function.comp_def, apply_ite Prod.fst, ite_self]
      cases hfind : trie.data.find? (fun entry => sameBytes entry.1 other) with
      | none => rfl
      | some entry =>
        have hother : sameBytes entry.1 other = true :=
          List.find?_some (p := fun entry : ByteArray × ByteArray => sameBytes entry.1 other) hfind
        simp [hne entry.1 hother]
    · -- The new entry at the end is not an entry of the other key.
      have hkey : sameBytes key other = false :=
        Bool.eq_false_iff.mpr fun hother => h ((sameBytes_iff key other).mp hother).symm
      simp [List.find?_append, hkey]

/-- Setting or removing a key keeps the keys distinct, as Yellow Paper Appendix D assumes. -/
theorem nodup_keys_trieSet {trie : Trie} (hkeys : (trie.data.map Prod.fst).Nodup)
    (key value : ByteArray) : ((trieSet trie key value).data.map Prod.fst).Nodup := by
  unfold trieSet
  split
  · -- Removing entries takes a sublist of the distinct keys.
    exact (List.Sublist.map Prod.fst List.filter_sublist).nodup hkeys
  · split
    · -- Replacing a value leaves every key in its place.
      have unchanged : (trie.data.map (fun (k, v) =>
          if sameBytes k key then (k, value) else (k, v))).map Prod.fst
          = trie.data.map Prod.fst := by
        simp only [List.map_map, Function.comp_def, apply_ite Prod.fst, ite_self]
      rw [unchanged]
      exact hkeys
    · -- A new key is absent from the old keys, so appending it preserves uniqueness.
      rename_i habsent
      simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
      refine ⟨hkeys, by simp, ?_⟩
      intro old hold new hnew heq
      simp only [List.mem_singleton] at hnew
      obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hold
      exact habsent (List.any_eq_true.mpr
        ⟨entry, hentry, (sameBytes_iff _ _).mpr (hkey.trans (heq.trans hnew))⟩)

/-- Setting any list of pairs from an empty trie gives distinct keys.

Yellow Paper Appendix D assumes distinct keys.

This is the construction used by the trie root export, including repeated keys and deletions. -/
theorem nodup_keys_foldl_trieSet (secured : Bool) (pairs : List (ByteArray × ByteArray)) :
    ((pairs.foldl (fun trie (key, value) => trieSet trie key value)
      ⟨secured, []⟩).data.map Prod.fst).Nodup := by
  -- Each update preserves uniqueness, regardless of the keys still to be set.
  have preserve : ∀ (rest : List (ByteArray × ByteArray)) (trie : Trie),
      (trie.data.map Prod.fst).Nodup →
      ((rest.foldl (fun trie (key, value) => trieSet trie key value) trie).data.map
        Prod.fst).Nodup := by
    intro rest
    induction rest with
    | nil => intro trie hkeys; exact hkeys
    | cons entry rest ih =>
      intro trie hkeys
      exact ih _ (nodup_keys_trieSet hkeys entry.1 entry.2)
  exact preserve pairs ⟨secured, []⟩ List.nodup_nil

/-- Setting pairs does not change whether the trie hashes its keys. -/
theorem secured_foldl_trieSet (pairs : List (ByteArray × ByteArray)) (trie : Trie) :
    (pairs.foldl (fun trie (key, value) => trieSet trie key value) trie).secured
      = trie.secured := by
  induction pairs generalizing trie with
  | nil => rfl
  | cons entry rest ih =>
    rw [List.foldl_cons, ih]
    simp only [trieSet]
    split <;> first | rfl | (split <;> rfl)

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem TrieError.code_injective (e₁ e₂ : TrieError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [TrieError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Trie
