module

public import EthLib.Execution.Proofs.Trie.Root
public import EthLib.Execution.Proofs.Trie.HexPrefix

/-!
# Proofs: the root ignores insertion order

Two clients that hold the same map must compute the same root, whatever order they set its keys in.

The node composition picks the first key in two places, and neither pick matters:

- The run that an extension consumes is the shortest common prefix of the first path with every path.
  Common prefixes satisfy `min(cpl(a, b), cpl(b, c)) <= cpl(a, c)`.
  So every path gives the same shortest one.
- The value of a branch is the value of the last key whose path ends there.
  When the paths are distinct, at most one ends there.

So the composition gives the same node for any reordering of keys with distinct paths.

The root then depends only on the map:

- A plain trie needs distinct keys.
- A secured trie needs distinct hashes of its keys, since two keys with one hash would share one path.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## Common prefixes -/

/-- Two paths share as many leading nibbles in either order. -/
theorem commonPrefixLength_comm : (a b : List Nibble) → commonPrefixLength a b = commonPrefixLength b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: restA, y :: restB => by
    simp only [commonPrefixLength, commonPrefixLength_comm restA restB]
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]

/-- A path shares all of its nibbles with itself. -/
theorem commonPrefixLength_self : (a : List Nibble) → commonPrefixLength a a = a.length
  | [] => rfl
  | _ :: rest => by simp [commonPrefixLength, commonPrefixLength_self rest]

/-- A path shares at most its own length with another. -/
theorem commonPrefixLength_le_length : (a b : List Nibble) → commonPrefixLength a b ≤ a.length
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | x :: restA, y :: restB => by
    simp only [commonPrefixLength, List.length_cons]
    split
    · exact Nat.succ_le_succ (commonPrefixLength_le_length restA restB)
    · exact Nat.zero_le _

/-- Paths that share `n` nibbles have the same first `n` nibbles. -/
theorem take_eq_of_le_commonPrefixLength : (n : Nat) → (a b : List Nibble) → n ≤ commonPrefixLength a b →
    a.take n = b.take n
  | 0, _, _, _ => by simp
  | n + 1, [], _, h => by simp [commonPrefixLength] at h
  | n + 1, _ :: _, [], h => by simp [commonPrefixLength] at h
  | n + 1, x :: restA, y :: restB, h => by
    simp only [commonPrefixLength] at h
    split at h
    · rename_i hxy
      simp only [List.take_succ_cons, hxy, take_eq_of_le_commonPrefixLength n restA restB (by omega)]
    · omega

/-- `a` and `c` share at least the smaller of what `a` shares with `b` and what `b` shares with `c`. -/
theorem min_commonPrefixLength_le : (a b c : List Nibble) →
    min (commonPrefixLength a b) (commonPrefixLength b c) ≤ commonPrefixLength a c
  | [], _, _ => by simp [commonPrefixLength]
  | _ :: _, [], _ => by simp [commonPrefixLength]
  | _ :: _, _ :: _, [] => by simp [commonPrefixLength]
  | x :: restA, y :: restB, z :: restC => by
    have ih := min_commonPrefixLength_le restA restB restC
    simp only [commonPrefixLength]
    by_cases hxy : x = y
    · by_cases hyz : y = z
      · subst hxy hyz
        simp only [↓reduceIte]
        omega
      · simp [hxy, hyz]
    · simp [hxy]

/-! ## Folds -/

/-- `n` is below a fold of minimums exactly when it is below the start and below every term. -/
theorem le_foldl_min_iff {α : Type} (f : α → Nat) (n : Nat) :
    (l : List α) → (start : Nat) →
      (n ≤ l.foldl (fun length entry => min length (f entry)) start ↔ n ≤ start ∧ ∀ entry ∈ l, n ≤ f entry)
  | [], start => by simp
  | entry :: rest, start => by
    simp only [List.foldl_cons, le_foldl_min_iff f n rest, List.forall_mem_cons, Nat.le_min]
    exact and_assoc

/-- A fold of minimums does not depend on the order of its terms. -/
theorem foldl_min_perm {α : Type} (f : α → Nat) {l l' : List α} (hperm : l.Perm l') (start : Nat) :
    l.foldl (fun length entry => min length (f entry)) start = l'.foldl (fun length entry => min length (f entry)) start := by
  apply Nat.le_antisymm
  · have h := (le_foldl_min_iff f _ l start).mp (Nat.le_refl _)
    exact (le_foldl_min_iff f _ l' start).mpr ⟨h.1, fun entry hmem => h.2 entry (hperm.mem_iff.mpr hmem)⟩
  · have h := (le_foldl_min_iff f _ l' start).mp (Nat.le_refl _)
    exact (le_foldl_min_iff f _ l start).mpr ⟨h.1, fun entry hmem => h.2 entry (hperm.mem_iff.mp hmem)⟩

/-- The longest path does not depend on the order of the keys. -/
theorem longestPath_perm {obj obj' : List (List Nibble × ByteArray)} (hperm : obj.Perm obj') :
    longestPath obj = longestPath obj' := by
  apply Nat.le_antisymm
  · rw [longestPath_le_iff]
    intro entry hmem
    exact (longestPath_le_iff obj' _).mp (Nat.le_refl _) entry (hperm.mem_iff.mp hmem)
  · rw [longestPath_le_iff]
    intro entry hmem
    exact (longestPath_le_iff obj _).mp (Nat.le_refl _) entry (hperm.mem_iff.mpr hmem)

/-- A fold that keeps the value of the last entry that satisfies `p` gives that value, or its start. -/
theorem foldl_last {α β : Type} (p : α → Bool) (value : α → β) :
    (l : List α) → (start : β) →
      l.foldl (fun acc entry => if p entry then value entry else acc) start
        = (((l.filter p).getLast?).map value).getD start
  | [], _ => rfl
  | entry :: rest, start => by
    rw [List.foldl_cons, foldl_last p value rest]
    by_cases h : p entry
    · simp only [h, ↓reduceIte, List.filter_cons_of_pos h, List.getLast?_cons]
      cases (rest.filter p).getLast? <;> rfl
    · simp [h, List.filter_cons_of_neg h]

/-- Two orderings of a list with at most one entry are the same list. -/
theorem eq_of_perm_of_length_le_one {α : Type} {l l' : List α} (hperm : l.Perm l') (hlength : l.length ≤ 1) :
    l = l' := by
  match l, hlength with
  | [], _ => exact List.Perm.nil_eq hperm
  | [x], _ => exact (List.perm_singleton.mp hperm.symm).symm

/-- A list without duplicates whose entries are all `c` has at most one entry. -/
theorem length_le_one_of_nodup {α : Type} {c : α} :
    (l : List α) → l.Nodup → (∀ x ∈ l, x = c) → l.length ≤ 1
  | [], _, _ => Nat.zero_le _
  | [_], _, _ => Nat.le_refl _
  | x :: y :: _, hnodup, hall => by
    have hx := hall x List.mem_cons_self
    have hy := hall y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ((List.nodup_cons.mp hnodup).1 ((hx.trans hy.symm) ▸ List.mem_cons_self)).elim

/-! ## Distinct paths -/

/-- A list whose image has no duplicates has none itself. -/
theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun _ _ hne heq => hne (congrArg f heq)) h

/-- An injective function keeps a list free of duplicates. -/
theorem nodup_map_of_injective {α β : Type} {f : α → β} (hinjective : Function.Injective f) {l : List α}
    (h : l.Nodup) : (l.map f).Nodup :=
  List.Pairwise.map f (fun _ _ hne heq => hne (hinjective heq)) h

/-- The paths of `obj` are distinct after their first `level` nibbles. -/
def Distinct (obj : List (List Nibble × ByteArray)) (level : Nat) : Prop :=
  (obj.map fun entry => entry.1.drop level).Nodup

/-- Paths that are distinct after `level` and share `n` more nibbles are distinct after `level + n`. -/
theorem Distinct.drop {obj : List (List Nibble × ByteArray)} {level n : Nat} (hdistinct : Distinct obj level)
    (common : List Nibble) (hcommon : ∀ entry ∈ obj, (entry.1.drop level).take n = common) :
    Distinct obj (level + n) := by
  apply nodup_of_map (fun rest => common ++ rest)
  -- After `level`, each path is the common nibbles, then the rest.
  have hsplit : (obj.map fun entry => entry.1.drop level)
      = ((obj.map fun entry => entry.1.drop (level + n)).map fun rest => common ++ rest) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro entry hmem
    simp only [Function.comp_apply, ← hcommon entry hmem, ← List.drop_drop, List.take_append_drop]
  rw [← hsplit]
  exact hdistinct

/-- The keys of one child are distinct one nibble further. -/
theorem Distinct.filter {obj : List (List Nibble × ByteArray)} {level : Nat} (hdistinct : Distinct obj level)
    (nibble : Nibble) :
    Distinct (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1) := by
  apply nodup_of_map (fun rest => nibble :: rest)
  -- After `level`, each path of the child is the nibble, then the rest.
  have hsplit : ((obj.filter fun (key, _) => key[level]? = some nibble).map fun entry => entry.1.drop level)
      = (((obj.filter fun (key, _) => key[level]? = some nibble).map fun entry => entry.1.drop (level + 1)).map
          fun rest => nibble :: rest) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro entry hmem
    have hnext : entry.1[level]? = some nibble := by simpa using (List.mem_filter.mp hmem).2
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hnext
    simp only [Function.comp_apply, List.drop_eq_getElem_cons hlt, hget]
  rw [← hsplit]
  exact (List.filter_sublist.map _).nodup hdistinct

/-- With distinct paths, at most one key's path ends at `level`. -/
theorem Distinct.length_filter_le_one {obj : List (List Nibble × ByteArray)} {level : Nat}
    (hdistinct : Distinct obj level) :
    (obj.filter fun (key, _) => key.length = level).length ≤ 1 := by
  rw [← List.length_map (f := fun entry : List Nibble × ByteArray => entry.1.drop level)]
  apply length_le_one_of_nodup (c := [])
  · exact (List.filter_sublist.map _).nodup hdistinct
  · intro rest hmem
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
    have hlength : entry.1.length = level := by simpa using (List.mem_filter.mp hentry).2
    simp [hlength]

/-- With distinct paths, the value of a branch does not depend on the order of the keys. -/
theorem branchValue_perm {obj obj' : List (List Nibble × ByteArray)} {level : Nat} (hperm : obj.Perm obj')
    (hdistinct : Distinct obj level) :
    obj.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value) ByteArray.empty
      = obj'.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value) ByteArray.empty := by
  have h := foldl_last (fun entry : List Nibble × ByteArray => decide (entry.1.length = level)) Prod.snd
  simp only [decide_eq_true_eq] at h
  have h₁ := h obj ByteArray.empty
  have h₂ := h obj' ByteArray.empty
  -- The keys that end here are the same one or none, in both orders.
  have hsame := eq_of_perm_of_length_le_one (hperm.filter _) hdistinct.length_filter_le_one
  have hfold : ∀ l : List (List Nibble × ByteArray),
      l.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value) ByteArray.empty
        = l.foldl (fun acc entry => if entry.1.length = level then entry.2 else acc) ByteArray.empty := fun _ => rfl
  rw [hfold, hfold, h₁, h₂, hsame]

/-! ## `patricialize` ignores the order -/

/-- The run that an extension consumes is the same from any key of the call. -/
theorem run_eq {obj : List (List Nibble × ByteArray)} {level : Nat} {a b : List Nibble × ByteArray}
    (ha : a ∈ obj) (hb : b ∈ obj) :
    obj.foldl (fun length entry => min length (commonPrefixLength (a.1.drop level) (entry.1.drop level)))
        (a.1.drop level).length
      = obj.foldl (fun length entry => min length (commonPrefixLength (b.1.drop level) (entry.1.drop level)))
        (b.1.drop level).length := by
  -- Each run is below the other, by the inequality on common prefixes through the other key.
  have below : ∀ a b, a ∈ obj → b ∈ obj →
      obj.foldl (fun length entry => min length (commonPrefixLength (a.1.drop level) (entry.1.drop level)))
          (a.1.drop level).length
        ≤ obj.foldl (fun length entry => min length (commonPrefixLength (b.1.drop level) (entry.1.drop level)))
          (b.1.drop level).length := by
    intro a b ha hb
    have hrun := (le_foldl_min_iff (fun entry : List Nibble × ByteArray => commonPrefixLength (a.1.drop level)
      (entry.1.drop level)) _ obj (a.1.drop level).length).mp (Nat.le_refl _)
    have hab := hrun.2 b hb
    rw [le_foldl_min_iff]
    refine ⟨Nat.le_trans hab ?_, fun entry hmem => ?_⟩
    · rw [commonPrefixLength_comm]
      exact commonPrefixLength_le_length _ _
    · have := min_commonPrefixLength_le (b.1.drop level) (a.1.drop level) (entry.1.drop level)
      rw [commonPrefixLength_comm (b.1.drop level)] at this
      have := hrun.2 entry hmem
      omega
  exact Nat.le_antisymm (below a b ha hb) (below b a hb ha)

/-- One step gives the same node for two orders of keys with distinct paths, when its nested calls do. -/
theorem patricializeStep_perm (hash : ByteArray → Hash32)
    {recurse : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode)}
    (hrecurse : ∀ obj obj' level, obj.Perm obj' → Distinct obj level → recurse obj level = recurse obj' level)
    {obj obj' : List (List Nibble × ByteArray)} {level : Nat} (hperm : obj.Perm obj') (hdistinct : Distinct obj level) :
    patricializeStep hash recurse obj level = patricializeStep hash recurse obj' level := by
  match obj, obj', hperm, hdistinct with
  | [], [], _, _ => rfl
  | [], _ :: _, hperm, _ => exact absurd hperm.length_eq (by simp)
  | [x], obj', hperm, _ => rw [List.perm_singleton.mp hperm.symm]
  | _ :: _ :: _, [], hperm, _ => exact absurd hperm.length_eq (by simp)
  | _ :: _ :: _, [_], hperm, _ => exact absurd hperm.length_eq (by simp)
  | (key₁, value₁) :: second :: rest, (key₂, value₂) :: second' :: rest', hperm, hdistinct =>
    simp only [patricializeStep_cons_cons]
    -- Both runs equal the run from the first key, over the keys of the first order.
    have hfirst₂ : (key₂, value₂) ∈ (key₁, value₁) :: second :: rest := hperm.mem_iff.mpr List.mem_cons_self
    have hrun : List.foldl (fun length (x : List Nibble × ByteArray) =>
          min length (commonPrefixLength (List.drop level key₂) (List.drop level x.1)))
          (List.drop level key₂).length ((key₂, value₂) :: second' :: rest')
        = List.foldl (fun length (x : List Nibble × ByteArray) =>
          min length (commonPrefixLength (List.drop level key₁) (List.drop level x.1)))
          (List.drop level key₁).length ((key₁, value₁) :: second :: rest) := by
      rw [← foldl_min_perm _ hperm]
      exact run_eq (a := (key₂, value₂)) (b := (key₁, value₁)) hfirst₂ List.mem_cons_self
    rw [hrun]
    split
    · -- An extension: the same run from either first key, and the same keys below it.
      rename_i hpositive
      have hle := (le_foldl_min_iff (fun entry : List Nibble × ByteArray =>
        commonPrefixLength (key₁.drop level) (entry.1.drop level)) _ ((key₁, value₁) :: second :: rest)
        (key₁.drop level).length).mp (Nat.le_refl _)
      have htake := take_eq_of_le_commonPrefixLength _ _ _ (hle.2 _ hfirst₂)
      have hcommon : ∀ entry ∈ (key₁, value₁) :: second :: rest,
          (entry.1.drop level).take _ = (key₁.drop level).take _ :=
        fun entry hmem => (take_eq_of_le_commonPrefixLength _ _ _ (hle.2 entry hmem)).symm
      rw [hrecurse _ _ _ hperm (hdistinct.drop _ hcommon), htake]
    · -- A branch: the same value, and each child holds the same keys in another order.
      rw [branchValue_perm hperm hdistinct]
      congr 1
      apply mapMVector_congr
      intro nibble _
      rw [hrecurse _ _ _ (hperm.filter _) (hdistinct.filter nibble)]

/-- Every budget gives the same node for two orders of keys with distinct paths. -/
theorem patricializeAux_perm (hash : ByteArray → Hash32) :
    (fuel : Nat) → (obj obj' : List (List Nibble × ByteArray)) → (level : Nat) → obj.Perm obj' →
      Distinct obj level → patricializeAux hash fuel obj level = patricializeAux hash fuel obj' level
  | 0, _, _, _, hperm, hdistinct => by
    simp only [patricializeAux_zero]
    exact patricializeStep_perm hash (fun _ _ _ _ _ => rfl) hperm hdistinct
  | fuel + 1, _, _, _, hperm, hdistinct => by
    simp only [patricializeAux_add_one]
    exact patricializeStep_perm hash
      (fun obj obj' level hperm' hdistinct' => patricializeAux_perm hash fuel obj obj' level hperm' hdistinct')
      hperm hdistinct

/-- `patricialize` gives the same node for two orders of keys with distinct paths. -/
theorem patricialize_perm (hash : ByteArray → Hash32) {obj obj' : List (List Nibble × ByteArray)} {level : Nat}
    (hperm : obj.Perm obj') (hdistinct : Distinct obj level) :
    patricialize hash obj level = patricialize hash obj' level := by
  rw [patricialize_eq, patricialize_eq, longestPath_perm hperm,
    patricializeAux_perm hash _ _ _ _ hperm hdistinct]

/-! ## The root ignores the order -/

/-- With no empty value, the entries become their paths and values, in order. -/
theorem prepareData_eq_keyPath (hash : ByteArray → Hash32) (secured : Bool) {data : List (ByteArray × ByteArray)}
    (hfull : ∀ entry ∈ data, entry.2.size ≠ 0) :
    prepareData hash data secured = .ok (data.map fun entry => (keyPath hash secured entry.1, entry.2)) := by
  rw [prepareData_ok hash secured data hfull]

/-- Once the entries are prepared, the root is the hash of the encoding of the node of `patricialize`. -/
theorem root_of_prepareData {hash : ByteArray → Hash32} {trie : Trie} {obj : List (List Nibble × ByteArray)}
    (h : prepareData hash trie.data trie.secured = .ok obj) :
    root hash trie = (do
      let rootNode ← (patricialize hash obj 0).mapError .rlp
      let encoded ← (encode (unencoded rootNode)).mapError .rlp
      return hash encoded) := by
  simp only [root_eq, h]
  rfl

/-- The root does not depend on the order of the entries, when the keys have distinct paths. -/
theorem root_perm (hash : ByteArray → Hash32) {secured : Bool} {data data' : List (ByteArray × ByteArray)}
    (hperm : data.Perm data') (hpaths : (data.map fun entry => keyPath hash secured entry.1).Nodup) :
    root hash ⟨secured, data⟩ = root hash ⟨secured, data'⟩ := by
  by_cases hempty : ∃ entry ∈ data, entry.2.size = 0
  · -- Both orders hold the empty value, so neither has a root.
    obtain ⟨entry, hmem, hsize⟩ := hempty
    rw [root_emptyValue hash _ ⟨entry, hmem, hsize⟩, root_emptyValue hash _ ⟨entry, hperm.mem_iff.mp hmem, hsize⟩]
  · -- Both orders give the same keys and values, in another order.
    have hfull : ∀ entry ∈ data, entry.2.size ≠ 0 := fun entry hmem hsize => hempty ⟨entry, hmem, hsize⟩
    have hfull' : ∀ entry ∈ data', entry.2.size ≠ 0 := fun entry hmem => hfull entry (hperm.mem_iff.mpr hmem)
    rw [root_of_prepareData (prepareData_eq_keyPath hash secured hfull),
      root_of_prepareData (prepareData_eq_keyPath hash secured hfull')]
    have hdistinct : Distinct (data.map fun entry => (keyPath hash secured entry.1, entry.2)) 0 := by
      simp only [Distinct, List.drop_zero, List.map_map]
      exact hpaths
    rw [patricialize_perm hash (hperm.map _) hdistinct]

/-- The bytes of a hash determine the hash. -/
theorem hashBytes_injective : Function.Injective fun digest : Hash32 => (⟨digest.toArray⟩ : ByteArray) := by
  intro a b h
  simp only [ByteArray.mk.injEq] at h
  exact Vector.toArray_inj.mp h

/-- A plain trie: two lists with distinct keys and the same entries have the same root. -/
theorem root_plain_eq (hash : ByteArray → Hash32) {data data' : List (ByteArray × ByteArray)}
    (hkeys : (data.map Prod.fst).Nodup) (hkeys' : (data'.map Prod.fst).Nodup)
    (hentries : ∀ entry, entry ∈ data ↔ entry ∈ data') :
    root hash ⟨false, data⟩ = root hash ⟨false, data'⟩ := by
  apply root_perm hash ((List.perm_ext_iff_of_nodup (nodup_of_map _ hkeys) (nodup_of_map _ hkeys')).mpr hentries)
  -- Distinct keys have distinct nibbles.
  simpa [keyPath_eq, List.map_map, Function.comp_def] using
    nodup_map_of_injective (fun _ _ h => bytesToNibbleList_injective h) hkeys

/-- A secured trie: two lists whose keys have distinct hashes and that hold the same entries have the same root. -/
theorem root_secured_eq (hash : ByteArray → Hash32) {data data' : List (ByteArray × ByteArray)}
    (hhashes : (data.map fun entry => hash entry.1).Nodup) (hhashes' : (data'.map fun entry => hash entry.1).Nodup)
    (hentries : ∀ entry, entry ∈ data ↔ entry ∈ data') :
    root hash ⟨true, data⟩ = root hash ⟨true, data'⟩ := by
  apply root_perm hash ((List.perm_ext_iff_of_nodup (nodup_of_map _ hhashes) (nodup_of_map _ hhashes')).mpr hentries)
  -- Distinct hashes have distinct bytes, and distinct bytes have distinct nibbles.
  have hbytes := nodup_map_of_injective hashBytes_injective hhashes
  simpa [keyPath_eq, List.map_map, Function.comp_def] using
    nodup_map_of_injective (fun _ _ h => bytesToNibbleList_injective h) hbytes

end EthLib.Execution.Trie
