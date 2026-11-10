module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Trie.Binding
public import EthLib.Execution.Proofs.Trie.Range

/-!
# Proofs: an accepted range is the trie between its two ends

A range that passes the range check gives each key between its two ends the trie's value.

Otherwise a search finds two different nodes with one hash.

So the range holds every 32-byte key of the trie there, and no other such key.

When the check shows no key after the range, this holds for every key from the start on.

When it shows a key after the range, the theorem does not say that the trie holds one.

The trie is any plain trie with the requested root and distinct keys.

Its keys are not hashed again: each is a 32-byte hash, as in the range.

A last section carries the result to a secured trie, such as a state or storage trie.

Such a trie has the root of the plain trie of its hashed keys.

The source is [`caps/snap.md`][snap], sections "AccountRange (0x01)" and "StorageRanges (0x03)".

[snap]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md

A hash of any input to 32 bytes has collisions, so the theorem names a search that returns one.

For each key, the range gives a proof of that key alone.

It takes the nodes on the two paths from the range proof, and builds the rest from the entries.

The single-key check accepts that proof, with the value that the entries give the key.

The search compares that proof with the trie's own proof of the key, node by node.

When it finds nothing, the two proofs are one, and so are the two values.

A range with no proof is the whole trie, and its single-key proofs are those of its entries.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## The proof of one key that a range gives -/

/-- The proof node that a reference names, as the range check reads it.

A hash names the first node of the range proof with that hash.

Any other reference names no proof node. -/
def referencedNodes (nodes : List (Hash32 × ByteArray)) : Item → List ByteArray
  | .bytes digest =>
    if digest.size = 32 then
      ((nodes.find? fun (hash, _) => hash.toList == digest.data.toList).map Prod.snd).toList
    else
      []
  | .list _ => []

/-- The proof of the rest of the path of one key, below the subtree that a reference holds.

The arguments follow the range check: the entries are those below the subtree.

On the path of an end, it takes the nodes of the range proof.

In a subtree between the two ends, it takes the proof of the node that the entries build there.

Elsewhere it takes no node. -/
def rangeProofBelow (hash : ByteArray → Hash32) (nodes : List (Hash32 × ByteArray))
    (left : List Nibble) (right : Option (List Nibble)) :
    Nat → Item → List Nibble → List (List Nibble × ByteArray) → List Nibble → List ByteArray
  | 0, _, _, _, _ => []
  | fuel + 1, reference, pre, entries, path =>
    match rangePlace left right pre with
    | .inside =>
      let built : Except RlpError (List ByteArray) := do
        let node ← patricialize hash entries pre.length
        let encoded ← encode (unencoded node)
        let below ← proofBelow hash (path.length + 1) entries pre.length path
        return (if encoded.size < 32 then [] else [encoded]) ++ below
      match built with
      | .ok single => single
      | .error _ => []
    | .boundary =>
      referencedNodes nodes reference ++
        match (lookupNode nodes reference).bind decodeNode with
        | .ok (.extension keySegment subnode) =>
          if keySegment = path.take keySegment.length then
            rangeProofBelow hash nodes left right fuel subnode (pre ++ keySegment) entries
              (path.drop keySegment.length)
          else
            []
        | .ok (.branch subnodes _) =>
          match path with
          | [] => []
          | nibble :: restOfPath =>
            rangeProofBelow hash nodes left right fuel subnodes[nibble] (pre ++ [nibble])
              (entries.filter fun (entryKey, _) => entryKey[pre.length]? = some nibble) restOfPath
        | _ => []
    | _ => []

/-- The proof of one key alone that a range of the trie of the requested root gives.

With a range proof, it follows the path of the key as the range check does.

With no range proof, it is the proof of the key in the trie of the entries. -/
def rangeKeyProof (hash : ByteArray → Hash32) (root start : Hash32)
    (entries : List (Hash32 × ByteArray)) (proof : List ByteArray) (key : Hash32) :
    List ByteArray :=
  if proof.isEmpty then
    let trie : Trie := ⟨false, entries.map fun (entryKey, value) => (⟨entryKey.toArray⟩, value)⟩
    match getProof hash trie ⟨key.toArray⟩ with
    | .ok single => single
    | .error _ => []
  else
    let obj := entries.map fun (entryKey, value) => (bytesToNibbleList ⟨entryKey.toArray⟩, value)
    let left := bytesToNibbleList ⟨start.toArray⟩
    rangeProofBelow hash (proof.map fun encoded => (hash encoded, encoded)) left
      (obj.getLast?.map Prod.fst) (left.length + 2) (.bytes ⟨root.toArray⟩) [] obj
      (bytesToNibbleList ⟨key.toArray⟩)

/-! ## The search -/

/-- The search compares the range's proof of a key with the trie's own proof of it.

It returns the first two nodes at one place that differ but have one hash. -/
def findRangeCollision (hash : ByteArray → Hash32) (trie : Trie) (root start : Hash32)
    (entries : List (Hash32 × ByteArray)) (proof : List ByteArray) (key : Hash32) :
    Option (ByteArray × ByteArray) :=
  match getProof hash trie ⟨key.toArray⟩ with
  | .ok honest => findProofCollision hash (rangeKeyProof hash root start entries proof key) honest
  | .error _ => none

/-- Every pair that the search returns is a collision. -/
theorem findRangeCollision_valid (hash : ByteArray → Hash32) {trie : Trie}
    {root start : Hash32} {entries : List (Hash32 × ByteArray)} {proof : List ByteArray}
    {key : Hash32} {pair : ByteArray × ByteArray}
    (h : findRangeCollision hash trie root start entries proof key = some pair) :
    IsCollision hash pair := by
  unfold findRangeCollision at h
  split at h
  · exact findProofCollision_valid hash _ _ h
  · cases h

/-- The search finds nothing when the range gives the trie's own proof of the key. -/
theorem findRangeCollision_of_eq (hash : ByteArray → Hash32) {trie : Trie}
    {root start : Hash32} {entries : List (Hash32 × ByteArray)} {proof : List ByteArray}
    {key : Hash32}
    (h : getProof hash trie ⟨key.toArray⟩ = .ok (rangeKeyProof hash root start entries proof key)) :
    findRangeCollision hash trie root start entries proof key = none := by
  simp only [findRangeCollision, h, findProofCollision_self]

/-- A whole trie sent with no proof, against the trie of its own entries, has no collision. -/
theorem findRangeCollision_whole (hash : ByteArray → Hash32) (root start key : Hash32)
    (entries : List (Hash32 × ByteArray)) :
    findRangeCollision hash
      ⟨false, entries.map fun (entryKey, value) => (⟨entryKey.toArray⟩, value)⟩
      root start entries [] key = none := by
  simp only [findRangeCollision, rangeKeyProof, List.isEmpty_nil, ↓reduceIte]
  split <;> simp_all [findProofCollision_self]

/-- The pair that the search returns holds a node of each of the two proofs of the key. -/
theorem mem_of_findRangeCollision (hash : ByteArray → Hash32) {trie : Trie}
    {root start : Hash32} {entries : List (Hash32 × ByteArray)} {proof : List ByteArray}
    {key : Hash32} {pair : ByteArray × ByteArray}
    (h : findRangeCollision hash trie root start entries proof key = some pair) :
    pair.1 ∈ rangeKeyProof hash root start entries proof key ∧
      ∃ honest, getProof hash trie ⟨key.toArray⟩ = .ok honest ∧ pair.2 ∈ honest := by
  unfold findRangeCollision at h
  split at h
  · rename_i honest hhonest
    obtain ⟨hrange, hmem⟩ := mem_of_findProofCollision hash _ _ h
    exact ⟨hrange, honest, hhonest, hmem⟩
  · cases h

/-! ## Following the nodes of the range proof -/

/-- An extension that decodes consumes at least one nibble. -/
private theorem segment_ne_nil_of_decodeNode {item : Item} {keySegment : List Nibble}
    {subnode : Item} (h : decodeNode item = .ok (.extension keySegment subnode)) :
    keySegment ≠ [] := by
  rintro rfl
  unfold decodeNode at h
  repeat' split at h
  all_goals simp_all

/-- Distinct paths that share a prefix are honest after it. -/
private theorem honest_of_prefix {entries : List (List Nibble × ByteArray)} {pre : List Nibble}
    (hpre : ∀ entry ∈ entries, pre <+: entry.1) (hnodup : (entries.map Prod.fst).Nodup)
    (hvalues : ∀ entry ∈ entries, entry.2.size ≠ 0) : Honest entries pre.length where
  distinct := by
    have hdistinct : Distinct entries 0 := by simpa [Distinct] using hnodup
    have h := hdistinct.drop pre fun entry hmem => by
      rw [List.drop_zero]
      exact (List.prefix_iff_eq_take.mp (hpre entry hmem)).symm
    rwa [Nat.zero_add] at h
  long := fun entry hmem => (hpre entry hmem).length_le
  full := hvalues

/-- The walk follows a reference with the node that the range check reads for it. -/
private theorem resolve_referencedNodes (hash : ByteArray → Hash32)
    {nodes : List (Hash32 × ByteArray)} (hnodes : ∀ node ∈ nodes, node.1 = hash node.2)
    {reference item : Item} (h : lookupNode nodes reference = .ok item) (rest : List ByteArray) :
    resolve hash reference (referencedNodes nodes reference ++ rest) = .ok (item, rest) := by
  cases reference with
  | list items =>
    simp only [lookupNode, Except.ok.injEq] at h
    subst h
    rfl
  | bytes digest =>
    by_cases hempty : digest.size = 0
    · simp only [lookupNode, hempty, ↓reduceIte, Except.ok.injEq] at h
      subst h
      simp [referencedNodes, resolve, hempty]
    · by_cases hsize : digest.size = 32
      · simp only [lookupNode, hsize, ↓reduceIte, Nat.succ_ne_zero] at h
        simp only [referencedNodes, hsize, ↓reduceIte]
        cases hfind : nodes.find? fun (hash, _) => hash.toList == digest.data.toList with
        | none => simp [hfind] at h
        | some node =>
          obtain ⟨digest', encoded⟩ := node
          simp only [hfind] at h
          -- The node found has the hash of the reference.
          have hmatch := List.find?_some hfind
          have hhash := hnodes _ (List.mem_of_find?_eq_some hfind)
          simp only [beq_iff_eq] at hmatch hhash
          simp only [Option.map_some, Option.toList_some, List.cons_append, resolve, hsize,
            ↓reduceIte, ← hhash, hmatch]
          cases hdecode : decode encoded with
          | error => simp [hdecode, Except.mapError] at h
          | ok decoded =>
            simp only [hdecode, Except.mapError, Except.ok.injEq] at h
            subst h
            rfl
      · simp [lookupNode, hempty, hsize] at h

/-- The walk down the proof that a range gives one key, below one call of the range check.

It gives the value that the entries of the call give the key, and leaves the nodes after the proof.

The key's path continues the path of the call, and follows the first end.

It precedes the last end, or the check shows no key after the range in the subtree. -/
private theorem follow_rangeProofBelow (hash : ByteArray → Hash32)
    {nodes : List (Hash32 × ByteArray)} (hnodes : ∀ node ∈ nodes, node.1 = hash node.2)
    {left : List Nibble} {right : Option (List Nibble)} {full : List Nibble} (hleft : left ≤ full) :
    (fuel : Nat) → {reference : Item} → {pre : List Nibble} →
      {entries : List (List Nibble × ByteArray)} → {path : List Nibble} → {result : Bool} →
      {fuel' : Nat} →
      checkSubtree hash nodes left right fuel reference pre entries = .ok result →
      full = pre ++ path → (right.all (full ≤ ·) ∨ result = false) →
      (∀ entry ∈ entries, pre <+: entry.1) → (entries.map Prod.fst).Nodup →
      (∀ entry ∈ entries, entry.2.size ≠ 0) → path.length < fuel' →
      ∀ rest, follow hash fuel' reference path
          (rangeProofBelow hash nodes left right fuel reference pre entries path ++ rest) =
        .ok (lookupAt entries pre.length path, rest)
  | 0, _, _, _, _, _, _, hcheck, _, _, _, _, _, _ => by cases hcheck
  | fuel + 1, reference, pre, entries, path, result, fuel', hcheck, hfull, hright, hpre, hnodup,
      hvalues, hfuel => by
    rw [checkSubtree] at hcheck
    rw [rangeProofBelow]
    cases hplace : rangePlace left right pre with
    | before =>
      -- The key follows the first end, so it is not below a subtree before the range.
      rw [hfull] at hleft
      exact absurd (append_lt_of_rangePlace_before hplace path) hleft
    | after =>
      -- The key is above the last end, so the check shows no key after the range here.
      obtain ⟨last, rfl, hlast⟩ := lt_append_of_rangePlace_after hplace path
      have hresult : result = false := by
        rcases hright with hright | hright
        · rw [hfull] at hright
          simp only [Option.all_some, decide_eq_true_eq] at hright
          exact absurd hlast hright
        · exact hright
      subst hresult
      simp only [hplace] at hcheck
      by_cases hempty : entries.isEmpty = true
      · rw [List.isEmpty_iff] at hempty
        subst hempty
        simp only [List.isEmpty_nil, ↓reduceIte, Except.ok.injEq, bne_eq_false_iff_eq] at hcheck
        subst hcheck
        obtain ⟨fuel', rfl⟩ : ∃ n, fuel' = n + 1 := ⟨fuel' - 1, by omega⟩
        intro rest
        rfl
      · simp [hempty] at hcheck
    | inside =>
      -- The parent holds the node that the entries build, so the walk is the honest one.
      simp only [hplace, Bind.bind, Except.bind, Except.mapError] at hcheck ⊢
      cases hnode : patricialize hash entries pre.length with
      | error => simp [hnode] at hcheck
      | ok node =>
        cases hheld : encodeInternalNode hash node with
        | error => simp [hnode, hheld] at hcheck
        | ok held =>
          by_cases hsame : held = reference
          · subst hsame
            obtain ⟨encoded, hencode, rfl⟩ := encode_of_encodeInternalNode hheld
            obtain ⟨below, hbelow⟩ := proofBelow_ok hash (path.length + 1) hnode path
            simp only [hencode, hbelow, pure, Except.pure]
            exact follow_child hash hencode (walk_honest hash fuel' (path.length + 1)
              (honest_of_prefix hpre hnodup hvalues) hfuel (Nat.lt_succ_self _) hnode hbelow)
          · simp [hnode, hheld, hsame] at hcheck
    | boundary =>
      simp only [hplace] at hcheck ⊢
      obtain ⟨fuel', rfl⟩ : ∃ n, fuel' = n + 1 := ⟨fuel' - 1, by omega⟩
      cases hlookup : lookupNode nodes reference with
      | error => simp [hlookup, Except.mapError, Bind.bind, Except.bind] at hcheck
      | ok item =>
        intro rest
        -- The walk reads the node of the range proof that the check reads.
        rw [List.append_assoc]
        simp only [follow, resolve_referencedNodes hash hnodes hlookup, Except.bind]
        simp only [hlookup, Except.mapError, Bind.bind, Except.bind] at hcheck
        by_cases hempty : item = .bytes .empty
        · -- No node: no entry, and the key is not set.
          subst hempty
          by_cases hentries : entries.isEmpty = true
          · rw [List.isEmpty_iff] at hentries
            subst hentries
            rfl
          · simp [hentries, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hcheck
        · cases hdecode : decodeNode item with
          | error => simp [hempty, hdecode] at hcheck
          | ok decoded =>
            obtain ⟨items, rfl⟩ : ∃ items, item = .list items := by
              cases item with
              | list items => exact ⟨items, rfl⟩
              | bytes => simp [decodeNode] at hdecode
            rw [walk_decoded hash fuel' hdecode]
            simp only [hempty, hdecode, ↓reduceIte] at hcheck
            cases decoded with
            | leaf restOfKey value =>
              dsimp only at hcheck ⊢
              by_cases hin : (decide (left ≤ pre ++ restOfKey) &&
                  right.all fun x => decide (pre ++ restOfKey ≤ x)) = true
              · -- A key inside the range: the one entry here.
                rw [ite_eq_left hin] at hcheck
                by_cases hentries : entries = [(pre ++ restOfKey, value)]
                · subst hentries
                  rw [lookupAt_single, List.drop_left, List.nil_append]
                · simp [hentries, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hcheck
              · -- A key outside the range: no entry here, and the key is another one.
                rw [ite_eq_right hin] at hcheck
                by_cases hentries : entries.isEmpty = true
                · rw [List.isEmpty_iff] at hentries
                  subst hentries
                  simp only [List.isEmpty_nil, ↓reduceIte, pure, Except.pure,
                    Except.ok.injEq] at hcheck
                  -- The leaf's key is not inside the range, but the key's is.
                  have hne : restOfKey ≠ path := by
                    rintro rfl
                    rw [← hfull] at hin hcheck
                    cases right with
                    | none => simp [hleft] at hin
                    | some last =>
                      simp only [Option.all_some, Option.any_some, decide_eq_true_eq,
                        Bool.and_eq_true] at hin hcheck hright
                      have hlast : last < full :=
                        Decidable.not_not.mp fun h => hin ⟨hleft, List.not_lt.mp h⟩
                      rcases hright with hright | hright
                      · exact hright hlast
                      · subst hright
                        exact absurd hlast (by simpa using hcheck.symm)
                  simp [hne, lookupAt_nil]
                · simp [hentries, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hcheck
            | extension keySegment subnode =>
              dsimp only at hcheck ⊢
              have hsegment := segment_ne_nil_of_decodeNode hdecode
              by_cases hprefixes :
                  (entries.all fun x => (pre ++ keySegment).isPrefixOf x.fst) = true
              · rw [ite_eq_left hprefixes] at hcheck
                -- Every entry continues with the segment after the path of the call.
                have hpre' : ∀ entry ∈ entries, pre ++ keySegment <+: entry.1 := fun entry hmem =>
                  List.isPrefixOf_iff_prefix.mp (List.all_eq_true.mp hprefixes entry hmem)
                have hcommon : ∀ entry ∈ entries,
                    (entry.1.drop pre.length).take keySegment.length = keySegment := by
                  intro entry hmem
                  obtain ⟨tail, htail⟩ := hpre' entry hmem
                  rw [← htail, List.append_assoc, List.drop_left, List.take_left]
                by_cases hfollow : keySegment = path.take keySegment.length
                · -- The key follows the segment: the subtree after it.
                  rw [ite_eq_left hfollow, ite_eq_left hfollow, lookupAt_extension hcommon hfollow]
                  have hlength : keySegment.length ≤ path.length := by
                    have := congrArg List.length hfollow
                    simp only [List.length_take] at this
                    omega
                  have hpositive : 0 < keySegment.length := List.length_pos_iff.mpr hsegment
                  have hfull' : full = pre ++ keySegment ++ path.drop keySegment.length := by
                    calc full = pre ++ (keySegment ++ path.drop keySegment.length) := by
                          conv => rhs; arg 2; arg 1; rw [hfollow]
                          rw [List.take_append_drop, hfull]
                      _ = _ := (List.append_assoc _ _ _).symm
                  have ih := follow_rangeProofBelow hash hnodes hleft fuel hcheck hfull' hright
                    hpre' hnodup hvalues (fuel' := fuel')
                    (by simp only [List.length_drop]; omega) rest
                  rwa [List.length_append] at ih
                · rw [ite_eq_right hfollow, ite_eq_right hfollow,
                    lookupAt_extension_none hcommon hfollow]
                  rfl
              · simp [hprefixes, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hcheck
            | branch subnodes value =>
              dsimp only at hcheck ⊢
              by_cases hvalue : value.size = 0
              · simp only [hvalue, ne_eq, not_true_eq_false, ↓reduceIte] at hcheck
                by_cases hlong : (entries.all fun x => decide (pre.length < x.fst.length)) = true
                · rw [ite_eq_left hlong] at hcheck
                  have hlong' := List.all_eq_true.mp hlong
                  generalize hmap : List.mapM (m := Except RangeError) _ (List.finRange 16) =
                    mapped at hcheck
                  cases mapped with
                  | error => cases hcheck
                  | ok afterRange =>
                    simp only [pure, Except.pure, Except.ok.injEq] at hcheck
                    match path with
                    | [] =>
                      -- Every key goes on below the branch, so none ends at it.
                      have hnone : lookupAt entries pre.length [] = none := by
                        simp only [lookupAt, Option.map_eq_none_iff, List.find?_eq_none,
                          List.drop_eq_nil_iff, decide_eq_true_eq]
                        intro entry hmem hle
                        have := hlong' entry hmem
                        simp only [decide_eq_true_eq] at this
                        omega
                      simp [hvalue, hnone]
                    | nibble :: restOfPath =>
                      -- The key goes on to the child of its next nibble.
                      obtain ⟨below, hbelow, hchild⟩ :=
                        exists_mem_of_mapM_ok hmap (List.mem_finRange nibble)
                      have hright' : (right.all fun x => decide (full ≤ x)) = true ∨
                          below = false := by
                        rcases hright with hright | hright
                        · exact .inl hright
                        · subst hright
                          refine .inr ?_
                          cases below
                          · rfl
                          · exact absurd hcheck (by simpa using hbelow)
                      have hpre' : ∀ entry ∈ entries.filter
                          (fun x => decide (x.fst[pre.length]? = some nibble)),
                          pre ++ [nibble] <+: entry.1 := by
                        intro entry hmem
                        obtain ⟨hmem, hnext⟩ := List.mem_filter.mp hmem
                        simp only [decide_eq_true_eq] at hnext
                        obtain ⟨tail, htail⟩ := hpre entry hmem
                        rw [← htail] at hnext ⊢
                        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hnext
                        cases tail with
                        | nil => simp at hnext
                        | cons first tail =>
                          simp only [List.getElem?_cons_zero, Option.some.injEq] at hnext
                          subst hnext
                          exact ⟨tail, by simp⟩
                      have ih := follow_rangeProofBelow hash hnodes hleft fuel hchild
                        (by rw [hfull, List.append_assoc]; rfl) hright' hpre'
                        ((List.filter_sublist.map _).nodup hnodup)
                        (fun entry hmem => hvalues entry (List.mem_filter.mp hmem).1)
                        (fuel' := fuel') (by simp only [List.length_cons] at hfuel; omega) rest
                      rw [List.length_append, List.length_singleton] at ih
                      rw [lookupAt_branch]
                      exact ih
                · simp [hlong, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hcheck
              · simp [hvalue, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hcheck

/-- The single-key check accepts a proof whose walk from the root uses every node. -/
private theorem verifyProof_of_follow (hash : ByteArray → Hash32) {root : Hash32}
    {key : ByteArray} {proof : List ByteArray} {value : Option ByteArray}
    (h : follow hash ((bytesToNibbleList key).length + 1) (.bytes ⟨root.toArray⟩)
      (bytesToNibbleList key) proof = .ok (value, [])) :
    verifyProof hash root false key proof = .ok value := by
  unfold follow at h
  simp only [verifyProof, keyPath_eq, Bool.false_eq_true, ↓reduceIte, Bind.bind]
  cases hres : resolve hash (.bytes ⟨root.toArray⟩) proof with
  | error => simp [hres, Except.bind] at h
  | ok next =>
    simp only [hres, Except.bind] at h ⊢
    rw [h]
    rfl

/-! ## Soundness -/

/-- The single-key check accepts the proof that an accepted range gives a key between its ends.

It gives the key the value that the entries give it.

When the range check shows no key after the range, the key need only follow the start. -/
theorem verifyProof_rangeKeyProof (hash : ByteArray → Hash32) {root' start : Hash32}
    {entries : List (Hash32 × ByteArray)} {proof : List ByteArray} {more : Bool}
    (hverify : verifyRange hash root' start entries proof = .ok more) (key : Hash32)
    (hstart : bytesToNibbleList ⟨start.toArray⟩ ≤ bytesToNibbleList ⟨key.toArray⟩)
    (hlast : more = false ∨ entries.getLast?.all fun last =>
      bytesToNibbleList ⟨key.toArray⟩ ≤ bytesToNibbleList ⟨last.1.toArray⟩) :
    verifyProof hash root' false ⟨key.toArray⟩ (rangeKeyProof hash root' start entries proof key) =
      .ok ((entries.find? fun entry => entry.1 = key).map Prod.snd) := by
  unfold verifyRange at hverify
  simp only [Bind.bind, Except.bind] at hverify
  generalize hobj : List.map (fun x : Hash32 × ByteArray =>
    (bytesToNibbleList ⟨x.fst.toArray⟩, x.snd)) entries = obj at hverify
  -- The checks that come before the proof: sorted keys after the start, with values.
  by_cases hsorted : strictlyIncreasing (obj.map Prod.fst) = true
  · by_cases hbefore : (obj.any fun x => decide (x.fst < bytesToNibbleList ⟨start.toArray⟩)) = true
    · simp [hsorted, hbefore, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hverify
    · by_cases hzero : (obj.any fun x => decide (x.snd.size = 0)) = true
      · simp only [hsorted, hbefore, hzero, ↓reduceIte, Bool.false_eq_true] at hverify
        cases hverify
      · simp only [hsorted, hbefore, hzero, ↓reduceIte, Bool.false_eq_true] at hverify
        have hnodup := nodup_of_strictlyIncreasing hsorted
        have hvalues : ∀ entry ∈ obj, entry.2.size ≠ 0 := fun entry hmem hsize =>
          hzero (List.any_eq_true.mpr ⟨entry, hmem, by simpa using hsize⟩)
        unfold rangeKeyProof
        by_cases hempty : proof.isEmpty = true
        · simp only [hempty, ↓reduceIte] at hverify ⊢
          -- The entries build the root, and the proof is the trie's own proof of the key.
          generalize hdata : List.map (fun x : Hash32 × ByteArray =>
            ((⟨x.fst.toArray⟩ : ByteArray), x.snd)) entries = data at hverify ⊢
          have hroot : root hash ⟨false, data⟩ = .ok root' := by
            cases hbuilt : root hash ⟨false, data⟩ with
            | error error =>
              rw [hbuilt] at hverify
              cases error <;> cases hverify
            | ok built =>
              rw [hbuilt] at hverify
              by_cases hsame : built = root'
              · rw [hsame]
              · simp [hsame, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hverify
          obtain ⟨single, hsingle⟩ := getProof_ok hash hroot ⟨key.toArray⟩
          rw [hsingle]
          have hpaths : (data.map fun entry => keyPath hash false entry.1).Nodup := by
            subst hdata hobj
            simpa [keyPath_eq, List.map_map, Function.comp_def] using hnodup
          dsimp only
          rw [verifyProof_getProof hash hroot hsingle hpaths, valueAt_plain]
          -- One key in bytes means one key.
          subst hdata
          simp only [List.find?_map, Option.map_map]
          congr 2
          apply find?_congr
          intro entry _
          simp only [Function.comp_apply]
          rw [Bool.eq_iff_iff, sameBytes_iff, decide_eq_true_iff]
          exact ⟨fun h => hashBytes_injective h, fun h => by rw [h]⟩
        · simp only [hempty, ↓reduceIte, Bool.false_eq_true] at hverify ⊢
          -- The walk from the root, with the proof that the range gives the key.
          have hobj' : List.map (fun x : Hash32 × ByteArray => match x with
              | (entryKey, value) => (bytesToNibbleList ⟨entryKey.toArray⟩, value)) entries =
              obj := hobj
          rw [hobj']
          have hnodes : ∀ node ∈ proof.map (fun encoded => (hash encoded, encoded)),
              node.1 = hash node.2 := by
            intro node hmem
            obtain ⟨encoded, -, rfl⟩ := List.mem_map.mp hmem
            rfl
          have hright : ((obj.getLast?.map Prod.fst).all fun x =>
              decide (bytesToNibbleList ⟨key.toArray⟩ ≤ x)) = true ∨ more = false := by
            rcases hlast with hlast | hlast
            · exact .inr hlast
            · refine .inl ?_
              rw [← hobj, List.getLast?_map]
              cases hget : entries.getLast? with
              | none => rfl
              | some last => simpa [hget] using hlast
          have hwalk := follow_rangeProofBelow hash hnodes hstart _ hverify
            (path := bytesToNibbleList ⟨key.toArray⟩) (List.nil_append _).symm hright
            (fun _ _ => List.nil_prefix) hnodup hvalues (Nat.lt_succ_self _) []
          rw [List.append_nil] at hwalk
          rw [verifyProof_of_follow hash hwalk, ← hobj, List.length_nil]
          -- One path means one key.
          simp only [lookupAt, List.drop_zero, List.find?_map, Option.map_map]
          congr 2
          apply find?_congr
          intro entry _
          simp only [Function.comp_apply, decide_eq_decide]
          exact ⟨fun h => hashBytes_injective (bytesToNibbleList_injective h),
            fun h => by rw [h]⟩
  · simp [hsorted, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hverify

/-- Soundness of a range: an accepted range gives each key between its ends the trie's value.

So the range holds every 32-byte key of the trie there, and no other such key.

When the range check shows no key after the range, each key need only follow the start.

The trie is any plain trie with the root, with distinct keys.

Otherwise the search returns a collision between the two proofs of the key. -/
theorem verifyRange_sound (hash : ByteArray → Hash32) {data : List (ByteArray × ByteArray)}
    {root' start : Hash32} {entries : List (Hash32 × ByteArray)} {proof : List ByteArray}
    {more : Bool}
    (hroot : root hash ⟨false, data⟩ = .ok root') (hkeys : (data.map Prod.fst).Nodup)
    (hverify : verifyRange hash root' start entries proof = .ok more) (key : Hash32)
    (hstart : bytesToNibbleList ⟨start.toArray⟩ ≤ bytesToNibbleList ⟨key.toArray⟩)
    (hlast : more = false ∨ entries.getLast?.all fun last =>
      bytesToNibbleList ⟨key.toArray⟩ ≤ bytesToNibbleList ⟨last.1.toArray⟩) :
    valueAt hash ⟨false, data⟩ ⟨key.toArray⟩ =
        (entries.find? fun entry => entry.1 = key).map Prod.snd ∨
      ∃ pair, findRangeCollision hash ⟨false, data⟩ root' start entries proof key = some pair ∧
        IsCollision hash pair := by
  obtain ⟨honest, hhonest⟩ := getProof_ok hash hroot ⟨key.toArray⟩
  rcases verifyProof_sound hash hroot hhonest hkeys
      (verifyProof_rangeKeyProof hash hverify key hstart hlast) with
    ⟨-, hvalue⟩ | ⟨pair, hfound, hcollision⟩ | ⟨pair, hfound, -⟩
  · exact .inl hvalue.symm
  · exact .inr ⟨pair, by simp only [findRangeCollision, hhonest, hfound], hcollision⟩
  · -- A plain trie has no two keys with one path.
    simp [findPathCollision] at hfound

/-! ## A secured trie -/

/-- Soundness of a range against a secured trie, such as a state or storage trie.

The keys of the range are hashes, since the trie stores each key under its hash.

An accepted range gives each hash between its ends the value of the trie's key with that hash.

When the range check shows no key after the range, each hash need only follow the start.

The keys of the trie must be distinct.

Otherwise the range search returns a collision in the plain trie of the hashed keys.

Or the trie has two keys with one hash, which the key search returns. -/
theorem verifyRange_sound_secured (hash : ByteArray → Hash32) {data : List (ByteArray × ByteArray)}
    {root' start : Hash32} {entries : List (Hash32 × ByteArray)} {proof : List ByteArray}
    {more : Bool}
    (hroot : root hash ⟨true, data⟩ = .ok root') (hkeys : (data.map Prod.fst).Nodup)
    (hverify : verifyRange hash root' start entries proof = .ok more) (key : Hash32)
    (hstart : bytesToNibbleList ⟨start.toArray⟩ ≤ bytesToNibbleList ⟨key.toArray⟩)
    (hlast : more = false ∨ entries.getLast?.all fun last =>
      bytesToNibbleList ⟨key.toArray⟩ ≤ bytesToNibbleList ⟨last.1.toArray⟩) :
    (data.find? fun entry => hash entry.1 = key).map Prod.snd =
        (entries.find? fun entry => entry.1 = key).map Prod.snd ∨
      (∃ pair, findRangeCollision hash
        ⟨false, data.map fun entry => (⟨(hash entry.1).toArray⟩, entry.2)⟩
        root' start entries proof key = some pair ∧ IsCollision hash pair) ∨
      ∃ pair, findPathCollision hash ⟨true, data⟩ = some pair ∧ IsCollision hash pair := by
  cases hcollision : findPathCollision hash ⟨true, data⟩ with
  | some pair => exact .inr (.inr ⟨pair, rfl, findPathCollision_valid hash hcollision⟩)
  | none =>
    -- With no two keys of one hash, the hashed keys are distinct.
    have hhashes := nodup_map_of_findKeyCollision hash _ hkeys
      (by simpa [findPathCollision] using hcollision)
    have hnodup : ((data.map fun entry => ((⟨(hash entry.1).toArray⟩ : ByteArray),
        entry.2)).map Prod.fst).Nodup := by
      simpa [List.map_map, Function.comp_def] using
        nodup_map_of_injective hashBytes_injective hhashes
    rw [root_secured_eq_plain] at hroot
    rcases verifyRange_sound hash hroot hnodup hverify key hstart hlast with hvalue | hfound
    · refine .inl ?_
      rw [← hvalue, valueAt_plain, List.find?_map, Option.map_map]
      -- Two hashes are equal exactly when their bytes are.
      congr 1
      apply find?_congr
      intro entry _
      simp only [Function.comp_apply]
      rw [Bool.eq_iff_iff, sameBytes_iff, decide_eq_true_iff]
      exact ⟨fun h => by rw [h], fun h => hashBytes_injective h⟩
    · exact .inr (.inl hfound)

end EthLib.Execution.Trie
