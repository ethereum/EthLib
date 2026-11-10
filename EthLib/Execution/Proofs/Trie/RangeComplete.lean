module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Trie.Binding
public import EthLib.Execution.Proofs.Trie.Range

/-!
# Proofs: the honest range passes the range check

A peer that holds the trie answers with the keys from the start on, in order, and a proof.

The proof holds the proof of the start and the proof of the last key it sends.

The range check accepts that answer, and it shows whether the trie holds a key after it.

The source is [`caps/snap.md`][snap], sections "AccountRange (0x01)" and "StorageRanges (0x03)".

[snap]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md

The check finds a node of the proof by its hash.

So a node of the proof that shares its hash with a different honest node could mislead it.

When that happens, a search returns the two nodes.

A peer may also send the whole trie from the start with no proof, which the check accepts.

It then shows no key after it.

The entries are values of the trie, so an account is in its full encoding, not the slim one.

A peer must send at least one key when the trie holds one from the start on.

So an empty answer is honest only when the trie holds no key from the start on.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## The search -/

/-- A node of the sent proof and a different node of the honest proofs, with one hash.

It returns the first honest node that has such a partner, with that partner first. -/
def findCrossCollision (hash : ByteArray → Hash32) (honest proof : List ByteArray) :
    Option (ByteArray × ByteArray) :=
  honest.findSome? fun y => (proof.find? fun x => x ≠ y ∧ hash x = hash y).map (·, y)

/-- Every pair that the search returns is a collision. -/
theorem findCrossCollision_valid (hash : ByteArray → Hash32) {honest proof : List ByteArray}
    {pair : ByteArray × ByteArray} (h : findCrossCollision hash honest proof = some pair) :
    IsCollision hash pair := by
  obtain ⟨y, -, hy⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
  have hpred := List.find?_some hx
  simp only [ne_eq, decide_eq_true_eq] at hpred
  exact hpred

/-- The search finds none exactly when no sent node shares a hash with another honest node. -/
theorem findCrossCollision_eq_none_iff (hash : ByteArray → Hash32)
    {honest proof : List ByteArray} :
    findCrossCollision hash honest proof = none ↔
      ∀ y ∈ honest, ∀ x ∈ proof, hash x = hash y → x = y := by
  simp only [findCrossCollision, List.findSome?_eq_none_iff, Option.map_eq_none_iff,
    List.find?_eq_none, ne_eq, decide_eq_true_eq, not_and]
  exact forall₂_congr fun _ _ => forall₂_congr fun _ _ => Decidable.not_imp_not

/-- A hash with no collision makes the search find none. -/
theorem findCrossCollision_of_injective (hash : ByteArray → Hash32)
    (hinjective : Function.Injective hash) (honest proof : List ByteArray) :
    findCrossCollision hash honest proof = none :=
  (findCrossCollision_eq_none_iff hash).mpr fun _ _ _ _ h => hinjective h

/-- The pair that the search returns holds a node of the sent proof, then an honest node. -/
theorem mem_of_findCrossCollision (hash : ByteArray → Hash32) {honest proof : List ByteArray}
    {pair : ByteArray × ByteArray} (h : findCrossCollision hash honest proof = some pair) :
    pair.1 ∈ proof ∧ pair.2 ∈ honest := by
  obtain ⟨y, hmem, hy⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
  exact ⟨List.mem_of_find?_eq_some hx, hmem⟩

/-! ## Where a subtree lies -/

/-- Whether an entry lies between the two ends of the range. -/
private def inRange (left : List Nibble) (right : Option (List Nibble))
    (entry : List Nibble × ByteArray) : Bool :=
  decide (left ≤ entry.1) && right.all fun last => decide (entry.1 ≤ last)

/-- Every path below a subtree inside the range lies between its two ends. -/
private theorem inRange_of_rangePlace_inside {left pre : List Nibble}
    {right : Option (List Nibble)} (h : rangePlace left right pre = .inside) (c : List Nibble)
    (value : ByteArray) :
    inRange left right (pre ++ c, value) = true ∧
      (right.any fun last => decide (last < pre ++ c)) = false := by
  obtain ⟨hleft, hright⟩ := between_of_rangePlace_inside h c
  cases right with
  | none => simp [inRange, List.le_of_lt hleft]
  | some last =>
    have hbelow := hright last rfl
    simp [inRange, List.le_of_lt hleft, List.le_of_lt hbelow, List.lt_asymm hbelow]

/-! ## The nodes that the check reads -/

/-- The absent node is held as the empty byte string. -/
private theorem encodeInternalNode_none (hash : ByteArray → Hash32) :
    encodeInternalNode hash none = .ok (.bytes .empty) := rfl

/-- A node is never held as the empty byte string. -/
private theorem encodeInternalNode_some_ne_empty {hash : ByteArray → Hash32}
    {node : InternalNode} {reference : Item}
    (h : encodeInternalNode hash (some node) = .ok reference) : reference ≠ .bytes .empty := by
  obtain ⟨encoded, -, rfl⟩ := encode_of_encodeInternalNode h
  split
  · exact unencoded_some_ne_empty node
  · intro h
    have := congrArg (fun item => match item with | .bytes b => b.size | .list _ => 0) h
    simp [size_hashBytes, ByteArray.size_empty] at this

/-! ## Paths below a prefix -/

/-- A path starts with a prefix and one more nibble exactly when it has both. -/
private theorem isPrefixOf_append_singleton (nibble : Nibble) :
    (pre key : List Nibble) →
      (pre ++ [nibble]).isPrefixOf key =
        (pre.isPrefixOf key && decide (key[pre.length]? = some nibble))
  | [], [] => rfl
  | [], k :: rest => by
    simp only [List.nil_append, List.isPrefixOf, List.length_nil, List.getElem?_cons_zero,
      Option.some.injEq, Bool.true_and, Bool.and_true]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨Eq.symm, Eq.symm⟩
  | _ :: _, [] => rfl
  | a :: pre, k :: rest => by
    simp only [List.cons_append, List.isPrefixOf, isPrefixOf_append_singleton nibble pre rest,
      List.length_cons, List.getElem?_cons_succ, Bool.and_assoc]

/-- The keys of one child of a branch are the keys that start with its path. -/
private theorem filter_branch (trie : List (List Nibble × ByteArray)) (pre : List Nibble)
    (nibble : Nibble) :
    ((trie.filter fun entry => pre.isPrefixOf entry.1).filter fun entry =>
      decide (entry.1[pre.length]? = some nibble)) =
      trie.filter fun entry => (pre ++ [nibble]).isPrefixOf entry.1 := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro entry _
  rw [isPrefixOf_append_singleton, Bool.and_comm]

/-- Keys that all continue a prefix with a segment are the keys that start with both. -/
private theorem filter_extension (trie : List (List Nibble × ByteArray)) (pre segment : List Nibble)
    (h : ∀ entry ∈ trie.filter (fun entry => pre.isPrefixOf entry.1),
      (pre ++ segment).isPrefixOf entry.1 = true) :
    trie.filter (fun entry => (pre ++ segment).isPrefixOf entry.1) =
      trie.filter fun entry => pre.isPrefixOf entry.1 := by
  have hsplit : trie.filter (fun entry => (pre ++ segment).isPrefixOf entry.1) =
      (trie.filter fun entry => pre.isPrefixOf entry.1).filter
        fun entry => (pre ++ segment).isPrefixOf entry.1 := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro entry _
    by_cases hlong : (pre ++ segment).isPrefixOf entry.1 = true
    · have hshort : pre.isPrefixOf entry.1 = true := List.isPrefixOf_iff_prefix.mpr
        ((List.prefix_append pre segment).trans (List.isPrefixOf_iff_prefix.mp hlong))
      simp [hlong, hshort]
    · simp [hlong]
  rw [hsplit, List.filter_eq_self.mpr h]

/-- The keys after the range below a branch are those below one of its children. -/
private theorem any_branch (sub : List (List Nibble × ByteArray)) (level : Nat)
    (p : List Nibble × ByteArray → Bool) (hlong : ∀ entry ∈ sub, level < entry.1.length) :
    ((List.finRange 16).map fun nibble =>
      (sub.filter fun entry => decide (entry.1[level]? = some nibble)).any p).any id =
      sub.any p := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_map, List.any_eq_true, List.mem_finRange, true_and, Function.comp_apply,
    id_eq, List.mem_filter]
  constructor
  · rintro ⟨_, entry, ⟨hmem, _⟩, hp⟩
    exact ⟨entry, hmem, hp⟩
  · rintro ⟨entry, hmem, hp⟩
    refine ⟨entry.1[level]'(hlong entry hmem), entry, ⟨hmem, ?_⟩, hp⟩
    simp

/-- A node built from some keys has a key. -/
private theorem exists_mem_of_patricialize_some {hash : ByteArray → Hash32}
    {sub : List (List Nibble × ByteArray)} {level : Nat} {node : InternalNode}
    (h : patricialize hash sub level = .ok (some node)) : ∃ entry, entry ∈ sub := by
  cases sub with
  | nil =>
    rw [show patricialize hash [] level = .ok none from patricializeAux_nil hash _ _] at h
    cases h
  | cons entry _ => exact ⟨entry, List.mem_cons_self⟩

/-- Below a branch, every key goes on past it, when all keys have one length. -/
private theorem length_lt_of_patricialize_branch {hash : ByteArray → Hash32}
    {sub : List (List Nibble × ByteArray)} {pre : List Nibble} {subnodes : Vector Item 16}
    {value : ByteArray} {n : Nat}
    (hnode : patricialize hash sub pre.length = .ok (some (.branch subnodes value)))
    (hprefix : ∀ entry ∈ sub, pre <+: entry.1) (hlength : ∀ entry ∈ sub, entry.1.length = n)
    (hnodup : (sub.map Prod.fst).Nodup) :
    ∀ entry ∈ sub, pre.length < entry.1.length := by
  intro entry hmem
  refine Nat.lt_of_not_le fun hshort => ?_
  -- A key that ends here is the path itself, and so is every key, so there is one key.
  have hall : ∀ key ∈ sub.map Prod.fst, key = pre := by
    intro key hkey
    obtain ⟨other, hother, rfl⟩ := List.mem_map.mp hkey
    have h₁ := hprefix other hother
    refine (h₁.eq_of_length ?_).symm
    have := h₁.length_le
    have := hlength other hother
    have := hlength entry hmem
    have := (hprefix entry hmem).length_le
    omega
  have hone := length_le_one_of_nodup _ hnodup hall
  rw [List.length_map] at hone
  match sub, hone with
  | [], _ => cases hnode
  | [_], _ => cases hnode

/-! ## The induction along the check -/

/-- The check accepts the honest range below one subtree of the trie.

The entries are those of the trie below the subtree that lie in the range.

The reference holds the node of the trie there, as its parent holds it, or by hash at the root.

On the path of an end, the honest nodes hold the nodes that the proof of that end holds below.

Each honest node is in the proof, and no other node of the proof shares its hash.

The check then shows whether the trie holds a key after the range below the subtree. -/
private theorem checkSubtree_honest (hash : ByteArray → Hash32) {honest proof : List ByteArray}
    (hhonest : ∀ y ∈ honest, y ∈ proof)
    (hcoll : ∀ y ∈ honest, ∀ x ∈ proof, hash x = hash y → x = y)
    {trie : List (List Nibble × ByteArray)} {left : List Nibble} {right : Option (List Nibble)}
    (hlength : ∀ entry ∈ trie, entry.1.length = left.length)
    (hrightLength : ∀ last, right = some last → last.length = left.length)
    (hleft : ∀ last, right = some last → left ≤ last)
    (hnodup : (trie.map Prod.fst).Nodup) :
    (fuel : Nat) → {reference : Item} → {pre : List Nibble} → {node : Option InternalNode} →
      left.length + 1 < fuel + pre.length → pre.length ≤ left.length + 1 →
      patricialize hash (trie.filter fun entry => pre.isPrefixOf entry.1) pre.length = .ok node →
      (encodeInternalNode hash node = .ok reference ∨ (pre = [] ∧ ∃ encoded,
        encode (unencoded node) = .ok encoded ∧ encoded ∈ honest ∧
        reference = .bytes ⟨(hash encoded).toArray⟩)) →
      (∀ path, (path = left ∨ right = some path) → pre.isPrefixOf path = true →
        (∀ encoded, encode (unencoded node) = .ok encoded → 32 ≤ encoded.size →
          encoded ∈ honest) ∧
        ∃ fuel' below, (path.drop pre.length).length < fuel' ∧
          proofBelow hash fuel' (trie.filter fun entry => pre.isPrefixOf entry.1) pre.length
            (path.drop pre.length) = .ok below ∧ ∀ x ∈ below, x ∈ honest) →
      checkSubtree hash (proof.map fun encoded => (hash encoded, encoded)) left right fuel
          reference pre
          ((trie.filter fun entry => pre.isPrefixOf entry.1).filter (inRange left right)) =
        .ok ((trie.filter fun entry => pre.isPrefixOf entry.1).any fun entry =>
          right.any fun last => decide (last < entry.1))
  | 0, _, pre, _, hfuel, hpre, _, _, _ => by omega
  | fuel + 1, reference, pre, node, hfuel, hpre, hnode, hheld, hpaths => by
    generalize hsub : (trie.filter fun entry => pre.isPrefixOf entry.1) = sub at hnode hpaths ⊢
    have hsubPrefix : ∀ entry ∈ sub, pre <+: entry.1 := by
      intro entry hmem
      rw [← hsub] at hmem
      exact List.isPrefixOf_iff_prefix.mp (List.mem_filter.mp hmem).2
    -- Away from the ends, the reference is how the parent holds the node.
    have hheld' : rangePlace left right pre ≠ .boundary →
        encodeInternalNode hash node = .ok reference := by
      intro hplace
      rcases hheld with hheld | ⟨rfl, -⟩
      · exact hheld
      · simp [rangePlace] at hplace
    rw [checkSubtree]
    cases hplace : rangePlace left right pre with
    | before =>
      -- Every key here is below the first end, so none is in the range or after it.
      have hbelow : ∀ entry ∈ sub, entry.1 < left := by
        intro entry hmem
        obtain ⟨c, hc⟩ := hsubPrefix entry hmem
        rw [← hc]
        exact append_lt_of_rangePlace_before hplace c
      have hnone : sub.filter (inRange left right) = [] := by
        refine List.filter_eq_nil_iff.mpr fun entry hmem => ?_
        simp [inRange, List.not_le.mpr (hbelow entry hmem)]
      have hfalse : (sub.any fun entry => right.any fun last => decide (last < entry.1)) =
          false := by
        refine List.any_eq_false.mpr fun entry hmem => ?_
        cases hright : right with
        | none => simp
        | some last =>
          have := hleft last hright
          simp only [Option.any_some, decide_eq_true_eq]
          exact fun hlast => this (List.lt_trans hlast (hbelow entry hmem))
      simp only [hnone, hfalse, List.isEmpty_nil, ↓reduceIte]
    | after =>
      -- Every key here is above the last end, so none is in the range.
      have hafter : ∀ entry ∈ sub, ∃ last, right = some last ∧ last < entry.1 := by
        intro entry hmem
        obtain ⟨c, hc⟩ := hsubPrefix entry hmem
        rw [← hc]
        exact lt_append_of_rangePlace_after hplace c
      have hnone : sub.filter (inRange left right) = [] := by
        refine List.filter_eq_nil_iff.mpr fun entry hmem => ?_
        obtain ⟨last, hright, hlast⟩ := hafter entry hmem
        simp [inRange, hright, List.not_le.mpr hlast]
      have hheld := hheld' (by simp [hplace])
      simp only [hnone, List.isEmpty_nil, ↓reduceIte, Except.ok.injEq]
      cases node with
      | none =>
        cases built_of_patricialize hash hnode with
        | none hobj =>
          subst hobj
          rw [encodeInternalNode_none] at hheld
          cases hheld
          simp
      | some node =>
        -- A node holds a key, and that key is after the range.
        have hne := encodeInternalNode_some_ne_empty hheld
        obtain ⟨entry, hmem⟩ := exists_mem_of_patricialize_some hnode
        obtain ⟨last, hright, hlast⟩ := hafter entry hmem
        rw [bne_iff_ne.mpr hne]
        exact (List.any_eq_true.mpr ⟨entry, hmem, by simp [hright, hlast]⟩).symm
    | inside =>
      -- Every key here is in the range, so the entries are the keys of the subtree.
      have hinside : ∀ entry ∈ sub, inRange left right entry = true ∧
          (right.any fun last => decide (last < entry.1)) = false := by
        intro entry hmem
        obtain ⟨c, hc⟩ := hsubPrefix entry hmem
        obtain ⟨key, value⟩ := entry
        dsimp only at hc ⊢
        subst hc
        exact inRange_of_rangePlace_inside hplace c value
      have hall : sub.filter (inRange left right) = sub :=
        List.filter_eq_self.mpr fun entry hmem => (hinside entry hmem).1
      have hfalse : (sub.any fun entry => right.any fun last => decide (last < entry.1)) =
          false := List.any_eq_false.mpr fun entry hmem => by simp [(hinside entry hmem).2]
      have hheld := hheld' (by simp [hplace])
      simp [hall, hfalse, hnode, hheld, Except.mapError, Bind.bind, Except.bind]
    | boundary =>
      obtain ⟨path, hend, hprefix⟩ := exists_end_of_rangePlace_boundary hplace
      obtain ⟨hself, fuel', below, hfuel', hbelow, hbelowMem⟩ := hpaths path hend hprefix
      have hpathLength : path.length = left.length := by
        rcases hend with rfl | hright
        · rfl
        · exact hrightLength path hright
      have hpreLength : pre.length ≤ left.length := by
        rw [← hpathLength]
        exact (List.isPrefixOf_iff_prefix.mp hprefix).length_le
      -- The check reads the node of the trie here.
      have hlookup : lookupNode (proof.map fun encoded => (hash encoded, encoded)) reference =
          .ok (unencoded node) := by
        rcases hheld with hheld | ⟨-, encoded, hencode, hmem, rfl⟩
        · obtain ⟨encoded, hencode, rfl⟩ := encode_of_encodeInternalNode hheld
          split
          · exact lookupNode_unencoded _ node
          · rename_i hlong
            have hmem := hself encoded hencode (by omega)
            exact lookupNode_hash hash hencode (hhonest _ hmem) (hcoll _ hmem)
        · exact lookupNode_hash hash hencode (hhonest _ hmem) (hcoll _ hmem)
      simp only [hlookup, Except.mapError, Bind.bind, Except.bind]
      cases node with
      | none =>
        cases built_of_patricialize hash hnode with
        | none hobj =>
          subst hobj
          rfl
      | some node =>
        simp only [unencoded_some_ne_empty node, ↓reduceIte]
        have hsubNodup : (sub.map Prod.fst).Nodup := by
          rw [← hsub]
          exact hnodup.sublist (List.filter_sublist.map _)
        have hsubLength : ∀ entry ∈ sub, entry.1.length = left.length := fun entry hmem =>
          hlength entry (List.mem_filter.mp (hsub ▸ hmem)).1
        cases built_of_patricialize hash hnode with
        | leaf key value hobj =>
          subst hobj
          have hkey : pre ++ key.drop pre.length = key := by
            obtain ⟨t, ht⟩ := hsubPrefix (key, value) List.mem_cons_self
            simp only at ht
            subst ht
            simp
          simp only [decodeNode_leaf, hkey]
          by_cases hin : inRange left right (key, value) = true
          · -- The key is in the range: it is the one entry, and no key after it is here.
            have hin' := hin
            simp only [inRange] at hin'
            rw [ite_eq_left_of_eq_true _ _ (eq_true hin')]
            simp only [List.filter_cons_of_pos hin, List.filter_nil, ↓reduceIte, pure,
              Except.pure, List.any_cons, List.any_nil, Bool.or_false]
            cases hright : right with
            | none => rfl
            | some last =>
              rw [hright] at hin'
              simp only [Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at hin'
              simp [List.not_lt.mpr hin'.2]
          · -- The key is outside the range: no entry, and the key may be after it.
            have hin' := hin
            simp only [inRange] at hin'
            rw [ite_eq_right_of_eq_false _ _ (eq_false hin')]
            simp [List.filter_cons_of_neg hin, pure, Except.pure]
        | extension keySegment subnode child hsegment hcommon hchild hsubnode =>
          simp only [decodeNode_extension hsegment]
          -- Every key here continues with the segment.
          have hdeeper : ∀ entry ∈ sub, (pre ++ keySegment).isPrefixOf entry.1 = true := by
            intro entry hmem
            obtain ⟨t, ht⟩ := hsubPrefix entry hmem
            have htake := hcommon entry hmem
            rw [← ht, List.drop_left] at htake
            rw [← ht, List.isPrefixOf_iff_prefix, List.prefix_append_right_inj]
            exact htake ▸ List.take_prefix _ _
          rw [ite_eq_left_of_eq_true _ _ (eq_true (List.all_eq_true.mpr fun entry hmem =>
            hdeeper entry (List.mem_filter.mp hmem).1))]
          have hsub' : trie.filter (fun entry => (pre ++ keySegment).isPrefixOf entry.1) = sub := by
            rw [filter_extension trie pre keySegment (by rw [hsub]; exact hdeeper), hsub]
          obtain ⟨entry, hmem⟩ := exists_mem_of_patricialize_some hnode
          have hsegmentLength : pre.length + keySegment.length ≤ left.length := by
            have h₁ := congrArg List.length (hcommon entry hmem)
            have h₂ := hsubLength entry hmem
            simp only [List.length_take, List.length_drop] at h₁
            omega
          have hpositive : 0 < keySegment.length := List.length_pos_iff.mpr hsegment
          have ih := checkSubtree_honest hash hhonest hcoll hlength hrightLength hleft hnodup fuel
            (reference := subnode) (pre := pre ++ keySegment) (node := child)
            (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
            (by rw [hsub', List.length_append]; exact hchild) (.inl hsubnode) (by
              intro path' hend' hprefix'
              have hshort : pre.isPrefixOf path' = true := List.isPrefixOf_iff_prefix.mpr
                ((List.prefix_append pre keySegment).trans
                  (List.isPrefixOf_iff_prefix.mp hprefix'))
              obtain ⟨-, fuel'', below'', hfuel'', hbelow'', hmem''⟩ :=
                hpaths path' hend' hshort
              obtain ⟨encoded, hencode, -⟩ := encode_of_encodeInternalNode hsubnode
              obtain ⟨u, hu⟩ := List.isPrefixOf_iff_prefix.mp hprefix'
              have hfollow : keySegment = (path'.drop pre.length).take keySegment.length := by
                rw [← hu, List.append_assoc, List.drop_left, List.take_left]
              obtain ⟨f, rfl⟩ : ∃ f, fuel'' = f + 1 := ⟨fuel'' - 1, by omega⟩
              obtain ⟨belowChild, hchildBelow, rfl⟩ :=
                proofBelow_extension hnode hchild hencode hfollow hbelow''
              rw [hsub']
              refine ⟨fun encoded' hencode' hlong => ?_, f, belowChild, ?_, ?_,
                fun x hx => hmem'' x (List.mem_append_right _ hx)⟩
              · rw [hencode] at hencode'
                cases hencode'
                exact hmem'' _ (by simp [Nat.not_lt.mpr hlong])
              · have hlen := congrArg List.length hu
                simp only [List.length_drop, List.length_append] at hfuel'' hlen ⊢
                omega
              · rw [List.length_append, ← List.drop_drop]
                exact hchildBelow)
          rw [hsub'] at ih
          exact ih
        | branch subnodes hchildren value hvalue =>
          simp only [decodeNode_branch]
          -- Every key goes on below the branch, so the branch holds no value.
          have hlong := length_lt_of_patricialize_branch hnode hsubPrefix hsubLength hsubNodup
          have hvalue0 : value.size = 0 := by
            have hnone : sub.filter (fun entry => decide (entry.1.length = pre.length)) = [] :=
              List.filter_eq_nil_iff.mpr fun entry hmem => by
                simpa using Nat.ne_of_gt (hlong entry hmem)
            have hlast := foldl_last (fun entry : List Nibble × ByteArray =>
              decide (entry.1.length = pre.length)) Prod.snd sub .empty
            rw [hnone] at hlast
            simp only [decide_eq_true_eq] at hlast
            rw [hvalue]
            exact (congrArg ByteArray.size hlast).trans rfl
          have hall : ((sub.filter (inRange left right)).all fun x =>
              decide (pre.length < x.fst.length)) = true :=
            List.all_eq_true.mpr fun entry hmem =>
              decide_eq_true (hlong entry (List.mem_filter.mp hmem).1)
          have hchildOk : ∀ nibble : Nibble,
              checkSubtree hash (proof.map fun encoded => (hash encoded, encoded)) left right fuel
                subnodes[nibble] (pre ++ [nibble])
                ((sub.filter (inRange left right)).filter fun x =>
                  decide (x.fst[pre.length]? = some nibble)) =
              .ok ((sub.filter fun entry => decide (entry.1[pre.length]? = some nibble)).any
                fun entry => right.any fun last => decide (last < entry.1)) := by
            intro nibble
            obtain ⟨child, hchild, hsubnode⟩ := hchildren nibble
            have hchild' : patricialize hash
                (sub.filter fun entry => decide (entry.1[pre.length]? = some nibble))
                (pre.length + 1) = .ok child := hchild
            have hsub' : trie.filter (fun entry => (pre ++ [nibble]).isPrefixOf entry.1) =
                sub.filter fun entry => decide (entry.1[pre.length]? = some nibble) := by
              rw [← filter_branch, hsub]
            have hentries : ((sub.filter (inRange left right)).filter fun x =>
                decide (x.fst[pre.length]? = some nibble)) =
                (sub.filter fun entry => decide (entry.1[pre.length]? = some nibble)).filter
                  (inRange left right) := by
              rw [List.filter_filter, List.filter_filter]
              apply List.filter_congr
              intro entry _
              exact Bool.and_comm _ _
            have ih := checkSubtree_honest hash hhonest hcoll hlength hrightLength hleft hnodup fuel
              (reference := subnodes[nibble]) (pre := pre ++ [nibble]) (node := child)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by rw [hsub', List.length_append, List.length_singleton]; exact hchild')
              (.inl hsubnode) (by
                intro path' hend' hprefix'
                have hsplit := isPrefixOf_append_singleton nibble pre path'
                rw [hprefix', eq_comm, Bool.and_eq_true, decide_eq_true_eq] at hsplit
                obtain ⟨hshort, hnext⟩ := hsplit
                obtain ⟨-, fuel'', below'', hfuel'', hbelow'', hmem''⟩ :=
                  hpaths path' hend' hshort
                obtain ⟨encoded, hencode, -⟩ := encode_of_encodeInternalNode hsubnode
                have hdrop : path'.drop pre.length = nibble :: path'.drop (pre.length + 1) :=
                  (drop_eq_cons_iff _ _ _ _).mpr ⟨hnext, rfl⟩
                rw [hdrop] at hbelow'' hfuel''
                obtain ⟨f, rfl⟩ : ∃ f, fuel'' = f + 1 := ⟨fuel'' - 1, by omega⟩
                obtain ⟨belowChild, hchildBelow, rfl⟩ :=
                  proofBelow_branch hnode hchild' hencode hbelow''
                rw [hsub']
                refine ⟨fun encoded' hencode' hlong => ?_, f, belowChild, ?_, ?_,
                  fun x hx => hmem'' x (List.mem_append_right _ hx)⟩
                · rw [hencode] at hencode'
                  cases hencode'
                  exact hmem'' _ (by simp [Nat.not_lt.mpr hlong])
                · simp only [List.length_cons] at hfuel''
                  simp only [List.length_append, List.length_singleton]
                  omega
                · simpa only [List.length_append, List.length_singleton] using hchildBelow)
            rw [hsub'] at ih
            rw [hentries]
            exact ih
          rw [EthLib.Base.mapM_eq_ok_map fun nibble _ => hchildOk nibble]
          simp only [hvalue0, ne_eq, not_true_eq_false, ↓reduceIte, hall]
          rw [any_branch sub pre.length _ hlong]
          rfl

/-- In a list sorted by key, the first entries are those up to the last of them. -/
private theorem filter_take_eq {α : Type} (key : α → List Nibble) {l : List α}
    (hpairwise : l.Pairwise fun a b => key a < key b) {count : Nat} {last : α}
    (hlast : (l.take count).getLast? = some last) :
    l.filter (fun entry => decide (key entry ≤ key last)) = l.take count := by
  obtain ⟨front, hfront⟩ := List.getLast?_eq_some_iff.mp hlast
  have hsplit := List.take_append_drop count l
  rw [hfront] at hsplit
  rw [← hsplit] at hpairwise
  conv => lhs; rw [← List.take_append_drop count l]
  rw [List.filter_append, hfront]
  have hrest : (l.drop count).filter (fun entry => decide (key entry ≤ key last)) = [] := by
    refine List.filter_eq_nil_iff.mpr fun entry hmem => ?_
    have := (List.pairwise_append.mp hpairwise).2.2 last
      (List.mem_append_right _ List.mem_cons_self) entry hmem
    simpa using List.not_le.mpr this
  rw [hrest, List.append_nil]
  refine List.filter_eq_self.mpr fun entry hmem => ?_
  rcases List.mem_append.mp hmem with hmem | hmem
  · have := (List.pairwise_append.mp (List.pairwise_append.mp hpairwise).1).2.2 entry hmem
      last List.mem_cons_self
    simpa using List.le_of_lt this
  · rw [List.mem_singleton.mp hmem]
    simp

/-! ## The check from the root -/

/-- The check accepts the honest range from the root, when honest nodes hold the proof of each end.

The entries are the keys of the trie in the range.

Each honest node is in the proof, and no other node of the proof shares its hash. -/
private theorem checkSubtree_root (hash : ByteArray → Hash32) {data : List (Hash32 × ByteArray)}
    {root' : Hash32} {honest proof : List ByteArray} (hhonest : ∀ y ∈ honest, y ∈ proof)
    (hcoll : ∀ y ∈ honest, ∀ x ∈ proof, hash x = hash y → x = y) (start : Hash32)
    {right : Option (List Nibble)}
    (hroot : root hash ⟨false, data.map fun entry => (⟨entry.1.toArray⟩, entry.2)⟩ = .ok root')
    (hsorted : strictlyIncreasing
      (data.map fun entry => bytesToNibbleList ⟨entry.1.toArray⟩) = true)
    (hleft : ∀ last, right = some last → bytesToNibbleList ⟨start.toArray⟩ ≤ last)
    (hproofs : ∀ path, (path = bytesToNibbleList ⟨start.toArray⟩ ∨ right = some path) →
      ∃ key : Hash32, path = bytesToNibbleList ⟨key.toArray⟩ ∧ ∃ single,
        getProof hash ⟨false, data.map fun entry => (⟨entry.1.toArray⟩, entry.2)⟩
          ⟨key.toArray⟩ = .ok single ∧ ∀ x ∈ single, x ∈ honest) :
    checkSubtree hash (proof.map fun encoded => (hash encoded, encoded))
        (bytesToNibbleList ⟨start.toArray⟩) right
        ((bytesToNibbleList ⟨start.toArray⟩).length + 2) (.bytes ⟨root'.toArray⟩) []
        ((data.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)).filter
          (inRange (bytesToNibbleList ⟨start.toArray⟩) right)) =
      .ok ((data.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)).any
        fun entry => right.any fun last => decide (last < entry.1)) := by
  generalize hleftPath : bytesToNibbleList ⟨start.toArray⟩ = left at hleft hproofs ⊢
  have hkeyLength : ∀ key : Hash32, (bytesToNibbleList ⟨key.toArray⟩).length = 64 := by
    intro key
    rw [length_bytesToNibbleList, size_hashBytes]
  have hpaths := nodup_toArray_of_strictlyIncreasing hsorted
  -- The trie of the entries, as paths and values.
  have htrie : ((data.map fun entry => ((⟨entry.1.toArray⟩ : ByteArray), entry.2)).map
      fun entry => (keyPath hash false entry.1, entry.2)) =
      data.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2) := by
    simp [List.map_map, Function.comp_def, keyPath_eq]
  have hkeys : (((data.map fun entry => ((⟨entry.1.toArray⟩ : ByteArray), entry.2)).map
      fun entry => keyPath hash false entry.1)).Nodup := by
    simp only [keyPath_eq, Bool.false_eq_true, ↓reduceIte]
    rw [show (fun entry : ByteArray × ByteArray => bytesToNibbleList entry.fst) =
      bytesToNibbleList ∘ Prod.fst from rfl, ← List.map_map]
    exact nodup_map_of_injective (fun _ _ h => bytesToNibbleList_injective h) hpaths
  generalize htrie' : (data.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)) =
    trie at htrie
  obtain ⟨key, -, single, hsingle, hsingleMem⟩ := hproofs left (.inl rfl)
  obtain ⟨rootNode, encoded, below, hnode, hencode, hroot', rfl, -, -, -⟩ :=
    honest_root hroot hsingle hkeys
  rw [htrie] at hnode
  subst hroot'
  have hfilter : (trie.filter fun entry => ([] : List Nibble).isPrefixOf entry.1) = trie :=
    List.filter_eq_self.mpr fun _ _ => rfl
  have ih := checkSubtree_honest hash hhonest hcoll (trie := trie) (left := left) (right := right)
    (by
      intro entry hmem
      rw [← htrie'] at hmem
      obtain ⟨original, -, rfl⟩ := List.mem_map.mp hmem
      rw [← hleftPath, hkeyLength, hkeyLength])
    (by
      intro last hlast
      obtain ⟨key, rfl, -⟩ := hproofs last (.inr hlast)
      rw [← hleftPath, hkeyLength, hkeyLength])
    hleft
    (by
      rw [← htrie', List.map_map]
      exact nodup_of_strictlyIncreasing hsorted)
    (left.length + 2) (reference := .bytes ⟨(hash encoded).toArray⟩) (pre := [])
    (node := rootNode) (by simp) (by simp) (by rw [hfilter]; exact hnode)
    (.inr ⟨rfl, encoded, hencode, hsingleMem _ List.mem_cons_self, rfl⟩) (by
      intro path hend _
      obtain ⟨key, rfl, single', hsingle', hsingleMem'⟩ := hproofs path hend
      obtain ⟨rootNode', encoded', below', hnode', hencode', -, rfl, hbelow', -, -⟩ :=
        honest_root hroot hsingle' hkeys
      rw [htrie, hnode] at hnode'
      cases hnode'
      rw [hencode] at hencode'
      cases hencode'
      refine ⟨fun encoded' h _ => ?_, (bytesToNibbleList ⟨key.toArray⟩).length + 1, below', ?_, ?_,
        ?_⟩
      · rw [hencode] at h
        cases h
        exact hsingleMem' _ List.mem_cons_self
      · simp
      · rw [hfilter, List.length_nil, List.drop_zero]
        rw [htrie] at hbelow'
        simpa only [keyPath_eq, Bool.false_eq_true, ↓reduceIte] using hbelow'
      · exact fun x hx => hsingleMem' x (List.mem_cons_of_mem _ hx))
  rw [hfilter] at ih
  exact ih

/-- Completeness of a range: the first keys of the trie from the start pass the range check.

The keys of the trie are 32-byte hashes, listed in increasing order.

Any trie of distinct keys can be listed so, with the same root.

The proof holds the proof of the start and the proof of the last key, in any order.

The check shows a key after the range exactly when the trie holds one.

Otherwise a node of the proof shares its hash with a different honest node.

The search returns the two. -/
theorem verifyRange_complete (hash : ByteArray → Hash32) {data : List (Hash32 × ByteArray)}
    {root' : Hash32} (start : Hash32) (count : Nat) {last : Hash32 × ByteArray}
    {first second proof : List ByteArray}
    (hroot : root hash ⟨false, data.map fun entry => (⟨entry.1.toArray⟩, entry.2)⟩ = .ok root')
    (hsorted : strictlyIncreasing
      (data.map fun entry => bytesToNibbleList ⟨entry.1.toArray⟩) = true)
    (hlast : ((data.filter fun entry => bytesToNibbleList ⟨start.toArray⟩ ≤
      bytesToNibbleList ⟨entry.1.toArray⟩).take count).getLast? = some last)
    (hfirst : getProof hash ⟨false, data.map fun entry => (⟨entry.1.toArray⟩, entry.2)⟩
      ⟨start.toArray⟩ = .ok first)
    (hsecond : getProof hash ⟨false, data.map fun entry => (⟨entry.1.toArray⟩, entry.2)⟩
      ⟨last.1.toArray⟩ = .ok second) (hproof : ∀ x ∈ first ++ second, x ∈ proof) :
    verifyRange hash root' start
        ((data.filter fun entry => bytesToNibbleList ⟨start.toArray⟩ ≤
          bytesToNibbleList ⟨entry.1.toArray⟩).take count) proof =
        .ok (data.any fun entry =>
          bytesToNibbleList ⟨last.1.toArray⟩ < bytesToNibbleList ⟨entry.1.toArray⟩) ∨
      ∃ pair, findCrossCollision hash (first ++ second) proof = some pair ∧
        IsCollision hash pair := by
  cases hfind : findCrossCollision hash (first ++ second) proof with
  | some pair => exact .inr ⟨pair, rfl, findCrossCollision_valid hash hfind⟩
  | none =>
    refine .inl ?_
    have hcoll := (findCrossCollision_eq_none_iff hash).mp hfind
    generalize hleftPath : bytesToNibbleList ⟨start.toArray⟩ = left at hlast ⊢
    generalize hrange : (data.filter fun entry =>
      decide (left ≤ bytesToNibbleList ⟨entry.1.toArray⟩)) = range at hlast
    generalize hsent : range.take count = sent at hlast
    have hpairwise : data.Pairwise fun a b =>
        bytesToNibbleList ⟨a.1.toArray⟩ < bytesToNibbleList ⟨b.1.toArray⟩ :=
      List.pairwise_map.mp ((strictlyIncreasing_iff_pairwise _).mp hsorted)
    have hsentSub : sent.Sublist data := by
      rw [← hsent, ← hrange]
      exact (List.take_sublist _ _).trans List.filter_sublist
    have hfull : ∀ entry ∈ data, entry.2.size ≠ 0 := by
      intro entry hmem hsize
      rw [root_emptyValue hash _ ⟨(⟨entry.1.toArray⟩, entry.2), List.mem_map_of_mem hmem, hsize⟩]
        at hroot
      cases hroot
    have hstart : ∀ entry ∈ sent, left ≤ bytesToNibbleList ⟨entry.1.toArray⟩ := by
      intro entry hmem
      rw [← hsent, ← hrange] at hmem
      simpa using (List.mem_filter.mp (List.mem_of_mem_take hmem)).2
    have hlastMem : last ∈ sent := List.mem_of_getLast? hlast
    rw [← hleftPath] at hstart
    -- The proof holds the proof of the start, which has a node.
    have hne : proof ≠ [] := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (getProof_ne_nil hfirst)
      exact List.ne_nil_of_mem (hproof x (List.mem_append_left _ hx))
    rw [verifyRange_eq hash root' start sent proof
        ((strictlyIncreasing_iff_pairwise _).mpr
          (List.pairwise_map.mpr (hpairwise.sublist hsentSub)))
        hstart (fun entry hmem => hfull entry (hsentSub.subset hmem)),
      ite_eq_right_of_eq_false _ _ (eq_false (by simp [hne]))]
    rw [hleftPath] at hstart ⊢
    have h := checkSubtree_root hash hproof hcoll start
      (right := some (bytesToNibbleList ⟨last.1.toArray⟩)) hroot hsorted
      (by
        rintro _ ⟨⟩
        rw [hleftPath]
        exact hstart last hlastMem)
      (by
        intro path hpath
        rcases hpath with rfl | hpath
        · exact ⟨start, rfl, first, hfirst, fun _ hx => List.mem_append_left _ hx⟩
        · cases hpath
          exact ⟨last.1, rfl, second, hsecond, fun _ hx => List.mem_append_right _ hx⟩)
    rw [hleftPath] at h
    -- The trie's keys in the range are the keys sent.
    have hentries : (data.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)).filter
        (inRange left (some (bytesToNibbleList ⟨last.1.toArray⟩))) =
        sent.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2) := by
      rw [List.filter_map, ← hsent, ← filter_take_eq (fun entry : Hash32 × ByteArray =>
          bytesToNibbleList ⟨entry.1.toArray⟩)
        (hpairwise.sublist (hrange ▸ List.filter_sublist)) (hsent ▸ hlast), ← hrange,
        List.filter_filter]
      congr 1
      apply List.filter_congr
      intro entry _
      simp [inRange, Bool.and_comm]
    rw [hentries] at h
    simp only [List.getLast?_map, hlast, Option.map_some]
    rw [h, List.any_map]
    rfl

/-- Completeness of an empty range: with no key from the start on, the proof of the start passes.

The proof may hold other nodes too.

The check then shows no key after the range.

Otherwise a node of the proof shares its hash with a different honest node.

The search returns the two. -/
theorem verifyRange_complete_nil (hash : ByteArray → Hash32) {data : List (Hash32 × ByteArray)}
    {root' : Hash32} (start : Hash32) {first proof : List ByteArray}
    (hroot : root hash ⟨false, data.map fun entry => (⟨entry.1.toArray⟩, entry.2)⟩ = .ok root')
    (hsorted : strictlyIncreasing
      (data.map fun entry => bytesToNibbleList ⟨entry.1.toArray⟩) = true)
    (hnone : ∀ entry ∈ data,
      bytesToNibbleList ⟨entry.1.toArray⟩ < bytesToNibbleList ⟨start.toArray⟩)
    (hfirst : getProof hash ⟨false, data.map fun entry => (⟨entry.1.toArray⟩, entry.2)⟩
      ⟨start.toArray⟩ = .ok first) (hproof : ∀ x ∈ first, x ∈ proof) :
    verifyRange hash root' start [] proof = .ok false ∨
      ∃ pair, findCrossCollision hash first proof = some pair ∧ IsCollision hash pair := by
  cases hfind : findCrossCollision hash first proof with
  | some pair => exact .inr ⟨pair, rfl, findCrossCollision_valid hash hfind⟩
  | none =>
    refine .inl ?_
    have hcoll := (findCrossCollision_eq_none_iff hash).mp hfind
    have hne : proof ≠ [] := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (getProof_ne_nil hfirst)
      exact List.ne_nil_of_mem (hproof x hx)
    rw [verifyRange_eq hash root' start [] proof rfl (by simp) (by simp),
      ite_eq_right_of_eq_false _ _ (eq_false (by simp [hne]))]
    have h := checkSubtree_root hash hproof hcoll start (right := none) hroot hsorted (by simp) (by
      intro path hpath
      rcases hpath with rfl | hpath
      · exact ⟨start, rfl, first, hfirst, fun _ hx => hx⟩
      · cases hpath)
    have hempty : (data.map fun entry => (bytesToNibbleList ⟨entry.1.toArray⟩, entry.2)).filter
        (inRange (bytesToNibbleList ⟨start.toArray⟩) none) = [] := by
      refine List.filter_eq_nil_iff.mpr fun entry hmem => ?_
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmem
      simp [inRange, List.not_le.mpr (hnone original horiginal)]
    rw [hempty, List.any_eq_false.mpr (by simp)] at h
    simpa using h

/-- Completeness of a whole trie: its keys in increasing order pass the check with no proof.

Every key must lie at or after the start.

The check then shows no key after them. -/
theorem verifyRange_whole (hash : ByteArray → Hash32) {data : List (Hash32 × ByteArray)}
    {root' : Hash32} (start : Hash32)
    (hroot : root hash ⟨false, data.map fun entry => (⟨entry.1.toArray⟩, entry.2)⟩ = .ok root')
    (hsorted : strictlyIncreasing
      (data.map fun entry => bytesToNibbleList ⟨entry.1.toArray⟩) = true)
    (hstart : ∀ entry ∈ data,
      bytesToNibbleList ⟨start.toArray⟩ ≤ bytesToNibbleList ⟨entry.1.toArray⟩) :
    verifyRange hash root' start data [] = .ok false := by
  have hfull : ∀ entry ∈ data, entry.2.size ≠ 0 := by
    intro entry hmem hsize
    rw [root_emptyValue hash _ ⟨(⟨entry.1.toArray⟩, entry.2), List.mem_map_of_mem hmem, hsize⟩]
      at hroot
    cases hroot
  rw [verifyRange_eq hash root' start data [] hsorted hstart hfull]
  rw [show (data.map fun x => ((⟨x.fst.toArray⟩ : ByteArray), x.snd)) =
    data.map fun entry => (⟨entry.1.toArray⟩, entry.2) from rfl, hroot]
  simp

end EthLib.Execution.Trie
