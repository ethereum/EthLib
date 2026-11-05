module

public import EthLib.Execution.Trie.Proof
public import EthLib.Execution.Proofs.Trie.Order
public import EthLib.Serialization.Proofs.Rlp.Canonical

/-!
# Proofs: `Trie.Proof`

Completeness: the proof that the trie builds for a key verifies against the trie's root.

It gives the value of the key, or `none` when the key is not set.

The proof rests on one induction down the key's path, at each node of the trie.

The walk decodes each node from its encoding, and finds a child held by hash as the next proof node.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## Decoding inverts `unencoded` -/

/-- A leaf decodes from its item. -/
theorem decodeNode_leaf (restOfKey : List Nibble) (value : ByteArray) :
    decodeNode (unencoded (some (.leaf restOfKey value))) = .ok (.leaf restOfKey value) := by
  simp only [unencoded, decodeNode, compactToNibbleList_nibbleListToCompact]

/-- An extension that consumes at least one nibble decodes from its item. -/
theorem decodeNode_extension {keySegment : List Nibble} (hsegment : keySegment ≠ []) (subnode : Item) :
    decodeNode (unencoded (some (.extension keySegment subnode))) = .ok (.extension keySegment subnode) := by
  match keySegment, hsegment with
  | _ :: _, _ => simp only [unencoded, decodeNode, compactToNibbleList_nibbleListToCompact]

/-- A list of 17 items decodes as a branch when its last item is a byte string. -/
theorem decodeNode_seventeen (items : List Item) (hlength : items.length = 17) :
    decodeNode (.list items)
      = match items[16] with
        | .bytes value => .ok (.branch ⟨(items.take 16).toArray, by simp [hlength]⟩ value)
        | .list _ => .error .invalidNode := by
  match items, hlength with
  | _ :: _ :: _ :: _, hlength =>
    simp only [decodeNode, hlength, ↓reduceDIte]
    rfl

/-- A branch decodes from its item. -/
theorem decodeNode_branch (subnodes : Vector Item 16) (value : ByteArray) :
    decodeNode (unencoded (some (.branch subnodes value))) = .ok (.branch subnodes value) := by
  have hlength : (subnodes.toList ++ [Item.bytes value]).length = 17 := by simp
  simp only [unencoded]
  rw [decodeNode_seventeen _ hlength]
  -- The 17th item is the value, and the first 16 are the children.
  have hlast : (subnodes.toList ++ [Item.bytes value])[16] = .bytes value := by
    rw [List.getElem_append_right (by simp)]
    simp
  simp only [hlast]
  -- The first 16 items are the children.
  have htake : (subnodes.toList ++ [Item.bytes value]).take 16 = subnodes.toList := List.take_left' (by simp)
  congr 3
  rw [htake]
  rfl

/-! ## Following a reference -/

/-- How a parent holds a node, from the encoding of the node. -/
theorem encodeInternalNode_of_encode {hash : ByteArray → Hash32} {node : Option InternalNode} {encoded : ByteArray}
    (h : encode (unencoded node) = .ok encoded) :
    encodeInternalNode hash node
      = .ok (if encoded.size < 32 then unencoded node else .bytes ⟨(hash encoded).toArray⟩) := by
  simp only [encodeInternalNode, h, Bind.bind, Except.bind]
  split <;> rfl

/-- The item of a node is a list, or the empty byte string for no node. -/
theorem unencoded_shape : (node : Option InternalNode) → (∃ items, unencoded node = .list items) ∨ unencoded node = .bytes .empty
  | none => .inr rfl
  | some (.leaf _ _) => .inl ⟨_, rfl⟩
  | some (.extension _ _) => .inl ⟨_, rfl⟩
  | some (.branch _ _) => .inl ⟨_, rfl⟩

/-- A node held inside its parent is followed without a proof node. -/
theorem resolve_unencoded (hash : ByteArray → Hash32) (node : Option InternalNode) (proof : List ByteArray) :
    resolve hash (unencoded node) proof = .ok (unencoded node, proof) := by
  rcases unencoded_shape node with ⟨items, h⟩ | h <;> rw [h] <;> rfl

/-- The bytes of a hash have 32 bytes. -/
theorem size_hashBytes (digest : Hash32) : (⟨digest.toArray⟩ : ByteArray).size = 32 := by
  simp [ByteArray.size]

/-- A node held by hash is followed through its encoding, the next node of the proof. -/
theorem resolve_hash (hash : ByteArray → Hash32) {node : Option InternalNode} {encoded : ByteArray}
    (h : encode (unencoded node) = .ok encoded) (rest : List ByteArray) :
    resolve hash (.bytes ⟨(hash encoded).toArray⟩) (encoded :: rest) = .ok (unencoded node, rest) := by
  have hdecode : decode encoded = .ok (unencoded node) := (decode_eq_ok_iff _ _).mpr h
  simp [resolve, size_hashBytes, hdecode, Except.mapError, Bind.bind, Except.bind, pure, Except.pure, Vector.toList]

/-! ## The nodes that `patricialize` builds -/

/-- The calls that the induction follows: the paths are distinct after `level`, at least `level` long, and every value is set. -/
structure Honest (obj : List (List Nibble × ByteArray)) (level : Nat) : Prop where
  /-- The paths are distinct after their first `level` nibbles. -/
  distinct : Distinct obj level
  /-- Every path has at least `level` nibbles. -/
  long : ∀ entry ∈ obj, level ≤ entry.1.length
  /-- No value is the empty byte string. -/
  full : ∀ entry ∈ obj, entry.2.size ≠ 0

/-- Each result of `mapMVector` is `f` of the entry at the same place. -/
theorem mapMVector_ok {α β ε : Type} {f : α → Except ε β} :
    (xs : List α) → {ys : Vector β xs.length} → mapMVector f xs = .ok ys →
      ∀ (j : Nat) (hj : j < xs.length), f xs[j] = .ok ys[j]
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | x :: rest, ys, h, j, hj => by
    simp only [mapMVector, Bind.bind, Except.bind] at h
    cases hx : f x with
    | error => simp [hx] at h
    | ok y =>
      cases hrest : mapMVector f rest with
      | error => simp [hx, hrest] at h
      | ok zs =>
        simp only [hx, hrest, pure, Except.pure, Except.ok.injEq] at h
        subst h
        cases j with
        | zero => simpa using hx
        | succ j => simpa using mapMVector_ok rest hrest j (by simpa using hj)

/-- What `patricialize` builds from keys that are honest at `level`, when it succeeds. -/
inductive Built (hash : ByteArray → Hash32) (obj : List (List Nibble × ByteArray)) (level : Nat) :
    Option InternalNode → Prop where
  /-- No key: no node. -/
  | none (hobj : obj = []) : Built hash obj level none
  /-- One key: a leaf with the rest of its path and its value. -/
  | leaf (key : List Nibble) (value : ByteArray) (hobj : obj = [(key, value)]) :
      Built hash obj level (some (.leaf (key.drop level) value))
  /-- Every path continues with `keySegment`: an extension, and the node of the same keys after it. -/
  | extension (keySegment : List Nibble) (subnode : Item) (child : Option InternalNode)
      (hsegment : keySegment ≠ [])
      (hcommon : ∀ entry ∈ obj, (entry.1.drop level).take keySegment.length = keySegment)
      (hchild : patricialize hash obj (level + keySegment.length) = .ok child)
      (hsubnode : encodeInternalNode hash child = .ok subnode) :
      Built hash obj level (some (.extension keySegment subnode))
  /-- A branch: the node of each next nibble, and the value of the key that ends here. -/
  | branch (subnodes : Vector Item 16)
      (hchildren : ∀ nibble : Nibble, ∃ child,
        patricialize hash (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1) = .ok child ∧
        encodeInternalNode hash child = .ok subnodes[nibble])
      (value : ByteArray)
      (hvalue : value = obj.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value) .empty) :
      Built hash obj level (some (.branch subnodes value))

/-- Every node that `patricialize` builds is one of the four kinds of `Built`. -/
theorem built_of_patricialize (hash : ByteArray → Hash32) {obj : List (List Nibble × ByteArray)} {level : Nat}
    {node : Option InternalNode} (h : patricialize hash obj level = .ok node) : Built hash obj level node := by
  -- One step of `patricialize`, whose nested calls have a budget that fits.
  have hstep : patricialize hash obj level = patricializeStep hash (patricializeAux hash (longestPath obj)) obj level := rfl
  rw [hstep] at h
  match obj, h with
  | [], h =>
    simp only [patricializeStep, Except.ok.injEq] at h
    exact h ▸ .none rfl
  | [(key, value)], h =>
    simp only [patricializeStep, Except.ok.injEq] at h
    exact h ▸ .leaf key value rfl
  | (key₁, value₁) :: second :: rest, h =>
    simp only [patricializeStep] at h
    have hfits : ∀ sub deeper, 0 < deeper → longestPath sub ≤ longestPath ((key₁, value₁) :: second :: rest) →
        patricializeAux hash (longestPath ((key₁, value₁) :: second :: rest)) sub deeper = patricialize hash sub deeper :=
      fun sub deeper hdeeper hle => patricializeAux_eq_patricialize hash (by omega)
    split at h
    · -- An extension.
      rename_i hpositive
      have hrun := (le_foldl_min_iff (fun entry : List Nibble × ByteArray =>
        commonPrefixLength (key₁.drop level) (entry.1.drop level)) _ ((key₁, value₁) :: second :: rest)
        (key₁.drop level).length).mp (Nat.le_refl _)
      generalize hp : List.foldl (fun length (x : List Nibble × ByteArray) =>
          min length (commonPrefixLength (List.drop level key₁) (List.drop level x.1)))
          (List.drop level key₁).length ((key₁, value₁) :: second :: rest) = p at h hrun hpositive
      simp only [Bind.bind, Except.bind] at h
      cases hc : patricializeAux hash (longestPath ((key₁, value₁) :: second :: rest)) ((key₁, value₁) :: second :: rest)
          (level + p) with
      | error => simp [hc] at h
      | ok child =>
        cases hs : encodeInternalNode hash child with
        | error => simp [hc, hs] at h
        | ok subnode =>
          simp only [hc, hs, pure, Except.pure, Except.ok.injEq] at h
          subst h
          -- The run has `p` nibbles, and every path continues with it.
          have hlength : ((key₁.drop level).take p).length = p := by
            simp only [List.length_take]
            exact Nat.min_eq_left hrun.1
          refine .extension _ _ child ?_ ?_ ?_ hs
          · intro hnil
            rw [hnil] at hlength
            simp at hlength
            omega
          · intro entry hmem
            rw [hlength]
            exact (take_eq_of_le_commonPrefixLength _ _ _ (hrun.2 entry hmem)).symm
          · rw [hlength, ← hfits _ _ (by omega) (Nat.le_refl _), hc]
    · -- A branch.
      simp only [Bind.bind, Except.bind] at h
      generalize hchildren : mapMVector _ (List.finRange 16) = children at h
      cases children with
      | error => cases h
      | ok subnodes =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine .branch _ ?_ _ rfl
        intro nibble
        have hentry := mapMVector_ok _ hchildren nibble.val (by simp)
        simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta] at hentry
        cases hc : patricializeAux hash (longestPath ((key₁, value₁) :: second :: rest))
            (((key₁, value₁) :: second :: rest).filter fun (key, _) => key[level]? = some nibble) (level + 1) with
        | error => simp [hc] at hentry
        | ok child =>
          simp only [hc] at hentry
          refine ⟨child, ?_, ?_⟩
          · rw [← hfits _ _ (by omega) (longestPath_filter_le _ _), hc]
          · simpa using hentry

/-! ## The value at the end of a path -/

/-- The value of the key whose path, after its first `level` nibbles, is `path`. -/
def lookupAt (obj : List (List Nibble × ByteArray)) (level : Nat) (path : List Nibble) : Option ByteArray :=
  (obj.find? fun entry => entry.1.drop level = path).map Prod.snd

/-- `find?` gives the same entry for two tests that agree on every entry. -/
theorem find?_congr {α : Type} {p q : α → Bool} : (l : List α) → (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: rest, h => by
    simp only [List.find?_cons, h x List.mem_cons_self,
      find?_congr rest fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- A path after `level` starts with a nibble exactly when the nibble is at `level`, and then continues with the rest. -/
theorem drop_eq_cons_iff (key : List Nibble) (level : Nat) (nibble : Nibble) (rest : List Nibble) :
    key.drop level = nibble :: rest ↔ key[level]? = some nibble ∧ key.drop (level + 1) = rest := by
  constructor
  · intro h
    have hlt : level < key.length := by
      have := congrArg List.length h
      simp only [List.length_drop, List.length_cons] at this
      omega
    rw [List.drop_eq_getElem_cons hlt] at h
    simp only [List.cons.injEq] at h
    exact ⟨by simp [hlt, h.1], h.2⟩
  · rintro ⟨hget, hrest⟩
    obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hget
    rw [List.drop_eq_getElem_cons hlt, hval, hrest]

/-- No key, no value. -/
theorem lookupAt_nil (level : Nat) (path : List Nibble) : lookupAt [] level path = none := rfl

/-- One key: its value when the path is the rest of its path. -/
theorem lookupAt_single (key : List Nibble) (value : ByteArray) (level : Nat) (path : List Nibble) :
    lookupAt [(key, value)] level path = if key.drop level = path then some value else none := by
  by_cases h : key.drop level = path <;> simp [lookupAt, h]

/-- Under an extension that the path follows, the value is the one after the extension. -/
theorem lookupAt_extension {obj : List (List Nibble × ByteArray)} {level : Nat} {keySegment path : List Nibble}
    (hcommon : ∀ entry ∈ obj, (entry.1.drop level).take keySegment.length = keySegment)
    (hpath : keySegment = path.take keySegment.length) :
    lookupAt obj level path = lookupAt obj (level + keySegment.length) (path.drop keySegment.length) := by
  unfold lookupAt
  congr 1
  apply find?_congr
  intro entry hmem
  -- Both paths start with the segment, so they agree exactly when their rests agree.
  have hentry := hcommon entry hmem
  simp only [decide_eq_decide, ← List.drop_drop]
  constructor
  · intro h
    rw [h]
  · intro h
    calc entry.1.drop level
        = (entry.1.drop level).take keySegment.length ++ (entry.1.drop level).drop keySegment.length :=
          (List.take_append_drop _ _).symm
      _ = path.take keySegment.length ++ path.drop keySegment.length := by rw [hentry, h, ← hpath]
      _ = path := List.take_append_drop _ _

/-- Under an extension that the path leaves, no key has the path. -/
theorem lookupAt_extension_none {obj : List (List Nibble × ByteArray)} {level : Nat} {keySegment path : List Nibble}
    (hcommon : ∀ entry ∈ obj, (entry.1.drop level).take keySegment.length = keySegment)
    (hpath : ¬keySegment = path.take keySegment.length) :
    lookupAt obj level path = none := by
  simp only [lookupAt, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  intro entry hmem h
  exact hpath ((hcommon entry hmem).symm.trans (by rw [h]))

/-- Under a branch, the value of a path that continues with a nibble is the value in that nibble's child. -/
theorem lookupAt_branch (obj : List (List Nibble × ByteArray)) (level : Nat) (nibble : Nibble) (path : List Nibble) :
    lookupAt obj level (nibble :: path)
      = lookupAt (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1) path := by
  unfold lookupAt
  rw [List.find?_filter]
  congr 1
  apply find?_congr
  intro entry _
  simp only [drop_eq_cons_iff, decide_eq_true_eq]

/-- At a branch, the value of the path that ends there is the branch's value, unless that value is empty. -/
theorem lookupAt_branch_nil {obj : List (List Nibble × ByteArray)} {level : Nat} (honest : Honest obj level) :
    lookupAt obj level []
      = (let value := obj.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value) .empty
         if value.size = 0 then none else some value) := by
  -- A path ends at `level` exactly when it has `level` nibbles.
  have hends : ∀ entry ∈ obj, decide (entry.1.drop level = []) = decide (entry.1.length = level) := by
    intro entry hmem
    have := honest.long entry hmem
    simp only [List.drop_eq_nil_iff, decide_eq_decide]
    omega
  have hfind : obj.find? (fun entry => entry.1.drop level = []) = obj.find? (fun entry => entry.1.length = level) :=
    find?_congr obj hends
  have hlast := foldl_last (fun entry : List Nibble × ByteArray => decide (entry.1.length = level)) Prod.snd obj .empty
  have hfold : obj.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value) ByteArray.empty
      = obj.foldl (fun acc entry => if decide (entry.1.length = level) = true then entry.2 else acc) ByteArray.empty := by
    simp only [decide_eq_true_eq]
  simp only [lookupAt, hfind]
  rw [hfold, hlast, ← List.head?_filter]
  -- At most one path ends here.
  have hone := honest.distinct.length_filter_le_one
  generalize hends' : obj.filter (fun entry => decide (entry.1.length = level)) = ending at hone
  match ending, hone with
  | [], _ => simp
  | [entry], _ =>
    have hmem : entry ∈ obj := (List.mem_filter.mp (hends' ▸ List.mem_singleton_self entry)).1
    simp [honest.full entry hmem]

/-! ## One step of the walk -/

/-- Follow a reference with the proof, then walk on from the node it points to. -/
def follow (hash : ByteArray → Hash32) (fuel : Nat) (reference : Item) (path : List Nibble) (proof : List ByteArray) :
    Except ProofError (Option ByteArray × List ByteArray) :=
  (resolve hash reference proof).bind fun next => walk hash fuel next.1 path next.2

/-- No node: the key is not set, and no proof node is used. -/
theorem walk_none (hash : ByteArray → Hash32) (fuel : Nat) (path : List Nibble) (proof : List ByteArray) :
    walk hash (fuel + 1) (unencoded none) path proof = .ok (none, proof) := rfl

/-- One step of the walk on a node that decodes. -/
theorem walk_decoded (hash : ByteArray → Hash32) (fuel : Nat) {items : List Item} {decoded : InternalNode}
    (hdecode : decodeNode (.list items) = .ok decoded) (path : List Nibble) (proof : List ByteArray) :
    walk hash (fuel + 1) (.list items) path proof
      = match decoded with
        | .leaf restOfKey value => .ok (if restOfKey = path then some value else none, proof)
        | .extension keySegment subnode =>
          if keySegment = path.take keySegment.length then follow hash fuel subnode (path.drop keySegment.length) proof
          else .ok (none, proof)
        | .branch subnodes value =>
          match path with
          | [] => .ok (if value.size = 0 then none else some value, proof)
          | nibble :: restOfPath => follow hash fuel subnodes[nibble] restOfPath proof := by
  cases decoded with
  | leaf =>
    simp only [walk, hdecode, Bind.bind, Except.bind]
    rfl
  | extension =>
    simp only [walk, hdecode, Bind.bind, Except.bind]
    split <;> rfl
  | branch =>
    simp only [walk, hdecode, Bind.bind, Except.bind]
    cases path <;> rfl

/-- A leaf: its value when the path is the rest of its key. -/
theorem walk_leaf (hash : ByteArray → Hash32) (fuel : Nat) (restOfKey : List Nibble) (value : ByteArray)
    (path : List Nibble) (proof : List ByteArray) :
    walk hash (fuel + 1) (unencoded (some (.leaf restOfKey value))) path proof
      = .ok (if restOfKey = path then some value else none, proof) :=
  walk_decoded hash fuel (decodeNode_leaf restOfKey value) path proof

/-- An extension: the node after it when the path follows it, and no value otherwise. -/
theorem walk_extension (hash : ByteArray → Hash32) (fuel : Nat) {keySegment : List Nibble} (hsegment : keySegment ≠ [])
    (subnode : Item) (path : List Nibble) (proof : List ByteArray) :
    walk hash (fuel + 1) (unencoded (some (.extension keySegment subnode))) path proof
      = if keySegment = path.take keySegment.length then follow hash fuel subnode (path.drop keySegment.length) proof
        else .ok (none, proof) :=
  walk_decoded hash fuel (decodeNode_extension hsegment subnode) path proof

/-- A branch at the end of the path: its value, unless that value is empty. -/
theorem walk_branch_nil (hash : ByteArray → Hash32) (fuel : Nat) (subnodes : Vector Item 16) (value : ByteArray)
    (proof : List ByteArray) :
    walk hash (fuel + 1) (unencoded (some (.branch subnodes value))) [] proof
      = .ok (if value.size = 0 then none else some value, proof) :=
  walk_decoded hash fuel (decodeNode_branch subnodes value) [] proof

/-- A branch inside the path: the child of the next nibble. -/
theorem walk_branch_cons (hash : ByteArray → Hash32) (fuel : Nat) (subnodes : Vector Item 16) (value : ByteArray)
    (nibble : Nibble) (path : List Nibble) (proof : List ByteArray) :
    walk hash (fuel + 1) (unencoded (some (.branch subnodes value))) (nibble :: path) proof
      = follow hash fuel subnodes[nibble] path proof :=
  walk_decoded hash fuel (decodeNode_branch subnodes value) (nibble :: path) proof

/-! ## Following a child -/

/-- How a parent holds a node fixes the encoding of the node. -/
theorem encode_of_encodeInternalNode {hash : ByteArray → Hash32} {node : Option InternalNode} {reference : Item}
    (h : encodeInternalNode hash node = .ok reference) :
    ∃ encoded, encode (unencoded node) = .ok encoded ∧
      reference = if encoded.size < 32 then unencoded node else .bytes ⟨(hash encoded).toArray⟩ := by
  cases hencode : encode (unencoded node) with
  | error => simp [encodeInternalNode, hencode, Bind.bind, Except.bind] at h
  | ok encoded =>
    rw [encodeInternalNode_of_encode hencode] at h
    exact ⟨encoded, rfl, (Except.ok.inj h).symm⟩

/-- The walk follows a child with the honest proof as it walks the child itself.

It gives the child's value and leaves the rest of the proof. -/
theorem follow_child (hash : ByteArray → Hash32) {fuel : Nat} {child : Option InternalNode} {encoded : ByteArray}
    {path : List Nibble} {below : List ByteArray} {value : Option ByteArray}
    (hencode : encode (unencoded child) = .ok encoded)
    (hcomplete : ∀ rest, walk hash fuel (unencoded child) path (below ++ rest) = .ok (value, rest))
    (rest : List ByteArray) :
    follow hash fuel
      (if encoded.size < 32 then unencoded child else .bytes ⟨(hash encoded).toArray⟩) path
      (((if encoded.size < 32 then [] else [encoded]) ++ below) ++ rest) = .ok (value, rest) := by
  split
  · -- Held inside its parent: no proof node.
    simp only [List.nil_append, follow, resolve_unencoded, Except.bind]
    exact hcomplete rest
  · -- Held by hash: the next proof node is the encoding of the child.
    simp only [follow, List.cons_append, resolve_hash hash hencode, Except.bind]
    exact hcomplete rest

/-! ## The induction down the path -/

/-- Keys that every path continues with `keySegment` stay honest after it. -/
theorem Honest.extension {obj : List (List Nibble × ByteArray)} {level : Nat} {keySegment : List Nibble}
    (honest : Honest obj level)
    (hcommon : ∀ entry ∈ obj, (entry.1.drop level).take keySegment.length = keySegment) :
    Honest obj (level + keySegment.length) where
  distinct := honest.distinct.drop keySegment hcommon
  long := by
    intro entry hmem
    -- The path holds the whole segment after `level`.
    have h := congrArg List.length (hcommon entry hmem)
    simp only [List.length_take, List.length_drop] at h
    have := honest.long entry hmem
    omega
  full := honest.full

/-- The keys of one child of a branch stay honest one nibble further. -/
theorem Honest.filter {obj : List (List Nibble × ByteArray)} {level : Nat} (honest : Honest obj level)
    (nibble : Nibble) :
    Honest (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1) where
  distinct := honest.distinct.filter nibble
  long := by
    intro entry hmem
    have hnext : entry.1[level]? = some nibble := by simpa using (List.mem_filter.mp hmem).2
    exact (List.getElem?_eq_some_iff.mp hnext).1
  full := fun entry hmem => honest.full entry (List.mem_filter.mp hmem).1

/-- The walk down the path of the node that `patricialize` builds, with the proof that `proofBelow` builds.

With that proof and any nodes after it, the walk gives the value of the path.

It leaves the nodes after the proof. -/
theorem walk_honest (hash : ByteArray → Hash32) :
    (fuel fuel' : Nat) → {obj : List (List Nibble × ByteArray)} → {level : Nat} → {path : List Nibble} →
      {node : Option InternalNode} → {below : List ByteArray} →
      Honest obj level → path.length < fuel → path.length < fuel' →
      patricialize hash obj level = .ok node → proofBelow hash fuel' obj level path = .ok below →
      ∀ rest,
        walk hash fuel (unencoded node) path (below ++ rest) = .ok (lookupAt obj level path, rest)
  | 0, _, _, _, _, _, _, _, hfuel, _, _, _ => absurd hfuel (Nat.not_lt_zero _)
  | _, 0, _, _, _, _, _, _, _, hfuel', _, _ => absurd hfuel' (Nat.not_lt_zero _)
  | fuel + 1, fuel' + 1, obj, level, path, node, below, honest, hfuel, hfuel', hnode, hbelow => by
    simp only [proofBelow, hnode, Bind.bind, Except.bind] at hbelow
    cases built_of_patricialize hash hnode with
    | none hobj =>
      -- No node: no proof node, and the key is not set.
      simp only [pure, Except.pure, Except.ok.injEq] at hbelow
      subst hbelow hobj
      exact walk_none hash fuel path
    | leaf key value hobj =>
      -- A leaf: no proof node, and its value when the path is the rest of its key.
      simp only [pure, Except.pure, Except.ok.injEq] at hbelow
      subst hbelow hobj
      intro rest
      rw [walk_leaf, lookupAt_single]
      simp
    | extension keySegment subnode child hsegment hcommon hchild hsubnode =>
      obtain ⟨encoded, hencode, rfl⟩ := encode_of_encodeInternalNode hsubnode
      dsimp only at hbelow
      by_cases hfollow : keySegment = path.take keySegment.length
      · -- The path follows the extension: the child, after the segment.
        rw [ite_eq_left_of_eq_true _ _ (eq_true hfollow)] at hbelow
        simp only [hchild, hencode] at hbelow
        cases hrest : proofBelow hash fuel' obj (level + keySegment.length) (path.drop keySegment.length) with
        | error => simp [hrest] at hbelow
        | ok below' =>
          simp only [hrest, pure, Except.pure, Except.ok.injEq] at hbelow
          subst hbelow
          -- The segment has at least one nibble, so the rest of the path is shorter.
          have hlength : keySegment.length ≤ path.length := by
            have := congrArg List.length hfollow
            simp only [List.length_take] at this
            omega
          have hpositive : 0 < keySegment.length := List.length_pos_iff.mpr hsegment
          have ih := walk_honest hash fuel fuel' (honest.extension hcommon)
            (by simp only [List.length_drop]; omega) (by simp only [List.length_drop]; omega) hchild hrest
          rw [lookupAt_extension hcommon hfollow]
          intro rest
          rw [walk_extension hash fuel hsegment, ite_eq_left_of_eq_true _ _ (eq_true hfollow)]
          exact follow_child hash hencode ih rest
      · -- The path leaves the extension: no proof node, and the key is not set.
        rw [ite_eq_right_of_eq_false _ _ (eq_false hfollow)] at hbelow
        simp only [pure, Except.pure, Except.ok.injEq] at hbelow
        subst hbelow
        rw [lookupAt_extension_none hcommon hfollow]
        intro rest
        rw [walk_extension hash fuel hsegment, ite_eq_right_of_eq_false _ _ (eq_false hfollow)]
        rfl
    | branch subnodes hchildren value hvalue =>
      dsimp only at hbelow
      match path with
      | [] =>
        -- The path ends here: no proof node, and the branch's value.
        simp only [pure, Except.pure, Except.ok.injEq] at hbelow
        subst hbelow hvalue
        rw [lookupAt_branch_nil honest]
        intro rest
        rw [walk_branch_nil]
        rfl
      | nibble :: restOfPath =>
        -- The path continues: the child of its next nibble.
        obtain ⟨child, hchild, hsubnode⟩ := hchildren nibble
        obtain ⟨encoded, hencode, hreference⟩ := encode_of_encodeInternalNode hsubnode
        simp only [hchild, hencode] at hbelow
        cases hrest : proofBelow hash fuel' (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1)
            restOfPath with
        | error => simp [hrest] at hbelow
        | ok below' =>
          simp only [hrest, pure, Except.pure, Except.ok.injEq] at hbelow
          subst hbelow
          have ih := walk_honest hash fuel fuel' (honest.filter nibble)
            (by simp only [List.length_cons] at hfuel; omega) (by simp only [List.length_cons] at hfuel'; omega)
            hchild hrest
          rw [lookupAt_branch]
          intro rest
          rw [walk_branch_cons, hreference]
          exact follow_child hash hencode ih rest

/-! ## Building a proof -/

/-- Below a node that is built from some keys, the proof of every path can be built. -/
theorem proofBelow_ok (hash : ByteArray → Hash32) :
    (fuel : Nat) → {obj : List (List Nibble × ByteArray)} → {level : Nat} →
      {node : Option InternalNode} → patricialize hash obj level = .ok node → (path : List Nibble) →
        ∃ below, proofBelow hash fuel obj level path = .ok below
  | 0, _, _, _, _, _ => ⟨[], rfl⟩
  | fuel + 1, obj, level, node, h, path => by
    -- A child that the path enters is built, so its encoding and the proof below it can be built.
    have hchild : ∀ {sub : List (List Nibble × ByteArray)} {deeper : Nat}
        {child : Option InternalNode} {subnode : Item}, patricialize hash sub deeper = .ok child →
        encodeInternalNode hash child = .ok subnode → ∀ rest, ∃ below, (do
          let encoded ← encode (unencoded (← patricialize hash sub deeper))
          let below ← proofBelow hash fuel sub deeper rest
          return (if encoded.size < 32 then [] else [encoded]) ++ below)
            = Except.ok (ε := RlpError) below := by
      intro sub deeper child subnode hpatricialize hsubnode rest
      obtain ⟨encoded, hencode, -⟩ := encode_of_encodeInternalNode hsubnode
      obtain ⟨below, hbelow⟩ := proofBelow_ok hash fuel hpatricialize rest
      exact ⟨(if encoded.size < 32 then [] else [encoded]) ++ below,
        by simp [hpatricialize, hencode, hbelow, Bind.bind, Except.bind, pure, Except.pure]⟩
    cases built_of_patricialize hash h with
    | none => exact ⟨[], by simp [proofBelow, h, Bind.bind, Except.bind, pure, Except.pure]⟩
    | leaf => exact ⟨[], by simp [proofBelow, h, Bind.bind, Except.bind, pure, Except.pure]⟩
    | extension keySegment subnode child _ _ hpatricialize hsubnode =>
      by_cases hfollow : keySegment = path.take keySegment.length
      · obtain ⟨below, hbelow⟩ := hchild hpatricialize hsubnode (path.drop keySegment.length)
        refine ⟨below, ?_⟩
        simp only [proofBelow, h, Bind.bind, Except.bind]
        rw [ite_eq_left hfollow]
        exact hbelow
      · refine ⟨[], ?_⟩
        simp only [proofBelow, h, Bind.bind, Except.bind]
        rw [ite_eq_right hfollow]
        rfl
    | branch subnodes hchildren value _ =>
      cases path with
      | nil => exact ⟨[], by simp [proofBelow, h, Bind.bind, Except.bind, pure, Except.pure]⟩
      | cons nibble rest =>
        obtain ⟨child, hpatricialize, hsubnode⟩ := hchildren nibble
        obtain ⟨below, hbelow⟩ := hchild hpatricialize hsubnode rest
        exact ⟨below, by simp only [proofBelow, h, Bind.bind, Except.bind]; exact hbelow⟩

/-- A trie with a root has a proof for every key. -/
theorem getProof_ok (hash : ByteArray → Hash32) {trie : Trie} {root' : Hash32}
    (hroot : root hash trie = .ok root') (key : ByteArray) :
    ∃ proof, getProof hash trie key = .ok proof := by
  simp only [root, Bind.bind, Except.bind, Except.mapError] at hroot
  simp only [getProof, Bind.bind, Except.bind, Except.mapError]
  -- The root's own steps succeed, and the proof below the root node can be built.
  cases hobj : prepareData hash trie.data trie.secured with
  | error => simp [hobj] at hroot
  | ok obj =>
    cases hnode : patricialize hash obj 0 with
    | error => simp [hobj, hnode] at hroot
    | ok node =>
      cases hencode : encode (unencoded node) with
      | error => simp [hobj, hnode, hencode] at hroot
      | ok encoded =>
        generalize keyPath hash trie.secured key = path
        obtain ⟨below, hbelow⟩ := proofBelow_ok hash (path.length + 1) hnode path
        exact ⟨encoded :: below, by simp [hnode, hencode, hbelow, pure, Except.pure]⟩

/-! ## Completeness -/

/-- The value that a trie gives a key: the value of the entry whose path is the key's path, or `none`. -/
def valueAt (hash : ByteArray → Hash32) (trie : Trie) (key : ByteArray) : Option ByteArray :=
  (trie.data.find? fun entry => keyPath hash trie.secured entry.1 = keyPath hash trie.secured key).map Prod.snd

/-- The facts that completeness takes from a trie with a root and a proof. -/
theorem honest_root {hash : ByteArray → Hash32} {trie : Trie} {key : ByteArray} {root' : Hash32}
    {honestProof : List ByteArray}
    (hroot : root hash trie = .ok root') (hproof : getProof hash trie key = .ok honestProof)
    (hpaths : (trie.data.map fun entry => keyPath hash trie.secured entry.1).Nodup) :
    ∃ rootNode encoded below,
      patricialize hash (trie.data.map fun entry => (keyPath hash trie.secured entry.1, entry.2)) 0 = .ok rootNode ∧
      encode (unencoded rootNode) = .ok encoded ∧ root' = hash encoded ∧ honestProof = encoded :: below ∧
      proofBelow hash ((keyPath hash trie.secured key).length + 1)
        (trie.data.map fun entry => (keyPath hash trie.secured entry.1, entry.2)) 0 (keyPath hash trie.secured key)
          = .ok below ∧
      Honest (trie.data.map fun entry => (keyPath hash trie.secured entry.1, entry.2)) 0 ∧
      lookupAt (trie.data.map fun entry => (keyPath hash trie.secured entry.1, entry.2)) 0
        (keyPath hash trie.secured key) = valueAt hash trie key := by
  -- A trie with a root has no empty value, so its entries become their paths and values.
  have hfull : ∀ entry ∈ trie.data, entry.2.size ≠ 0 := by
    intro entry hmem hsize
    rw [root_emptyValue hash trie ⟨entry, hmem, hsize⟩] at hroot
    cases hroot
  have hprepare := prepareData_eq_keyPath hash trie.secured hfull
  generalize hobj : trie.data.map (fun entry => (keyPath hash trie.secured entry.1, entry.2)) = obj at hprepare ⊢
  simp only [root, hprepare, Except.mapError, Bind.bind, Except.bind] at hroot
  simp only [getProof, hprepare, Except.mapError, Bind.bind, Except.bind] at hproof
  cases hnode : patricialize hash obj 0 with
  | error => simp [hnode] at hroot
  | ok rootNode =>
    cases hencode : encode (unencoded rootNode) with
    | error => simp [hnode, hencode] at hroot
    | ok encoded =>
      cases hbelow : proofBelow hash ((keyPath hash trie.secured key).length + 1) obj 0 (keyPath hash trie.secured key) with
      | error => simp [hnode, hencode, hbelow] at hproof
      | ok below =>
        simp only [hnode, hencode, pure, Except.pure, Except.ok.injEq] at hroot
        simp only [hnode, hencode, hbelow, pure, Except.pure, Except.ok.injEq] at hproof
        refine ⟨rootNode, encoded, below, rfl, hencode, hroot.symm, hproof.symm, rfl, ?_, ?_⟩
        · -- The paths are distinct, at least 0 nibbles long, and every value is set.
          subst hobj
          refine ⟨?_, fun _ _ => Nat.zero_le _, ?_⟩
          · simp only [Distinct, List.drop_zero, List.map_map]
            exact hpaths
          · intro entry hmem
            obtain ⟨original, hmem', rfl⟩ := List.mem_map.mp hmem
            exact hfull original hmem'
        · subst hobj
          simp only [lookupAt, valueAt, List.drop_zero, List.find?_map, Option.map_map]
          rfl

/-- Completeness: the proof that `getProof` builds verifies against the trie's root, and gives the key's value.

The keys must have distinct paths, which holds for distinct keys in a plain trie and for distinct hashes in a secured trie. -/
theorem verifyProof_getProof (hash : ByteArray → Hash32) {trie : Trie} {key : ByteArray} {root' : Hash32}
    {proof : List ByteArray}
    (hroot : root hash trie = .ok root') (hproof : getProof hash trie key = .ok proof)
    (hpaths : (trie.data.map fun entry => keyPath hash trie.secured entry.1).Nodup) :
    verifyProof hash root' trie.secured key proof = .ok (valueAt hash trie key) := by
  obtain ⟨rootNode, encoded, below, hnode, hencode, rfl, rfl, hbelow, honest, hlookup⟩ :=
    honest_root hroot hproof hpaths
  have hwalk :=
    walk_honest hash _ _ honest (Nat.lt_succ_self _) (Nat.lt_succ_self _) hnode hbelow []
  simp only [List.append_nil] at hwalk
  simp only [verifyProof, resolve_hash hash hencode, Bind.bind, Except.bind, hwalk, hlookup]
  rfl

/-- In a plain trie, the value that a proof gives is the value of the key itself, which `trieGet` reads. -/
theorem valueAt_plain (hash : ByteArray → Hash32) (data : List (ByteArray × ByteArray)) (key : ByteArray) :
    valueAt hash ⟨false, data⟩ key = (data.find? fun entry => sameBytes entry.1 key).map Prod.snd := by
  unfold valueAt
  congr 1
  apply find?_congr
  intro entry _
  -- Two keys have the same nibbles exactly when they are the same bytes.
  simp only [keyPath, Bool.false_eq_true, ↓reduceIte]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, sameBytes_iff]
  constructor
  · intro h
    exact bytesToNibbleList_injective h
  · intro h
    rw [h]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem ProofError.code_injective (e₁ e₂ : ProofError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ProofError.code] at h; exact absurd h (by decide))

/-- A proof error never has the code of a trie error, so one Python class carries both. -/
theorem ProofError.code_ne_trie (e : ProofError) (r : TrieError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [ProofError.code, TrieError.code] <;> decide

end EthLib.Execution.Trie
