module

public import EthLib.Serialization.Proofs.Ssz.Codec.BindingTrace
public import EthLib.Serialization.Proofs.Ssz.Codec.NodeWidths
public import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain

/-! Expanded commitment computations preserve the executable root and complete node widths. -/

@[expose] public section

namespace EthLib.Serialization.Ssz.CommitmentTree

/-- Complete supplied computations remain complete when arranged in a perfect tree. -/
theorem perfectTrees_complete (depth : Nat) (trees : Nat → CommitmentTree)
    (complete : ∀ i, (trees i).Complete) : (perfectTrees depth trees).Complete := by
  -- Combining complete child computations preserves their complete leaves at every added tree level.
  induction depth generalizing trees with
  | zero => exact complete 0
  | succ depth ih => exact ⟨ih _ complete, ih _ (fun i => complete _)⟩

/-- Implicit padding preserves complete node widths. -/
theorem bounded_complete (trees : Array CommitmentTree) (capacity : Nat)
    (complete : ∀ tree ∈ trees, tree.Complete) : (bounded trees capacity).Complete := by
  -- Each padded position selects either a complete supplied computation or a plain 32-byte zero node.
  apply perfectTrees_complete
  intro i
  unfold paddedTrees
  cases found : trees[i]? with
  | none => simp [Complete]
  | some tree => exact complete tree (Array.mem_of_getElem? found)

/-- Progressive grouping preserves complete nodes along its entire spine. -/
theorem progressive_complete (trees : List CommitmentTree) (level : Nat)
    (complete : ∀ tree ∈ trees, tree.Complete) : (progressive trees level).Complete := by
  -- The bounded prefix and the remaining spine both inherit completeness from the supplied positions.
  induction trees, level using progressive.induct with
  | case1 trees level empty => simp [progressive, empty, Complete]
  | case2 trees level nonempty ih =>
    rw [progressive, ite_eq_right nonempty]
    exact ⟨bounded_complete _ _ (fun tree member => complete tree
      (List.mem_of_mem_take (by simpa using member))),
      ih (fun tree member => complete tree (List.mem_of_mem_drop member))⟩

end EthLib.Serialization.Ssz.CommitmentTree

namespace EthLib.Serialization.Ssz

private theorem trace_slots (hash : ByteArray → ByteArray) (budget : Nat)
    (children : ∀ shape value root,
      (hashTreeRootAtM (Hasher.ofHash (m := Id) hash) budget shape value).run = .ok root →
      ∃ tree, valueTreeAt budget shape value = .ok tree ∧ tree.root hash = root ∧ tree.Complete) :
    ∀ (slots : List (Option (Desc × Value))) (roots : List Bytes),
    slots.mapM (fun slot : Option (Desc × Value) => match slot with
      | none => Except.ok zeroChunk
      | some (shape, value) =>
        (hashTreeRootAtM (Hasher.ofHash (m := Id) hash) budget shape value).run) = .ok roots →
    ∃ trees : List CommitmentTree, slots.mapM (fun slot : Option (Desc × Value) => match slot with
      | none => Except.ok (CommitmentTree.leaf zeroChunk)
      | some (shape, value) => valueTreeAt budget shape value) = .ok trees ∧
      trees.map (·.root hash) = roots ∧ ∀ tree ∈ trees, tree.Complete := by
  -- Expand each occupied slot recursively while preserving its position in the root sequence.
  intro slots
  induction slots with
  | nil =>
    intro roots success
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at success
    subst roots
    exact ⟨[], rfl, rfl, by simp⟩
  | cons slot slots ih =>
    intro roots success
    simp only [List.mapM_cons] at success
    -- Successful materialization requires the head slot and the remaining slots to root successfully.
    cases first : (match slot with
      | none => Except.ok zeroChunk
      | some (shape, value) =>
        (hashTreeRootAtM (Hasher.ofHash (m := Id) hash) budget shape value).run) <;>
    cases rest : slots.mapM (fun slot : Option (Desc × Value) => match slot with
      | none => Except.ok zeroChunk
      | some (shape, value) =>
        (hashTreeRootAtM (Hasher.ofHash (m := Id) hash) budget shape value).run) <;>
      simp only [first, rest, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        reduceCtorEq] at success
    rename_i root _
    -- The remaining slots already have complete expanded computations with the expected roots.
    obtain ⟨trees, traced, same, complete⟩ := ih _ rest
    -- A gap contributes a plain zero leaf, while an occupied slot uses the recursive child expansion.
    obtain ⟨tree, wrote, rooted, width⟩ : ∃ tree, (match slot with
        | none => Except.ok (CommitmentTree.leaf zeroChunk)
        | some (shape, value) => valueTreeAt budget shape value) = .ok tree ∧
        tree.root hash = root ∧ tree.Complete := by
      cases slot with
      | none => cases first; exact ⟨.leaf zeroChunk, rfl, rfl, zeroChunk_size⟩
      | some pair => exact children pair.1 pair.2 root first
    -- Prepending the expanded head preserves ordered roots and complete node widths.
    exact ⟨tree :: trees,
      by simp only [List.mapM_cons, wrote, traced, Bind.bind, Except.bind, pure, Except.pure],
      by simpa [same, rooted] using success, List.forall_mem_cons.mpr ⟨width, complete⟩⟩

/--
Every root that a hash computes has a complete expanded computation with exactly that result.

The zero subtrees are expanded into the binary hashes they stand for.
-/
theorem valueTreeAt_of_hashTreeRootAtM (hash : ByteArray → ByteArray)
    (budget : Nat) (shape : Desc) (value : Value) (root : Bytes)
    (success : (hashTreeRootAtM (Hasher.ofHash (m := Id) hash) budget shape value).run = .ok root) :
    ∃ tree, valueTreeAt budget shape value = .ok tree ∧ tree.root hash = root ∧ tree.Complete := by
  -- Each occupied child uses one less recursion step, matching the executable root computation.
  induction budget generalizing shape value root with
  | zero => simp [hashTreeRootAtM_id_zero] at success
  | succ budget ih =>
    -- Read the run as a plain computation with errors.
    replace success : @Eq (Except Err Bytes)
        (hashTreeRootAtM (Hasher.ofHash (m := Id) hash) (budget + 1) shape value).run
        (.ok root) := success
    -- Overall success requires the layout and all selected child roots to exist.
    cases laid : merkleLayout shape value with
    | error err => simp [hashTreeRootAtM_id_succ, laid, Bind.bind, Except.bind] at success
    | ok layout =>
      cases materialized : (layoutChunksAtM (Hasher.ofHash (m := Id) hash) budget layout).run with
      | error err => simp [hashTreeRootAtM_id_succ, laid, materialized, Bind.bind,
          Except.bind] at success
      | ok chunks =>
        replace materialized : @Eq (Except Err (Array Bytes))
            (layoutChunksAtM (Hasher.ofHash (m := Id) hash) budget layout).run
            (.ok chunks) := materialized
        -- Successful layouts contain 32-byte packed nodes and 32-byte mixing words.
        have widths := merkleLayout_width shape value layout laid
        -- Replace every materialized root by a complete computation with exactly that root.
        have tracing : ∃ trees, layoutTreesAt budget layout = .ok trees ∧
            trees.map (·.root hash) = chunks ∧ ∀ tree ∈ trees, tree.Complete := by
          cases leaves : layout.leaves with
          -- Packed nodes need no internal hashes, so plain leaves already reproduce them.
          | packed data =>
            have eqChunks : data = chunks := by
              simpa [layoutChunksAtM_id_eq, leaves, Leaves.count, pure, Except.pure]
                using materialized
            subst chunks
            exact ⟨data.map CommitmentTree.leaf, by simp [layoutTreesAt, leaves],
              by simp [Array.map_map, Function.comp_def, CommitmentTree.root], by
                intro tree member
                obtain ⟨node, inside, rfl⟩ := Array.mem_map.mp member
                exact widths.1 data leaves node inside⟩
          -- Nested slots are expanded in order, including the zero leaves occupying gaps.
          | nested slots =>
            simp only [layoutChunksAtM_id_eq, leaves, Leaves.count, Option.getD_none,
              List.drop_zero, Nat.sub_zero, List.take_length] at materialized
            -- List materialization comes before the array, so each slot remains identifiable.
            have normalized : (slots.mapM (fun slot : Option (Desc × Value) => match slot with
                | none => Except.ok zeroChunk
                | some (shape, value) =>
                  (hashTreeRootAtM (Hasher.ofHash (m := Id) hash) budget shape value).run)).bind
                (fun roots => Except.ok roots.toArray) = .ok chunks := by
              apply Eq.trans ?_ materialized
              congr 2
            cases rooted : slots.mapM (fun slot : Option (Desc × Value) => match slot with
              | none => Except.ok zeroChunk
              | some (shape, value) =>
                (hashTreeRootAtM (Hasher.ofHash (m := Id) hash) budget shape value).run) <;>
              simp only [Except.bind, rooted, Except.ok.injEq, reduceCtorEq] at normalized
            -- The slot expansion keeps the ordered roots and gives complete child computations.
            obtain ⟨trees, traced, same, complete⟩ := trace_slots hash budget ih slots _ rooted
            refine ⟨trees.toArray, ?_, by simpa [List.map_toArray, same] using normalized,
              by simpa using complete⟩
            simp only [layoutTreesAt, leaves, pure, Except.pure, Bind.bind, Except.bind]
            apply Eq.trans ?_ (congrArg (fun result : Except Err (List CommitmentTree) =>
              result.bind fun result => Except.ok result.toArray) traced)
            congr 2
        obtain ⟨trees, traced, rooted, complete⟩ := tracing
        -- Replacing each root with its computation preserves the leaf count used for capacity checks.
        have counts : trees.size = chunks.size := by rw [← rooted, Array.size_map]
        cases limited : layout.limit with
        -- With no fixed capacity, the expanded progressive spine uses the same prefix roots and suffixes.
        | none =>
          have eqRoot :
              ((CommitmentTree.progressive trees.toList).withMixin layout.mixin).root hash
                = root := by
            cases mixed : layout.mixin <;>
              simpa [mixed, hashTreeRootAtM_id_succ, laid, materialized, limited, Bind.bind,
              Except.bind, pure, Except.pure, CommitmentTree.withMixin_root_ofHash (hash := hash),
              CommitmentTree.progressive_root_ofHash (hash := hash), List.map_toArray,
              ← Array.toList_map, rooted]
              using success
          refine ⟨(CommitmentTree.progressive trees.toList).withMixin layout.mixin,
            by simp [valueTreeAt, laid, traced, limited, Bind.bind, Except.bind, pure, Except.pure],
            eqRoot, ?_⟩
          -- Complete children give a complete progressive tree before any metadata is attached.
          have full := CommitmentTree.progressive_complete trees.toList 0 (by simpa using complete)
          -- A complete metadata word preserves completeness when attached as the final right child.
          cases mixed : layout.mixin with
          | none => exact full
          | some word => exact ⟨full, widths.2 word mixed⟩
        -- A bounded root can succeed only when its capacity covers every materialized child.
        | some capacity =>
          by_cases over : capacity < chunks.size
          · simp [hashTreeRootAtM_id_succ, laid, materialized, limited,
              merkleizeBoundedUncheckedM_id_eq, over, Bind.bind, Except.bind] at success
          · have bounded := CommitmentTree.bounded_complete trees capacity complete
            -- Expanding padding and nested children keeps the tree root and the final hash.
            have eqRoot :
                ((CommitmentTree.bounded trees capacity).withMixin layout.mixin).root hash
                  = root := by
              cases mixed : layout.mixin <;>
                simpa [mixed, hashTreeRootAtM_id_succ, laid, materialized, limited,
                merkleizeBoundedUncheckedM_id_eq, over, Bind.bind, Except.bind, pure, Except.pure,
                CommitmentTree.withMixin_root_ofHash (hash := hash),
                CommitmentTree.bounded_root_ofHash (hash := hash), rooted] using success
            refine ⟨(CommitmentTree.bounded trees capacity).withMixin layout.mixin,
              by simp [valueTreeAt, laid, traced, limited, counts, over, Bind.bind, Except.bind,
                pure, Except.pure], eqRoot, ?_⟩
            cases mixed : layout.mixin with
            | none => exact bounded
            | some word => exact ⟨bounded, widths.2 word mixed⟩

/--
Every successful SSZ root has a complete expanded computation with exactly the same result.

Cached zero subtrees are expanded into the binary hashes they represent.
-/
theorem valueTreeAt_of_hashTreeRootAt (budget : Nat) (shape : Desc) (value : Value)
    (root : Bytes) (success : hashTreeRootAt budget shape value = .ok root) :
    ∃ tree, valueTreeAt budget shape value = .ok tree ∧ tree.root = root ∧ tree.Complete := by
  -- The specification's hasher is the one built from SHA-256 alone.
  rw [hashTreeRootAt, ← ofHash_sha256] at success
  exact valueTreeAt_of_hashTreeRootAtM _ budget shape value root success

/-- A successful expanded computation with sufficient type depth is complete and refines the SSZ root. -/
theorem valueTreeAt_complete {budget : Nat} {shape : Desc} {value : Value}
    {tree : CommitmentTree} (enough : shape.nesting ≤ budget)
    (sound : shape.wellFormed = .ok ()) (fits : Fits shape value)
    (traced : valueTreeAt budget shape value = .ok tree) :
    tree.Complete ∧ hashTreeRootAt budget shape value = .ok tree.root := by
  -- Admissibility and a sufficient type-depth budget guarantee an executable root.
  obtain ⟨root, rooted, _⟩ := hashTreeRootAt_total budget shape value enough sound fits
  -- Expanding that root yields a complete computation with the same result.
  obtain ⟨other, otherTrace, same, complete⟩ :=
    valueTreeAt_of_hashTreeRootAt budget shape value root rooted
  -- Deterministic expansion identifies that complete computation with the supplied successful one.
  cases Except.ok.inj (traced.symm.trans otherTrace)
  exact ⟨complete, same ▸ rooted⟩

/-- The public root computation has a complete trace with exactly the same commitment. -/
theorem valueTree_of_hashTreeRoot (shape : Desc) (value : Value) (root : Bytes)
    (success : hashTreeRoot shape value = .ok root) :
    ∃ tree, valueTree shape value = .ok tree ∧ tree.root = root ∧ tree.Complete :=
  -- The public root and its expansion use the same budget derived from the type depth.
  valueTreeAt_of_hashTreeRootAt shape.nesting shape value root success

/-- The root that any hash computes has a complete trace with exactly that commitment. -/
theorem valueTree_of_hashTreeRootM (hash : ByteArray → ByteArray) (shape : Desc) (value : Value)
    (root : Bytes)
    (success : (hashTreeRootM (Hasher.ofHash (m := Id) hash) shape value).run = .ok root) :
    ∃ tree, valueTree shape value = .ok tree ∧ tree.root hash = root ∧ tree.Complete :=
  -- The root and its expansion use the same budget derived from the type depth.
  valueTreeAt_of_hashTreeRootAtM hash shape.nesting shape value root success

private theorem mapM_success_relation {α β ε : Type} (f : α → Except ε β)
    {xs : List α} {ys : List β} (success : xs.mapM f = .ok ys) :
    ys.length = xs.length ∧ ∀ i (hi : i < xs.length) (hj : i < ys.length),
      f xs[i] = .ok ys[i] := by
  -- An error-free list traversal produces one result for each input, in the same order.
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at success
    subst ys
    exact ⟨rfl, by simp⟩
  | cons x xs ih =>
    -- Overall success excludes failure in either the head operation or the remaining traversal.
    cases head : f x <;> cases tail : xs.mapM f <;>
      simp only [List.mapM_cons, head, tail, Bind.bind, Except.bind, pure, Except.pure,
        Except.ok.injEq, reduceCtorEq] at success
    subst ys
    -- The tail already preserves its count and the result associated with each input position.
    obtain ⟨lengths, each⟩ := ih tail
    refine ⟨by simp [lengths], fun i hi hj => ?_⟩
    -- The first position uses the head result, while each later position refers to the tail traversal.
    cases i with
    | zero => exact head
    | succ i => exact each i (by simpa using hi) (by simpa using hj)

/-- Nested materialization records one successful child computation at every supplied slot. -/
theorem layoutTreesAt_nested_relation (budget : Nat) (layout : MerkleLayout)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (trees : Array CommitmentTree) (success : layoutTreesAt budget layout = .ok trees) :
    trees.size = slots.length ∧ ∀ i (hi : i < slots.length) (hj : i < trees.size),
      match slots[i] with
      | none => trees[i] = CommitmentTree.leaf zeroChunk
      | some (shape, value) => valueTreeAt budget shape value = .ok trees[i] := by
  -- Each slot either expands its selected value or contributes a plain zero leaf for a gap.
  let f : Option (Desc × Value) → Except Err CommitmentTree := fun slot => match slot with
    | none => .ok (.leaf zeroChunk)
    | some (shape, value) => valueTreeAt budget shape value
  -- Separate the ordered list traversal from its final conversion to an array.
  have normalized : (slots.mapM f).bind (fun result => .ok result.toArray) = .ok trees := by
    apply Eq.trans ?_ success
    simp only [layoutTreesAt, nested, pure, Except.pure, Bind.bind]
    congr 2
  cases wrote : slots.mapM f <;> simp only [wrote, Except.bind, Except.ok.injEq, reduceCtorEq] at normalized
  subst trees
  -- Successful traversal gives both the preserved position count and each slot's exact result.
  obtain ⟨lengths, each⟩ := mapM_success_relation f wrote
  refine ⟨by simpa using lengths, fun i hi hj => ?_⟩
  have rooted := each i hi (by simpa using hj)
  -- At an inactive position the result is a zero leaf.
  -- An occupied position retains its own value expansion.
  cases selected : slots[i] with
  | none =>
    simp only [f, selected, Except.ok.injEq] at rooted
    exact rooted.symm
  | some pair =>
    simpa only [f, selected, List.getElem_toArray] using rooted

/-- Nested traces retain exactly the number of declared slots, including inactive slots. -/
theorem layoutTreesAt_nested_size (budget : Nat) (layout : MerkleLayout)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (trees : Array CommitmentTree) (success : layoutTreesAt budget layout = .ok trees) :
    trees.size = slots.length :=
  -- The positional correspondence also states that materialization never drops or adds a slot.
  (layoutTreesAt_nested_relation budget layout slots nested trees success).1

/-- Every present nested slot is the trace of its selected value at the same position. -/
theorem layoutTreesAt_nested_getElem (budget : Nat) (layout : MerkleLayout)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (trees : Array CommitmentTree) (success : layoutTreesAt budget layout = .ok trees)
    (index : Nat) (inside : index < slots.length) (child : Desc) (value : Value)
    (selected : slots[index] = some (child, value)) :
    valueTreeAt budget child value = .ok (trees[index]'(by
      rw [layoutTreesAt_nested_size budget layout slots nested trees success]; exact inside)) := by
  -- Specialize the positional correspondence to the occupied slot selected by the caller.
  have relation := layoutTreesAt_nested_relation budget layout slots nested trees success
  -- The preserved slot count makes the same position valid in the materialized array.
  have atIndex := relation.2 index inside (by omega)
  simpa only [selected] using atIndex

end EthLib.Serialization.Ssz
