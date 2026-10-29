import EthLib.Consensus.Ssz.Codec.Root
import EthLib.Consensus.Proofs.Ssz.Codec.LayoutLaws

/-! Type depth bounds rooting, and materialized leaves preserve positions and intervals. -/

namespace EthLib.Consensus.Ssz

private theorem mapM_window {α β ε : Type} (f : α → Except ε β)
    {xs : List α} {ys : List β} (success : xs.mapM f = .ok ys)
    (start count : Nat) :
    ((xs.drop start).take count).mapM f = .ok ((ys.drop start).take count) := by
  -- A successful traversal supplies a successful root for each retained position.
  induction xs generalizing ys start count with
  | nil => simp_all [Pure.pure, Except.pure]
  | cons x xs ih =>
    cases hx : f x <;> cases ht : xs.mapM f <;>
      simp_all [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure, eq_comm (b := ys)]
    -- Skipping removes a matched pair, while taking retains the same root.
    rcases start with _ | start <;> rcases count with _ | count <;>
      simp_all [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have := ih 0 count
    simp_all

private theorem mapM_congr_on {α β ε : Type} (f g : α → Except ε β)
    (xs : List α) (same : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  -- Equal roots at every occupied position give equal traversals, including errors.
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, same x (by simp),
      ih (fun y hy => same y (by simp [hy]))]

/-- Type depth bounds all recursion, so larger budgets give exactly the same root or error. -/
theorem hashTreeRootAt_budget_eq (shape : Desc) (value : Value) (left right : Nat)
    (leftEnough : shape.nesting ≤ left) (rightEnough : shape.nesting ≤ right) :
    hashTreeRootAt left shape value = hashTreeRootAt right shape value := by
  -- Each present leaf has strictly smaller type depth, independent of its value.
  generalize depthEq : shape.nesting = depth
  induction depth using Nat.strongRecOn generalizing shape value left right with
  | ind depth ih =>
    have positive : 0 < shape.nesting := by
      cases shape <;> simp [Desc.nesting]
    rcases left with _ | left; · omega
    rcases right with _ | right; · omega
    -- Layout selection itself is independent of recursion budget.
    cases hl : merkleLayout shape value with
    | error e => simp [hashTreeRootAt, hl, Bind.bind, Except.bind]
    | ok layout =>
      -- Equal child roots give equal leaves before either tree shape hashes them.
      have chunksEq : layoutChunksAt left layout = layoutChunksAt right layout := by
        rcases layout with ⟨leaves, limit, mixin⟩
        cases leaves with
        | packed data => simp [layoutChunksAt]
        | nested slots =>
          simp only [layoutChunksAt, Leaves.count, Option.getD_none,
            List.drop_zero, Nat.sub_zero, List.take_length]
          apply congrArg (fun result : Except Err (List Bytes) =>
            result.bind (fun nodes => .ok nodes.toArray))
          apply mapM_congr_on
          intro slot member
          cases slot with
          | none => rfl
          | some pair =>
            -- Entering one child spends one level from each sufficient budget.
            have smaller := merkleLayout_child_nesting shape value _ hl slots rfl
              pair.1 pair.2 member
            exact ih pair.1.nesting (by omega) pair.1 pair.2 left right
              (by omega) (by omega) rfl
      simp [hashTreeRootAt, hl, chunksEq, Bind.bind, Except.bind]

/-- Any sufficient recursion budget agrees with the root computed at the type's own depth. -/
theorem hashTreeRootAt_eq_hashTreeRoot (shape : Desc) (value : Value) (budget : Nat)
    (enough : shape.nesting ≤ budget) :
    hashTreeRootAt budget shape value = hashTreeRoot shape value := by
  -- The public root chooses exactly the declared nesting depth.
  exact hashTreeRootAt_budget_eq shape value budget shape.nesting enough (Nat.le_refl _)

/-- A successful value root comes from a complete layout and a successful contents tree. -/
theorem hashTreeRoot_materializes (shape : Desc) (value : Value) (root : Bytes)
    (success : hashTreeRoot shape value = .ok root) :
    ∃ layout chunks contents,
      merkleLayout shape value = .ok layout ∧
      layoutChunksAt (shape.nesting - 1) layout = .ok chunks ∧
      (match layout.limit with
        | none => Except.ok (merkleizeProgressiveUnchecked chunks.toList)
        | some capacity => merkleizeBoundedUnchecked chunks (some capacity)) = .ok contents ∧
      root = (match layout.mixin with
        | none => contents
        | some word => mixIn contents word) := by
  -- Every intermediate failure is propagated before the final root can be returned.
  have positive : 0 < shape.nesting := by cases shape <;> simp [Desc.nesting]
  unfold hashTreeRoot at success
  cases depth : shape.nesting with
  | zero => omega
  | succ budget =>
    cases laid : merkleLayout shape value with
    | error e => simp [depth, hashTreeRootAt, laid, Bind.bind, Except.bind] at success
    | ok layout =>
      cases materialized : layoutChunksAt budget layout with
      | error e => simp [depth, hashTreeRootAt, laid, materialized, Bind.bind, Except.bind] at success
      | ok chunks =>
        cases contents : (match layout.limit with
          | none => Except.ok (merkleizeProgressiveUnchecked chunks.toList)
          | some capacity => merkleizeBoundedUnchecked chunks (some capacity)) with
        | error e =>
          simp only [depth, hashTreeRootAt, laid, materialized, Bind.bind, Except.bind] at success
          cases limit : layout.limit <;> simp_all
        | ok tree =>
          refine ⟨layout, chunks, tree, rfl, by simpa [depth] using materialized, contents, ?_⟩
          simp only [depth, hashTreeRootAt, laid, materialized, Bind.bind, Except.bind] at success
          cases limit : layout.limit <;>
            simp_all [Pure.pure, Except.pure]
          all_goals exact success.symm

/-- Leaf intervals are budget-independent once both budgets cover every nested type. -/
theorem layoutChunksAt_budget_eq (layout : MerkleLayout) (left right : Nat)
    (enough : ∀ slots, layout.leaves = .nested slots →
      ∀ child inner, some (child, inner) ∈ slots →
        child.nesting ≤ left ∧ child.nesting ≤ right)
    (start : Nat := 0) (stop : Option Nat := none) :
    layoutChunksAt left layout start stop = layoutChunksAt right layout start stop := by
  -- Slicing only removes leaves, so the depth bound still covers every visited value.
  rcases layout with ⟨leaves, limit, mixin⟩
  cases leaves with
  | packed data => simp [layoutChunksAt]
  | nested slots =>
    simp only [layoutChunksAt]
    apply congrArg (fun result : Except Err (List Bytes) =>
      result.bind (fun nodes => .ok nodes.toArray))
    apply mapM_congr_on
    intro slot member
    cases slot with
    | none => rfl
    | some pair =>
      -- A member of a sliced interval is still a member of the original nested layout.
      have bounds := enough slots rfl pair.1 pair.2
        (List.mem_of_mem_drop (List.mem_of_mem_take member))
      exact hashTreeRootAt_budget_eq pair.1 pair.2 left right bounds.1 bounds.2

private theorem mapM_length {α β ε : Type} (f : α → Except ε β)
    {xs : List α} {ys : List β} (success : xs.mapM f = .ok ys) :
    ys.length = xs.length := by
  -- A successful traversal replaces each input by exactly one output.
  induction xs generalizing ys with
  | nil => simp_all [Pure.pure, Except.pure]
  | cons x xs ih =>
    cases hx : f x <;> cases ht : xs.mapM f <;>
      simp_all [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure, eq_comm (b := ys)]

/-- Successful materialization produces one node per leaf, including empty positions. -/
theorem layoutChunksAt_size (budget : Nat) (layout : MerkleLayout)
    (chunks : Array Bytes) (success : layoutChunksAt budget layout = .ok chunks) :
    chunks.size = layout.leaves.count := by
  -- Packed data already counts nodes, and nested traversal preserves the slot count.
  rcases layout with ⟨leaves, limit, mixin⟩
  cases leaves with
  | packed data =>
    simp only [layoutChunksAt, pure, Except.pure, Leaves.count, Option.getD_none, Array.extract_size,
      Except.ok.injEq] at success
    subst chunks
    rfl
  | nested values =>
    simp only [layoutChunksAt, Leaves.count, Option.getD_none, List.drop_zero,
      Nat.sub_zero, List.take_length] at success
    let f : Option (Desc × Value) → Except Err Bytes := fun slot =>
      match slot with
      | none => .ok zeroChunk
      | some (shape, value) => hashTreeRootAt budget shape value
    change (do let ys ← values.mapM f; pure ys.toArray) = .ok chunks at success
    cases h : values.mapM f with
    | error e => simp [h, Bind.bind, Except.bind] at success
    | ok ys =>
      simp only [bind, Except.bind, h, pure, Except.pure, Except.ok.injEq] at success
      subst chunks
      exact mapM_length f h

private theorem mapM_success_member {α β ε : Type} (f : α → Except ε β)
    {xs : List α} {ys : List β} (success : xs.mapM f = .ok ys)
    (x : α) (member : x ∈ xs) : ∃ y, f x = .ok y := by
  -- A successful complete traversal cannot hide an error at any included position.
  induction xs generalizing ys with
  | nil => simp at member
  | cons first rest ih =>
    cases head : f first <;> cases tail : rest.mapM f <;>
      simp_all [List.mapM_cons, Bind.bind, Except.bind]
    rcases member with rfl | member <;> simp_all

/-- Every present leaf of a successfully materialized layout has a successful root. -/
theorem layoutChunksAt_child_root (budget : Nat) (layout : MerkleLayout)
    (chunks : Array Bytes) (success : layoutChunksAt budget layout = .ok chunks)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (child : Desc) (inner : Value) (member : some (child, inner) ∈ slots) :
    ∃ root, hashTreeRootAt budget child inner = .ok root := by
  -- Materialization roots every present slot before returning the array of leaves.
  simp only [layoutChunksAt, nested, Leaves.count, Option.getD_none, List.drop_zero,
    Nat.sub_zero, List.take_length] at success
  let f : Option (Desc × Value) → Except Err Bytes := fun slot =>
    match slot with
    | none => .ok zeroChunk
    | some (shape, value) => hashTreeRootAt budget shape value
  change (do let ys ← slots.mapM f; pure ys.toArray) = .ok chunks at success
  cases h : slots.mapM f with
  | error e => simp [h, Bind.bind, Except.bind] at success
  | ok ys => exact mapM_success_member f h (some (child, inner)) member

/-- Rooting an interval agrees with slicing a successful materialization of all leaves. -/
theorem layoutChunksAt_window (budget : Nat) (layout : MerkleLayout)
    (chunks : Array Bytes) (success : layoutChunksAt budget layout = .ok chunks)
    (start stop : Nat) :
    layoutChunksAt budget layout start (some stop) = .ok (chunks.extract start stop) := by
  -- Packed nodes are already materialized, so only nested values require traversal.
  rcases layout with ⟨leaves, limit, mixin⟩
  cases leaves with
  | packed data =>
    simp only [layoutChunksAt, pure, Except.pure, Leaves.count, Option.getD_none, Array.extract_size,
      Except.ok.injEq, Option.getD_some] at success ⊢
    subst chunks
    rfl
  | nested values =>
    let root : Option (Desc × Value) → Except Err Bytes := fun slot =>
      match slot with
      | none => pure zeroChunk
      | some (shape, value) => hashTreeRootAt budget shape value
    simp only [layoutChunksAt, Leaves.count, Option.getD_none, List.drop_zero,
      Nat.sub_zero, List.take_length] at success
    change (do let ys ← values.mapM root; pure ys.toArray) = .ok chunks at success
    cases h : values.mapM root with
    | error e => simp [h, Bind.bind, Except.bind] at success
    | ok ys =>
      simp only [bind, Except.bind, h, pure, Except.pure, Except.ok.injEq] at success
      subst chunks
      -- List slicing and array slicing use the same half-open interval.
      -- Rooting and slicing commute because each retained position has an independent successful root.
      have window := mapM_window root h start (stop - start)
      simp only [layoutChunksAt, Option.getD_some]
      change (do
        let zs ← ((values.drop start).take (stop - start)).mapM root
        pure zs.toArray) = .ok (ys.toArray.extract start stop)
      rw [window]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure,
        List.extract_toArray, List.extract_eq_take_drop]

/-- A one-leaf interval roots exactly that nested value, or returns zero for an empty slot. -/
theorem layoutChunksAt_singleton (budget : Nat) (layout : MerkleLayout)
    (slots : List (Option (Desc × Value))) (nested : layout.leaves = .nested slots)
    (index : Nat) (inside : index < slots.length) :
    layoutChunksAt budget layout index (some (index + 1)) =
      (do
        let root ← match slots[index] with
          | none => pure zeroChunk
          | some (child, inner) => hashTreeRootAt budget child inner
        pure #[root]) := by
  -- A one-position half-open interval retains exactly the selected slot after its prefix is removed.
  simp only [layoutChunksAt, nested, Option.getD_some, Nat.add_sub_cancel_left,
    List.drop_eq_getElem_cons inside, List.take_succ_cons, List.take_zero,
    List.mapM_cons, List.mapM_nil]
  cases slot : slots[index] with
  | none => rfl
  | some pair =>
    cases root : hashTreeRootAt budget pair.1 pair.2 <;>
      simp [root, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Rooting a suffix agrees with dropping the same prefix of all materialized leaves. -/
theorem layoutChunksAt_suffix (budget : Nat) (layout : MerkleLayout)
    (chunks : Array Bytes) (success : layoutChunksAt budget layout = .ok chunks)
    (start : Nat) :
    layoutChunksAt budget layout start = .ok (chunks.extract start chunks.size) := by
  -- An omitted upper endpoint is the leaf count, which successful materialization preserves.
  have sized := layoutChunksAt_size budget layout chunks success
  have window := layoutChunksAt_window budget layout chunks success start layout.leaves.count
  simpa [layoutChunksAt, sized] using window

end EthLib.Consensus.Ssz
