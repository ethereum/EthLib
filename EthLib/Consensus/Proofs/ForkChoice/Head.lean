module

public import EthLib.Consensus.ForkChoice.Head
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Proofs.ForkChoice.Store

/-!
# Proofs: the head of the fork choice

The children of a node are the known blocks whose parent is the node's block.

The choice among weighted children returns one of them, and none of them is above it.

Without a boosted block, the weight of a node is its votes in the justified state.

The head has no child among the viable nodes, so the walk stops only at a leaf.

From Gloas the children, the weight and the head fail as not yet specified.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

/-- The heavier of two weighted nodes is at least as large as the first. -/
theorem heavier_ge_left (a b : ForkChoiceNode × Gwei) :
    (compareWeighted (heavier a b) a).isGE := by
  unfold heavier
  split
  · rename_i lt
    rw [Std.OrientedCmp.eq_swap (cmp := compareWeighted), lt]
    rfl
  · rw [Std.ReflCmp.compare_self (cmp := compareWeighted)]
    rfl

/-- The heavier of two weighted nodes is at least as large as the second. -/
theorem heavier_ge_right (a b : ForkChoiceNode × Gwei) :
    (compareWeighted (heavier a b) b).isGE := by
  unfold heavier
  split
  · rw [Std.ReflCmp.compare_self (cmp := compareWeighted)]
    rfl
  · rename_i notLt
    revert notLt
    cases compareWeighted a b <;> simp

/-- The heavier of two weighted nodes is one of them. -/
theorem heavier_eq (a b : ForkChoiceNode × Gwei) : heavier a b = a ∨ heavier a b = b := by
  unfold heavier
  split <;> simp

/-- Folding the choice over a list returns an element of the list. -/
theorem foldl_heavier_mem (first : ForkChoiceNode × Gwei) (rest : List (ForkChoiceNode × Gwei)) :
    rest.foldl heavier first ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldl_cons]
    have := ih (heavier first x)
    simp only [List.mem_cons] at this ⊢
    rcases heavier_eq first x with same | same <;> rw [same] at this ⊢
    · rcases this with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · rcases this with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr h)

/-- No element of the list is above the result of the fold. -/
theorem foldl_heavier_ge (first : ForkChoiceNode × Gwei) (rest : List (ForkChoiceNode × Gwei)) :
    ∀ x ∈ first :: rest, (compareWeighted (rest.foldl heavier first) x).isGE := by
  induction rest generalizing first with
  | nil =>
    intro x mem
    rw [List.mem_singleton.mp mem, List.foldl_nil,
      Std.ReflCmp.compare_self (cmp := compareWeighted)]
    rfl
  | cons y rest ih =>
    intro x mem
    have step := ih (heavier first y)
    rw [List.foldl_cons]
    simp only [List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · exact Std.TransCmp.isGE_trans (step _ List.mem_cons_self) (heavier_ge_left _ _)
    · exact Std.TransCmp.isGE_trans (step _ List.mem_cons_self) (heavier_ge_right _ _)
    · exact step x (List.mem_cons_of_mem _ mem)

/-- The choice returns the node of an element of the list, and no element is above it. -/
theorem chooseHeaviest_some {weighted : List (ForkChoiceNode × Gwei)} {chosen : ForkChoiceNode}
    (found : chooseHeaviest weighted = some chosen) :
    ∃ weight, (chosen, weight) ∈ weighted ∧
      ∀ x ∈ weighted, (compareWeighted (chosen, weight) x).isGE := by
  cases weighted with
  | nil => cases found
  | cons first rest =>
    simp only [chooseHeaviest, Option.some.injEq] at found
    subst found
    exact ⟨_, foldl_heavier_mem first rest, foldl_heavier_ge first rest⟩

/-- The choice returns none only on the empty list. -/
theorem chooseHeaviest_eq_none {weighted : List (ForkChoiceNode × Gwei)} :
    chooseHeaviest weighted = none ↔ weighted = [] := by
  cases weighted <;> simp [chooseHeaviest]

namespace Store

variable {config : Config} {store : Store preset fork}

/-- From Gloas the children of a node are not yet specified here, so they fail. -/
theorem getNodeChildren_of_gloas {node : ForkChoiceNode} (gloas : .glamsterdam ≤ fork) :
    store.getNodeChildren node = .error (.forkNotYetSpecified fork) := by
  simp [getNodeChildren, gloas, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map]

/-- From Gloas the weight of a node is not yet specified here, so it fails. -/
theorem getWeight_of_gloas {node : ForkChoiceNode} (gloas : .glamsterdam ≤ fork) :
    store.getWeight config node = .error (.forkNotYetSpecified fork) := by
  simp [getWeight, gloas, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- From Gloas the head is not yet specified here, so it fails. -/
theorem getHead_of_gloas (gloas : .glamsterdam ≤ fork) :
    store.getHead config = .error (.forkNotYetSpecified fork) := by
  simp [getHead, gloas, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- The children of a node are the pending nodes of the known blocks whose parent is its block. -/
theorem mem_getNodeChildren {node child : ForkChoiceNode} {children : List ForkChoiceNode}
    (found : store.getNodeChildren node = .ok children) :
    child ∈ children ↔ child.payloadStatus = .pending ∧
      ∃ block, store.blocks[child.root]? = some block ∧ block.parentRoot = node.root := by
  by_cases gloas : .glamsterdam ≤ fork
  · rw [getNodeChildren_of_gloas gloas] at found
    cases found
  simp only [getNodeChildren, gloas, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at found
  subst found
  obtain ⟨root, status⟩ := child
  simp only [List.mem_filterMap, Prod.exists, Std.TreeMap.mem_toList_iff_getElem?_eq_some]
  constructor
  · rintro ⟨r, block, found, choice⟩
    split at choice
    · cases choice
      exact ⟨rfl, block, found, ‹_›⟩
    · cases choice
  · rintro ⟨pending, block, found, parent⟩
    cases pending
    exact ⟨root, block, found, by simp [parent]⟩

/-- Without a boosted block, the weight of a node is its votes in the justified state. -/
theorem getWeight_of_no_boost {node : ForkChoiceNode} (before : fork < .glamsterdam)
    (noBoost : store.proposerBoostRoot = Vector.replicate 32 0) :
    store.getWeight config node =
      store.checkpointState store.justifiedCheckpoint >>= store.getAttestationScore node := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp [getWeight, later, noBoost]

/-- The heaviest child is computed from the weighted children among the given nodes. -/
theorem heaviestChild_eq {nodes : List ForkChoiceNode} {node : ForkChoiceNode}
    {result : Option ForkChoiceNode} (found : store.heaviestChild config nodes node = .ok result) :
    ∃ children weighted, store.getNodeChildren node = .ok children ∧
      (children.filter (· ∈ nodes)).mapM
        (fun child => (child, ·) <$> store.getWeight config child) = .ok weighted ∧
      chooseHeaviest weighted = result := by
  unfold heaviestChild at found
  cases hc : store.getNodeChildren node with
  | error e => simp [hc, bind, Except.bind] at found
  | ok children =>
    simp only [hc, bind, Except.bind] at found
    cases hw : (children.filter (· ∈ nodes)).mapM
        (fun child => (child, ·) <$> store.getWeight config child) with
    | error e => simp [hw] at found
    | ok weighted =>
      simp only [hw, pure, Except.pure, Except.ok.injEq] at found
      exact ⟨children, weighted, rfl, hw, found⟩

/-- The walk stops at a node with no child among the given nodes. -/
theorem getHeadFrom_leaf {nodes : List ForkChoiceNode} {start head : ForkChoiceNode}
    (walk : store.getHeadFrom config nodes start = .ok head) :
    ∃ children, store.getNodeChildren head = .ok children ∧ ∀ child ∈ children, child ∉ nodes := by
  induction start using getHeadFrom.induct store with
  | _ start ih =>
    rw [getHeadFrom] at walk
    cases found : store.heaviestChild config nodes start with
    | error e => simp [found, bind, Except.bind] at walk
    | ok result =>
      obtain ⟨children, weighted, hc, hw, choice⟩ := heaviestChild_eq found
      cases result with
      | none =>
        simp [found, bind, Except.bind, pure, Except.pure] at walk
        subst walk
        rw [chooseHeaviest_eq_none] at choice
        subst choice
        have empty := List.length_eq_zero_iff.mp (mapM_ok_length hw).symm
        refine ⟨children, hc, fun child mem inNodes => ?_⟩
        have : child ∈ children.filter (· ∈ nodes) := List.mem_filter.mpr ⟨mem, by simpa⟩
        rw [empty] at this
        cases this
      | some child =>
        simp only [found, bind, Except.bind] at walk
        split at walk
        · exact ih child ‹_› walk
        · cases walk

/-- The walk returns its starting node or one of the given nodes. -/
theorem getHeadFrom_mem {nodes : List ForkChoiceNode} {start head : ForkChoiceNode}
    (walk : store.getHeadFrom config nodes start = .ok head) : head = start ∨ head ∈ nodes := by
  induction start using getHeadFrom.induct store with
  | _ start ih =>
    rw [getHeadFrom] at walk
    cases found : store.heaviestChild config nodes start with
    | error e => simp [found, bind, Except.bind] at walk
    | ok result =>
      cases result with
      | none =>
        simp [found, bind, Except.bind, pure, Except.pure] at walk
        exact .inl walk.symm
      | some child =>
        simp only [found, bind, Except.bind] at walk
        split at walk
        · rcases ih child ‹_› walk with same | mem
          · obtain ⟨children, weighted, -, hw, choice⟩ := heaviestChild_eq found
            obtain ⟨weight, mem, -⟩ := chooseHeaviest_some choice
            rw [same]
            obtain ⟨source, member, pair⟩ := mapM_ok_mem hw _ mem
            cases weighed : store.getWeight config source <;>
              simp [weighed, Functor.map, Except.map] at pair
            obtain ⟨rfl, -⟩ := pair
            exact Or.inr (of_decide_eq_true (List.mem_filter.mp member).2)
          · exact .inr mem
        · cases walk

/-- The head has no child among the viable nodes. -/
theorem getHead_leaf {head : ForkChoiceNode} (found : store.getHead config = .ok head) :
    ∃ nodes children, store.getFilteredNodeTree config = .ok nodes ∧
      store.getNodeChildren head = .ok children ∧ ∀ child ∈ children, child ∉ nodes := by
  by_cases gloas : .glamsterdam ≤ fork
  · rw [getHead_of_gloas gloas] at found
    cases found
  simp only [getHead, gloas, ↓reduceIte, bind, Except.bind] at found
  cases tree : store.getFilteredNodeTree config with
  | error e => simp [tree] at found
  | ok nodes =>
    simp only [tree] at found
    obtain ⟨children, hc, leaf⟩ := getHeadFrom_leaf found
    exact ⟨nodes, children, rfl, hc, leaf⟩

end Store

end EthLib.Consensus
