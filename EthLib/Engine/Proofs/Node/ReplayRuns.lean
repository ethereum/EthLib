module

public import EthLib.Engine.Proofs.Node.Ancestry
import all EthLib.Engine.Proofs.Node.Ancestry
import all EthLib.Engine.Proofs.Node.Grounded
import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the valid blocks of an execution node run on the chain of their parent

Each valid block of a node reached from a starting block runs on the chain of its valid parent.

The starting block has no valid parent and no transaction, and the head of the node is valid.

It assumes that the node knows no block under the parent hash of the starting block.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Block BlockChain RecentBlock runBody stateTransition)
open EthLib.Execution.Transactions (Transaction)

namespace Node

variable {node : Node}

/-! ## A body that passes the transition runs -/

/-- A block that passes the transition has a body that runs on its chain. -/
private theorem runBody_of_stateTransition {chain : BlockChain} {fork : Fork}
    {block : Block fork Transaction} {checkSeal : Bool} {post : Execution.State.State}
    (h : stateTransition chain block checkSeal = .ok post) : ∃ r, runBody chain block = .ok r := by
  obtain ⟨-, -, -, hashes, output, roots, hHashes, hOutput, hRoots, -, -⟩ :=
    Execution.Blocks.stateTransition_eq_ok h
  exact ⟨⟨output, roots⟩, Execution.Blocks.runBody_eq_ok.mpr ⟨hashes, hHashes, hOutput, hRoots⟩⟩

/-! ## Each accepted block is the block of its kept request -/

/-- Each accepted block of a node is the block that the node decodes from its kept request. -/
private def Decodes (node : Node) : Prop :=
  ∀ hash b version params, node.blocks.lookup hash = some b →
    b.validity = .accepted version params → ∃ checked : CheckedBlock version,
      checkNewPayload node.config version params = .ok (.ok checked) ∧
        b.full = ⟨checked.fork, checked.block⟩

/-- Recording a block that is not accepted, or the block of its request, keeps the property. -/
private theorem Decodes.record {hash : Hash32} {b : KnownBlock} (hd : node.Decodes)
    (hb : ∀ version params, b.validity = .accepted version params →
      ∃ checked : CheckedBlock version,
        checkNewPayload node.config version params = .ok (.ok checked) ∧
          b.full = ⟨checked.fork, checked.block⟩) :
    (node.record hash b).Decodes := by
  intro x c version params hc hval
  by_cases hx : x = hash
  · subst hx
    simp only [Node.record, List.lookup, beq_self_eq_true, Option.some.injEq] at hc
    subst hc
    exact hb version params hval
  · rw [record_lookup_of_ne _ _ hx] at hc
    exact hd x c version params hc hval

/-- A run keeps the property. -/
private theorem Decodes.executeOn {hash : Hash32}
    {block : (fork : Fork) × Block fork Transaction} {post : Execution.State.State}
    {version : Nat} {params : Lean.Json} (hd : node.Decodes) :
    (node.executeOn hash block post version params).2.Decodes := by
  simp only [Node.executeOn]
  split
  · exact hd
  · simp only [recordExecution]
    split
    · exact hd.record fun _ _ h => by cases h
    · split
      · exact hd.record fun _ _ h => by cases h
      · exact hd

/-- The answer by the parent to the block of a request keeps the property. -/
private theorem Decodes.onParent {hash : Hash32} {version : Nat} {params : Lean.Json}
    {checked : CheckedBlock version} (hd : node.Decodes)
    (hC : checkNewPayload node.config version params = .ok (.ok checked)) :
    (node.onParent hash ⟨checked.fork, checked.block⟩ version params).2.Decodes := by
  simp only [Node.onParent]
  split
  · split
    · exact hd.executeOn
    · exact hd.record fun v p h => by cases h; exact ⟨checked, hC, rfl⟩
  · exact hd.record fun v p h => by cases h; exact ⟨checked, hC, rfl⟩
  · exact hd.record fun _ _ h => by cases h
  · exact hd

/-- A step of `engine_newPayload` keeps the property. -/
private theorem Decodes.newPayloadStep {version : Nat} {params : Lean.Json} (hd : node.Decodes) :
    (node.newPayloadStep version params).2.Decodes := by
  unfold Node.newPayloadStep
  split
  · exact hd
  · exact hd
  · rename_i checked hC
    dsimp only
    split
    · exact hd
    · split
      · exact hd
      · exact hd
      · exact hd.onParent hC

/-- Validation keeps the property. -/
private theorem Decodes.validateChain (hd : node.Decodes) (fuel : Nat) (hash : Hash32) :
    (node.validateChain fuel hash).Decodes := by
  induction fuel generalizing node hash with
  | zero => exact hd
  | succ fuel ih =>
    simp only [Node.validateChain]
    split
    · rename_i block pow v p hb
      have hd' := ih hd block.2.header.parentHash
      split
      · exact hd'.executeOn
      · exact hd'.record fun _ _ h => by cases h
      · exact hd'
    · exact hd

/-- A step of `engine_forkchoiceUpdated` keeps the property. -/
private theorem Decodes.forkchoiceUpdatedStep {version : Nat} {params : Lean.Json}
    (hd : node.Decodes) : (node.forkchoiceUpdatedStep version params).2.Decodes := by
  have hh : (node.validateHead version params).Decodes := by
    simp only [Node.validateHead]
    split
    · exact hd.validateChain _ _
    · exact hd
  simp only [Node.forkchoiceUpdatedStep]
  split
  · exact hh
  · simp only [updateStep]
    split
    · exact hh
    · exact hh

/-! ## Each valid block runs again on the chain of its parent -/

/-- A block runs on the chain of its valid parent, or sits on the root hash with no transaction. -/
private def RunsAt (node : Node) (root : Hash32) (b : KnownBlock) : Prop :=
  (∃ before, node.validState b.full.2.header.parentHash = some before ∧
    ∃ r, runBody (node.chainAt b.full.2.header.parentHash before) b.full.2 = .ok r) ∨
  (b.full.2.header.parentHash = root ∧ b.full.2.transactions = [])

/-- Each known valid block of a node runs on the chain of its parent, or has no transaction. -/
private def Runs (node : Node) (root : Hash32) : Prop :=
  ∀ hash b post, node.blocks.lookup hash = some b → b.validity = .valid post → node.RunsAt root b

/-- A block that runs in a node runs the same in a later node that does not know the root. -/
private theorem RunsAt.keeps {later : Node} {root : Hash32} {b : KnownBlock}
    (hv : node.ValidParents root) (hk : Keeps node later)
    (hRoot : later.blocks.lookup root = none) (h : node.RunsAt root b) : later.RunsAt root b := by
  rcases h with ⟨before, hs, r, hr⟩ | h
  · exact .inl ⟨before, hk.validState hs, r, by rw [hk.chainAt_eq hv hRoot hs]; exact hr⟩
  · exact .inr h

/-- A later node whose valid blocks are known as such before keeps the property. -/
private theorem Runs.mono {later : Node} {root : Hash32} (hR : node.Runs root)
    (hv : node.ValidParents root) (hk : Keeps node later)
    (hRoot : later.blocks.lookup root = none)
    (hNew : ∀ hash b post, later.blocks.lookup hash = some b → b.validity = .valid post →
      node.blocks.lookup hash = some b) : later.Runs root :=
  fun hash b post hb hval => (hR hash b post (hNew hash b post hb hval) hval).keeps hv hk hRoot

/-- Recording a block over a new or accepted hash keeps the property.

A valid recorded block must run on the chain of its parent, or have no transaction. -/
private theorem Runs.record {root hash : Hash32} {b : KnownBlock} (hR : node.Runs root)
    (hv : node.ValidParents root)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hRoot : (node.record hash b).blocks.lookup root = none)
    (hb : ∀ post, b.validity = .valid post → node.RunsAt root b) :
    (node.record hash b).Runs root := by
  intro x c post hc hval
  refine RunsAt.keeps hv (keeps_record hFresh) hRoot ?_
  by_cases hx : x = hash
  · subst hx
    simp only [Node.record, List.lookup, beq_self_eq_true, Option.some.injEq] at hc
    subst hc
    exact hb post hval
  · rw [record_lookup_of_ne _ _ hx] at hc
    exact hR x c post hc hval

/-- A run of the block of its request, on a valid parent, over a new or accepted hash, keeps it.

The block that runs is the block that the node records. -/
private theorem Runs.executeOn {root hash : Hash32} {version : Nat} {params : Lean.Json}
    {checked : CheckedBlock version} {post : Execution.State.State} (hR : node.Runs root)
    (hv : node.ValidParents root)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hC : checkNewPayload node.config version params = .ok (.ok checked))
    (hp : node.validState checked.block.header.parentHash = some post) :
    (node.executeOn hash ⟨checked.fork, checked.block⟩ post version params).2.blocks.lookup root =
      none →
      (node.executeOn hash ⟨checked.fork, checked.block⟩ post version params).2.Runs root := by
  simp only [Node.executeOn]
  cases hN : newPayloadOnChain node.transition
      (node.totalDifficulty checked.block.header.parentHash)
      (node.chainAt checked.block.header.parentHash post) version params with
  | error e => exact fun _ => hR
  | ok res =>
    obtain ⟨status, reason, next⟩ := res
    cases next with
    | none =>
      simp only [recordExecution]
      split
      · exact fun hRoot => hR.record hv hFresh hRoot fun _ h => by cases h
      · exact fun _ => hR
    | some p =>
      obtain ⟨blk, post'⟩ := p
      obtain ⟨-, checked', hC', hST, -⟩ := of_newPayloadOnChain_some hN
      -- The chain has the configuration of the node, so the request gives the same block.
      rw [show (node.chainAt checked.block.header.parentHash post).config = node.config from rfl,
        hC] at hC'
      cases hC'
      intro hRoot
      exact hR.record hv hFresh hRoot fun _ _ => .inl ⟨post, hp, runBody_of_stateTransition hST⟩

/-- The answer by the parent to the block of a request, over a new or accepted hash, keeps it. -/
private theorem Runs.onParent {root hash : Hash32} {version : Nat} {params : Lean.Json}
    {checked : CheckedBlock version} (hR : node.Runs root) (hv : node.ValidParents root)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hC : checkNewPayload node.config version params = .ok (.ok checked)) :
    (node.onParent hash ⟨checked.fork, checked.block⟩ version params).2.blocks.lookup root =
      none → (node.onParent hash ⟨checked.fork, checked.block⟩ version params).2.Runs root := by
  simp only [Node.onParent]
  split
  · rename_i blk pow post hp
    split
    · exact hR.executeOn hv hFresh hC (validState_eq_some_iff.mpr ⟨_, hp, rfl⟩)
    · exact fun hRoot => hR.record hv hFresh hRoot fun _ h => by cases h
  · exact fun hRoot => hR.record hv hFresh hRoot fun _ h => by cases h
  · exact fun hRoot => hR.record hv hFresh hRoot fun _ h => by cases h
  · exact fun _ => hR

/-- A step of `engine_newPayload` keeps the property. -/
private theorem Runs.newPayloadStep {root : Hash32} {version : Nat} {params : Lean.Json}
    (hR : node.Runs root) (hv : node.ValidParents root) :
    (node.newPayloadStep version params).2.blocks.lookup root = none →
      (node.newPayloadStep version params).2.Runs root := by
  unfold Node.newPayloadStep
  split
  · exact fun _ => hR
  · exact fun _ => hR
  · rename_i checked hC
    dsimp only
    split
    · exact fun _ => hR
    · split
      · exact fun _ => hR
      · exact fun _ => hR
      · rename_i hNotValid hNotInvalid
        -- The payload is neither valid nor invalid, so it is new or accepted.
        refine hR.onParent hv (fun ⟨blk, pow, v⟩ hk => ?_) hC
        cases v with
        | valid post => exact absurd hk (hNotValid blk pow post)
        | invalid => exact absurd hk (hNotInvalid blk pow)
        | accepted v' p' => rfl

/-- Validation keeps the property. -/
private theorem Runs.validateChain {root : Hash32} (hR : node.Runs root)
    (hv : node.ValidParents root) (hd : node.Decodes) (fuel : Nat) (hash : Hash32) :
    (node.validateChain fuel hash).blocks.lookup root = none →
      (node.validateChain fuel hash).Runs root := by
  induction fuel generalizing node hash with
  | zero => exact fun _ => hR
  | succ fuel ih =>
    simp only [Node.validateChain]
    split
    · rename_i block pow v p hb
      -- The accepted block is the block of its request.
      obtain ⟨checked, hC, hfull⟩ := hd hash _ v p hb rfl
      dsimp only at hfull
      subst hfull
      have hv' := hv.validateChain fuel checked.block.header.parentHash
      -- The block is still accepted after the validation of the chain of its parent.
      have hk : (node.validateChain fuel checked.block.header.parentHash).blocks.lookup hash =
          some _ := validateChain_lookup_accepted hb rfl fuel
      have hFresh : ∀ c, (node.validateChain fuel checked.block.header.parentHash).blocks.lookup
          hash = some c → c.validity.isAccepted = true := by
        intro c hc
        rw [hk] at hc
        cases hc
        rfl
      have hC' : checkNewPayload (node.validateChain fuel checked.block.header.parentHash).config
          v p = .ok (.ok checked) := by
        rw [validateChain_config]
        exact hC
      split
      · rename_i post hp
        intro hRoot
        have hRootM := (keeps_executeOn hFresh).lookup_eq_none hRoot
        exact (ih hR hv hd checked.block.header.parentHash hRootM).executeOn hv' hFresh hC'
          (validState_eq_some_iff.mpr ⟨_, hp, rfl⟩) hRoot
      · intro hRoot
        have hRootM := (keeps_record hFresh).lookup_eq_none hRoot
        exact (ih hR hv hd checked.block.header.parentHash hRootM).record hv' hFresh hRoot
          fun _ h => by cases h
      · exact ih hR hv hd _
    · exact fun _ => hR

/-- A step of `engine_forkchoiceUpdated` keeps the property. -/
private theorem Runs.forkchoiceUpdatedStep {root : Hash32} {version : Nat} {params : Lean.Json}
    (hR : node.Runs root) (hv : node.ValidParents root) (hd : node.Decodes) :
    (node.forkchoiceUpdatedStep version params).2.blocks.lookup root = none →
      (node.forkchoiceUpdatedStep version params).2.Runs root := by
  have hh : (node.validateHead version params).blocks.lookup root = none →
      (node.validateHead version params).Runs root := by
    simp only [Node.validateHead]
    split
    · exact hR.validateChain hv hd _ _
    · exact fun _ => hR
  simp only [Node.forkchoiceUpdatedStep]
  split
  · exact hh
  · simp only [updateStep]
    split
    · exact hh
    · exact hh

/-! ## Every reached node -/

/-- A step of `engine_newPayload` keeps the forkchoice state. -/
private theorem newPayloadStep_forkchoice (node : Node) (version : Nat) (params : Lean.Json) :
    (node.newPayloadStep version params).2.forkchoice = node.forkchoice := by
  unfold Node.newPayloadStep
  repeat' split
  all_goals first
    | rfl
    | exact (executeOn_forkchoice _ _ _ _ _ _).1
    | simp only [Node.onParent]
      repeat' split
      all_goals first | rfl | exact (executeOn_forkchoice _ _ _ _ _ _).1

/-- A known block that is valid has a state after it. -/
private theorem validState_of_isValid {hash : Hash32} {b : KnownBlock}
    (hb : node.blocks.lookup hash = some b) (hv : b.validity.isValid = true) :
    ∃ s, node.validState hash = some s := by
  obtain ⟨full, pow, v⟩ := b
  cases v with
  | valid p => exact ⟨p, validState_eq_some_iff.mpr ⟨_, hb, rfl⟩⟩
  | invalid => simp [Validity.isValid] at hv
  | accepted _ _ => simp [Validity.isValid] at hv

/-- Every node that the steps reach from a node that starts from a block has a valid head. -/
private theorem Reachable.head_valid {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat} {start : Node}
    (hStart : Node.start config transition anchor post total = some start)
    (hr : Reachable start node) : ∃ s, node.validState node.forkchoice.headBlockHash = some s := by
  induction hr with
  | refl =>
    obtain ⟨hash, pow, hb, hh⟩ := blocks_of_start hStart
    rw [hh]
    refine ⟨post, ?_⟩
    unfold Node.validState
    rw [hb]
    simp
  | newPayload version params _ ih =>
    obtain ⟨s, hs⟩ := ih
    rw [newPayloadStep_forkchoice]
    exact ⟨s, (Reachable.newPayload version params .refl).validState hs⟩
  | @forkchoiceUpdated n version params _ ih =>
    obtain ⟨s, hs⟩ := ih
    rcases forkchoiceUpdatedStep_head_valid n version params with h | ⟨b, hb, hv⟩
    · rw [h]
      exact ⟨s, (Reachable.forkchoiceUpdated version params .refl).validState hs⟩
    · exact validState_of_isValid hb hv
  | @forkchoiceUpdatedBuild n builder version params _ ih =>
    obtain ⟨s, hs⟩ := ih
    rw [(forkchoiceUpdatedBuildStep_keeps _ _ _ _).2.2, validState_of_blocks_eq
      (forkchoiceUpdatedBuildStep_keeps _ _ _ _).1]
    rcases forkchoiceUpdatedStep_head_valid n version params with h | ⟨b, hb, hv⟩
    · rw [h]
      exact ⟨s, (Reachable.forkchoiceUpdated version params .refl).validState hs⟩
    · exact validState_of_isValid hb hv
  | getPayload setup version id _ ih => exact ih

/-- In every node reached from a starting block, each accepted block is the block of its request. -/
private theorem Reachable.decodes {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat} {start : Node}
    (hStart : Node.start config transition anchor post total = some start)
    (hr : Reachable start node) : node.Decodes := by
  induction hr with
  | refl =>
    obtain ⟨hash, pow, hb, -⟩ := blocks_of_start hStart
    intro x c v p hc hval
    rw [hb] at hc
    cases eq_of_lookup_singleton hc
    cases hval
  | newPayload version params _ ih => exact ih.newPayloadStep
  | forkchoiceUpdated version params _ ih => exact ih.forkchoiceUpdatedStep
  | forkchoiceUpdatedBuild builder version params _ ih =>
    intro x c v p hc hval
    rw [(forkchoiceUpdatedBuildStep_keeps _ _ _ _).1] at hc
    rw [(forkchoiceUpdatedBuildStep_keeps _ _ _ _).2.1]
    exact ih.forkchoiceUpdatedStep x c v p hc hval
  | getPayload setup version id _ ih => exact ih

/-- In every node reached from a starting block, each valid block runs on the chain of its parent.

The starting block may instead have no transaction.

It assumes that the node knows no block under the parent hash of the starting block. -/
private theorem Reachable.runs {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat} {start : Node}
    (hStart : Node.start config transition anchor post total = some start)
    (hr : Reachable start node) (hRoot : node.blocks.lookup anchor.header.parentHash = none) :
    node.Runs anchor.header.parentHash := by
  have hv₀ := validParents_of_start hStart
  induction hr with
  | refl =>
    obtain ⟨hash, pow, hb, -⟩ := blocks_of_start hStart
    intro x c v hc hval
    rw [hb] at hc
    cases eq_of_lookup_singleton hc
    exact .inr ⟨rfl, rfl⟩
  | newPayload version params hr' ih =>
    have hPrev := (Reachable.newPayload version params .refl).lookup_eq_none hRoot
    exact (ih hPrev).newPayloadStep (hr'.validParents hv₀) hRoot
  | forkchoiceUpdated version params hr' ih =>
    have hPrev := (Reachable.forkchoiceUpdated version params .refl).lookup_eq_none hRoot
    exact (ih hPrev).forkchoiceUpdatedStep (hr'.validParents hv₀) (hr'.decodes hStart) hRoot
  | @forkchoiceUpdatedBuild n builder version params hr' ih =>
    have hPrev := (Reachable.forkchoiceUpdatedBuild builder version params .refl).lookup_eq_none
      hRoot
    obtain ⟨hb, hc, -⟩ := forkchoiceUpdatedBuildStep_keeps n builder version params
    have hRootF : (n.forkchoiceUpdatedStep version params).2.blocks.lookup
        anchor.header.parentHash = none := by
      rw [← hb]
      exact hRoot
    have hF := (ih hPrev).forkchoiceUpdatedStep (hr'.validParents hv₀) (hr'.decodes hStart)
      hRootF
    exact hF.mono ((hr'.validParents hv₀).forkchoiceUpdatedStep) (keeps_of_blocks_eq hb hc) hRoot
      fun x b _ h _ => by rw [← hb]; exact h
  | getPayload setup version id _ ih => exact ih hRoot

end Node

end EthLib.Engine
