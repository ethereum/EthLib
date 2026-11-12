module

public import EthLib.Consensus.Proofs.DirectSafety.Execution
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
import EthLib.Consensus.Proofs.Containers.Misc
import EthLib.Consensus.Proofs.Transition.BlockRoots
import EthLib.Consensus.Proofs.Transition.TargetUpgrades
import EthLib.Consensus.Proofs.Transition.PayloadInputs
import EthLib.Consensus.Proofs.Transition.RootLinks

/-!
# Hash evidence restricted to the supplied executions

Collision evidence uses the selected block headers, not beacon-state commitments.

States are included only for the zero-root alternative.

Caching a slot fills a zero state root of the latest header, unless the state hashes to zero.

A later slot can then refill it.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- An object of a run whose root the evidence may name: a block header or a state. -/
inductive HashObject (preset : Preset) where
  | header (value : BeaconBlockHeader)
  | state (value : ForkedBeaconState preset)

/-- The root of the object, when hashing succeeds. -/
def HashObject.root (object : HashObject preset) : Option Root :=
  match object with
  | .header h => (hashTreeRoot h).toOption
  | .state s => (hashTreeRoot s.state).toOption

/-- The inputs of the binary hashes that the root of a header computes; none for a state. -/
def HashObject.messages (object : HashObject preset) : List Bytes :=
  match object with
  | .header h => ((valueTree (SszType.desc BeaconBlockHeader) (SszType.toValue h)).toOption.map
      (fun tree => tree.messages)).getD []
  | .state _ => []

/-- The objects that a step exposes: its two states, their headers and the header of its block.

A slot step also exposes the state and the header after caching. -/
def _root_.EthLib.Consensus.Step.hashObjects {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : List (HashObject preset) :=
  [.state before, .state after, .header before.state.latestBlockHeader,
    .header after.state.latestBlockHeader] ++
  (match step with
  | .slot _ => match (processSlot before.state).toOption with
    | none => []
    | some cached => [.state ⟨before.fork, cached⟩, .header cached.latestBlockHeader]
  | .block _ signed _ _ => (blockHeader signed.message).toList.map HashObject.header)

/-- The objects of the steps of a run, with the first state and its header. -/
def _root_.EthLib.Consensus.Run.hashObjects {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : List (HashObject preset) :=
  match run with
  | .nil => [.state first, .header first.state.latestBlockHeader]
  | .snoc pre step => pre.hashObjects ++ step.hashObjects

/-- Two different inputs of the SHA-256 node hash with one digest, or an object whose root is zero.

Both are read among the given objects. -/
def HashEvidence (objects : List (HashObject preset)) : Prop :=
  (∃ x ∈ objects.flatMap HashObject.messages, ∃ y ∈ objects.flatMap HashObject.messages,
    MessageCollision x y) ∨
  ∃ object ∈ objects, object.root = some (Vector.replicate 32 0)

private theorem header_binding (objects : List (HashObject preset)) (a b : BeaconBlockHeader)
    (one : .header a ∈ objects) (two : .header b ∈ objects) (root : Root)
    (sameA : hashTreeRoot a = .ok root) (sameB : hashTreeRoot b = .ok root) :
    a = b ∨ HashEvidence objects := by
  have sized (h : BeaconBlockHeader) :
      CommitmentSized (SszType.desc BeaconBlockHeader) (SszType.toValue h) := by
    refine .container fun pair member => ?_
    simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues] at member
    repeat' rcases member with rfl | member
    all_goals first | exact .byteVector _ _ | exact .uint _ _
  rcases SszType.hashTreeRoot_binding (sized a) (sized b) sameA sameB with same | collision
  · exact .inl same
  · obtain ⟨leftTree, rightTree, leftOk, rightOk, x, y, _, leftMem, rightMem, collided⟩ :=
      collision
    right
    left
    refine ⟨x, List.mem_flatMap.mpr ⟨.header a, one, ?_⟩,
      y, List.mem_flatMap.mpr ⟨.header b, two, ?_⟩, collided⟩
    · simpa [HashObject.messages, leftOk, Except.toOption] using leftMem
    · simpa [HashObject.messages, rightOk, Except.toOption] using rightMem

private theorem header_deposit {fork : Fork} {before after : BeaconState preset fork}
    {early : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks early before deposit = .ok after) :
    after.latestBlockHeader = before.latestBlockHeader := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok ok
  exact (frame_applyDeposit applied).latestBlockHeader

private theorem genesis_header {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    g.state.latestBlockHeader.slot = 0 ∧
      g.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 := by
  obtain ⟨hash, time, deposits, initialized⟩ := genesis
  obtain ⟨before, time, root, deposited, activated, finalRoot, dep, act, stateEq⟩ :=
    initializeBeaconStateFromEth1_ok initialized
  have depositedHeader : deposited.latestBlockHeader =
      (emptyGenesisState config before time hash deposits.size.toUInt64 root).latestBlockHeader :=
    foldlM_ok_invariant (fun s => s.latestBlockHeader =
      (emptyGenesisState config before time hash deposits.size.toUInt64 root).latestBlockHeader)
      (fun _ _ _ same ok => by
        simp only [genesisDeposit, bind_ok_iff] at ok
        obtain ⟨_, _, ok⟩ := ok
        exact (header_deposit ok).trans same) rfl dep
  have activatedHeader : activated.latestBlockHeader = deposited.latestBlockHeader :=
    foldlM_ok_invariant (fun s => s.latestBlockHeader = deposited.latestBlockHeader)
      (fun _ _ _ same ok => by
        simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, set⟩ := ok
        exact (payloadInputs_setValidatorAt set).latestBlockHeader.trans same) rfl act
  rw [stateEq]
  change activated.latestBlockHeader.slot = 0 ∧
    activated.latestBlockHeader.stateRoot = Vector.replicate 32 0
  rw [activatedHeader, depositedHeader]
  exact ⟨rfl, rfl⟩

/-- A root that a slot step makes readable was readable before, or is the root of the cached header.

The cached header is the one that caching the slot leaves, and its root is at the slot before. -/
private theorem slot_root_origin {before after : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks before = .ok after) {slot : Slot} {root : Root}
    (read : getBlockRootAtSlot after.state slot = .ok root) :
    getBlockRootAtSlot before.state slot = .ok root ∨
      slot = before.state.slot ∧ ∃ cached, processSlot before.state = .ok cached ∧
        hashTreeRoot cached.latestBlockHeader = .ok root := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  obtain ⟨cached, cachedOk, _, _, header, _⟩ := advanceSlot_cachedRoots advancedOk
  -- The upgrades keep the slot and the roots.
  rw [getBlockRootAtSlot_congr (processUpgrades_slot upgraded)
    (processUpgrades_blockRoots upgraded)] at read
  rcases getBlockRootAtSlot_advanceSlot_cases advancedOk read with ⟨_, earlier⟩ | ⟨same, hashed⟩
  · exact .inl earlier
  · exact .inr ⟨same, cached, cachedOk, header ▸ hashed⟩

private theorem step_slots {before after : ForkedBeaconState preset}
    (step : Step config checks before after) :
    before.state.slot.toNat ≤ after.state.slot.toNat ∧
      ∀ header ∈ step.headers, header.slot = before.state.slot := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    obtain ⟨-, -, -, -, -, -, -, next⟩ := advanceSlot_cachedRoots advancedOk
    have kept : after.state.slot.toNat = advanced.slot.toNat :=
      congrArg UInt64.toNat (processUpgrades_slot upgraded)
    exact ⟨by omega, by simp [Step.headers]⟩
  | block engine signed due ok =>
    have same := (frame_processBlock (applySignedBlock_ok ok).2.1).slot
    refine ⟨by rw [same], ?_⟩
    intro header member
    simp only [Step.headers, Option.mem_toList] at member
    unfold blockHeader at member
    cases body : (hashTreeRoot signed.message.body).toOption <;>
      simp [body] at member
    subst header
    exact (processBlock_parentRoot (applySignedBlock_ok ok).2.1).1

/-- The slot never decreases along a run. -/
theorem _root_.EthLib.Consensus.Run.slot_le {a b : ForkedBeaconState preset}
    (run : Run config checks a b) :
    a.state.slot.toNat ≤ b.state.slot.toNat := by
  induction run with
  | nil => exact Nat.le_refl _
  | snoc _ edge ih => exact ih.trans (step_slots edge).1

private theorem path_append_stable {g a b : ForkedBeaconState preset}
    (pre : Run config checks g a) (tail : Run config checks a b) (epoch : Epoch)
    (before : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < a.state.slot.toNat) :
    (pre.append tail).checkpointPath epoch = pre.checkpointPath epoch := by
  induction tail with
  | nil => rfl
  | @snoc middle last tail step ih =>
    have empty : step.headers.filter
        (fun h => h.slot.toNat ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro h member
      have same := (step_slots step).2 h member
      have bound := tail.slot_le
      simp only [same, decide_eq_true_eq]
      omega
    simpa only [Run.append, Run.checkpointPath, Run.headers, List.filter_append, empty,
      List.append_nil] using ih

private inductive HeaderChain (objects : List (HashObject preset)) :
    List BeaconBlockHeader → BeaconBlockHeader → Prop where
  | genesis {header} (zero : header.slot = 0) :
      HeaderChain objects [] header
  | block {headers parent header} (pre : HeaderChain objects headers parent)
      (parentRoot : hashTreeRoot parent = .ok header.parentRoot)
      (later : parent.slot < header.slot) (member : .header parent ∈ objects) :
      HeaderChain objects (headers ++ [header]) header

private theorem HeaderChain.mono {one two : List (HashObject preset)}
    {headers : List BeaconBlockHeader} {header : BeaconBlockHeader}
    (chain : HeaderChain one headers header) (subset : one ⊆ two) :
    HeaderChain two headers header := by
  induction chain with
  | genesis zero => exact .genesis zero
  | block _ parent later member ih => exact .block ih parent later (subset member)

private theorem HeaderChain.binding {objects : List (HashObject preset)}
    {one two : List BeaconBlockHeader} {a b : BeaconBlockHeader}
    (left : HeaderChain objects one a) (right : HeaderChain objects two b)
    (same : a = b) : one = two ∨ HashEvidence objects := by
  induction left generalizing two b with
  | genesis zero =>
    cases right with
    | genesis => exact .inl rfl
    | block pre parent later member =>
      have later := UInt64.lt_iff_toNat_lt.mp later
      rw [← same, zero] at later
      simp at later
  | @block headers parent header pre hashed later member ih =>
    cases right with
    | genesis zero =>
      have later := UInt64.lt_iff_toNat_lt.mp later
      rw [same, zero] at later
      simp at later
    | @block other parent' header' pre' hashed' later' member' =>
      cases same
      rcases header_binding objects parent parent' member member' _ hashed hashed'
          with eq | evidence
      · rcases ih pre' eq with eq | evidence
        · exact .inl (congrArg (· ++ [header]) eq)
        · exact .inr evidence
      · exact .inr evidence

private def HeaderState (objects : List (HashObject preset))
    (headers : List BeaconBlockHeader) (state : ForkedBeaconState preset) : Prop :=
  (state.state.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0 ∧
    HeaderChain objects headers state.state.latestBlockHeader) ∨
  (state.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 ∧
    state.state.latestBlockHeader.slot = state.state.slot ∧
    ∀ root, hashTreeRoot state.state = .ok root →
      HeaderChain objects headers { state.state.latestBlockHeader with stateRoot := root })

private theorem HeaderState.cached {objects : List (HashObject preset)}
    {headers : List BeaconBlockHeader} {state : ForkedBeaconState preset}
    (invariant : HeaderState objects headers state)
    {cached : BeaconState preset state.fork} (ok : processSlot state.state = .ok cached) :
    HeaderChain objects headers cached.latestBlockHeader := by
  obtain ⟨root, hashed, header⟩ := processSlot_latestBlockHeader ok
  rcases invariant with ⟨nonzero, chain⟩ | ⟨zero, _, pending⟩
  · simpa only [header, nonzero, ↓reduceIte] using chain
  · simpa only [header, zero, ↓reduceIte] using pending root hashed

private theorem HeaderState.mono {one two : List (HashObject preset)}
    {headers : List BeaconBlockHeader} {state : ForkedBeaconState preset}
    (invariant : HeaderState one headers state) (subset : one ⊆ two) :
    HeaderState two headers state := by
  rcases invariant with ⟨nonzero, chain⟩ | ⟨zero, slot, pending⟩
  · exact .inl ⟨nonzero, chain.mono subset⟩
  · exact .inr ⟨zero, slot, fun root hashed => (pending root hashed).mono subset⟩

private theorem run_header_state {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (nonzero : ∀ object ∈ run.hashObjects, object.root ≠ some (Vector.replicate 32 0)) :
    HeaderState run.hashObjects run.headers a := by
  induction run with
  | nil =>
    obtain ⟨zeroSlot, zeroRoot⟩ := genesis_header genesis
    obtain ⟨_, _, _, initialized⟩ := genesis
    have stateSlot := (initializeBeaconStateFromEth1_checkpoints initialized).1
    right
    refine ⟨zeroRoot, zeroSlot.trans stateSlot.symm, ?_⟩
    intro root hashed
    exact HeaderChain.genesis zeroSlot
  | @snoc middle last pre step ih =>
    have invariant := (ih (fun object member =>
      nonzero object (List.mem_append_left _ member))).mono
        (fun _ member => List.mem_append_left step.hashObjects member)
    cases step with
    | slot ok =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
      obtain ⟨cached, cachedOk, _, _, header, _, _, _⟩ :=
        advanceSlot_cachedRoots advancedOk
      have header := (latestBlockHeader_processUpgrades upgraded).trans header
      have chain := invariant.cached cachedOk
      left
      refine ⟨?_, ?_⟩
      · obtain ⟨root, hashed, filled⟩ := processSlot_latestBlockHeader cachedOk
        have nz := nonzero (.state middle) (by simp [Run.hashObjects, Step.hashObjects])
        have nzRoot : root ≠ Vector.replicate 32 0 := by
          intro eq
          exact nz (by simp [HashObject.root, hashed, eq, Except.toOption])
        rw [header, filled]
        split
        · exact nzRoot
        · assumption
      · simpa only [Run.headers, Run.hashObjects, Step.headers, List.append_nil, header] using chain
    | block engine signed due ok =>
      rename_i fork before after
      obtain ⟨slot, later, parent⟩ := processBlock_parentRoot (applySignedBlock_ok ok).2.1
      have ready : HeaderChain (pre.hashObjects ++ (Step.block engine signed due ok).hashObjects)
          pre.headers before.latestBlockHeader := by
        rcases invariant with ⟨_, chain⟩ | ⟨_, same, _⟩
        · exact chain
        · rw [same, slot] at later
          exact False.elim (UInt64.lt_irrefl _ later)
      obtain ⟨bodyRoot, bodyOk, header⟩ :=
        latestBlockHeader_processBlock (applySignedBlock_ok ok).2.1
      have stateRoot := (applySignedBlock_ok ok).2.2 rfl
      right
      refine ⟨by simp only [header], ?_, ?_⟩
      · simpa only [header, (frame_processBlock (applySignedBlock_ok ok).2.1).slot] using slot
      · intro root hashed
        have eq : root = signed.message.stateRoot := Except.ok.inj (hashed.symm.trans stateRoot)
        subst root
        have selected : blockHeader signed.message = some
            ⟨signed.message.slot, signed.message.proposerIndex, signed.message.parentRoot,
              signed.message.stateRoot, bodyRoot⟩ := by
          simp [blockHeader, bodyOk, Except.toOption]
        simp only [Run.headers, Step.headers, selected, Option.toList_some, header]
        exact HeaderChain.block ready parent later
          (by simp [Run.hashObjects, Step.hashObjects, selected])

private theorem run_headers_le {g a : ForkedBeaconState preset}
    (run : Run config checks g a) :
    ∀ header ∈ run.headers, header.slot.toNat ≤ a.state.slot.toNat := by
  induction run with
  | nil => simp [Run.headers]
  | snoc pre step ih =>
    intro header member
    rcases List.mem_append.mp member with member | member
    · exact (ih header member).trans (step_slots step).1
    · rw [(step_slots step).2 header member]
      exact (step_slots step).1

private theorem run_root_chain {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (nonzero : ∀ object ∈ run.hashObjects, object.root ≠ some (Vector.replicate 32 0))
    {slot : Slot} {root : Root} (read : getBlockRootAtSlot a.state slot = .ok root) :
    ∃ header : BeaconBlockHeader, .header header ∈ run.hashObjects ∧
      hashTreeRoot header = .ok root ∧
      HeaderChain run.hashObjects
        (run.headers.filter fun h => h.slot.toNat ≤ slot.toNat) header := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, initialized⟩ := genesis
    have zero := (initializeBeaconStateFromEth1_checkpoints initialized).1
    have before := (getBlockRootAtSlot_ok_iff.mp read).1
    rw [zero] at before
    simp [GENESIS_SLOT] at before
  | @snoc middle last pre step ih =>
    have nz : ∀ object ∈ pre.hashObjects, object.root ≠ some (Vector.replicate 32 0) :=
      fun object member => nonzero object (List.mem_append_left _ member)
    have liftEarlier (earlier : getBlockRootAtSlot middle.state slot = .ok root)
        (empty : step.headers.filter (fun h => h.slot.toNat ≤ slot.toNat) = []) :
        ∃ header : BeaconBlockHeader, .header header ∈ (pre.snoc step).hashObjects ∧
          hashTreeRoot header = .ok root ∧ HeaderChain (pre.snoc step).hashObjects
            ((pre.snoc step).headers.filter fun h => h.slot.toNat ≤ slot.toNat) header := by
      obtain ⟨header, member, hashed, chain⟩ := ih nz earlier
      refine ⟨header, List.mem_append_left _ member, hashed, ?_⟩
      simpa only [Run.headers, Run.hashObjects, List.filter_append, empty, List.append_nil] using
        chain.mono (fun _ member => List.mem_append_left step.hashObjects member)
    cases step with
    | slot ok =>
      rcases slot_root_origin ok read with earlier | ⟨same, cached, cachedOk, hashed⟩
      · exact liftEarlier earlier (by simp [Step.headers])
      -- The root at the slot before is that of the header that caching the slot leaves.
      · subst slot
        have chain := ((run_header_state pre genesis nz).mono
          (fun _ member => List.mem_append_left (Step.slot ok).hashObjects member)).cached cachedOk
        refine ⟨cached.latestBlockHeader, ?_, hashed, ?_⟩
        · simp [Run.hashObjects, Step.hashObjects, cachedOk, Except.toOption]
        · have filtered : pre.headers.filter
              (fun h => h.slot.toNat ≤ middle.state.slot.toNat) = pre.headers :=
            List.filter_eq_self.mpr (fun h member => by simpa using run_headers_le pre h member)
          simpa only [Run.headers, Run.hashObjects, Step.headers, List.append_nil, filtered]
            using chain
    | block engine signed due ok =>
      rename_i fork before after
      have frame := frame_processBlock (applySignedBlock_ok ok).2.1
      have roots := processBlock_blockRoots (applySignedBlock_ok ok).2.1
      have earlier : getBlockRootAtSlot before slot = .ok root := by
        simpa only [getBlockRootAtSlot_congr frame.slot roots] using read
      apply liftEarlier earlier
      apply List.filter_eq_nil_iff.mpr
      intro h member
      have same := (step_slots (.block engine signed due ok)).2 h member
      have before := (getBlockRootAtSlot_ok_iff.mp earlier).1
      simp only [same, decide_eq_true_eq]
      omega

/-- Equal checkpoint roots identify equal header prefixes, or the scan finds hash evidence. -/
private theorem checkpoint_binding {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (genesis : Genesis (config := config) (checks := checks) g)
    (epoch : Epoch) (root : Root)
    (one : getBlockRoot a.state epoch = .ok root)
    (two : getBlockRoot b.state epoch = .ok root) :
    left.checkpointPath epoch = right.checkpointPath epoch ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  by_cases evidence : HashEvidence (left.hashObjects ++ right.hashObjects)
  · exact .inr evidence
  have nonzero : ∀ object ∈ left.hashObjects ++ right.hashObjects,
      object.root ≠ some (Vector.replicate 32 0) := by
    intro object member zero
    exact evidence (.inr ⟨object, member, zero⟩)
  obtain ⟨slot₁, start₁, read₁⟩ := getBlockRoot_ok_iff.mp one
  obtain ⟨slot₂, start₂, read₂⟩ := getBlockRoot_ok_iff.mp two
  have sameSlot : slot₁ = slot₂ := Except.ok.inj (start₁.symm.trans start₂)
  subst slot₂
  obtain ⟨h₁, mem₁, hash₁, chain₁⟩ := run_root_chain left genesis
    (fun object member => nonzero object (List.mem_append_left _ member)) read₁
  obtain ⟨h₂, mem₂, hash₂, chain₂⟩ := run_root_chain right genesis
    (fun object member => nonzero object (List.mem_append_right _ member)) read₂
  rcases header_binding _ h₁ h₂ (List.mem_append_left _ mem₁)
      (List.mem_append_right _ mem₂) root hash₁ hash₂ with same | collision
  · have chain₁ := chain₁.mono (fun _ member => List.mem_append_left right.hashObjects member)
    have chain₂ := chain₂.mono (fun _ member => List.mem_append_right left.hashObjects member)
    rcases chain₁.binding chain₂ same with paths | collision
    · left
      have start := (Uint64.mulChecked_ok_iff.mp start₁).2
      simpa only [Run.checkpointPath, start] using paths
    · exact False.elim (evidence collision)
  · exact False.elim (evidence collision)

private theorem hashObjects_append_subset {g a b : ForkedBeaconState preset}
    (pre : Run config checks g a) (tail : Run config checks a b) :
    pre.hashObjects ⊆ (pre.append tail).hashObjects := by
  induction tail with
  | nil => exact fun _ h => h
  | snoc tail step ih => exact fun _ h => List.mem_append_left _ (ih h)

private theorem hashEvidence_mono {one two : List (HashObject preset)}
    (subset : one ⊆ two) (evidence : HashEvidence one) : HashEvidence two := by
  rcases evidence with ⟨x, xm, y, ym, collision⟩ | ⟨object, member, zero⟩
  · left
    have mem {z} (member : z ∈ one.flatMap HashObject.messages) :
        z ∈ two.flatMap HashObject.messages := by
      obtain ⟨object, member, hashed⟩ := List.mem_flatMap.mp member
      exact List.mem_flatMap.mpr ⟨object, subset member, hashed⟩
    exact ⟨x, mem xm, y, mem ym, collision⟩
  · exact .inr ⟨object, subset member, zero⟩

/-- Two slot steps of the runs that cache one root for an epoch give the same headers up to it.

Each step comes after the first slot of the epoch, while its root is still in the buffer.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

The runs start at one genesis built from deposits. -/
theorem checkpoint_binding_cached {g a b before₁ after₁ before₂ after₂ : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (genesis : Genesis (config := config) (checks := checks) g)
    (ok₁ : advanceSlotAcross config checks before₁ = .ok after₁)
    (ok₂ : advanceSlotAcross config checks before₂ = .ok after₂)
    (member₁ : left.Contains (.slot ok₁)) (member₂ : right.Contains (.slot ok₂))
    (cached₁ : BeaconState preset before₁.fork) (cached₂ : BeaconState preset before₂.fork)
    (cachedOk₁ : processSlot before₁.state = .ok cached₁)
    (cachedOk₂ : processSlot before₂.state = .ok cached₂)
    (epoch : Epoch) (root : Root)
    (read₁ : getBlockRoot cached₁ epoch = .ok root)
    (read₂ : getBlockRoot cached₂ epoch = .ok root)
    (early₁ : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < before₁.state.slot.toNat)
    (early₂ : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < before₂.state.slot.toNat)
    (recent₁ : before₁.state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (recent₂ : before₂.state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    left.checkpointPath epoch = right.checkpointPath epoch ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  rw [getBlockRoot_processSlot cachedOk₁ recent₁] at read₁
  rw [getBlockRoot_processSlot cachedOk₂ recent₂] at read₂
  obtain ⟨pre₁, post₁, rfl⟩ := left.contains_split (.slot ok₁) member₁
  obtain ⟨pre₂, post₂, rfl⟩ := right.contains_split (.slot ok₂) member₂
  have paths₁ := path_append_stable pre₁ ((Run.nil.snoc (.slot ok₁)).append post₁) epoch early₁
  have paths₂ := path_append_stable pre₂ ((Run.nil.snoc (.slot ok₂)).append post₂) epoch early₂
  rw [Run.append_assoc] at paths₁ paths₂
  rcases checkpoint_binding pre₁ pre₂ genesis epoch root
      read₁ read₂ with same | evidence
  · exact .inl (paths₁.trans (same.trans paths₂.symm))
  · right
    apply hashEvidence_mono (one := pre₁.hashObjects ++ pre₂.hashObjects) _ evidence
    intro object member
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (hashObjects_append_subset _ post₁
        (List.mem_append_left _ member))
    · exact List.mem_append_right _ (hashObjects_append_subset _ post₂
        (List.mem_append_left _ member))

end EthLib.Consensus.DirectSafety
