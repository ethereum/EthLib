module

public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Transition.FfgRoots
public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import EthLib.Consensus.Proofs.Transition.Slot

/-!
# Proofs: the roots that a beacon state records follow the blocks applied to it

A state records the root of its latest block header at each slot that it passes.

The first slot after a block fills the state root of that header.

So it records the root of the block, when the block step checks its state root.

The header check of the next block makes its parent root the root recorded at the slot before it.

So one transition records the parent root of its block at each slot from the slot of the state.

There is one exception.

When the state before hashes to the zero root, the first slot leaves the header unfilled.

That slot then records the root of the header as it was.

The same holds along a run of a chain, where blocks and upgrades come between the slots.

Two consecutive slots record the same root, or the parent root and the root of a block step.

The other cases are a pair that the first state records, the first pair, and a zero preimage.

The first pair is the pair that the first slot of the run adds.

Its second root is that of the first header, filled with the root of the first state.

Its first root is the root at the slot before the first state, or the zero root at slot zero.

A zero preimage is a state of the run that hashes to the zero root.

Without a zero preimage, the pairs of the last state are in order for a map from roots.

The map must order each block step after its parent.

It must also order the pairs of the first state and the first pair.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The latest block header across upgrades -/

/-- The queue of a validator that waits for activation keeps the inputs of a payload. -/
private theorem payloadInputs_queuePreActivation {fork : Fork}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    PayloadInputs state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, set₁, _, set₂, rfl⟩ := computed
  exact ((payloadInputs_setBalance set₁).trans (payloadInputs_setValidator set₂)).trans
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The queue of the excess balance of a validator keeps the inputs of a payload. -/
private theorem payloadInputs_queueCompoundingExcess {fork : Fork}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    PayloadInputs state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · have queued := liftAccessor_ok.mp computed
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
        exact (payloadInputs_setBalance set).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases queued
        exact PayloadInputs.refl _
    · cases computed
      exact PayloadInputs.refl _
  · cases computed
    exact PayloadInputs.refl _

/-- Each upgrade keeps the latest block header. -/
private theorem latestBlockHeader_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.latestBlockHeader = pre.state.latestBlockHeader := by
  obtain ⟨fork, before⟩ := pre
  cases fork <;> simp only [upgradeNext] at computed
  all_goals try solve | cases computed; rfl | cases computed
  all_goals try simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  case phase0 =>
    obtain ⟨after, upgraded, rfl⟩ := computed
    obtain ⟨middle, folded, committee, rfl⟩ := upgradeToAltair_ok upgraded
    obtain ⟨participation, rfl, _⟩ := foldlM_translateAttestation folded
    rfl
  case dencun =>
    obtain ⟨after, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := upgraded
    exact ((PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_queuePreActivation ok)
      queued).trans (PayloadInputs.foldlM
        (fun _ _ _ ok => payloadInputs_queueCompoundingExcess ok) compounded)).latestBlockHeader
  case pectra =>
    obtain ⟨after, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    rfl
  case fusaka =>
    obtain ⟨after, upgraded, rfl⟩ := computed
    unfold upgradeToGloas at upgraded
    obtain ⟨_, _, rest⟩ := bind_ok_iff.mp upgraded
    obtain ⟨_, _, onboarded⟩ := bind_ok_iff.mp rest
    obtain ⟨⟨_, _, rfl⟩, _⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    rfl
  case glamsterdam =>
    obtain ⟨after, upgraded, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    rfl

/-- The upgrades due at a slot keep the latest block header. -/
private theorem latestBlockHeader_processUpgrades {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    after.state.latestBlockHeader = forked.state.latestBlockHeader :=
  processUpgrades_induction
    (property := fun state => state.state.latestBlockHeader = forked.state.latestBlockHeader)
    (fun same stepOk => (latestBlockHeader_upgradeNext stepOk).trans same) rfl computed

/-! ## One transition -/

section Transition

variable {fork : Fork} {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- A header with a state root other than zero stays the same through any number of slots. -/
private theorem advanceSlots_latestBlockHeader_of_ne :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      state.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0 →
      after.latestBlockHeader = state.latestBlockHeader
  | 0, state, after, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    rw [← computed]
  | count + 1, state, after, computed, filled => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨_, -, header⟩ := advanceSlot_latestBlockHeader nextOk
    simp only [filled, ↓reduceIte] at header
    rw [advanceSlots_latestBlockHeader_of_ne count rest (header ▸ filled), header]

/-- A header that the filling leaves with a zero state root was filled with the zero root.

So the filling changed nothing. -/
private theorem unfilled_of_filled {header filled : BeaconBlockHeader} {stateRoot : Root}
    (equation : filled = if header.stateRoot = Vector.replicate 32 0 then
      { header with stateRoot := stateRoot } else header)
    (unfilled : filled.stateRoot = Vector.replicate 32 0) :
    stateRoot = Vector.replicate 32 0 ∧ filled = header := by
  by_cases empty : header.stateRoot = Vector.replicate 32 0
  · simp only [empty, ↓reduceIte] at equation
    have zero : stateRoot = Vector.replicate 32 0 := by rw [equation] at unfilled; exact unfilled
    refine ⟨zero, ?_⟩
    rw [equation, zero, ← empty]
  · simp only [empty, ↓reduceIte] at equation
    exact absurd (equation ▸ unfilled) empty

/-- The root of the header after a slot is that of the header at the end, or of the header before.

The header before counts only when the slot leaves it unfilled.

Then the state before hashes to zero. -/
private theorem hashTreeRoot_latestBlockHeader_advanceSlots {count : Nat}
    {next last : BeaconState preset fork}
    (step : advanceSlot config checks state = .ok next)
    (rest : advanceSlots config checks count next = .ok last) {root : Root}
    (rooted : hashTreeRoot next.latestBlockHeader = .ok root) :
    hashTreeRoot last.latestBlockHeader = .ok root ∨
      (hashTreeRoot state = .ok (Vector.replicate 32 0) ∧
        hashTreeRoot state.latestBlockHeader = .ok root) := by
  obtain ⟨stateRoot, hashed, header⟩ := advanceSlot_latestBlockHeader step
  by_cases filled : next.latestBlockHeader.stateRoot = Vector.replicate 32 0
  · obtain ⟨zero, same⟩ := unfilled_of_filled header filled
    rw [same] at rooted
    exact .inr ⟨zero ▸ hashed, rooted⟩
  · exact .inl (by rw [advanceSlots_latestBlockHeader_of_ne count rest filled]; exact rooted)

/-- A root that some slots make readable was readable before them, or comes from the header.

It is the root of the header at the end.

Or the state before hashes to zero, and it is the root of the header before. -/
private theorem getBlockRootAtSlot_advanceSlots :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after → ∀ {slot : Slot} {root : Root},
      getBlockRootAtSlot after slot = .ok root →
      (slot < state.slot ∧ getBlockRootAtSlot state slot = .ok root) ∨
        (state.slot ≤ slot ∧ (hashTreeRoot after.latestBlockHeader = .ok root ∨
          (hashTreeRoot state = .ok (Vector.replicate 32 0) ∧
            hashTreeRoot state.latestBlockHeader = .ok root)))
  | 0, state, after, computed, slot, root, read => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .inl ⟨(getBlockRootAtSlot_read read).1, read⟩
  | count + 1, state, after, computed, slot, root, read => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    have succ := advanceSlot_slot nextOk
    rcases getBlockRootAtSlot_advanceSlots count rest read with ⟨_, nextRead⟩ | ⟨later, rooted⟩
    · rcases getBlockRootAtSlot_advanceSlot_cases nextOk nextRead with
        ⟨before, read⟩ | ⟨same, rooted⟩
      · exact .inl ⟨before, read⟩
      · exact .inr ⟨same.symm ▸ UInt64.le_refl _,
          hashTreeRoot_latestBlockHeader_advanceSlots nextOk rest rooted⟩
    · refine .inr ⟨UInt64.le_iff_toNat_le.mpr ?_, ?_⟩
      · have := UInt64.le_iff_toNat_le.mp later
        omega
      · rcases rooted with rooted | ⟨-, rooted⟩
        · exact .inl rooted
        · exact hashTreeRoot_latestBlockHeader_advanceSlots nextOk rest rooted

/-- A block that the state transition accepts leaves the roots of the slots before it as follows.

A root of an older slot is that of the state before.

A root from the first slot of the transition on is the parent root of the block.

Or the state before hashes to the zero root, and it is the root of the header before. -/
private theorem getBlockRootAtSlot_stateTransition {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after)
    {slot : Slot} {root : Root} (read : getBlockRootAtSlot after slot = .ok root) :
    (slot < state.slot ∧ getBlockRootAtSlot state slot = .ok root) ∨
      (state.slot ≤ slot ∧ (root = signed.message.parentRoot ∨
        (hashTreeRoot state = .ok (Vector.replicate 32 0) ∧
          hashTreeRoot state.latestBlockHeader = .ok root))) := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  rw [getBlockRootAtSlot_congr (processBlock_slot blockOk) (processBlock_blockRoots blockOk)]
    at read
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨-, -, slotsOk⟩ := slotsOk
  rcases getBlockRootAtSlot_advanceSlots _ slotsOk read with older | ⟨later, rooted | zero⟩
  · exact .inl older
  · refine .inr ⟨later, .inl ?_⟩
    have parent := (processBlock_parentRoot blockOk).2.2
    rw [rooted] at parent
    exact Except.ok.inj parent
  · exact .inr ⟨later, .inr zero⟩

/-- A root that a transition records from the slot of the state is the parent root of its block.

The slot is at least the slot of the state, and the root is read in the state after the block.

The other case is that the state before the transition hashes to the zero root.

Then the first slot records the root of the latest block header as it was. -/
theorem getBlockRootAtSlot_stateTransition_cases {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after)
    {slot : Slot} {root : Root} (atLeast : state.slot ≤ slot)
    (read : getBlockRootAtSlot after slot = .ok root) :
    root = signed.message.parentRoot ∨
      (hashTreeRoot state = .ok (Vector.replicate 32 0) ∧
        hashTreeRoot state.latestBlockHeader = .ok root) := by
  rcases getBlockRootAtSlot_stateTransition computed read with ⟨older, -⟩ | ⟨-, cases⟩
  · exact absurd atLeast (UInt64.not_le.mpr older)
  · exact cases

/-- A block that the state transition accepts keeps the roots of the slots before the state. -/
theorem getBlockRootAtSlot_stateTransition_of_lt {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after)
    {slot : Slot} {root : Root} (before : slot < state.slot)
    (read : getBlockRootAtSlot after slot = .ok root) :
    getBlockRootAtSlot state slot = .ok root := by
  rcases getBlockRootAtSlot_stateTransition computed read with ⟨-, older⟩ | ⟨later, -⟩
  · exact older
  · exact absurd before (UInt64.not_lt.mpr later)

/-- A header that some slots leave with a zero state root is the header before them. -/
private theorem advanceSlots_latestBlockHeader_of_eq :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      after.latestBlockHeader.stateRoot = Vector.replicate 32 0 →
      after.latestBlockHeader = state.latestBlockHeader
  | 0, state, after, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    rw [← computed]
  | count + 1, state, after, computed, unfilled => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    have same := advanceSlots_latestBlockHeader_of_eq count rest unfilled
    obtain ⟨_, -, header⟩ := advanceSlot_latestBlockHeader nextOk
    rw [same, (unfilled_of_filled header (by rw [← same]; exact unfilled)).2]

/-- A root that a state within a transition records follows the same cases as after the block.

The state is some slots after the state before the transition.

Some more slots lead from it to the state on which the block runs.

A root of an older slot is that of the state before.

A root from the first slot of the transition on is the parent root of the block.

Or the state before hashes to the zero root, and it is the root of the header before.

Epoch processing within the transition reads such a state. -/
theorem getBlockRootAtSlot_advanceSlots_cases {count more : Nat}
    {middle last : BeaconState preset fork} {block : BeaconBlock preset fork}
    (first : advanceSlots config checks count state = .ok middle)
    (rest : advanceSlots config checks more middle = .ok last)
    (processed : processBlock config checks engine last block = .ok after)
    {slot : Slot} {root : Root} (read : getBlockRootAtSlot middle slot = .ok root) :
    (slot < state.slot ∧ getBlockRootAtSlot state slot = .ok root) ∨
      (state.slot ≤ slot ∧ (root = block.parentRoot ∨
        (hashTreeRoot state = .ok (Vector.replicate 32 0) ∧
          hashTreeRoot state.latestBlockHeader = .ok root))) := by
  rcases getBlockRootAtSlot_advanceSlots count first read with older | ⟨later, rooted | zero⟩
  · exact .inl older
  · refine .inr ⟨later, ?_⟩
    by_cases filled : middle.latestBlockHeader.stateRoot = Vector.replicate 32 0
    · -- An unfilled header after the first slot means that the state before hashes to zero.
      cases count with
      | zero =>
        simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at first
        subst first
        exact absurd later (UInt64.not_le.mpr (getBlockRootAtSlot_read read).1)
      | succ count =>
        simp only [advanceSlots, bind_ok_iff] at first
        obtain ⟨next, nextOk, run⟩ := first
        have same := advanceSlots_latestBlockHeader_of_eq count run filled
        obtain ⟨stateRoot, hashed, header⟩ := advanceSlot_latestBlockHeader nextOk
        obtain ⟨zero, unchanged⟩ := unfilled_of_filled header (by rw [← same]; exact filled)
        rw [same, unchanged] at rooted
        exact .inr ⟨zero ▸ hashed, rooted⟩
    · -- A filled header stays until the block, which names its root as the parent.
      rw [← advanceSlots_latestBlockHeader_of_ne more rest filled] at rooted
      exact .inl (Except.ok.inj (rooted.symm.trans (processBlock_parentRoot processed).2.2))
  · exact .inr ⟨later, .inr zero⟩

end Transition

/-! ## A run of a chain -/

/-- One slot of a chain, with the upgrades due at the slot it reaches.

It moves the slot on by one, and writes the root of the new header at the slot before the new one.

A root that it makes readable was readable before it, or is that root.

The new header is the one before, with its state root filled by the root of the state before. -/
private theorem advanceSlotAcross_cases {forked after : ForkedBeaconState preset}
    (computed : advanceSlotAcross config checks forked = .ok after) :
    after.state.slot.toNat = forked.state.slot.toNat + 1 ∧
      (∃ root, hashTreeRoot after.state.latestBlockHeader = .ok root ∧
        readCircular after.state.blockRoots.elements (after.state.slot - 1) = .ok root) ∧
      (∀ {slot : Slot} {root : Root}, getBlockRootAtSlot after.state slot = .ok root →
        (slot < forked.state.slot ∧ getBlockRootAtSlot forked.state slot = .ok root) ∨
          (slot = forked.state.slot ∧ hashTreeRoot after.state.latestBlockHeader = .ok root)) ∧
      ∃ root, hashTreeRoot forked.state = .ok root ∧
        after.state.latestBlockHeader =
          if forked.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
            { forked.state.latestBlockHeader with stateRoot := root }
          else forked.state.latestBlockHeader := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  have slot := processUpgrades_slot upgraded
  have roots := processUpgrades_blockRoots upgraded
  have header := latestBlockHeader_processUpgrades upgraded
  refine ⟨(congrArg UInt64.toNat slot).trans (advanceSlot_slot advancedOk), ?_, ?_, ?_⟩
  · obtain ⟨root, rooted, read⟩ := advanceSlot_latestBlockRoot advancedOk
    exact ⟨root, by rw [header]; exact rooted, by rw [roots, slot]; exact read⟩
  · intro slot' root read
    rw [getBlockRootAtSlot_congr slot roots] at read
    rw [header]
    exact getBlockRootAtSlot_advanceSlot_cases advancedOk read
  · obtain ⟨root, hashed, filled⟩ := advanceSlot_latestBlockHeader advancedOk
    exact ⟨root, hashed, by rw [header]; exact filled⟩

/-- A state of a run that hashes to the zero root. -/
private def ZeroPreimage (config : Config) (checks : SignatureChecks)
    (first last : ForkedBeaconState preset) : Prop :=
  ∃ forked : ForkedBeaconState preset,
    Relation.ReflTransGen (ChainStep config checks) first forked ∧
    Relation.ReflTransGen (ChainStep config checks) forked last ∧
    hashTreeRoot forked.state = .ok (Vector.replicate 32 0)

/-- The ways in which a pair of roots that a state of a run records can arise. -/
private def LinkCases (config : Config) (checks : SignatureChecks)
    (first last : ForkedBeaconState preset) (link : Root × Root) : Prop :=
  link.1 = link.2 ∨
    (∃ (fork : Fork) (engine : ExecutionEngine preset fork) (pre post : BeaconState preset fork)
        (signed : SignedBeaconBlock preset fork) (validateResult : Bool) (stateRoot : Root),
      Relation.ReflTransGen (ChainStep config checks) first ⟨fork, pre⟩ ∧
      applySignedBlock config checks engine pre signed validateResult = .ok post ∧
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, post⟩ last ∧
      signed.message.parentRoot = link.1 ∧ hashTreeRoot post = .ok stateRoot ∧
      hashTreeRoot { signed.message with stateRoot := stateRoot } = .ok link.2) ∨
    link ∈ rootLinks first.state ∨
    ((if first.state.slot = 0 then link.1 = Vector.replicate 32 0 else
        readCircular first.state.blockRoots.elements (first.state.slot - 1) = .ok link.1) ∧
      ∃ stateRoot, hashTreeRoot first.state = .ok stateRoot ∧
      hashTreeRoot (if first.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
        { first.state.latestBlockHeader with stateRoot := stateRoot }
      else first.state.latestBlockHeader) = .ok link.2) ∨
    ZeroPreimage config checks first last

/-- What a state of a run says about the root that the next slot records.

In the first case the state records the root of its latest header at the slot before it.

The next slot then records the same root, unless it fills the header.

It fills the header when its state root is zero.

Such a header stays unfilled through a slot only if the state before that slot hashed to zero.

So such a header comes only from a state of the run that hashes to zero, a zero preimage.

In the second case the state has just taken a block.

Its header is that of the block, and the next slot fills it with the root of the state.

The next slot then records the root of the block, next to the root of the parent.

In the third case the state is the first one, and its next slot gives the first pair. -/
private def HeaderCases (config : Config) (checks : SignatureChecks)
    (first last forked : ForkedBeaconState preset) : Prop :=
  (forked.state.slot = 0 ∨ ∃ root,
      readCircular forked.state.blockRoots.elements (forked.state.slot - 1) = .ok root ∧
        hashTreeRoot forked.state.latestBlockHeader = .ok root ∧
        (forked.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 →
          ZeroPreimage config checks first last)) ∨
    (forked.state.slot ≠ 0 ∧ forked.state.latestBlockHeader.slot = forked.state.slot ∧
      forked.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 ∧
      ∃ parent, readCircular forked.state.blockRoots.elements (forked.state.slot - 1) = .ok parent ∧
        ∀ stateRoot root, hashTreeRoot forked.state = .ok stateRoot →
          hashTreeRoot { forked.state.latestBlockHeader with stateRoot := stateRoot } = .ok root →
            LinkCases config checks first last (parent, root)) ∨
    (forked = first ∧ forked.state.slot ≠ 0 ∧
      (forked.state.latestBlockHeader.slot = forked.state.slot ∨ ∃ root,
        readCircular forked.state.blockRoots.elements (forked.state.slot - 1) = .ok root ∧
          hashTreeRoot forked.state.latestBlockHeader = .ok root))

/-- The pair that a slot adds to the roots is a case.

The state before the slot is past slot zero and meets the header cases. -/
private theorem linkCases_of_headerCases {first last before : ForkedBeaconState preset}
    (header : HeaderCases config checks first last before) (moved : before.state.slot ≠ 0)
    {parent root stateRoot : Root}
    (read : readCircular before.state.blockRoots.elements (before.state.slot - 1) = .ok parent)
    (hashed : hashTreeRoot before.state = .ok stateRoot)
    (rooted : hashTreeRoot (if before.state.latestBlockHeader.stateRoot = Vector.replicate 32 0
      then { before.state.latestBlockHeader with stateRoot := stateRoot }
      else before.state.latestBlockHeader) = .ok root) :
    LinkCases config checks first last (parent, root) := by
  rcases header with (slot | ⟨recorded, read', rooted', empty⟩) |
    ⟨-, -, unfilled, parent', read', cases⟩ | ⟨rfl, -, -⟩
  · exact absurd slot moved
  · have same : recorded = parent := Except.ok.inj (read'.symm.trans read)
    by_cases filled : before.state.latestBlockHeader.stateRoot = Vector.replicate 32 0
    · exact .inr (.inr (.inr (.inr (empty filled))))
    · simp only [filled, ↓reduceIte] at rooted
      exact .inl (same.symm.trans (Except.ok.inj (rooted'.symm.trans rooted)))
  · have same : parent' = parent := Except.ok.inj (read'.symm.trans read)
    simp only [unfilled, ↓reduceIte] at rooted
    exact same ▸ cases stateRoot root hashed rooted
  · -- The first slot from the first state gives the first pair.
    refine .inr (.inr (.inr (.inl ⟨?_, stateRoot, hashed, rooted⟩)))
    simp only [moved, ↓reduceIte]
    exact read

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

/-- Along a run, each pair of roots that a state records is one of the cases.

The first state is at slot zero, has its latest header at its slot, or records that header's root.

That root is recorded at the slot before the first state. -/
private theorem rootLinks_cases_aux {first last : ForkedBeaconState preset}
    (recorded : first.state.slot = 0 ∨ first.state.latestBlockHeader.slot = first.state.slot ∨
      ∃ root,
        readCircular first.state.blockRoots.elements (first.state.slot - 1) = .ok root ∧
          hashTreeRoot first.state.latestBlockHeader = .ok root) :
    ∀ {forked : ForkedBeaconState preset},
      Relation.ReflTransGen (ChainStep config checks) first forked →
      Relation.ReflTransGen (ChainStep config checks) forked last →
      first.state.slot.toNat ≤ forked.state.slot.toNat ∧ (forked.state.slot = 0 → forked = first) ∧
        (∀ link ∈ rootLinks forked.state, LinkCases config checks first last link) ∧
        HeaderCases config checks first last forked := by
  intro forked reach
  induction reach with
  | refl =>
    intro _
    refine ⟨Nat.le_refl _, fun _ => rfl, fun link member => .inr (.inr (.inl member)), ?_⟩
    by_cases slot : first.state.slot = 0
    · exact .inl (.inl slot)
    · rcases recorded with zero | rest
      · exact absurd zero slot
      · exact .inr (.inr ⟨rfl, slot, rest⟩)
  | @tail before after reach step ih =>
    intro toLast
    have toBefore := Relation.ReflTransGen.head step toLast
    have toAfter := Relation.ReflTransGen.tail reach step
    obtain ⟨floor, atZero, links, header⟩ := ih toBefore
    cases step with
    | slot computed =>
      obtain ⟨sum, ⟨written, rooted, writtenRead⟩, origin, stateRoot, hashed, filled⟩ :=
        advanceSlotAcross_cases computed
      refine ⟨by omega, fun zero => ?_, ?_, ?_⟩
      · have := congrArg UInt64.toNat zero
        simp at this
        omega
      · rintro ⟨root₁, root₂⟩ (⟨slot, readA, readB⟩ | ⟨isZero, readZero⟩)
        · -- Two consecutive slots: both were recorded before, or the second is the new root.
          obtain ⟨ltA, -⟩ := getBlockRootAtSlot_read readA
          obtain ⟨ltB, -⟩ := getBlockRootAtSlot_read readB
          have ltA' := UInt64.lt_iff_toNat_lt.mp ltA
          have succ : (slot + 1).toNat = slot.toNat + 1 := by
            have := after.state.slot.toNat_lt
            rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
          rcases origin readB with ⟨olderB, readB'⟩ | ⟨sameB, rootedB⟩
          · rcases origin readA with ⟨-, readA'⟩ | ⟨sameA, -⟩
            · exact links (root₁, root₂) (.inl ⟨slot, readA', readB'⟩)
            · have := UInt64.lt_iff_toNat_lt.mp olderB
              have := congrArg UInt64.toNat sameA
              omega
          · rcases origin readA with ⟨-, readA'⟩ | ⟨sameA, -⟩
            · have moved : before.state.slot ≠ 0 := by
                intro zero
                have := congrArg UInt64.toNat sameB
                rw [succ, zero] at this
                simp at this
              have pred : before.state.slot - 1 = slot := by
                rw [← sameB]
                exact UInt64.add_sub_cancel slot 1
              rw [filled] at rootedB
              refine linkCases_of_headerCases header moved ?_ hashed rootedB
              rw [pred]
              exact (getBlockRootAtSlot_read readA').2
            · have := congrArg UInt64.toNat sameB
              have := congrArg UInt64.toNat sameA
              omega
        · -- The zero root and the root at slot zero.
          rcases origin readZero with ⟨-, read0⟩ | ⟨sameZero, rootedZero⟩
          · exact links (root₁, root₂) (.inr ⟨isZero, read0⟩)
          · -- No block comes at slot zero, so the state before is the first one.
            have zeroSlot : before.state.slot = 0 := by
              have := congrArg UInt64.toNat sameZero
              exact UInt64.toNat_inj.mp (by simpa using this.symm)
            have same : before = first := atZero zeroSlot
            have first0 : first.state.slot = 0 := same ▸ zeroSlot
            rw [same] at hashed filled
            rw [filled] at rootedZero
            refine .inr (.inr (.inr (.inl ⟨?_, stateRoot, hashed, rootedZero⟩)))
            simp only [first0, ↓reduceIte]
            exact isZero
      · -- The new header was filled by the state before it, unless the state hashed to zero.
        refine .inl (.inr ⟨written, writtenRead, rooted, fun empty => ?_⟩)
        obtain ⟨zero, -⟩ := unfilled_of_filled filled empty
        exact ⟨before, reach, toBefore, zero ▸ hashed⟩
    | @block fork pre post engine signed validateResult applied =>
      obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
      have slot := processBlock_slot blockOk
      have roots := processBlock_blockRoots blockOk
      obtain ⟨atSlot, newer, parentHashed⟩ := processBlock_parentRoot blockOk
      obtain ⟨bodyRoot, bodyRooted, headerEq⟩ := latestBlockHeader_processBlock blockOk
      have moved : pre.slot ≠ 0 := by
        intro zero
        have := UInt64.lt_iff_toNat_lt.mp newer
        rw [atSlot, zero] at this
        simp at this
      -- The state before the block has not just taken a block, so it records its header's root.
      obtain ⟨parent, readParent, isParent⟩ : ∃ parent,
          readCircular pre.blockRoots.elements (pre.slot - 1) = .ok parent ∧
            signed.message.parentRoot = parent := by
        rcases header with (zero | ⟨parent, readParent, hashedHeader, -⟩) |
          ⟨-, headerSlot, -⟩ | ⟨-, -, headerSlot | ⟨parent, readParent, hashedHeader⟩⟩
        · exact absurd zero moved
        · exact ⟨parent, readParent, Except.ok.inj (parentHashed.symm.trans hashedHeader)⟩
        · rw [headerSlot, atSlot] at newer
          exact absurd newer (UInt64.lt_irrefl _)
        · rw [headerSlot, atSlot] at newer
          exact absurd newer (UInt64.lt_irrefl _)
        · exact ⟨parent, readParent, Except.ok.inj (parentHashed.symm.trans hashedHeader)⟩
      refine ⟨by rw [slot]; exact floor, fun zero => ?_, fun link member => ?_,
        .inr (.inl ⟨?_, ?_, ?_, parent, ?_, ?_⟩)⟩
      · rw [slot] at zero
        exact absurd zero moved
      · rw [rootLinks_congr slot roots] at member
        exact links link member
      · rw [slot]
        exact moved
      · rw [headerEq, slot]
        exact atSlot
      · rw [headerEq]
      · rw [roots, slot]
        exact readParent
      · intro stateRoot root hashed rooted
        rw [headerEq] at rooted
        have block := BeaconBlock.hashTreeRoot_header
          (block := { signed.message with stateRoot := stateRoot }) bodyRooted
        exact .inr (.inl ⟨fork, engine, pre, post, signed, validateResult, stateRoot, reach,
          applied, toLast, isParent, hashed, block.symm.trans rooted⟩)

/-- The roots that a state records at consecutive slots, along a run of a chain.

Two consecutive slots record the same root, or the parent root and the root of a block step.

The block step lies on a run between the first and the last state.

It may skip the check of the state root.

So the root of the block is that of the block with another state root.

That state root is the root of the state after the step.

A step that checks the state root has that root in its block already, so the block is unchanged.

The pair may also be one that the first state records.

It may be the first pair, which the first slot of the run adds.

Its second root is that of the first header, filled with the root of the first state.

Its first root is the root at the slot before the first state, or the zero root at slot zero.

Or a state of the run hashes to the zero root, which leaves the latest header unfilled at its slot.

The first state is at slot zero, or its latest header is at its own slot, as after a block.

Or it records the root of its latest header at the slot before it.

Every state that a block or a slot produces meets this.

Otherwise a block on the first state could name a parent that the state does not record. -/
theorem rootLinks_cases_of_chainSteps {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last)
    (recorded : first.state.slot = 0 ∨ first.state.latestBlockHeader.slot = first.state.slot ∨
      ∃ root,
        readCircular first.state.blockRoots.elements (first.state.slot - 1) = .ok root ∧
          hashTreeRoot first.state.latestBlockHeader = .ok root)
    {root₁ root₂ : Root} (member : (root₁, root₂) ∈ rootLinks last.state) :
    root₁ = root₂ ∨
      (∃ (fork : Fork) (engine : ExecutionEngine preset fork) (pre post : BeaconState preset fork)
          (signed : SignedBeaconBlock preset fork) (validateResult : Bool) (stateRoot : Root),
        Relation.ReflTransGen (ChainStep config checks) first ⟨fork, pre⟩ ∧
        applySignedBlock config checks engine pre signed validateResult = .ok post ∧
        Relation.ReflTransGen (ChainStep config checks) ⟨fork, post⟩ last ∧
        signed.message.parentRoot = root₁ ∧ hashTreeRoot post = .ok stateRoot ∧
        hashTreeRoot { signed.message with stateRoot := stateRoot } = .ok root₂) ∨
      (root₁, root₂) ∈ rootLinks first.state ∨
      ((if first.state.slot = 0 then root₁ = Vector.replicate 32 0 else
          readCircular first.state.blockRoots.elements (first.state.slot - 1) = .ok root₁) ∧
        ∃ stateRoot, hashTreeRoot first.state = .ok stateRoot ∧
          hashTreeRoot (if first.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
            { first.state.latestBlockHeader with stateRoot := stateRoot }
          else first.state.latestBlockHeader) = .ok root₂) ∨
      ∃ forked : ForkedBeaconState preset,
        Relation.ReflTransGen (ChainStep config checks) first forked ∧
        Relation.ReflTransGen (ChainStep config checks) forked last ∧
        hashTreeRoot forked.state = .ok (Vector.replicate 32 0) :=
  (rootLinks_cases_aux recorded steps Relation.ReflTransGen.refl).2.2.1 (root₁, root₂) member

/-- Along a run, a map from roots that orders each block step after its parent orders the links.

The map goes to a preorder.

It orders the parent root of each block step before the root of its block.

The step is on any run between the first and the last state.

The root of its block takes the root of the state after the step as its state root.

The map must also order the pairs of the first state, and the first pair.

The links of the last state are then in order, unless a state of the run hashes to the zero root.

So it gives the order of the links that a step of the justified roots asks of the last state.

Each state of the run is the last state of a shorter run, which gives the order at every step. -/
theorem zeroPreimage_or_rootLinks_le_of_chainSteps {β : Type*} [Preorder β] {block : Root → β}
    {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last)
    (recorded : first.state.slot = 0 ∨ first.state.latestBlockHeader.slot = first.state.slot ∨
      ∃ root,
        readCircular first.state.blockRoots.elements (first.state.slot - 1) = .ok root ∧
          hashTreeRoot first.state.latestBlockHeader = .ok root)
    (start : ∀ link ∈ rootLinks first.state, block link.1 ≤ block link.2)
    (opening : ∀ before stateRoot root : Root,
      (if first.state.slot = 0 then before = Vector.replicate 32 0 else
        readCircular first.state.blockRoots.elements (first.state.slot - 1) = .ok before) →
      hashTreeRoot first.state = .ok stateRoot →
      hashTreeRoot (if first.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
        { first.state.latestBlockHeader with stateRoot := stateRoot }
      else first.state.latestBlockHeader) = .ok root → block before ≤ block root)
    (ordered : ∀ (fork : Fork) (engine : ExecutionEngine preset fork)
      (pre post : BeaconState preset fork) (signed : SignedBeaconBlock preset fork)
      (validateResult : Bool) (stateRoot root : Root),
      Relation.ReflTransGen (ChainStep config checks) first ⟨fork, pre⟩ →
      applySignedBlock config checks engine pre signed validateResult = .ok post →
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, post⟩ last →
      hashTreeRoot post = .ok stateRoot →
      hashTreeRoot { signed.message with stateRoot := stateRoot } = .ok root →
      block signed.message.parentRoot ≤ block root) :
    (∃ forked : ForkedBeaconState preset,
      Relation.ReflTransGen (ChainStep config checks) first forked ∧
      Relation.ReflTransGen (ChainStep config checks) forked last ∧
      hashTreeRoot forked.state = .ok (Vector.replicate 32 0)) ∨
    ∀ link ∈ rootLinks last.state, block link.1 ≤ block link.2 := by
  by_cases zero : ∃ forked : ForkedBeaconState preset,
    Relation.ReflTransGen (ChainStep config checks) first forked ∧
    Relation.ReflTransGen (ChainStep config checks) forked last ∧
    hashTreeRoot forked.state = .ok (Vector.replicate 32 0)
  · exact .inl zero
  · refine .inr fun link member => ?_
    rcases rootLinks_cases_of_chainSteps steps recorded (root₁ := link.1) (root₂ := link.2)
      member with
      same | ⟨fork, engine, pre, post, signed, validateResult, stateRoot, before, applied, after,
        parent, hashed, rooted⟩ | recorded' | ⟨opened, stateRoot, hashed, rooted⟩ | found
    · exact (congrArg block same).le
    · rw [← parent]
      exact ordered fork engine pre post signed validateResult stateRoot link.2 before applied after
        hashed rooted
    · exact start link recorded'
    · exact opening link.1 stateRoot link.2 opened hashed rooted
    · exact absurd found zero

end EthLib.Consensus
