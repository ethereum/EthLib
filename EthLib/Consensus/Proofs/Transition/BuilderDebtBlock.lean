module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtOperations
public import EthLib.Consensus.Proofs.Transition.BuilderDebtWithdrawals
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.TargetSlots

/-!
# Proofs: blocks and slots keep each builder's debt covered

The balance of each builder covers its debt, from the upgrade to Gloas on.

The upgrade starts with no debt, no payment and a latest bid of no value.

A block keeps the invariant, as a whole.

Its parent payload settles the parent payment and weakens the invariant.

Its withdrawals keep the weaker form, and its bid restores the invariant.

Its operations and its sync aggregate keep it.

The slots keep it too, under a payment quorum of at least one gwei.

So no builder withdrawal falls short, in a block from a covered state after a full parent.

Each registry must hold at most 2^40 entries, so that the index of a withdrawal names one builder.

The state transition does not bound the registries, so the theorems assume both bounds.

They assume them after the block or at the end of a chain, since no step shrinks a registry.

An epoch must also have at least two slots, so that the current epoch is never the far future one.

The upgrade to Heze carries the invariant over.

So the invariant also holds across the fork upgrades, on the way to the slot of each block.

[EIP-7732] adds the builders, their bids, their payments and their withdrawals.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- The mainnet and minimal presets have at least two slots in an epoch. -/
theorem twoSlotsPerEpoch_presets :
    2 ≤ Preset.mainnet.SLOTS_PER_EPOCH.toNat ∧ 2 ≤ Preset.minimal.SLOTS_PER_EPOCH.toNat := by
  decide

/-! ## The upgrades -/

/-- A state with no pending payment, no queued withdrawal and a latest bid of no value is covered.
-/
private theorem BuilderDebtCovered.of_empty {gloas : .glamsterdam ≤ fork}
    (payments : (state.builderPendingPayments gloas).elements = Vector.replicate _ .empty)
    (withdrawals : (state.builderPendingWithdrawals gloas).data = #[])
    (value : (state.latestExecutionPayloadBid gloas).value = 0) :
    BuilderDebtCovered state gloas := by
  have total : ∀ index, pendingBuilderTotal state gloas index = 0 := fun _ => by
    simp [pendingBuilderTotal, owedBy, payments, withdrawals, BuilderPendingPayment.empty]
  have late : ∀ index, lateBidValue state gloas index = 0 := fun _ => by
    simp [lateBidValue, value]
  have empty : ∀ k, paymentAt state gloas k = .empty := fun k => by
    simp only [paymentAt, payments]
    rw [Vector.getElem?_replicate]
    split <;> rfl
  refine ⟨fun index => ?_, fun index _ _ _ => ?_, fun position _ => ?_, fun k _ => empty k⟩
  · rw [total, late]
    exact Nat.zero_le _
  · rw [total, late]
  · rw [empty]
    exact ⟨rfl, .inl rfl⟩

/-- The upgrade to Gloas starts with each builder's debt covered. -/
theorem builderDebtCovered_upgradeToGloas {pre : BeaconState preset .fusaka}
    {post : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok post) :
    BuilderDebtCovered post (by decide) := by
  unfold upgradeToGloas at computed
  obtain ⟨root, -, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨window, -, onboarded⟩ := bind_ok_iff.mp rest
  obtain ⟨⟨builders, pending, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
  exact .of_empty rfl rfl rfl

/-- The upgrade to Heze keeps each builder's debt covered. -/
theorem BuilderDebtCovered.upgradeToHeze {pre : BeaconState preset .glamsterdam}
    {post : BeaconState preset .hegota} (holds : BuilderDebtCovered pre (by decide))
    (computed : upgradeToHeze config pre = .ok post) : BuilderDebtCovered post (by decide) := by
  obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp computed
  -- The upgrade copies every field that the invariant reads, and the bid keeps its value.
  have position : parentPaymentPosition (upgradeHezeFields config pre) =
      parentPaymentPosition pre := rfl
  have total : ∀ index, pendingBuilderTotal (upgradeHezeFields config pre) (by decide) index =
      pendingBuilderTotal pre (by decide) index := fun _ => rfl
  have late : ∀ index, lateBidValue (upgradeHezeFields config pre) (by decide) index =
      lateBidValue pre (by decide) index := fun _ => by
    simp only [lateBidValue, latePaymentOpen, position]
    rfl
  have balance : ∀ index, builderBalance (upgradeHezeFields config pre) (by decide) index =
      builderBalance pre (by decide) index := fun _ => rfl
  refine ⟨fun index => ?_, fun index builder found exited => ?_, fun p found => ?_,
    fun k later => ?_⟩
  · rw [total, late, balance]
    exact holds.covered index
  · rw [total, late]
    exact holds.exitedClear index builder found exited
  · exact holds.parentFresh p (position ▸ found)
  · exact holds.laterEmpty k fun parent found => later parent (position ▸ found)

/-! ## Blocks -/

/-- A builder deposit never shrinks the registry of builders. -/
private theorem builders_size_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    (state.builders gloas).data.size ≤ (after.builders gloas).data.size := by
  unfold Consensus.processBuilderDepositRequest at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Nat.le_refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      unfold addBuilderToRegistry
      dsimp only
      split
      · simp [BeaconState.putBuilder]
      · simp
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Nat.le_refl _
  · dsimp only at computed
    split at computed
    all_goals
      simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
        Uint64.addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, rfl⟩ := computed
      simp [BeaconState.putBuilder]

/-- A builder exit request never shrinks the registry of builders. -/
private theorem builders_size_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    (state.builders gloas).data.size ≤ (after.builders gloas).data.size := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact Nat.le_refl _
  simp only [initiateBuilderExit, bind_ok_iff] at exited
  obtain ⟨_, _, _, _, set⟩ := exited
  obtain ⟨_, rfl⟩ := setBuilder_ok set
  simp [BeaconState.putBuilder]

/-- The parent payload never shrinks the registry of builders. -/
private theorem builders_size_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    (state.builders gloas).data.size ≤ (after.builders gloas).data.size := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, _, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk, buildersOk,
      exitsOk, -, rfl⟩
  · exact Nat.le_refl _
  have paid := settleParentPayment_builders settledOk
  -- The requests of validators keep the builder fields.
  have frame :=
    (BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_processDepositRequest ok)
      depositsOk).trans <|
    (BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_processConsolidationRequest ok)
      consolidationsOk
  have deposited := foldlM_ok_invariant
    (fun s => (state.builders gloas).data.size ≤ (s.builders gloas).data.size)
    (fun _ _ _ before ok => Nat.le_trans before (builders_size_processBuilderDepositRequest ok))
    (Nat.le_of_eq (by rw [frame.builders, paid])) buildersOk
  exact foldlM_ok_invariant
    (fun s => (state.builders gloas).data.size ≤ (s.builders gloas).data.size)
    (fun _ _ _ before ok => Nat.le_trans before (builders_size_processBuilderExitRequest ok))
    deposited exitsOk

/-- The sync aggregate keeps the builder fields, the slot and the slot of the latest block. -/
private theorem builderFrame_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    BuilderFrame state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine BuilderFrame.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (builderFrame_increaseBalance raised).trans (builderFrame_increaseBalance paid)
  · exact builderFrame_decreaseBalance (liftAccessor_ok.mp ok)

/-- With at least two slots in an epoch, the current epoch is never the far future one. -/
private theorem getCurrentEpoch_ne_farFuture (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (state : BeaconState preset fork) : getCurrentEpoch state ≠ FAR_FUTURE_EPOCH := by
  intro far
  have epoch := congrArg UInt64.toNat far
  rw [getCurrentEpoch_toNat] at epoch
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have half := Nat.div_le_div_left (a := state.slot.toNat) twoSlots (by decide)
  have := state.slot.toNat_lt_size
  simp only [UInt64.size] at this
  omega

/-- From Gloas, a block runs its parent, header, withdrawal and bid steps, then the rest.

Except the operations, the rest keeps the builder fields.

It also keeps the slot and the slot of the latest block.

After the header, no step shrinks a registry, and the steps keep the number of builders. -/
private theorem processBlock_gloas_steps (gloas : .glamsterdam ≤ fork)
    {block : BeaconBlock preset fork}
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    ∃ parented headed withdrawn bidded voted operated, ∃ payload,
      Consensus.processParentExecutionPayload config checks state gloas block.body =
        .ok parented ∧
      processBlockHeader parented block = .ok headed ∧
      processWithdrawals headed (Nat.le_trans (by decide) gloas) payload = .ok withdrawn ∧
      processExecutionPayloadBid config checks withdrawn gloas
        (block.body.signedExecutionPayloadBid gloas) = .ok bidded ∧
      BuilderFrame bidded voted ∧
      processOperations config checks voted block.body state.latestBlockHeader.slot =
        .ok operated ∧
      BuilderFrame operated after ∧
      headed.validators.data.size ≤ after.validators.data.size ∧
      (headed.builders gloas).data.size = (after.builders gloas).data.size := by
  obtain ⟨parented, headed, withdrawn, bidded, revealed, voted, operated, _, parentOk, headedOk,
    withdrawnOk, biddedOk, revealedOk, votedOk, kept, operatedOk, synced⟩ :=
    processBlock_gloas_ok gloas computed
  have revealedFrame : BuilderFrame bidded revealed := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- Heze drops the vote on the deposit contract.
  have votedFrame : BuilderFrame revealed voted ∧ BlockFrame revealed voted := by
    by_cases before : fork < .hegota
    · refine ⟨?_, frame_processEth1Data (votedOk before)⟩
      obtain ⟨_, _, rest⟩ := processEth1Data_eq (votedOk before)
      rw [← rest]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [kept (Nat.le_of_not_lt before)]
      exact ⟨BuilderFrame.refl _, BlockFrame.refl _⟩
  have syncedFrame := builderFrame_processSyncAggregate synced
  have grows := Nat.le_trans (frame_processWithdrawals withdrawnOk).registryGrows <|
    Nat.le_trans (frame_processExecutionPayloadBid biddedOk).registryGrows <|
    Nat.le_trans (frame_processRandao revealedOk).registryGrows <|
    Nat.le_trans votedFrame.2.registryGrows <|
    Nat.le_trans (frame_processOperations operatedOk).registryGrows
      (frame_processSyncAggregate synced).registryGrows
  refine ⟨parented, headed, withdrawn, bidded, voted, operated, _, parentOk, headedOk,
    withdrawnOk, biddedOk, revealedFrame.trans votedFrame.1, operatedOk, syncedFrame, grows, ?_⟩
  rw [← processWithdrawals_builders_size (gloas := gloas) withdrawnOk, syncedFrame.builders,
    processOperations_builders gloas operatedOk, votedFrame.1.builders, revealedFrame.builders,
    processExecutionPayloadBid_builders gloas biddedOk]

/-- From Gloas, a block never shrinks the registry of builders. -/
theorem processBlock_buildersGrow (gloas : .glamsterdam ≤ fork) {block : BeaconBlock preset fork}
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    (state.builders gloas).data.size ≤ (after.builders gloas).data.size := by
  obtain ⟨parented, headed, _, _, _, _, _, parentOk, headedOk, -, -, -, -, -, -, size⟩ :=
    processBlock_gloas_steps gloas computed
  have kept : headed.builders = parented.builders := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    rfl
  rw [← size, kept]
  exact builders_size_processParentExecutionPayload parentOk

/-- From Gloas, the parent payload and the header of a block leave the invariant inside a block.

The latest block is then at the slot of the state, which is not the first slot. -/
private theorem BuilderDebtCovered.headed {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} {parented headed : BeaconState preset fork}
    (holds : BuilderDebtCovered state gloas)
    (parentOk : Consensus.processParentExecutionPayload config checks state gloas block.body =
      .ok parented)
    (headedOk : processBlockHeader parented block = .ok headed) :
    BuilderDebtSettled headed gloas ∧ headed.latestBlockHeader.slot = headed.slot ∧
      headed.slot ≠ 0 := by
  have inputs := payloadInputs_processParentExecutionPayload parentOk
  have slot : parented.slot = state.slot := inputs.slot
  have header : parented.latestBlockHeader = state.latestBlockHeader := inputs.latestBlockHeader
  obtain ⟨same, newer, -⟩ := processBlockHeader_checks headedOk
  have older : state.latestBlockHeader.slot < state.slot := by
    rw [← slot, ← header, ← same]
    exact newer
  obtain ⟨settled, placed⟩ :=
    (holds.processParentExecutionPayload older parentOk).processBlockHeader headedOk
  refine ⟨settled, placed, ?_⟩
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
  show parented.slot ≠ 0
  rw [slot]
  intro zero
  rw [zero] at older
  exact absurd older (by simp)

/-- From Gloas, a block keeps each builder's debt covered.

The preset needs a positive payment quorum and at least two slots in an epoch.

Each registry must hold at most 2^40 entries after the block. -/
theorem BuilderDebtCovered.processBlock (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} (holds : BuilderDebtCovered state gloas)
    (validatorsFit : after.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (after.builders gloas).data.size ≤ 2 ^ 40)
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    BuilderDebtCovered after gloas := by
  obtain ⟨parented, headed, withdrawn, bidded, voted, operated, _, parentOk, headedOk,
    withdrawnOk, biddedOk, votedFrame, operatedOk, syncedFrame, grows, size⟩ :=
    processBlock_gloas_steps gloas computed
  obtain ⟨settled, placed, started⟩ := holds.headed parentOk headedOk
  -- The withdrawals keep the form inside a block, and the bid restores the invariant.
  have withdrawnInputs := payloadInputs_processWithdrawals withdrawnOk
  have paid := settled.processWithdrawals (Nat.le_trans grows validatorsFit)
    (by rw [size]; exact buildersFit) (getCurrentEpoch_ne_farFuture twoSlots headed) withdrawnOk
  have bidInputs := payloadInputs_processExecutionPayloadBid biddedOk
  have bidSlot : bidded.slot = headed.slot := bidInputs.slot.trans withdrawnInputs.slot
  have bidHeader : bidded.latestBlockHeader = headed.latestBlockHeader :=
    bidInputs.latestBlockHeader.trans withdrawnInputs.latestBlockHeader
  have bidHolds := paid.processExecutionPayloadBid positive
    (by rw [withdrawnInputs.latestBlockHeader, withdrawnInputs.slot]; exact placed) biddedOk
  -- The operations then keep it, and so do the steps around them.
  have operatedHolds := (bidHolds.of_frame votedFrame).processOperations positive
    (by rw [votedFrame.headerSlot, votedFrame.slot, bidHeader, bidSlot]; exact placed)
    (by rw [votedFrame.slot, bidSlot]; exact started) operatedOk
  exact operatedHolds.of_frame syncedFrame

/-- From Gloas, after a full parent, a block's withdrawals lower each builder's balance.

They lower it by what they take.

They run on the state after the parent payload and the header of the block.

Each registry must hold at most 2^40 entries after the block. -/
theorem BuilderDebtCovered.processBlock_builderBalance {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} (holds : BuilderDebtCovered state gloas)
    (validatorsFit : after.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (after.builders gloas).data.size ≤ 2 ^ 40)
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    ∃ paid headed,
      Consensus.processParentExecutionPayload config checks state gloas block.body = .ok paid ∧
      processBlockHeader paid block = .ok headed ∧
      ∀ (capella : .shapella ≤ fork)
        (payload : Until .glamsterdam fork (ExecutionPayload preset fork))
        (withdrawn : BeaconState preset fork) (expected : ExpectedWithdrawals),
        isParentBlockFull headed gloas = true →
        getExpectedWithdrawals headed capella = .ok expected →
        Consensus.processWithdrawals headed capella payload = .ok withdrawn →
        ∀ index : BuilderIndex, index.toNat < (headed.builders gloas).data.size →
          builderBalance withdrawn gloas index +
              withdrawnFrom expected.withdrawals (convertBuilderIndexToValidatorIndex index) =
            builderBalance headed gloas index := by
  obtain ⟨parented, headed, _, _, _, _, _, parentOk, headedOk, -, -, -, -, -, grows, size⟩ :=
    processBlock_gloas_steps gloas computed
  obtain ⟨settled, -, -⟩ := holds.headed parentOk headedOk
  refine ⟨parented, headed, parentOk, headedOk,
    fun _ _ _ _ full expectedOk withdrawnOk _ member => ?_⟩
  exact settled.processWithdrawals_builderBalance (Nat.le_trans grows validatorsFit)
    (by rw [size]; exact buildersFit) full expectedOk withdrawnOk member

/-! ## Slots and the state transition -/

/-- A run of slots never shrinks the registry of validators. -/
theorem processSlots_registryGrows {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    state.validators.data.size ≤ after.validators.data.size := by
  simp only [Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨-, -, advanced⟩ := computed
  exact advanceSlots_registryGrows advanced

/-- From Gloas, each valid block keeps each builder's debt covered, with the slots before it.

The preset needs a positive payment quorum and at least two slots in an epoch.

Each registry must hold at most 2^40 entries after the block. -/
theorem BuilderDebtCovered.stateTransition (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (holds : BuilderDebtCovered state gloas)
    (validatorsFit : after.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (after.builders gloas).data.size ≤ 2 ^ 40)
    (computed : Consensus.stateTransition config checks engine state signed validateResult =
      .ok after) :
    BuilderDebtCovered after gloas := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  exact (holds.processSlots positive slotsOk).processBlock positive twoSlots validatorsFit
    buildersFit blockOk

/-- A chain of valid blocks never shrinks the registry of validators. -/
private theorem stateTransitions_registryGrows {validateResult : Bool} :
    ∀ {blocks : List (SignedBeaconBlock preset fork)} {state after : BeaconState preset fork},
      blocks.foldlM (fun state signed =>
        Consensus.stateTransition config checks engine state signed validateResult) state =
          .ok after →
      state.validators.data.size ≤ after.validators.data.size
  | [], _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Nat.le_refl _
  | _ :: _, _, _, computed => by
    rw [List.foldlM_cons] at computed
    obtain ⟨_, stepOk, restOk⟩ := bind_ok_iff.mp computed
    obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok stepOk
    exact Nat.le_trans (Nat.le_trans (processSlots_registryGrows slotsOk)
      (frame_processBlock blockOk).registryGrows) (stateTransitions_registryGrows restOk)

/-- From Gloas, a chain of valid blocks never shrinks the registry of builders. -/
theorem stateTransitions_buildersGrow (gloas : .glamsterdam ≤ fork) {validateResult : Bool} :
    ∀ {blocks : List (SignedBeaconBlock preset fork)} {state after : BeaconState preset fork},
      blocks.foldlM (fun state signed =>
        Consensus.stateTransition config checks engine state signed validateResult) state =
          .ok after →
      (state.builders gloas).data.size ≤ (after.builders gloas).data.size
  | [], _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Nat.le_refl _
  | _ :: _, _, _, computed => by
    rw [List.foldlM_cons] at computed
    obtain ⟨_, stepOk, restOk⟩ := bind_ok_iff.mp computed
    obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok stepOk
    have builders := processSlots_builders gloas slotsOk
    exact Nat.le_trans (by rw [← builders]; exact processBlock_buildersGrow gloas blockOk)
      (stateTransitions_buildersGrow gloas restOk)

/-- From Gloas, a chain of valid blocks keeps each builder's debt covered.

The preset needs a positive payment quorum and at least two slots in an epoch.

Each registry must hold at most 2^40 entries at the end of the chain. -/
theorem BuilderDebtCovered.stateTransitions (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {validateResult : Bool} :
    ∀ {blocks : List (SignedBeaconBlock preset fork)} {state after : BeaconState preset fork},
      BuilderDebtCovered state gloas →
      after.validators.data.size ≤ 2 ^ 40 → (after.builders gloas).data.size ≤ 2 ^ 40 →
      blocks.foldlM (fun state signed =>
        Consensus.stateTransition config checks engine state signed validateResult) state =
          .ok after →
      BuilderDebtCovered after gloas
  | [], _, _, holds, _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  | _ :: _, _, _, holds, validatorsFit, buildersFit, computed => by
    rw [List.foldlM_cons] at computed
    obtain ⟨_, stepOk, restOk⟩ := bind_ok_iff.mp computed
    -- The registries after the step bound those of the end of the chain.
    have stepped := holds.stateTransition positive twoSlots
      (Nat.le_trans (stateTransitions_registryGrows restOk) validatorsFit)
      (Nat.le_trans (stateTransitions_buildersGrow gloas restOk) buildersFit) stepOk
    exact BuilderDebtCovered.stateTransitions positive twoSlots stepped validatorsFit buildersFit
      restOk

/-! ## Across the fork upgrades -/

/-- From Gloas, the balance of each builder covers its debt; before Gloas there is nothing to cover.
-/
def ForkedBuilderDebtCovered (forked : ForkedBeaconState preset) : Prop :=
  ∀ gloas : .glamsterdam ≤ forked.fork, BuilderDebtCovered forked.state gloas

/-- An upgrade keeps each builder's debt covered. -/
private theorem ForkedBuilderDebtCovered.upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (holds : ForkedBuilderDebtCovered pre)
    (computed : Consensus.upgradeNext config checks pre = .ok post) :
    ForkedBuilderDebtCovered post.val := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  -- Only the upgrades to Gloas and to Heze reach a fork that has builders.
  all_goals first
    | (subst computed; intro gloas; dsimp only at gloas; exact absurd gloas (by decide))
    | (obtain ⟨_, upgraded, rfl⟩ := computed
       first
        | (intro gloas; dsimp only at gloas; exact absurd gloas (by decide))
        | exact fun _ => builderDebtCovered_upgradeToGloas upgraded
        | exact fun _ => (holds (Nat.le_refl _)).upgradeToHeze upgraded)

/-- The upgrades due at a slot keep each builder's debt covered. -/
theorem ForkedBuilderDebtCovered.processUpgrades {forked after : ForkedBeaconState preset}
    (holds : ForkedBuilderDebtCovered forked)
    (computed : Consensus.processUpgrades config checks forked = .ok after) :
    ForkedBuilderDebtCovered after := by
  fun_induction Consensus.processUpgrades config checks forked generalizing after with
  | case1 forked _ more =>
    obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    exact more step (holds.upgradeNext stepOk) rest
  | case2 forked _ =>
    cases computed
    exact holds

/-- With a positive quorum, one slot keeps each builder's debt covered, with its upgrades. -/
theorem ForkedBuilderDebtCovered.advanceSlotAcross
    (positive : preset.PaymentQuorumPositive) {forked after : ForkedBeaconState preset}
    (holds : ForkedBuilderDebtCovered forked)
    (computed : Consensus.advanceSlotAcross config checks forked = .ok after) :
    ForkedBuilderDebtCovered after := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  exact ForkedBuilderDebtCovered.processUpgrades (forked := ⟨forked.fork, advanced⟩)
    (fun gloas => (holds gloas).advanceSlot positive advancedOk) upgraded

/-- With a positive quorum, slots keep each builder's debt covered, with the upgrades on the way.
-/
theorem ForkedBuilderDebtCovered.advanceSlotsAcross
    (positive : preset.PaymentQuorumPositive) :
    ∀ {count : Nat} {forked after : ForkedBeaconState preset}, ForkedBuilderDebtCovered forked →
      Consensus.advanceSlotsAcross config checks count forked = .ok after →
      ForkedBuilderDebtCovered after
  | 0, _, _, holds, computed => by
    simp only [Consensus.advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  | _ + 1, _, _, holds, computed => by
    simp only [Consensus.advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨_, nextOk, rest⟩ := computed
    exact ForkedBuilderDebtCovered.advanceSlotsAcross positive
      (holds.advanceSlotAcross positive nextOk) rest

/-- With a positive quorum, a run of slots keeps each builder's debt covered, across forks.

The upgrades on the way keep it too.

So the state before any block of a chain across forks is covered. -/
theorem ForkedBuilderDebtCovered.processSlotsAcross (positive : preset.PaymentQuorumPositive)
    {forked after : ForkedBeaconState preset} {slot : Slot}
    (holds : ForkedBuilderDebtCovered forked)
    (computed : Consensus.processSlotsAcross config checks forked slot = .ok after) :
    ForkedBuilderDebtCovered after := by
  simp only [Consensus.processSlotsAcross, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  exact ForkedBuilderDebtCovered.advanceSlotsAcross positive holds computed

/-- From Gloas, each valid block keeps each builder's debt covered, from a state of any fork.

The upgrades on the way to the slot of the block keep it too.

The preset needs a positive payment quorum and at least two slots in an epoch.

From Gloas, each registry must hold at most 2^40 entries after the block. -/
theorem ForkedBuilderDebtCovered.stateTransitionAcross (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {fork : Base.Fork}
    {engine : ExecutionEngine preset fork} {forked : ForkedBeaconState preset}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    {after : BeaconState preset fork} (holds : ForkedBuilderDebtCovered forked)
    (validatorsFit : .glamsterdam ≤ fork → after.validators.data.size ≤ 2 ^ 40)
    (buildersFit : ∀ gloas : .glamsterdam ≤ fork, (after.builders gloas).data.size ≤ 2 ^ 40)
    (computed :
      Consensus.stateTransitionAcross config checks engine forked signed validateResult =
        .ok after) :
    ForkedBuilderDebtCovered ⟨fork, after⟩ := by
  obtain ⟨advanced, slotsOk, applied⟩ := stateTransitionAcross_ok computed
  have advancedHolds := holds.processSlotsAcross positive slotsOk
  obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
  exact fun gloas => (advancedHolds gloas).processBlock positive twoSlots (validatorsFit gloas)
    (buildersFit gloas) blockOk

end EthLib.Consensus
