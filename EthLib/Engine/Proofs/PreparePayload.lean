module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Proofs.Builders
public import EthLib.Consensus.Proofs.Mutators
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.ParentPayload
public import EthLib.Consensus.Proofs.Transition.Withdrawals
public import EthLib.Engine.PreparePayload

/-!
# Proofs: the forkchoice update of a proposer

The terminal block search finds a block of the chain that reaches the terminal total difficulty.

Its parent is the zero hash, or a block of the chain below that difficulty.

The search finds none only when each block that reaches the difficulty has a parent that does too.

It fails only on a block that reaches the difficulty and whose parent the chain does not hold.

A forkchoice update states its head, its time, its mix, its withdrawals and its parent root.

Before the merge, the fork choice accepts a first payload on its head, on conditions.

With a configured terminal block hash, the block must be of the slot of the state.

Without one, the hashes of the chain must differ and no block may name the zero hash as its parent.

A block whose payload follows the update passes the parent, mix, time and withdrawal checks.

It must pass the header step on the state of the proposer.

Its execution part then fails only on the blob count, the execution layer, a hash, or an accessor.
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Consensus
open Serialization.Ssz.SszType

variable {preset : Preset} {fork : Fork} {config : Config}

/-! ## The terminal block of proof of work -/

/-- A block that the search finds is in the blocks it read, and is a valid terminal block.

It reaches the terminal total difficulty.

Its parent is the zero hash, or a block of the chain whose total difficulty is below it. -/
theorem getPowBlockAtTerminalTotalDifficulty_go_eq_ok_some {powChain rest : List PowBlock}
    {block : PowBlock}
    (found : getPowBlockAtTerminalTotalDifficulty.go config powChain rest = .ok (some block)) :
    block ∈ rest ∧ config.TERMINAL_TOTAL_DIFFICULTY ≤ block.totalDifficulty ∧
      (block.parentHash = ZERO_HASH ∨
        ∃ parent, findPowBlock powChain block.parentHash = some parent ∧
        isValidTerminalPowBlock config block parent = true) := by
  induction rest with
  | nil => simp [getPowBlockAtTerminalTotalDifficulty.go] at found
  | cons head tail step =>
    unfold getPowBlockAtTerminalTotalDifficulty.go at found
    split at found
    · rename_i reached
      split at found
      · rename_i genesis
        cases found
        exact ⟨List.mem_cons_self, reached, .inl genesis⟩
      · split at found
        · cases found
        · rename_i parent known
          split at found
          · rename_i valid
            cases found
            exact ⟨List.mem_cons_self, reached, .inr ⟨parent, known, valid⟩⟩
          · obtain ⟨mem, rest⟩ := step found
            exact ⟨List.mem_cons_of_mem _ mem, rest⟩
    · obtain ⟨mem, rest⟩ := step found
      exact ⟨List.mem_cons_of_mem _ mem, rest⟩

/-- The search finds no block when each block of the chain that reaches the difficulty fails.

Such a block names a parent other than the zero hash, and the chain holds that parent.

That parent reaches the difficulty too.

The search finds no block only then. -/
theorem getPowBlockAtTerminalTotalDifficulty_go_eq_ok_none_iff {powChain rest : List PowBlock} :
    getPowBlockAtTerminalTotalDifficulty.go config powChain rest = .ok none ↔
      ∀ block ∈ rest, config.TERMINAL_TOTAL_DIFFICULTY ≤ block.totalDifficulty →
        block.parentHash ≠ ZERO_HASH ∧
          ∃ parent, findPowBlock powChain block.parentHash = some parent ∧
          config.TERMINAL_TOTAL_DIFFICULTY ≤ parent.totalDifficulty := by
  induction rest with
  | nil => simp [getPowBlockAtTerminalTotalDifficulty.go]
  | cons head tail step =>
    unfold getPowBlockAtTerminalTotalDifficulty.go
    simp only [List.mem_cons, forall_eq_or_imp]
    split
    · rename_i reached
      split
      · rename_i genesis
        simp [reached, genesis]
      · rename_i notGenesis
        split
        · rename_i unknown
          simp [reached, unknown]
        · rename_i parent known
          split
          · rename_i valid
            simp only [isValidTerminalPowBlock, Bool.and_eq_true, decide_eq_true_eq] at valid
            constructor
            · intro same
              cases same
            · rintro ⟨first, -⟩
              obtain ⟨-, other, otherKnown, otherReached⟩ := first reached
              rw [known] at otherKnown
              cases otherKnown
              exact absurd otherReached (BitVec.not_le.mpr valid.2)
          · rename_i invalid
            simp only [isValidTerminalPowBlock, reached, decide_true, Bool.true_and,
              decide_eq_true_eq, BitVec.not_lt] at invalid
            rw [step]
            simp [notGenesis, known, invalid, reached]
    · rename_i below
      rw [step]
      simp [below]

/-- The search fails only on a block that reaches the difficulty and whose parent is unknown.

That block names a parent other than the zero hash, and the error names that parent. -/
theorem getPowBlockAtTerminalTotalDifficulty_go_eq_error {powChain rest : List PowBlock}
    {error : ProposerError}
    (failed : getPowBlockAtTerminalTotalDifficulty.go config powChain rest = .error error) :
    ∃ block ∈ rest, config.TERMINAL_TOTAL_DIFFICULTY ≤ block.totalDifficulty ∧
      block.parentHash ≠ ZERO_HASH ∧ findPowBlock powChain block.parentHash = none ∧
      error = .unknownPowBlock block.parentHash := by
  induction rest with
  | nil => simp [getPowBlockAtTerminalTotalDifficulty.go] at failed
  | cons head tail step =>
    unfold getPowBlockAtTerminalTotalDifficulty.go at failed
    split at failed
    · rename_i reached
      split at failed
      · cases failed
      · rename_i notGenesis
        split at failed
        · rename_i unknown
          cases failed
          exact ⟨head, List.mem_cons_self, reached, notGenesis, unknown, rfl⟩
        · split at failed
          · cases failed
          · obtain ⟨block, mem, rest⟩ := step failed
            exact ⟨block, List.mem_cons_of_mem _ mem, rest⟩
    · obtain ⟨block, mem, rest⟩ := step failed
      exact ⟨block, List.mem_cons_of_mem _ mem, rest⟩

/-- A configured terminal block hash names the block of the chain with that hash, if any. -/
theorem getTerminalPowBlock_of_ne {powChain : List PowBlock}
    (configured : config.TERMINAL_BLOCK_HASH ≠ EMPTY_BLOCK_HASH) :
    getTerminalPowBlock config powChain =
      .ok (findPowBlock powChain config.TERMINAL_BLOCK_HASH) := by
  simp [getTerminalPowBlock, configured]

/-- The block of a chain with a hash has that hash, and is in the chain. -/
theorem findPowBlock_eq_some {powChain : List PowBlock} {hash : Hash32} {block : PowBlock}
    (found : findPowBlock powChain hash = some block) :
    block ∈ powChain ∧ block.blockHash = hash := by
  unfold findPowBlock at found
  exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

/-- In a chain whose hashes differ, a block of the chain is the block with its hash. -/
theorem findPowBlock_of_mem {powChain : List PowBlock} {block : PowBlock}
    (distinct : (powChain.map (·.blockHash)).Nodup) (mem : block ∈ powChain) :
    findPowBlock powChain block.blockHash = some block := by
  unfold findPowBlock
  induction powChain with
  | nil => simp at mem
  | cons head tail step =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at distinct
    rcases List.mem_cons.mp mem with rfl | later
    · simp
    · have other : head.blockHash ≠ block.blockHash := fun same => distinct.1 block later same.symm
      simp [other, step distinct.2 later]

/-! ## The forkchoice update -/

/-- Once the merge is complete, and always from Capella, the head is the latest payload hash. -/
theorem payloadHeadBlockHash_of_merged {state : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {powChain : List PowBlock}
    (merged : .shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true) :
    payloadHeadBlockHash config state bellatrix powChain =
      .ok (some (state.latestExecutionPayloadHeader bellatrix).blockHash) := by
  simp [payloadHeadBlockHash, merged]

/-- Before the merge, a configured terminal block hash that is not yet active asks for nothing. -/
theorem payloadHeadBlockHash_of_inactive {state : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {powChain : List PowBlock}
    (premerge : ¬ (.shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true))
    (configured : config.TERMINAL_BLOCK_HASH ≠ EMPTY_BLOCK_HASH)
    (early : getCurrentEpoch state < config.TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH) :
    payloadHeadBlockHash config state bellatrix powChain = .ok none := by
  simp [payloadHeadBlockHash, premerge, configured, early]

/-- Otherwise, before the merge, the head is the hash of the terminal block of proof of work. -/
theorem payloadHeadBlockHash_of_premerge {state : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {powChain : List PowBlock}
    (premerge : ¬ (.shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true))
    (active : ¬ (config.TERMINAL_BLOCK_HASH ≠ EMPTY_BLOCK_HASH ∧
      getCurrentEpoch state < config.TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH)) :
    payloadHeadBlockHash config state bellatrix powChain =
      (getTerminalPowBlock config powChain).map (·.map (·.blockHash)) := by
  simp only [payloadHeadBlockHash, premerge, active, ↓reduceIte]

/-- The withdrawals of the attributes are those the state expects, from Capella. -/
theorem payloadAttributesWithdrawals_spec {state : BeaconState preset fork}
    {withdrawals : Since .shapella fork (List Execution.Blocks.Withdrawal)}
    (computed : payloadAttributesWithdrawals state = .ok withdrawals) (capella : .shapella ≤ fork) :
    ∃ expected, getExpectedWithdrawals state capella = .ok expected ∧
      withdrawals capella = expected.withdrawals.toList.map executionWithdrawal := by
  simp only [payloadAttributesWithdrawals, capella, ↓reduceDIte] at computed
  obtain ⟨expected, found, built⟩ := bind_ok_iff.mp computed
  obtain rfl := Except.ok.inj built
  exact ⟨expected, mapError_ok_iff.mp found, rfl⟩

/-- The parent root of the attributes is the root of the latest block header, from Deneb. -/
theorem payloadAttributesParentRoot_spec {state : BeaconState preset fork}
    {root : Since .dencun fork Hash32}
    (computed : payloadAttributesParentRoot state = .ok root) (deneb : .dencun ≤ fork) :
    hashTreeRoot state.latestBlockHeader = .ok (root deneb) := by
  simp only [payloadAttributesParentRoot, deneb, ↓reduceDIte] at computed
  obtain ⟨value, hashed, built⟩ := bind_ok_iff.mp computed
  obtain rfl := Except.ok.inj built
  exact mapError_ok_iff.mp hashed

/-- The forkchoice update of a proposer, from what it is built of.

Its head is the head of its rules, and its safe and finalized blocks are those given.

The timestamp is the time of the slot of the state, and the RANDAO mix is that of its epoch.

The fee recipient is the one given.

From Capella the withdrawals are those the state expects, as the execution layer reads them.

From Deneb the parent root is the root of the latest block header of the state. -/
theorem prepareExecutionPayload_eq_ok_some {state : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {powChain : List PowBlock} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork}
    (prepared :
      prepareExecutionPayload config state bellatrix safe finalized feeRecipient powChain =
        .ok (some (update, attributes))) :
    payloadHeadBlockHash config state bellatrix powChain = .ok (some update.headBlockHash) ∧
      update.safeBlockHash = safe ∧ update.finalizedBlockHash = finalized ∧
      computeTimeAtSlot config state.genesisTime state.slot = .ok attributes.timestamp ∧
      getRandaoMix state (getCurrentEpoch state) = .ok attributes.prevRandao ∧
      attributes.suggestedFeeRecipient = feeRecipient ∧
      (∀ capella : .shapella ≤ fork, ∃ expected,
        getExpectedWithdrawals state capella = .ok expected ∧
        attributes.withdrawals capella = expected.withdrawals.toList.map executionWithdrawal) ∧
      (∀ deneb : .dencun ≤ fork,
        hashTreeRoot state.latestBlockHeader = .ok (attributes.parentBeaconBlockRoot deneb)) := by
  unfold prepareExecutionPayload at prepared
  obtain ⟨head, headed, built⟩ := bind_ok_iff.mp prepared
  cases head with
  | none => simp [pure, Except.pure] at built
  | some head =>
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
      Prod.mk.injEq] at built
    obtain ⟨timestamp, timed, mix, mixed, withdrawals, withdrawn, root, rooted, rfl, rfl⟩ := built
    exact ⟨headed, rfl, rfl, mapError_ok_iff.mp timed, mapError_ok_iff.mp mixed, rfl,
      payloadAttributesWithdrawals_spec withdrawn, payloadAttributesParentRoot_spec rooted⟩

/-- The proposer asks for no update exactly when its rules give no head. -/
theorem prepareExecutionPayload_eq_ok_none_iff {state : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {powChain : List PowBlock} :
    prepareExecutionPayload config state bellatrix safe finalized feeRecipient powChain =
        .ok none ↔
      payloadHeadBlockHash config state bellatrix powChain = .ok none := by
  constructor
  · intro prepared
    obtain ⟨head, headed, built⟩ := bind_ok_iff.mp prepared
    cases head with
    | none => exact headed
    | some head =>
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, reduceCtorEq, and_false,
        exists_false] at built
  · intro headed
    simp [prepareExecutionPayload, headed, bind, Except.bind, pure, Except.pure]

/-! ## The first payload, in the fork choice -/

/-- Before the merge, a block on a configured terminal block hash passes the merge check.

The block must be of the slot of the state, and its payload must name the head as its parent. -/
theorem validateMergeBlock_of_payloadHeadBlockHash_of_configured {state : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {powChain : List PowBlock}
    {head : Hash32} {block : BeaconBlock preset fork} {powBlock : Hash32 → Option PowBlock}
    (configured : config.TERMINAL_BLOCK_HASH ≠ EMPTY_BLOCK_HASH)
    (premerge : ¬ (.shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true))
    (headed : payloadHeadBlockHash config state bellatrix powChain = .ok (some head))
    (slot : block.slot = state.slot)
    (parent : (block.body.executionPayload bellatrix).parentHash = head) :
    validateMergeBlock config powBlock block bellatrix = .ok () := by
  by_cases early : getCurrentEpoch state < config.TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH
  · rw [payloadHeadBlockHash_of_inactive premerge configured early] at headed
    cases headed
  rw [payloadHeadBlockHash_of_premerge premerge (fun both => early both.2),
    getTerminalPowBlock_of_ne configured] at headed
  simp only [Except.map, Except.ok.injEq, Option.map_eq_some_iff] at headed
  obtain ⟨terminal, found, rfl⟩ := headed
  have named := (findPowBlock_eq_some found).2
  unfold validateMergeBlock
  have nonzero : config.TERMINAL_BLOCK_HASH ≠ Vector.replicate 32 0 := configured
  simp only [nonzero, ne_eq, not_false_eq_true, ↓reduceIte, parent, named]
  rw [slot]
  simp [getCurrentEpoch] at early
  simp [UInt64.not_lt.mpr early, pure, Except.pure]

/-- Before the merge, a block on the head of the terminal total difficulty passes the merge check.

The check finds the blocks of proof of work in the chain the proposer read.

The hashes of the chain must differ, and no block may name the zero hash as its parent.

The payload of the block must name the head as its parent. -/
theorem validateMergeBlock_of_payloadHeadBlockHash_of_difficulty {state : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {powChain : List PowBlock}
    {head : Hash32} {block : BeaconBlock preset fork}
    (unset : config.TERMINAL_BLOCK_HASH = EMPTY_BLOCK_HASH)
    (premerge : ¬ (.shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true))
    (headed : payloadHeadBlockHash config state bellatrix powChain = .ok (some head))
    (distinct : (powChain.map (·.blockHash)).Nodup)
    (rooted : ∀ pow ∈ powChain, pow.parentHash ≠ ZERO_HASH)
    (parent : (block.body.executionPayload bellatrix).parentHash = head) :
    validateMergeBlock config (findPowBlock powChain) block bellatrix = .ok () := by
  rw [payloadHeadBlockHash_of_premerge premerge (fun both => both.1 unset)] at headed
  simp only [getTerminalPowBlock, unset, ne_eq, not_true_eq_false, ↓reduceIte,
    getPowBlockAtTerminalTotalDifficulty] at headed
  cases searched : getPowBlockAtTerminalTotalDifficulty.go config powChain powChain with
  | error e => simp [searched, Except.map] at headed
  | ok found =>
    simp only [searched, Except.map, Except.ok.injEq, Option.map_eq_some_iff] at headed
    obtain ⟨terminal, rfl, rfl⟩ := headed
    obtain ⟨mem, -, genesis | ⟨before, known, valid⟩⟩ :=
      getPowBlockAtTerminalTotalDifficulty_go_eq_ok_some searched
    · exact absurd genesis (rooted terminal mem)
    unfold validateMergeBlock
    have zero : ¬ config.TERMINAL_BLOCK_HASH ≠ Vector.replicate 32 0 := fun ne => ne unset
    simp only [zero, ↓reduceIte, parent, findPowBlock_of_mem distinct mem, known, valid,
      pure, Except.pure]

/-! ## The payload, in the transition -/

/-- Two states that agree on what the checks of a payload read of them.

They have one slot, one genesis time, one buffer of RANDAO mixes and one latest payload header.

They also have one latest block header.

From Gloas they have one latest block hash and one latest bid. -/
structure PayloadInputs (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  genesisTime : after.genesisTime = state.genesisTime
  randaoMixes : after.randaoMixes = state.randaoMixes
  latestExecutionPayloadHeader :
    after.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader
  latestBlockHeader : after.latestBlockHeader = state.latestBlockHeader
  latestBlockHash : after.latestBlockHash = state.latestBlockHash
  latestExecutionPayloadBid : after.latestExecutionPayloadBid = state.latestExecutionPayloadBid

theorem PayloadInputs.refl (state : BeaconState preset fork) : PayloadInputs state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PayloadInputs.trans {first second third : BeaconState preset fork}
    (one : PayloadInputs first second) (two : PayloadInputs second third) :
    PayloadInputs first third :=
  ⟨two.slot.trans one.slot, two.genesisTime.trans one.genesisTime,
    two.randaoMixes.trans one.randaoMixes,
    two.latestExecutionPayloadHeader.trans one.latestExecutionPayloadHeader,
    two.latestBlockHeader.trans one.latestBlockHeader,
    two.latestBlockHash.trans one.latestBlockHash,
    two.latestExecutionPayloadBid.trans one.latestExecutionPayloadBid⟩

/-- A withdrawal changes a balance, and none of the inputs of a payload. -/
theorem payloadInputs_applyWithdrawal {state after : BeaconState preset fork}
    {withdrawal : Consensus.Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : PayloadInputs state after := by
  unfold applyWithdrawal at computed
  split at computed
  · obtain ⟨_, _, set⟩ := bind_ok_iff.mp computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, set⟩ := decreaseBalance_ok computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Applying the expected withdrawals changes none of the inputs of a payload. -/
theorem payloadInputs_applyExpectedWithdrawals {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    PayloadInputs state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : PayloadInputs state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM_ok_invariant (PayloadInputs state)
      (fun _ _ _ before ok => before.trans (payloadInputs_applyWithdrawal ok))
      (PayloadInputs.refl state) appliedOk
  have two : PayloadInputs applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · obtain ⟨_, _, built⟩ := bind_ok_iff.mp indexedOk
      cases built
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases indexedOk
      exact PayloadInputs.refl _
  have three : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → PayloadInputs kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact PayloadInputs.refl _
      · obtain ⟨_, _, built⟩ := bind_ok_iff.mp ok
        cases built
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases ok
      exact PayloadInputs.refl _
  have queued : PayloadInputs indexed (if electra : .pectra ≤ fork then
      updatePendingPartialWithdrawals (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) electra expected.processedPartialWithdrawalsCount
    else if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) := by
    split <;> split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have four : PayloadInputs finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    obtain ⟨_, _, last⟩ := bind_ok_iff.mp last
    dsimp only at last
    split at last
    · cases last
    · cases last
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact one.trans (two.trans (queued.trans ((three _ sweptOk).trans four)))

/-- The withdrawal step changes none of the inputs of a payload. -/
theorem payloadInputs_processWithdrawals {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (Consensus.ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    PayloadInputs state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp computed
      exact payloadInputs_applyExpectedWithdrawals (liftAccessor_ok.mp applied)
    · cases computed
      exact PayloadInputs.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact payloadInputs_applyExpectedWithdrawals applied

/-- The header step changes only the latest block header. -/
theorem payloadInputs_processBlockHeader {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (computed : processBlockHeader state block = .ok after) :
    after.slot = state.slot ∧ after.genesisTime = state.genesisTime ∧
      after.randaoMixes = state.randaoMixes ∧
      after.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A payload on the update of a proposer passes the checks of its parent, mix and time.

The state that checks it must agree with the state of the proposer on what those checks read.

That is the slot, the genesis time, the RANDAO mixes and the latest payload header.

The payload must name the head of the update as its parent.

It must also carry the mix and the timestamp of the attributes.

Its processing then fails only on the number of blobs, the execution layer, or a hash. -/
theorem processExecutionPayload_eq_error_of_prepareExecutionPayload
    {state checked : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {powChain : List PowBlock} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork} {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {error : TransitionError}
    (prepared :
      prepareExecutionPayload config state bellatrix safe finalized feeRecipient powChain =
        .ok (some (update, attributes)))
    (slot : checked.slot = state.slot) (genesisTime : checked.genesisTime = state.genesisTime)
    (randaoMixes : checked.randaoMixes = state.randaoMixes)
    (latest : checked.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader)
    (parent : (body.executionPayload bellatrix).parentHash = update.headBlockHash)
    (randao : (body.executionPayload bellatrix).prevRandao = attributes.prevRandao)
    (time : (body.executionPayload bellatrix).timestamp = attributes.timestamp)
    (failed : processExecutionPayload config engine checked body bellatrix = .error error) :
    error = .tooManyBlobCommitments ∨ error = .invalidExecutionPayload ∨
      ∃ fault, error = .ssz fault := by
  obtain ⟨headed, -, -, timed, mixed, -⟩ := prepareExecutionPayload_eq_ok_some prepared
  unfold processExecutionPayload at failed
  dsimp only at failed
  -- The parent check reads the latest payload header, which the two states share.
  have parentOk : (.shapella ≤ fork ∨ isMergeTransitionComplete checked bellatrix = true) →
      (body.executionPayload bellatrix).parentHash =
        (checked.latestExecutionPayloadHeader bellatrix).blockHash := by
    intro merged
    simp only [isMergeTransitionComplete, latest] at merged ⊢
    rw [payloadHeadBlockHash_of_merged merged, Except.ok.injEq, Option.some.injEq] at headed
    rw [parent, headed]
  rcases bind_eq_error failed with checkFailed | ⟨_, -, failed⟩
  · rw [(ensure_ok_iff (u := ())).mpr parentOk] at checkFailed
    cases checkFailed
  -- The mix and the time read the same fields of the two states.
  have mixOk : getRandaoMix checked (getCurrentEpoch checked) = .ok attributes.prevRandao := by
    simpa [getRandaoMix, getCurrentEpoch, slot, randaoMixes] using mixed
  have timeOk : computeTimeAtSlot config checked.genesisTime checked.slot =
      .ok attributes.timestamp := by
    rw [slot, genesisTime]
    exact timed
  rcases bind_eq_error failed with mixFailed | ⟨mix, mixRead, failed⟩
  · simp [liftAccessor, mixOk, Except.mapError] at mixFailed
  rw [liftAccessor_ok, mixOk, Except.ok.injEq] at mixRead
  subst mixRead
  rcases bind_eq_error failed with checkFailed | ⟨_, -, failed⟩
  · rw [(ensure_ok_iff (u := ())).mpr randao] at checkFailed
    cases checkFailed
  rcases bind_eq_error failed with timeFailed | ⟨slotTime, timeRead, failed⟩
  · simp [liftAccessor, liftArith, timeOk, Except.mapError] at timeFailed
  simp only [liftAccessor, liftArith, timeOk, Except.mapError, Except.ok.injEq] at timeRead
  subst timeRead
  rcases bind_eq_error failed with checkFailed | ⟨_, -, failed⟩
  · rw [(ensure_ok_iff (u := ())).mpr time] at checkFailed
    cases checkFailed
  -- The steps that remain fail only with errors of their own.
  rcases bind_eq_error failed with checkFailed | ⟨_, -, failed⟩
  · exact .inl (eq_of_ensure_eq_error checkFailed)
  rcases bind_eq_error failed with verifyFailed | ⟨_, -, failed⟩
  · cases verified : engine.verifyAndNotifyNewPayload (body.newPayloadRequest checked bellatrix) <;>
      simp [verified, liftSsz, Except.mapError] at verifyFailed
    exact .inr (.inr ⟨_, verifyFailed.symm⟩)
  rcases bind_eq_error failed with checkFailed | ⟨_, -, failed⟩
  · exact .inr (.inl (eq_of_ensure_eq_error checkFailed))
  rcases bind_eq_error failed with headerFailed | ⟨_, -, failed⟩
  · cases built : (body.executionPayload bellatrix).header <;>
      simp [built, liftSsz, Except.mapError] at headerFailed
    exact .inr (.inr ⟨_, headerFailed.symm⟩)
  · simp [pure, Except.pure] at failed

/-- The execution layer reads a withdrawal of the beacon chain field by field. -/
theorem executionWithdrawal_injective : Function.Injective executionWithdrawal := by
  intro one two same
  cases one
  cases two
  simp only [executionWithdrawal, Execution.Blocks.Withdrawal.mk.injEq] at same
  obtain ⟨rfl, rfl, rfl, rfl⟩ := same
  rfl

/-- From Capella, a payload with the withdrawals of the attributes passes the withdrawal check.

The step runs after the header of the block, on the state of the proposer.

Before Gloas the payload carries the withdrawals.

The execution layer must read them as the withdrawals of the attributes.

The step then fails only with an accessor error, when it applies them. -/
theorem processWithdrawals_eq_error_of_prepareExecutionPayload
    {state header : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {powChain : List PowBlock} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork} {block : BeaconBlock preset fork}
    {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (Consensus.ExecutionPayload preset fork)}
    {error : TransitionError}
    (prepared :
      prepareExecutionPayload config state bellatrix safe finalized feeRecipient powChain =
        .ok (some (update, attributes)))
    (headed : processBlockHeader state block = .ok header)
    (carried : ((payload bellatrix.2).withdrawals capella).data.toList.map executionWithdrawal =
      attributes.withdrawals capella)
    (failed : processWithdrawals header capella payload = .error error) :
    ∃ fault, error = .accessor fault := by
  obtain ⟨-, -, -, -, -, -, withdrawn, -⟩ := prepareExecutionPayload_eq_ok_some prepared
  obtain ⟨expected, found, same⟩ := withdrawn capella
  obtain ⟨_, _, stored⟩ := processBlockHeader_eq headed
  -- The header step does not touch what the expected withdrawals read.
  have foundAfter : getExpectedWithdrawals header capella = .ok expected := by
    rw [stored, getExpectedWithdrawals_latestBlockHeader]
    exact found
  rw [same] at carried
  have equal : ((payload bellatrix.2).withdrawals capella).data = expected.withdrawals :=
    Array.toList_inj.mp
      ((List.map_inj_right fun _ _ => (executionWithdrawal_injective ·)).mp carried)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt bellatrix.2
  simp only [processWithdrawals, notGloas, ↓reduceDIte] at failed
  rcases bind_eq_error failed with expectFailed | ⟨found', foundRead, failed⟩
  · rw [foundAfter] at expectFailed
    cases expectFailed
  rw [foundAfter, Except.ok.injEq] at foundRead
  subst foundRead
  rcases bind_eq_error failed with checkFailed | ⟨_, -, failed⟩
  · rw [(ensure_ok_iff (u := ())).mpr equal] at checkFailed
    cases checkFailed
  cases applied : applyExpectedWithdrawals header capella expected <;>
    simp [applied, liftAccessor, Except.mapError] at failed
  exact ⟨_, failed.symm⟩

/-- From Deneb, the payload request of the block names the parent root of the attributes.

The block passes the header step on the state of the proposer.

The state of the request keeps the latest block header of that step. -/
theorem parentBeaconBlockRoot_newPayloadRequest_of_prepareExecutionPayload
    {state header checked : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {powChain : List PowBlock} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork} {block : BeaconBlock preset fork}
    (prepared :
      prepareExecutionPayload config state bellatrix safe finalized feeRecipient powChain =
        .ok (some (update, attributes)))
    (headed : processBlockHeader state block = .ok header)
    (kept : checked.latestBlockHeader = header.latestBlockHeader) (deneb : .dencun ≤ fork) :
    (block.body.newPayloadRequest checked bellatrix).parentBeaconBlockRoot deneb =
      attributes.parentBeaconBlockRoot deneb := by
  obtain ⟨-, -, -, -, -, -, -, rooted⟩ := prepareExecutionPayload_eq_ok_some prepared
  obtain ⟨-, -, -, parentRoot, -⟩ := processBlockHeader_checks headed
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
  have same := (rooted deneb).symm.trans parentRoot
  simp only [Except.ok.injEq] at same
  simp only [BeaconBlockBody.newPayloadRequest, kept]
  exact same.symm

/-- A block whose payload follows the update of its proposer passes the payload checks.

The block passes the header step on the state of the proposer.

Its payload names the head of the update as its parent.

It carries the mix and the timestamp of the attributes.

From Capella the execution layer reads its withdrawals as those of the attributes.

Its execution part then fails only on the blob count, the execution layer, a hash or an accessor.
-/
theorem processBlockExecution_eq_error_of_prepareExecutionPayload
    {state header : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {powChain : List PowBlock} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {error : TransitionError}
    (prepared :
      prepareExecutionPayload config state bellatrix safe finalized feeRecipient powChain =
        .ok (some (update, attributes)))
    (headed : processBlockHeader state block = .ok header)
    (parent : (block.body.executionPayload bellatrix).parentHash = update.headBlockHash)
    (randao : (block.body.executionPayload bellatrix).prevRandao = attributes.prevRandao)
    (time : (block.body.executionPayload bellatrix).timestamp = attributes.timestamp)
    (carried : ∀ capella : .shapella ≤ fork,
      ((block.body.executionPayload bellatrix).withdrawals capella).data.toList.map
        executionWithdrawal = attributes.withdrawals capella)
    (failed : processBlockExecution config checks engine header block.body bellatrix.1 =
      .error error) :
    error = .tooManyBlobCommitments ∨ error = .invalidExecutionPayload ∨
      (∃ fault, error = .ssz fault) ∨ ∃ fault, error = .accessor fault := by
  obtain ⟨slot, genesisTime, randaoMixes, latest⟩ := payloadInputs_processBlockHeader headed
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt bellatrix.2
  unfold processBlockExecution at failed
  simp only [notGloas, ↓reduceDIte] at failed
  split at failed
  · rename_i capella
    rcases bind_eq_error failed with withdrawFailed | ⟨withdrawn, withdrawOk, failed⟩
    · obtain ⟨fault, rfl⟩ := processWithdrawals_eq_error_of_prepareExecutionPayload prepared headed
        (carried capella) withdrawFailed
      exact .inr (.inr (.inr ⟨fault, rfl⟩))
    have kept := payloadInputs_processWithdrawals withdrawOk
    rcases processExecutionPayload_eq_error_of_prepareExecutionPayload prepared
        (kept.slot.trans slot) (kept.genesisTime.trans genesisTime)
        (kept.randaoMixes.trans randaoMixes)
        (kept.latestExecutionPayloadHeader.trans latest) parent randao time failed with
      blobs | invalid | hashed
    · exact .inl blobs
    · exact .inr (.inl invalid)
    · exact .inr (.inr (.inl hashed))
  · split at failed
    · rcases processExecutionPayload_eq_error_of_prepareExecutionPayload prepared slot genesisTime
          randaoMixes latest parent randao time failed with blobs | invalid | hashed
      · exact .inl blobs
      · exact .inr (.inl invalid)
      · exact .inr (.inr (.inl hashed))
    · cases failed

/-! ## From Gloas -/

section Gloas

variable {checks : SignatureChecks} {store : Store preset fork} {head : ForkChoiceNode}
  {state base : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}

/-- The parent on which a proposer builds, as the fork choice decides at the current slot.

On the full node, the head is the hash of the latest bid.

The state is then the state after the payload that the store holds for the block of the head.

The withdrawals are those that this state expects.

On the empty node, the head is the parent hash of the latest bid.

The state then stays, with the withdrawals that it records. -/
theorem payloadParentGloas_eq_ok {withdrawals : Array Consensus.Withdrawal} {headBlockHash : Hash32}
    (computed : payloadParentGloas config checks store head state gloas =
      .ok (base, withdrawals, headBlockHash)) :
    ∃ slot, store.getCurrentSlot config = .ok slot ∧
      ((store.shouldBuildOnFull gloas head slot = .ok true ∧
        headBlockHash = (state.latestExecutionPayloadBid gloas).blockHash ∧
        ∃ envelope, (store.payloads gloas)[head.root]? = some envelope ∧
          applyParentExecutionPayload config checks state gloas envelope.executionRequests =
            .ok base ∧
          ∃ expected, getExpectedWithdrawals base (Nat.le_trans (by decide) gloas) = .ok expected ∧
            withdrawals = expected.withdrawals) ∨
       (store.shouldBuildOnFull gloas head slot = .ok false ∧
        headBlockHash = (state.latestExecutionPayloadBid gloas).parentBlockHash ∧ base = state ∧
        withdrawals = (state.payloadExpectedWithdrawals gloas).data)) := by
  unfold payloadParentGloas at computed
  obtain ⟨slot, slotted, computed⟩ := bind_ok_iff.mp computed
  obtain ⟨full, chosen, computed⟩ := bind_ok_iff.mp computed
  refine ⟨slot, mapError_ok_iff.mp slotted, ?_⟩
  cases full with
  | true =>
    simp only [↓reduceIte] at computed
    split at computed
    · rename_i envelope found
      obtain ⟨applied, appliedOk, computed⟩ := bind_ok_iff.mp computed
      obtain ⟨expected, expectedOk, computed⟩ := bind_ok_iff.mp computed
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
      obtain ⟨rfl, rfl, rfl⟩ := computed
      exact .inl ⟨mapError_ok_iff.mp chosen, rfl, envelope, found, mapError_ok_iff.mp appliedOk,
        expected, mapError_ok_iff.mp expectedOk, rfl⟩
    · cases computed
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl, rfl⟩ := computed
    exact .inr ⟨mapError_ok_iff.mp chosen, rfl, rfl, rfl⟩

/-- The forkchoice update of a proposer from Gloas, from what it is built of.

Its head and its withdrawals come from the parent on which the proposer builds, with a state.

Its safe and finalized blocks are those given.

The timestamp is the time of the slot of that state, and the RANDAO mix is that of its epoch.

The fee recipient and the target of the gas limit are those given.

The parent root is the root of the latest block header of that state, and the slot is its slot.

From Heze the transactions are those of the inclusion lists of the slot before, on the head. -/
theorem prepareExecutionPayloadGloas_eq_ok {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {targetGasLimit : UInt64} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork}
    {transactions : Since .hegota fork (List InclusionListTransaction)}
    (prepared : prepareExecutionPayloadGloas config checks store head state gloas safe finalized
      feeRecipient targetGasLimit = .ok (update, attributes, transactions)) :
    ∃ base withdrawals,
      payloadParentGloas config checks store head state gloas =
        .ok (base, withdrawals, update.headBlockHash) ∧
      update.safeBlockHash = safe ∧ update.finalizedBlockHash = finalized ∧
      computeTimeAtSlot config base.genesisTime base.slot = .ok attributes.timestamp ∧
      getRandaoMix base (getCurrentEpoch base) = .ok attributes.prevRandao ∧
      attributes.suggestedFeeRecipient = feeRecipient ∧
      (∀ capella : .shapella ≤ fork,
        attributes.withdrawals capella = withdrawals.toList.map executionWithdrawal) ∧
      (∀ deneb : .dencun ≤ fork,
        hashTreeRoot base.latestBlockHeader = .ok (attributes.parentBeaconBlockRoot deneb)) ∧
      attributes.slotNumber gloas = base.slot ∧ attributes.targetGasLimit gloas = targetGasLimit ∧
      (∀ heze : .hegota ≤ fork,
        getPayloadInclusionListTransactions store heze base head.root =
          .ok (transactions heze)) := by
  unfold prepareExecutionPayloadGloas at prepared
  obtain ⟨⟨base, withdrawals, headBlockHash⟩, parented, built⟩ := bind_ok_iff.mp prepared
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at built
  obtain ⟨timestamp, timed, mix, mixed, root, rooted, lists, listed, rfl, rfl, rfl⟩ := built
  refine ⟨base, withdrawals, parented, rfl, rfl, mapError_ok_iff.mp timed,
    mapError_ok_iff.mp mixed, rfl, fun _ => rfl, fun _ => mapError_ok_iff.mp rooted, rfl, rfl,
    fun heze => ?_⟩
  simp only [payloadInclusionListTransactions, heze, ↓reduceDIte] at listed
  obtain ⟨found, foundOk, built⟩ := bind_ok_iff.mp listed
  obtain rfl := Except.ok.inj built
  exact mapError_ok_iff.mp foundOk

/-- A block on the update of its proposer leaves the parent step with the state of the attributes.

Its bid builds on the head of the update.

From a full parent it carries the requests of the payload that the store holds.

The hashes of the latest bid differ. -/
private theorem processParentExecutionPayload_of_payloadParentGloas
    {withdrawals : Array Consensus.Withdrawal} {headBlockHash : Hash32}
    {body : BeaconBlockBody preset fork} {after : BeaconState preset fork}
    (parented : payloadParentGloas config checks store head state gloas =
      .ok (base, withdrawals, headBlockHash))
    (distinct : (state.latestExecutionPayloadBid gloas).blockHash ≠
      (state.latestExecutionPayloadBid gloas).parentBlockHash)
    (parentHash : (body.signedExecutionPayloadBid gloas).message.parentBlockHash = headBlockHash)
    (requests : ∀ envelope, (store.payloads gloas)[head.root]? = some envelope →
      body.parentExecutionRequests gloas = envelope.executionRequests)
    (parent : processParentExecutionPayload config checks state gloas body = .ok after) :
    after = base := by
  obtain ⟨_, _, ⟨_, rfl, envelope, found, applied, _⟩ | ⟨_, rfl, rfl, _⟩⟩ :=
    payloadParentGloas_eq_ok parented
  · simp only [processParentExecutionPayload, parentHash, ne_eq, not_true_eq_false,
      ↓reduceIte, bind_ok_iff, ensure_ok_iff, requests envelope found] at parent
    obtain ⟨_, _, _, _, appliedAgain⟩ := parent
    rw [applied, Except.ok.injEq] at appliedAgain
    exact appliedAgain.symm
  · simp only [processParentExecutionPayload, parentHash, Ne.symm distinct, ne_eq,
      not_false_eq_true,
      ↓reduceIte, bind_ok_iff, ensure_ok_iff, pure, Except.pure, Except.ok.injEq] at parent
    obtain ⟨_, _, rfl⟩ := parent
    rfl

/-- After the parent, header and withdrawal steps of such a block, the state matches the update.

Its latest block hash is the head, and it records the withdrawals of the attributes.

The empty case needs the latest block hash to be the parent hash of the latest bid. -/
private theorem withdrawals_of_prepareExecutionPayloadGloas
    {withdrawals : Array Consensus.Withdrawal} {headBlockHash : Hash32}
    {block : BeaconBlock preset fork} {parented header after : BeaconState preset fork}
    {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (Consensus.ExecutionPayload preset fork)}
    (computed : payloadParentGloas config checks store head state gloas =
      .ok (base, withdrawals, headBlockHash))
    (distinct : (state.latestExecutionPayloadBid gloas).blockHash ≠
      (state.latestExecutionPayloadBid gloas).parentBlockHash)
    (linked : state.latestBlockHash gloas = (state.latestExecutionPayloadBid gloas).parentBlockHash)
    (parentHash :
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = headBlockHash)
    (requests : ∀ envelope, (store.payloads gloas)[head.root]? = some envelope →
      block.body.parentExecutionRequests gloas = envelope.executionRequests)
    (parent : processParentExecutionPayload config checks state gloas block.body = .ok parented)
    (headed : processBlockHeader parented block = .ok header)
    (withdrawn : processWithdrawals header capella payload = .ok after) :
    after.latestBlockHash gloas = headBlockHash ∧
      (after.payloadExpectedWithdrawals gloas).data = withdrawals := by
  obtain rfl := processParentExecutionPayload_of_payloadParentGloas computed distinct parentHash
    requests parent
  obtain ⟨_, _, stored⟩ := processBlockHeader_eq headed
  have kept := payloadInputs_processWithdrawals withdrawn
  have hashKept : header.latestBlockHash = parented.latestBlockHash := by rw [stored]
  have bidKept : header.latestExecutionPayloadBid = parented.latestExecutionPayloadBid := by
    rw [stored]
  obtain ⟨_, _, ⟨_, rfl, envelope, _, applied, expected, found, rfl⟩ | ⟨_, rfl, rfl, rfl⟩⟩ :=
    payloadParentGloas_eq_ok computed
  · have hash := applyParentExecutionPayload_latestBlockHash applied
    have bid := applyParentExecutionPayload_latestExecutionPayloadBid applied
    have full : isParentBlockFull header gloas = true := by
      simp only [isParentBlockFull, hashKept, bidKept, hash, bid, beq_self_eq_true]
    obtain ⟨recorded, recordedOk, _, recordedData⟩ :=
      processWithdrawals_recorded gloas full withdrawn
    rw [stored, getExpectedWithdrawals_latestBlockHeader, found, Except.ok.injEq] at recordedOk
    subst recordedOk
    exact ⟨(congrFun kept.latestBlockHash gloas).trans ((congrFun hashKept gloas).trans hash),
      recordedData⟩
  · have empty : isParentBlockFull header gloas = false := by
      simp only [isParentBlockFull, hashKept, bidKept, linked, beq_eq_false_iff_ne, ne_eq]
      exact fun same => distinct same.symm
    rw [processWithdrawals_of_parentEmpty payload gloas empty, Except.ok.injEq] at withdrawn
    subst withdrawn
    refine ⟨(congrFun hashKept gloas).trans linked, ?_⟩
    rw [stored]

/-- A block that follows the update of its proposer leaves the head as the latest block hash.

The hash is that of the state after the parent, header and withdrawal steps of the block.

The block builds its bid on the head.

From a full parent it carries the requests of the payload that the store holds.

The hashes of the latest bid differ, and the latest block hash is the parent hash of that bid. -/
theorem latestBlockHash_of_prepareExecutionPayloadGloas {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {targetGasLimit : UInt64} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork}
    {transactions : Since .hegota fork (List InclusionListTransaction)}
    {block : BeaconBlock preset fork} {parented header after : BeaconState preset fork}
    {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (Consensus.ExecutionPayload preset fork)}
    (prepared : prepareExecutionPayloadGloas config checks store head state gloas safe finalized
      feeRecipient targetGasLimit = .ok (update, attributes, transactions))
    (distinct : (state.latestExecutionPayloadBid gloas).blockHash ≠
      (state.latestExecutionPayloadBid gloas).parentBlockHash)
    (linked : state.latestBlockHash gloas = (state.latestExecutionPayloadBid gloas).parentBlockHash)
    (parentHash :
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = update.headBlockHash)
    (requests : ∀ envelope, (store.payloads gloas)[head.root]? = some envelope →
      block.body.parentExecutionRequests gloas = envelope.executionRequests)
    (parent : processParentExecutionPayload config checks state gloas block.body = .ok parented)
    (headed : processBlockHeader parented block = .ok header)
    (withdrawn : processWithdrawals header capella payload = .ok after) :
    after.latestBlockHash gloas = update.headBlockHash := by
  obtain ⟨_, _, computed, -⟩ := prepareExecutionPayloadGloas_eq_ok prepared
  exact (withdrawals_of_prepareExecutionPayloadGloas computed distinct linked parentHash requests
    parent headed withdrawn).1

/-- Such a block records the withdrawals of the attributes, as the execution layer reads them.

They are recorded in the state after its parent, header and withdrawal steps.

The block builds its bid on the head.

From a full parent it carries the requests of the payload that the store holds.

The hashes of the latest bid differ, and the latest block hash is the parent hash of that bid. -/
theorem payloadExpectedWithdrawals_of_prepareExecutionPayloadGloas {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {targetGasLimit : UInt64} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork}
    {transactions : Since .hegota fork (List InclusionListTransaction)}
    {block : BeaconBlock preset fork} {parented header after : BeaconState preset fork}
    {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (Consensus.ExecutionPayload preset fork)}
    (prepared : prepareExecutionPayloadGloas config checks store head state gloas safe finalized
      feeRecipient targetGasLimit = .ok (update, attributes, transactions))
    (distinct : (state.latestExecutionPayloadBid gloas).blockHash ≠
      (state.latestExecutionPayloadBid gloas).parentBlockHash)
    (linked : state.latestBlockHash gloas = (state.latestExecutionPayloadBid gloas).parentBlockHash)
    (parentHash :
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = update.headBlockHash)
    (requests : ∀ envelope, (store.payloads gloas)[head.root]? = some envelope →
      block.body.parentExecutionRequests gloas = envelope.executionRequests)
    (parent : processParentExecutionPayload config checks state gloas block.body = .ok parented)
    (headed : processBlockHeader parented block = .ok header)
    (withdrawn : processWithdrawals header capella payload = .ok after) :
    (after.payloadExpectedWithdrawals gloas).data.toList.map executionWithdrawal =
      attributes.withdrawals capella := by
  obtain ⟨_, _, computed, -, -, -, -, -, carried, -⟩ := prepareExecutionPayloadGloas_eq_ok prepared
  rw [carried, (withdrawals_of_prepareExecutionPayloadGloas computed distinct linked parentHash
    requests parent headed withdrawn).2]

/-- Such a block meets the time, the mix and the slot of the attributes in the state it reaches.

That state is the one after its parent, header and withdrawal steps.

The block builds its bid on the head.

From a full parent it carries the requests of the payload that the store holds.

The hashes of the latest bid differ. -/
theorem slot_of_prepareExecutionPayloadGloas {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {targetGasLimit : UInt64} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork}
    {transactions : Since .hegota fork (List InclusionListTransaction)}
    {block : BeaconBlock preset fork} {parented header after : BeaconState preset fork}
    {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (Consensus.ExecutionPayload preset fork)}
    (prepared : prepareExecutionPayloadGloas config checks store head state gloas safe finalized
      feeRecipient targetGasLimit = .ok (update, attributes, transactions))
    (distinct : (state.latestExecutionPayloadBid gloas).blockHash ≠
      (state.latestExecutionPayloadBid gloas).parentBlockHash)
    (parentHash :
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = update.headBlockHash)
    (requests : ∀ envelope, (store.payloads gloas)[head.root]? = some envelope →
      block.body.parentExecutionRequests gloas = envelope.executionRequests)
    (parent : processParentExecutionPayload config checks state gloas block.body = .ok parented)
    (headed : processBlockHeader parented block = .ok header)
    (withdrawn : processWithdrawals header capella payload = .ok after) :
    attributes.slotNumber gloas = after.slot ∧
      computeTimeAtSlot config after.genesisTime after.slot = .ok attributes.timestamp ∧
      getRandaoMix after (getCurrentEpoch after) = .ok attributes.prevRandao := by
  obtain ⟨_, _, computed, -, -, timed, mixed, -, -, -, slotted, -⟩ :=
    prepareExecutionPayloadGloas_eq_ok prepared
  obtain rfl := processParentExecutionPayload_of_payloadParentGloas computed distinct parentHash
    requests parent
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
  have kept := payloadInputs_processWithdrawals withdrawn
  refine ⟨by rw [slotted, kept.slot], by rw [kept.slot, kept.genesisTime]; exact timed, ?_⟩
  simpa [getRandaoMix, getCurrentEpoch, kept.slot, kept.randaoMixes] using mixed

/-- Such a block names the parent root of the attributes as its parent.

It passes the parent and header steps.

The block builds its bid on the head.

From a full parent it carries the requests of the payload that the store holds.

The hashes of the latest bid differ. -/
theorem parentRoot_of_prepareExecutionPayloadGloas {safe finalized : Hash32}
    {feeRecipient : ExecutionAddress} {targetGasLimit : UInt64} {update : ForkchoiceState}
    {attributes : PayloadAttributes fork}
    {transactions : Since .hegota fork (List InclusionListTransaction)}
    {block : BeaconBlock preset fork} {parented header : BeaconState preset fork}
    (prepared : prepareExecutionPayloadGloas config checks store head state gloas safe finalized
      feeRecipient targetGasLimit = .ok (update, attributes, transactions))
    (distinct : (state.latestExecutionPayloadBid gloas).blockHash ≠
      (state.latestExecutionPayloadBid gloas).parentBlockHash)
    (parentHash :
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = update.headBlockHash)
    (requests : ∀ envelope, (store.payloads gloas)[head.root]? = some envelope →
      block.body.parentExecutionRequests gloas = envelope.executionRequests)
    (parent : processParentExecutionPayload config checks state gloas block.body = .ok parented)
    (headed : processBlockHeader parented block = .ok header) (deneb : .dencun ≤ fork) :
    block.parentRoot = attributes.parentBeaconBlockRoot deneb := by
  obtain ⟨_, _, computed, -, -, -, -, -, -, rooted, -⟩ :=
    prepareExecutionPayloadGloas_eq_ok prepared
  obtain rfl := processParentExecutionPayload_of_payloadParentGloas computed distinct parentHash
    requests parent
  obtain ⟨-, -, -, parentRoot, -⟩ := processBlockHeader_checks headed
  have same := (rooted deneb).symm.trans parentRoot
  simp only [Except.ok.injEq] at same
  exact same.symm

end Gloas

end EthLib.Engine
