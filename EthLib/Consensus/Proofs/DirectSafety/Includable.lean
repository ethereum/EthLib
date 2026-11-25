module

public import EthLib.Consensus.Proofs.DirectSafety.Signatures
public import EthLib.Consensus.Proofs.Transition.AttesterSlashingAccepted
public import EthLib.Consensus.Proofs.Transition.Totality.ChainBlock
import EthLib.Consensus.Proofs.Transition.BlockLedger
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.ActivationExitOrder
import EthLib.Consensus.Proofs.Transition.Chain
import EthLib.Consensus.Proofs.Transition.ForkVersions
import EthLib.Consensus.Proofs.Transition.Totality.FlagsActive
import EthLib.Consensus.Proofs.Transition.Totality.SlashValidator
import EthLib.Consensus.Proofs.Transition.ValidatorKeys

/-!
# Includable slashings of the keys of signed direct safety

Signed direct safety finds keys that signed two conflicting attestation data.

It does not show that a state could slash them.

This module builds that slashing for a key that signed each data alone.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls Serialization.Ssz BlockLedger

variable {preset : Preset} {fork : Fork}

/-- The attester slashing of one validator by two signatures, one on each of two data.

Each attestation names the validator alone.

The preset must allow one attester or more, so that one index fits the list before Gloas. -/
def singleAttesterSlashing (index : ValidatorIndex) (first second : AttestationData)
    (firstSignature secondSignature : BLSSignature) (attesters : 1 ≤ maxAttesters preset fork) :
    AttesterSlashing preset fork :=
  -- An aggregate names all its signers, and its signature cannot drop one.
  --
  -- So an aggregate of one run may not verify against the registry of the other.
  --
  -- So a signature by the key alone on each data is the simplest case that suffices.
  let indices : ForkList .glamsterdam fork ValidatorIndex (maxAttesters preset fork) :=
    ⟨#[index], fun _ => attesters⟩
  ⟨⟨indices, first, firstSignature⟩, ⟨indices, second, secondSignature⟩⟩

/-- A state returns, on the slashing of a key by two signed conflicting data, what slashing returns.

So it accepts exactly when it can slash. -/
theorem processAttesterSlashing_single_eq_slashValidator {config : Config}
    {checks : SignatureChecks} {state : BeaconState preset fork} {genesisRoot : Root}
    {key : BLSPubkey} {first second : AttestationData} {firstFork secondFork : Fork}
    {firstDomain secondDomain : Domain} {firstRoot secondRoot : Root}
    -- The two data are a double or surround vote.
    (conflict : isSlashableAttestationData first second = true)
    -- Each data has the domain and signing root of a signature.
    --
    -- Each domain is that of a fork version and of a genesis validators root.
    (firstDomained : computeDomain config DOMAIN_BEACON_ATTESTER (config.forkVersion firstFork)
      genesisRoot = .ok firstDomain)
    (firstRooted : computeSigningRoot first firstDomain = .ok firstRoot)
    (secondDomained : computeDomain config DOMAIN_BEACON_ATTESTER
      (config.forkVersion secondFork) genesisRoot = .ok secondDomain)
    (secondRooted : computeSigningRoot second secondDomain = .ok secondRoot)
    -- The two signatures are by the key alone, and each verifies on its signing root.
    (firstSignature secondSignature : BLSSignature)
    (firstVerified :
      checks.fastAggregateVerify #[key] (packBytes firstRoot) firstSignature = true)
    (secondVerified :
      checks.fastAggregateVerify #[key] (packBytes secondRoot) secondSignature = true)
    -- The state has the genesis validators root of the signatures.
    (rooted : state.genesisValidatorsRoot = genesisRoot)
    -- The state reads the fork version of each signature at the target epoch of its data.
    --
    -- It checks a signature only under its previous or current fork version.
    (windowFirst : state.forkVersions.versionAt first.target.epoch = config.forkVersion firstFork)
    (windowSecond :
      state.forkVersions.versionAt second.target.epoch = config.forkVersion secondFork)
    {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator) (keyEq : validator.pubkey = key)
    -- The validator of the key is slashable at the epoch of the state.
    --
    -- A withdrawable validator is not, and no slashing touches it.
    (slashable : isSlashableValidator validator (getCurrentEpoch state) = true)
    (attesters : 1 ≤ maxAttesters preset fork) :
    processAttesterSlashing config checks state
        (singleAttesterSlashing index first second firstSignature secondSignature attesters) =
      liftAccessor (slashValidator config state index) := by
  subst keyEq
  -- The state reads each fork version and the genesis root of its signature, so the same domain.
  refine processAttesterSlashing_eq_slashValidator_of_single rfl rfl conflict found slashable
    ⟨firstDomain, firstRoot, ?_, firstRooted, firstVerified⟩
    ⟨secondDomain, secondRoot, ?_, secondRooted, secondVerified⟩ fun _ => attesters
  · simp [singleAttesterSlashing, getDomain, windowFirst, rooted, firstDomained, Except.mapError]
  · simp [singleAttesterSlashing, getDomain, windowSecond, rooted, secondDomained, Except.mapError]

/-- The same, at a state that a run reaches from the genesis of the signatures.

Such a state has that genesis validators root, as each state of the runs does.

So only the fork versions remain to check. -/
theorem processAttesterSlashing_single_eq_slashValidator_run {config : Config}
    {checks : SignatureChecks} {g y : ForkedBeaconState preset} (run : Run config checks g y)
    {key : BLSPubkey} {first second : AttestationData} {firstFork secondFork : Fork}
    {firstDomain secondDomain : Domain} {firstRoot secondRoot : Root}
    (conflict : isSlashableAttestationData first second = true)
    (firstDomained : computeDomain config DOMAIN_BEACON_ATTESTER (config.forkVersion firstFork)
      g.state.genesisValidatorsRoot = .ok firstDomain)
    (firstRooted : computeSigningRoot first firstDomain = .ok firstRoot)
    (secondDomained : computeDomain config DOMAIN_BEACON_ATTESTER
      (config.forkVersion secondFork) g.state.genesisValidatorsRoot = .ok secondDomain)
    (secondRooted : computeSigningRoot second secondDomain = .ok secondRoot)
    (firstSignature secondSignature : BLSSignature)
    (firstVerified :
      checks.fastAggregateVerify #[key] (packBytes firstRoot) firstSignature = true)
    (secondVerified :
      checks.fastAggregateVerify #[key] (packBytes secondRoot) secondSignature = true)
    (windowFirst :
      y.state.forkVersions.versionAt first.target.epoch = config.forkVersion firstFork)
    (windowSecond :
      y.state.forkVersions.versionAt second.target.epoch = config.forkVersion secondFork)
    {index : ValidatorIndex} {validator : Validator}
    (found : getValidator y.state index = .ok validator) (keyEq : validator.pubkey = key)
    (slashable : isSlashableValidator validator (getCurrentEpoch y.state) = true)
    (attesters : 1 ≤ maxAttesters preset y.fork) :
    processAttesterSlashing config checks y.state
        (singleAttesterSlashing index first second firstSignature secondSignature attesters) =
      liftAccessor (slashValidator config y.state index) :=
  processAttesterSlashing_single_eq_slashValidator conflict firstDomained firstRooted
    secondDomained secondRooted firstSignature secondSignature firstVerified secondVerified
    run.genesisValidatorsRoot windowFirst windowSecond found keyEq slashable attesters

/-! ## A slashing in a block of a key activated and not yet withdrawable -/

/-- Two attestation data that the test of slashable votes flags, each with a signing root.

Each root is in the attester domain of a version of the config.

For each data, a state on a run from `g` reads that version at the target epoch of the data. -/
structure VotePairAt (config : Config) (checks : SignatureChecks) (g : ForkedBeaconState preset)
    (d1 d2 : AttestationData) (f1 f2 : Fork) (r1 r2 : Root) (z1 z2 : ForkedBeaconState preset) :
    Prop where
  /-- The two data are a double or surround vote. -/
  conflict : isSlashableAttestationData d1 d2 = true
  /-- The first root is the signing root of the first data, in its attester domain. -/
  root1 : ∃ domain, computeDomain config DOMAIN_BEACON_ATTESTER (config.forkVersion f1)
    g.state.genesisValidatorsRoot = .ok domain ∧ computeSigningRoot d1 domain = .ok r1
  /-- The second root is the signing root of the second data, in its attester domain. -/
  root2 : ∃ domain, computeDomain config DOMAIN_BEACON_ATTESTER (config.forkVersion f2)
    g.state.genesisValidatorsRoot = .ok domain ∧ computeSigningRoot d2 domain = .ok r2
  /-- A run from `g` reaches the first reference state. -/
  run1 : Nonempty (Run config checks g z1)
  /-- The first reference state reads the first version at the target epoch of the first data. -/
  read1 : z1.state.forkVersions.versionAt d1.target.epoch = config.forkVersion f1
  /-- A run from `g` reaches the second reference state. -/
  run2 : Nonempty (Run config checks g z2)
  /-- The second reference state reads the second version at the second data's target epoch. -/
  read2 : z2.state.forkVersions.versionAt d2.target.epoch = config.forkVersion f2

/-- Advancing to a slot still in the epoch of a state keeps its fork and its registry. -/
private theorem validators_advanceSlotsAcross_of_epoch {config : Config}
    {checks : SignatureChecks} :
    ∀ (count : Nat) {x y : ForkedBeaconState preset},
      advanceSlotsAcross config checks count x = .ok y →
      (x.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat =
        (getCurrentEpoch x.state).toNat →
      ∃ last : BeaconState preset x.fork, y = ⟨x.fork, last⟩ ∧
        last.validators = x.state.validators
  | 0, x, y, computed, _ => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    exact ⟨x.state, computed.symm, rfl⟩
  | count + 1, x, y, computed, inside => by
    simp only [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨middle, middleOk, rest⟩ := computed
    have middleSlot := advanceSlotsAcross_slot 1 (by
      simpa [advanceSlotsAcross] using middleOk : advanceSlotsAcross config checks 1 x = .ok middle)
    have xEpoch := getCurrentEpoch_toNat x.state
    have sameEpoch : getCurrentEpoch middle.state = getCurrentEpoch x.state := by
      apply UInt64.toNat_inj.mp
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, middleSlot]
      have upper : (x.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤
          (x.state.slot.toNat + (count + 1)) / preset.SLOTS_PER_EPOCH.toNat :=
        Nat.div_le_div_right (by omega)
      have lower : x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
          (x.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat :=
        Nat.div_le_div_right (by omega)
      omega
    have restInside : (middle.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat =
        (getCurrentEpoch middle.state).toNat := by
      rw [sameEpoch, middleSlot, show x.state.slot.toNat + 1 + count =
        x.state.slot.toNat + (count + 1) by omega]
      exact inside
    obtain ⟨cached, next, cachedOk, rfl⟩ := advanceSlotAcross_of_same_epoch middleOk sameEpoch
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    obtain ⟨last, rfl, same⟩ := validators_advanceSlotsAcross_of_epoch count rest restInside
    exact ⟨last, rfl, same⟩

/-- The registry of the second state is that of the first, aged.

Each old validator keeps its index, its activation epoch and any assigned exit epoch.

Once its exit is set, its withdrawable epoch only rises, and a set slashed flag stays set.

New validators are not activated. -/
private def Ages {fork : Fork} (a b : BeaconState preset fork) : Prop :=
  Lives a b ∧ RegistryLifecycle a b ∧ SlashedPersistence a b

private theorem Ages.trans {fork : Fork} {a b c : BeaconState preset fork} (one : Ages a b)
    (two : Ages b c) : Ages a c :=
  ⟨one.1.trans two.1 one.2.1 two.2.2, one.2.1.trans two.2.1, one.2.2.trans two.2.2⟩

private theorem Ages.of_validators {fork : Fork} {a b : BeaconState preset fork}
    (same : b.validators = a.validators) : Ages a b :=
  ⟨Lives.of_data (congrArg (·.data) same), .of_data (congrArg (·.data) same),
    .of_data (congrArg (·.data) same)⟩

/-- The steps of a block before its operations age the registry. -/
private theorem ages_operationsInput {config : Config} {checks : SignatureChecks} {fork : Fork}
    {engine : ExecutionEngine preset fork} {state input : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input) : Ages state input :=
  started.step_of Ages (fun _ => Ages.of_validators rfl) Ages.trans
    (fun _ paid => ⟨lives_processParentExecutionPayload paid,
      registryLifecycle_processParentExecutionPayload paid,
      .of_frame (frame_processParentExecutionPayload paid).toFrame⟩)
    (fun headed => Ages.of_validators (by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
      rfl))
    (fun _ executed => Ages.of_validators (processBlockExecution_validators executed))
    (fun revealed => Ages.of_validators (by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
      rfl))
    (fun _ voted => Ages.of_validators (by
      obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
      rw [← rest]))

/-- All proposer slashings and the first `j` attester slashings of a block age the registry. -/
private theorem ages_slashings {config : Config} {checks : SignatureChecks} {fork : Fork}
    {block : BeaconBlock preset fork} {j : Nat} {input proposed turn : BeaconState preset fork}
    (proposersOk : block.body.proposerSlashings.data.foldlM (processProposerSlashing config checks)
      input = .ok proposed)
    (attestersOk : (block.body.attesterSlashings.data.toList.take j).foldlM
      (processAttesterSlashing config checks) proposed = .ok turn) :
    Ages input turn := by
  rw [← Array.foldlM_toList] at proposersOk
  have proposedAges : Ages input proposed :=
    foldlM_ok_invariant (Ages input) (fun _ _ _ before ok => before.trans
      ⟨lives_processProposerSlashing ok, registryLifecycle_processProposerSlashing ok,
        .of_frame (frame_processProposerSlashing ok).toFrame⟩)
      (Ages.of_validators rfl) proposersOk
  exact foldlM_ok_invariant (Ages input) (fun _ _ _ before ok => before.trans
      ⟨lives_processAttesterSlashing ok, registryLifecycle_processAttesterSlashing ok,
        .of_frame (frame_processAttesterSlashing ok).toFrame⟩)
      proposedAges attestersOk

/-- The steps of a block before its attester slashing at a position age the registry. -/
private theorem ages_slashingTurn {config : Config} {checks : SignatureChecks} {fork : Fork}
    {engine : ExecutionEngine preset fork} {state turn : BeaconState preset fork}
    {block : BeaconBlock preset fork} {j : Nat}
    (turned : SlashingTurn config checks engine state block j turn) : Ages state turn := by
  obtain ⟨input, proposed, started, proposersOk, attestersOk⟩ := turned
  exact (ages_operationsInput started).trans (ages_slashings proposersOk attestersOk)

/-- Take a validator at position `i` of `x`, activated by the epoch of `x`, with no exit set.

The epoch of `x` is below the far future, and steps of a chain lead from `x` to `y`.

The record at position `i` of `y` is active at the epoch of `x`. -/
private theorem active_of_unexited {config : Config} {checks : SignatureChecks}
    {x y : ForkedBeaconState preset} (steps : Relation.ReflTransGen (ChainStep config checks) x y)
    {i : Nat} {validator : Validator} (found : x.state.validators.data[i]? = some validator)
    (activation : validator.activationEpoch ≤ getCurrentEpoch x.state)
    (far : validator.exitEpoch = FAR_FUTURE_EPOCH)
    (belowFar : getCurrentEpoch x.state < FAR_FUTURE_EPOCH) :
    ∃ record, y.state.validators.data[i]? = some record ∧
      isActiveValidator record (getCurrentEpoch x.state) = true := by
  have active : isActiveValidator validator (getCurrentEpoch x.state) = true := by
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, far]
    exact ⟨activation, belowFar⟩
  have activeKept : isActiveAt y.state (getCurrentEpoch x.state) i = true := by
    rw [activeKept_of_chainSteps steps _ (getCurrentEpoch_le_activityFixedEpoch x.state)]
    exact isActiveAt_eq_true_iff.mpr ⟨validator, found, active⟩
  exact isActiveAt_eq_true_iff.mp activeKept

/-- Take the state before the attester slashing at position `j`, in the epoch of `advanced`.

Its exits must be ordered.

Take the validator at index `i`, active at the epoch of `advanced`, and unslashed at the turn.

It is slashable there. -/
private theorem slashable_of_active {config : Config} {checks : SignatureChecks} {fork : Fork}
    {engine : ExecutionEngine preset fork} {advanced turn : BeaconState preset fork}
    {block : BeaconBlock preset fork} {j : Nat}
    (turned : SlashingTurn config checks engine advanced block j turn)
    (ordered : ExitsOrdered turn) (epochTurn : getCurrentEpoch turn = getCurrentEpoch advanced)
    {i : Nat} {mid : Validator} (midFound : advanced.validators.data[i]? = some mid)
    (active : isActiveValidator mid (getCurrentEpoch advanced) = true)
    {current : Validator} (currentFound : turn.validators.data[i]? = some current)
    (unslashed : current.slashed = false) :
    isSlashableValidator current (getCurrentEpoch turn) = true := by
  obtain ⟨input, started, -, keepsKept, -⟩ := slashingTurn_kept turned
  have stepActive : ActiveStep advanced turn :=
    (activeStep_operationsInput started).trans keepsKept.2
  have activeTurn : isActiveAt turn (getCurrentEpoch advanced) i = true := by
    rw [stepActive.2 _ (getCurrentEpoch_le_activityFixedEpoch advanced)]
    exact isActiveAt_eq_true_iff.mpr ⟨mid, midFound, active⟩
  obtain ⟨current', currentFound', currentActive⟩ := isActiveAt_eq_true_iff.mp activeTurn
  rw [currentFound, Option.some.injEq] at currentFound'
  subst currentFound'
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at currentActive
  -- Its exit is no later than its withdrawable epoch.
  have exitLe := ordered current (Array.mem_of_getElem? currentFound)
  simp only [isSlashableValidator, unslashed, epochTurn, Bool.not_false, Bool.true_and,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨currentActive.1, UInt64.lt_of_lt_of_le currentActive.2 exitLe⟩

/-- A validator of `x`, activated by the epoch of `x`, is slashable at a turn in the next epoch.

This holds for the validator at its position in the turn, if it is unslashed there. -/
private theorem slashable_of_nextEpoch {config : Config} {checks : SignatureChecks}
    -- The state `x` is reached by a run from a genesis of deposits.
    {g x : ForkedBeaconState preset} (shared : Run config checks g x)
    (genesis : Genesis config checks g)
    -- The withdrawal delay must be positive.
    (withdrawableDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    -- The validator at position `i` of `x` is activated by the epoch of `x`.
    {i : Nat} {validator : Validator} (found : x.state.validators.data[i]? = some validator)
    (activation : validator.activationEpoch ≤ getCurrentEpoch x.state)
    {advanced turn : BeaconState preset x.fork}
    {engine : ExecutionEngine preset x.fork} {block : BeaconBlock preset x.fork} {j : Nat}
    -- A run from `x` reaches a state at the fork of `x`, in the epoch after `x`.
    (slots : Run config checks x ⟨x.fork, advanced⟩)
    (next : (getCurrentEpoch advanced).toNat = (getCurrentEpoch x.state).toNat + 1)
    -- If that record at `x` is unslashed, the epoch after `x` is below its withdrawable epoch.
    --
    -- That withdrawable epoch is the one recorded at `x`.
    (withdrawableNext : validator.slashed = false →
      (getCurrentEpoch advanced).toNat < validator.withdrawableEpoch.toNat)
    -- The steps of a block from there reach its turn, at the same epoch, where exits are ordered.
    (turned : SlashingTurn config checks engine advanced block j turn)
    (ordered : ExitsOrdered turn)
    (epochTurn : getCurrentEpoch turn = getCurrentEpoch advanced)
    {current : Validator} (currentFound : turn.validators.data[i]? = some current)
    (unslashed : current.slashed = false) :
    isSlashableValidator current (getCurrentEpoch turn) = true := by
  have aged := ages_slashingTurn turned
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  -- The record at `advanced`, which the slots keep at the same position.
  obtain ⟨mid, midFound, midLife⟩ := slots.registryLifecycle.validators i validator found
  have stays := aged.1.later i mid current midFound currentFound
  -- Unslashed at the turn, the record was unslashed at `x`, since a set flag is never cleared.
  have xUnslashed : validator.slashed = false := by
    cases flag : validator.slashed
    · rfl
    · obtain ⟨w, read, marked⟩ := (slots.slashedPersistence.trans aged.2.2) i validator found flag
      rw [currentFound, Option.some.injEq] at read
      rw [← read, unslashed] at marked
      cases marked
  -- The epoch after `x` is below the withdrawable epoch at `x`, so below the far future.
  have bound := withdrawableNext xUnslashed
  have capped := validator.withdrawableEpoch.toNat_lt
  have activationSet : validator.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro same
    have := UInt64.le_iff_toNat_le.mp activation
    rw [same, farNat] at this
    omega
  have activationTurn : current.activationEpoch = validator.activationEpoch :=
    stays.activation.trans (midLife.activationEpoch activationSet)
  have extended := shared.append slots
  -- It remains that the epoch of the turn is below the withdrawable epoch at the turn.
  have ofLate : (getCurrentEpoch advanced).toNat < current.withdrawableEpoch.toNat →
      isSlashableValidator current (getCurrentEpoch turn) = true := fun late => by
    simp only [isSlashableValidator, unslashed, Bool.not_false, Bool.true_and,
      Bool.and_eq_true, decide_eq_true_eq, epochTurn, activationTurn]
    refine ⟨?_, UInt64.lt_iff_toNat_lt.mpr late⟩
    rw [UInt64.le_iff_toNat_le, next]
    have := UInt64.le_iff_toNat_le.mp activation
    omega
  by_cases far : validator.exitEpoch = FAR_FUTURE_EPOCH
  · -- With no exit at `x`, the record is active at the epoch of `x`, up to `advanced`.
    obtain ⟨mid', midFound', midActive⟩ := active_of_unexited slots.chainSteps found activation
      far (by rw [UInt64.lt_iff_toNat_lt, farNat]; omega)
    rw [midFound, Option.some.injEq] at midFound'
    subst midFound'
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at midActive
    by_cases midFar : mid.exitEpoch = FAR_FUTURE_EPOCH
    · -- Still no exit at `advanced`: active at the epoch of the turn, kept inside the block.
      have midActiveNext : isActiveValidator mid (getCurrentEpoch advanced) = true := by
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, midFar]
        constructor
        · rw [UInt64.le_iff_toNat_le, next]
          have := UInt64.le_iff_toNat_le.mp midActive.1
          omega
        · rw [UInt64.lt_iff_toNat_lt, farNat]
          omega
      exact slashable_of_active turned ordered epochTurn midFound midActiveNext currentFound
        unslashed
    · -- An exit set by `advanced` is after the epoch of `x`, and the delay follows it.
      have delay := extended.exit_withdrawable_delay genesis i mid midFound midFar
      have rises := (stays.withdrawable midFar).1
      have exitAfter := UInt64.lt_iff_toNat_lt.mp midActive.2
      rw [UInt64.le_iff_toNat_le] at rises
      exact ofLate (by omega)
  · -- An exit set at `x` is kept, and its withdrawable epoch is the delay after it.
    have exact := shared.withdrawable_eq_exit_delay genesis i validator found xUnslashed
    have midExit := midLife.exitEpoch far
    have midFar : mid.exitEpoch ≠ FAR_FUTURE_EPOCH := by rw [midExit]; exact far
    have delay := extended.exit_withdrawable_delay genesis i mid midFound midFar
    have rises := (stays.withdrawable midFar).1
    rw [UInt64.le_iff_toNat_le] at rises
    rw [midExit] at delay
    rcases exact with ⟨unset, -⟩ | equal
    · exact absurd unset far
    · exact ofLate (by omega)

/-- At the turn of its slashing, a validator of `x` keeps its key.

The slashing succeeds there, or the validator is already slashed there. -/
private theorem attesterSlashing_accepted_of_lifetime {config : Config} {checks : SignatureChecks}
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    {g x : ForkedBeaconState preset} (shared : Run config checks g x)
    (genesis : Genesis config checks g)
    {start : RunStart} {step : BlockStep} {limits : BlockLimits}
    {budget epochs lastEpoch startEpoch blocks : Nat}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (covers : step.Covers preset limits start budget epochs)
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    (holds : ChainHolds config start step budget startEpoch blocks x.state)
    (within : (getCurrentEpoch x.state).toNat ≤ startEpoch + epochs)
    -- The validator is a validator of `x`, activated and not yet withdrawable at its epoch.
    {i : Nat} {validator : Validator} (found : x.state.validators.data[i]? = some validator)
    (lifetime : validator.activationEpoch ≤ getCurrentEpoch x.state ∧
      getCurrentEpoch x.state < validator.withdrawableEpoch)
    {d1 d2 : AttestationData} {f1 f2 : Fork} {r1 r2 : Root} {z1 z2 : ForkedBeaconState preset}
    (pair : VotePairAt config checks g d1 d2 f1 f2 r1 r2 z1 z2)
    (sameFork1 : z1.fork = x.fork) (sameFork2 : z2.fork = x.fork)
    -- A pair of votes has a signature on each signing root that verifies for its key alone.
    (s1 s2 : BLSSignature)
    (verified1 : checks.fastAggregateVerify #[validator.pubkey] (packBytes r1) s1 = true)
    (verified2 : checks.fastAggregateVerify #[validator.pubkey] (packBytes r2) s2 = true)
    (attesters : 1 ≤ maxAttesters preset x.fork)
    -- The block is applied at `x` at a later slot, at the fork of `x`.
    {engine : ExecutionEngine preset x.fork} {block : BeaconBlock preset x.fork}
    {advanced turn : BeaconState preset x.fork} {j : Nat}
    (advancedOk : advanceSlotsAcross config checks (block.slot.toNat - x.state.slot.toNat) x =
      .ok ⟨x.fork, advanced⟩)
    (later : x.state.slot.toNat < block.slot.toNat)
    -- The block is in the epoch of `x` or in the next epoch.
    (nextAtMost : block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      (getCurrentEpoch x.state).toNat + 1)
    -- In the next epoch, the theorem takes three assumptions.
    (crossing : (getCurrentEpoch x.state).toNat < block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat →
      -- The block's epoch is at most the first epoch of the chain plus its number of epochs.
      block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs ∧
      -- The signers condition reads the last slot of the epoch of `x`, once its roots are cached.
      --
      -- Its signer epoch is the epoch before that of `x`, or epoch 0 itself when `x` is in epoch 0.
      --
      -- Its signers hold at most the current total active balance of the cached state.
      --
      -- That balance is the total active balance of the epoch of `x`.
      --
      -- Before Altair, the signers are unslashed attesters of the epoch's pending attestations.
      --
      -- Only those pending attestations that match the source count.
      --
      -- From Altair, the bound holds for each participation flag, not for the union of the flags.
      --
      -- For a flag, the signers are the unslashed validators active in that epoch that set it.
      --
      -- The comparison is required only when the reads of those balances and indices succeed.
      --
      -- No fact of a chain gives it: signers of that epoch may be inactive in the epoch of `x`.
      SignersAtEnds config checks x (block.slot.toNat - x.state.slot.toNat) ∧
      -- If the chosen validator is unslashed at `x`, take its withdrawable epoch recorded at `x`.
      --
      -- The block's epoch is below it.
      (validator.slashed = false →
        block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat < validator.withdrawableEpoch.toNat))
    -- The steps before the slashing in its body succeed, and reach a state.
    (turned : SlashingTurn config checks engine advanced block j turn)
    -- The block is within the limits.
    (bounded : BlockBounded limits block.body)
    -- Its body contains the slashing of the validator by those votes, at a position.
    (atJ : block.body.attesterSlashings.data.toList[j]? =
      some (singleAttesterSlashing i.toUInt64 d1 d2 s1 s2 attesters)) :
    ∃ later, turn.validators.data[i]? = some later ∧ later.pubkey = validator.pubkey ∧
      (later.slashed = true ∨ ∃ after, processAttesterSlashing config checks turn
        (singleAttesterSlashing i.toUInt64 d1 d2 s1 s2 attesters) = .ok after) := by
  -- The registry of `x` is within its limit, so the position is the index.
  have registry : x.state.RegistryWithinLimit :=
    (RunBounded.size_le holds.bounded).trans (holds.run conditions within).load.1
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have numeric := toNat_toUInt64_of_lt registry inside
  -- The slots stay in the epoch of `x` or reach the next one.
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := conditions.run.slots
    omega
  obtain ⟨slots⟩ := run_of_advanceSlotsAcross _ advancedOk
  have slotsSteps := slots.chainSteps
  have advancedSlot : advanced.slot.toNat = block.slot.toNat := by
    have := advanceSlotsAcross_slot _ advancedOk
    dsimp only at this
    omega
  have advancedEpoch : (getCurrentEpoch advanced).toNat =
      block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [getCurrentEpoch_toNat, advancedSlot]
  have xEpoch := getCurrentEpoch_toNat x.state
  have notBefore : (getCurrentEpoch x.state).toNat ≤
      block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [xEpoch]
    exact Nat.div_le_div_right later.le
  -- The steps before the slashing keep the frame and activity.
  obtain ⟨input, started, frameKept, keepsKept, -⟩ := slashingTurn_kept turned
  have frameTurn := (frame_operationsInput started).toFrame.trans frameKept
  have ordered : ExitsOrdered turn := frameTurn.exitsOrdered
    ((advanceSlotsAcross_invariant holds.invariant advancedOk).1.exitsOrdered)
  -- The validator keeps its key at the turn.
  have prefixTurn : validatorKeys x.state <+: validatorKeys turn :=
    ((validatorKeys_prefix_and_distinct_of_chainSteps slotsSteps).1.trans
      frameTurn.pubkeysPrefix)
  obtain ⟨current, currentFound, currentKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix prefixTurn found
  -- The epoch of the turn is the epoch of the block.
  have epochTurn : getCurrentEpoch turn = getCurrentEpoch advanced := by
    unfold getCurrentEpoch
    rw [frameTurn.slot]
  -- The block's epoch, the signers at the epoch ends, and slashability at the turn.
  obtain ⟨blockWithin, signers, slashableTurn⟩ : block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
        startEpoch + epochs ∧
      SignersAtEnds config checks x (block.slot.toNat - x.state.slot.toNat) ∧
      (current.slashed = false → isSlashableValidator current (getCurrentEpoch turn) = true) := by
    by_cases sameEpoch : block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
        (getCurrentEpoch x.state).toNat
    · have epochAdvanced : getCurrentEpoch advanced = getCurrentEpoch x.state :=
        UInt64.toNat_inj.mp (advancedEpoch.trans sameEpoch)
      refine ⟨by omega, ?_, ?_⟩
      · -- In the same epoch, no slot before the block ends an epoch: the condition holds.
        intro steps below reached reachedOk ends
        have reachedSlot := advanceSlotsAcross_slot _ reachedOk
        exfalso
        have boundary : (reached.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat =
            reached.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 :=
          Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero ends)
        have upper : (reached.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤
            block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat :=
          Nat.div_le_div_right (by omega)
        have lower : x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
            reached.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat :=
          Nat.div_le_div_right (by omega)
        omega
      · intro unslashed
        by_cases far : validator.exitEpoch = FAR_FUTURE_EPOCH
        · -- With no exit yet at `x`, it is active at the epoch of `x`, up to `advanced`.
          have below := getCurrentEpoch_succ_lt_farFuture conditions.run.roots.twoSlots x.state
          obtain ⟨mid, midFound, midActive⟩ := active_of_unexited slotsSteps found lifetime.1 far
            (by rw [UInt64.lt_iff_toNat_lt]; omega)
          exact slashable_of_active turned ordered epochTurn midFound
            (epochAdvanced ▸ midActive) currentFound unslashed
        · -- With an exit set, it keeps its activation, and its withdrawable epoch only rises.
          rw [epochTurn, epochAdvanced]
          obtain ⟨last, same, sameValidators⟩ :=
            validators_advanceSlotsAcross_of_epoch _ advancedOk
              (by rw [Nat.add_sub_cancel' (Nat.le_of_lt later)]; exact sameEpoch)
          obtain rfl : advanced = last := eq_of_heq (ForkedBeaconState.mk.inj same).2
          have aged := ages_slashingTurn turned
          have stays := aged.1.later i validator current (by rw [sameValidators]; exact found)
            currentFound
          simp only [isSlashableValidator, unslashed, stays.activation, Bool.not_false,
            Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨lifetime.1, UInt64.lt_of_lt_of_le lifetime.2 (stays.withdrawable far).1⟩
    · -- In the next epoch, the premise for that case gives the three requirements.
      have crossed : (getCurrentEpoch x.state).toNat <
          block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by omega
      obtain ⟨blockWithin, signers, withdrawableNext⟩ := crossing crossed
      refine ⟨blockWithin, signers, fun unslashed => slashable_of_nextEpoch shared genesis
        withdrawable found lifetime.1 slots (by omega)
        (fun flag => advancedEpoch ▸ withdrawableNext flag) turned ordered epochTurn
        currentFound unslashed⟩
  refine ⟨current, currentFound, currentKey, ?_⟩
  cases slashedFlag : current.slashed
  · right
    have slashable := slashableTurn slashedFlag
    -- The versions and the genesis root of the turn are those of the signatures.
    obtain ⟨hash, time, deposits, _, initialized⟩ := genesis
    obtain ⟨run1⟩ := pair.run1
    obtain ⟨run2⟩ := pair.run2
    have toAdvanced := shared.chainSteps.trans slotsSteps
    have versions1 := forkVersions_eq_of_fork initialized run1.chainSteps toAdvanced sameFork1
    have versions2 := forkVersions_eq_of_fork initialized run2.chainSteps toAdvanced sameFork2
    have rooted : turn.genesisValidatorsRoot = g.state.genesisValidatorsRoot :=
      frameTurn.genesisValidatorsRoot.trans
        ((genesisValidatorsRoot_chainSteps slotsSteps).trans shared.genesisValidatorsRoot)
    obtain ⟨domain1, domained1, rooted1⟩ := pair.root1
    obtain ⟨domain2, domained2, rooted2⟩ := pair.root2
    have window1 : turn.forkVersions.versionAt d1.target.epoch = config.forkVersion f1 := by
      rw [frameTurn.forkVersions]
      exact versions1 ▸ pair.read1
    have window2 : turn.forkVersions.versionAt d2.target.epoch = config.forkVersion f2 := by
      rw [frameTurn.forkVersions]
      exact versions2 ▸ pair.read2
    have currentRead : getValidator turn i.toUInt64 = .ok current :=
      getValidator_eq_ok_iff.mpr (by rwa [numeric])
    have accepted := processAttesterSlashing_single_eq_slashValidator pair.conflict domained1
      rooted1 domained2 rooted2 s1 s2 verified1 verified2 rooted window1 window2 currentRead
      currentKey slashable attesters
    -- Slashing the validator succeeds there.
    have insideTurn : i.toUInt64.toNat < turn.validators.data.size := by
      rw [numeric]
      exact (Array.getElem?_eq_some_iff.mp currentFound).1
    obtain ⟨after, slashed⟩ := slashValidator_total_of_block conditions fits covers withdrawable
      activationIncrement holds advancedOk later turned bounded blockWithin signers atJ
      (by rfl) insideTurn
    refine ⟨after, ?_⟩
    rw [accepted, slashed]
    rfl
  · exact .inl rfl

/-- A successful slashing of one validator leaves that validator slashed, with its key. -/
private theorem processAttesterSlashing_single_slashed {config : Config}
    {checks : SignatureChecks} {turn after : BeaconState preset fork}
    {index : ValidatorIndex} {later : Validator}
    {d1 d2 : AttestationData} {s1 s2 : BLSSignature}
    {attesters : 1 ≤ maxAttesters preset fork}
    (found : getValidator turn index = .ok later)
    (accepted : processAttesterSlashing config checks turn
      (singleAttesterSlashing index d1 d2 s1 s2 attesters) = .ok after) :
    ∃ slashed, getValidator after index = .ok slashed ∧
      slashed.pubkey = later.pubkey ∧ slashed.slashed = true := by
  -- Both lists of the slashing are `[index]`, so the slashed validator is the one at `index`.
  obtain ⟨named, member, -, flag⟩ := processAttesterSlashing_slashed accepted
  obtain rfl : named = index := by simpa [singleAttesterSlashing] using member
  -- The operation keeps the keys of the registry as a prefix, so that validator keeps its key.
  obtain ⟨current, currentFound, currentKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix
      (frame_processAttesterSlashing accepted).pubkeysPrefix (getValidator_eq_ok_iff.mp found)
  have read : getValidator after named = .ok current := getValidator_eq_ok_iff.mpr currentFound
  exact ⟨current, read, currentKey, by simpa [slashedFlag, read, Except.map] using flag⟩

/-- A block can slash a key of a validator of `x` that is activated and not yet withdrawable there.

At the state before its slashing, the slashing succeeds, or the validator is already slashed.

The theorem says nothing about the state after the block.

Nothing is said when that inclusion or that success fails. -/
theorem processAttesterSlashing_single_slashed_or_accepted_at {config : Config}
    {checks : SignatureChecks}
    -- The slashings vector has a nonzero length.
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    -- The state `x` lies on a run from a genesis of deposits.
    {g x : ForkedBeaconState preset} (shared : Run config checks g x)
    (genesis : Genesis config checks g)
    {start : RunStart} {step : BlockStep} {limits : BlockLimits}
    {budget epochs lastEpoch startEpoch blocks : Nat}
    (conditions : ChainConditions preset config start step budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    -- The step covers the limits.
    (covers : step.Covers preset limits start budget epochs)
    -- The withdrawal delay is positive.
    (withdrawable : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    -- An increment is at most the least balance to activate.
    (activationIncrement : preset.EFFECTIVE_BALANCE_INCREMENT ≤ preset.MIN_ACTIVATION_BALANCE)
    -- The facts of a chain hold at `x`, and the epoch of `x` is within the epochs of the chain.
    (holds : ChainHolds config start step budget startEpoch blocks x.state)
    (within : (getCurrentEpoch x.state).toNat ≤ startEpoch + epochs)
    -- A key names a validator of `x` that is activated and not yet withdrawable at its epoch.
    --
    -- Unlike an active validator, it may have exited.
    --
    -- As with an active one, it may already be slashed.
    {key : BLSPubkey}
    (lifetime : ∃ (i : Nat) (v : Validator), x.state.validators.data[i]? = some v ∧
      v.pubkey = key ∧ v.activationEpoch ≤ getCurrentEpoch x.state ∧
      getCurrentEpoch x.state < v.withdrawableEpoch)
    -- The pair is a double or surround vote.
    --
    -- The signatures and the states that read each vote are assumptions, not facts of the run.
    {d1 d2 : AttestationData} {f1 f2 : Fork} {r1 r2 : Root} {z1 z2 : ForkedBeaconState preset}
    (pair : VotePairAt config checks g d1 d2 f1 f2 r1 r2 z1 z2)
    -- Each vote is read at a state of a run from the genesis at the fork of `x`.
    --
    -- Reading each vote at the fork of `x` suffices but is not necessary.
    --
    -- A slashing at the next fork can still read a vote whose target is before that fork's epoch.
    (sameFork1 : z1.fork = x.fork) (sameFork2 : z2.fork = x.fork)
    -- A pair of votes has a signature on each signing root that verifies for that key alone.
    (s1 s2 : BLSSignature)
    (verified1 : checks.fastAggregateVerify #[key] (packBytes r1) s1 = true)
    (verified2 : checks.fastAggregateVerify #[key] (packBytes r2) s2 = true)
    -- An attester slashing of one validator fits at the fork of `x`.
    (attesters : 1 ≤ maxAttesters preset x.fork) :
    -- The validator is chosen before the block.
    ∃ index validator, (getValidator x.state index = .ok validator ∧ validator.pubkey = key) ∧
      -- Take any block within the limits, applied at `x` at a later slot, at the fork of `x`.
      ∀ {engine : ExecutionEngine preset x.fork} {block : BeaconBlock preset x.fork}
        {advanced turn : BeaconState preset x.fork} {j : Nat},
        advanceSlotsAcross config checks (block.slot.toNat - x.state.slot.toNat) x =
          .ok ⟨x.fork, advanced⟩ →
        x.state.slot.toNat < block.slot.toNat →
        -- The block is in the epoch of `x` or in the next epoch.
        --
        -- So a block at the first slot of an epoch is covered from any `x` in the epoch before.
        --
        -- A block two or more epochs after `x` is not covered.
        block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ (getCurrentEpoch x.state).toNat + 1 →
        -- In the next epoch, the slots cross one epoch end.
        --
        -- The theorem then takes three assumptions.
        ((getCurrentEpoch x.state).toNat < block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat →
          -- The block's epoch is at most the first epoch of the chain plus its number of epochs.
          block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs ∧
          -- The signers condition reads the last slot of the epoch of `x`.
          --
          -- It reads that slot once its roots are cached.
          --
          -- Its signer epoch is the epoch before that of `x`, or epoch 0 when `x` is in epoch 0.
          --
          -- Its signers hold at most the current total active balance of the cached state.
          --
          -- That balance is the total active balance of the epoch of `x`.
          --
          -- Before Altair, the signers are unslashed attesters of the epoch's pending attestations.
          --
          -- Only those pending attestations that match the source count.
          --
          -- From Altair, the bound holds for each participation flag, not for their union.
          --
          -- For a flag, the signers are the unslashed validators active in that epoch that set it.
          --
          -- The comparison is required only when the reads of those balances and indices succeed.
          --
          -- No fact of a chain gives it: signers of that epoch may be inactive in the epoch of `x`.
          SignersAtEnds config checks x (block.slot.toNat - x.state.slot.toNat) ∧
          -- If the chosen validator is unslashed at `x`, take its withdrawable epoch at `x`.
          --
          -- The block's epoch is below it.
          (validator.slashed = false →
            block.slot.toNat / preset.SLOTS_PER_EPOCH.toNat < validator.withdrawableEpoch.toNat)) →
        -- The steps before its operations succeed.
        --
        -- So do the slashings before the position of the slashing in its body.
        --
        -- The count checks of the operations are not read.
        SlashingTurn config checks engine advanced block j turn →
        BlockBounded limits block.body →
        -- Its body contains the slashing of that validator by those votes, at a position.
        block.body.attesterSlashings.data.toList[j]? =
          some (singleAttesterSlashing index d1 d2 s1 s2 attesters) →
        -- At the state that those steps reach, the validator still has the key.
        ∃ later, getValidator turn index = .ok later ∧ later.pubkey = key ∧
          -- The slashing succeeds there, or else the validator is already slashed there.
          (later.slashed = true ∨ ∃ after slashed, processAttesterSlashing config checks turn
            (singleAttesterSlashing index d1 d2 s1 s2 attesters) = .ok after ∧
              -- Right after that operation, the validator still has the key and is slashed.
              getValidator after index = .ok slashed ∧ slashed.pubkey = key ∧
                slashed.slashed = true) := by
  -- The key names a validator of `x`, activated and not yet withdrawable at its epoch.
  have registry : x.state.RegistryWithinLimit :=
    (RunBounded.size_le holds.bounded).trans (holds.run conditions within).load.1
  obtain ⟨i, validator, found, keyEq, activation, withdrawal⟩ := lifetime
  have numeric := toNat_toUInt64_of_lt registry (Array.getElem?_eq_some_iff.mp found).1
  subst keyEq
  refine ⟨i.toUInt64, validator, ⟨getValidator_eq_ok_iff.mpr (by rwa [numeric]), rfl⟩, ?_⟩
  intro engine block advanced turn j advancedOk later nextAtMost crossing turned bounded atJ
  obtain ⟨current, currentFound, currentKey, outcome⟩ := attesterSlashing_accepted_of_lifetime
    shared genesis conditions fits covers withdrawable activationIncrement holds within found
    ⟨activation, withdrawal⟩ pair sameFork1 sameFork2 s1 s2 verified1 verified2 attesters
    advancedOk later nextAtMost crossing turned bounded atJ
  have found : getValidator turn i.toUInt64 = .ok current :=
    getValidator_eq_ok_iff.mpr (by rwa [numeric])
  -- After a successful slashing, the validator at that index is slashed and keeps the key.
  refine ⟨current, found, currentKey, outcome.imp id fun ⟨after, accepted⟩ => ?_⟩
  obtain ⟨slashed, read, slashedKey, flag⟩ := processAttesterSlashing_single_slashed found accepted
  exact ⟨after, slashed, accepted, read, slashedKey.trans currentKey, flag⟩

end EthLib.Consensus.DirectSafety
