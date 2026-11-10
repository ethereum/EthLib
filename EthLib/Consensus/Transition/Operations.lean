module

public import EthLib.Consensus.Participation
public import EthLib.Consensus.PayloadTimeliness
public import EthLib.Consensus.Transition.Block
public import EthLib.Consensus.Transition.BuilderRequests
public import EthLib.Consensus.Transition.Requests
public import EthLib.Consensus.Transition.Withdrawals
public import EthLib.Serialization.Ssz.Merkle.Branch

/-!
# `Consensus.Transition.Operations`

The operations of a block: slashings, attestations, deposits and voluntary exits.

From Capella a block also changes BLS credentials to addresses.

From Electra the requests of the execution layer follow: deposits, withdrawals and consolidations.

A block runs them in that order, each kind in the order of the block.

Before Altair an attestation joins the pending attestations of its target epoch.

From Altair it sets the participation flags of its attesters, and pays the proposer for new flags.

A deposit must lie in the deposit tree that the chain has agreed on, at the next deposit index.

A deposit to a new key adds a validator if its signature is valid, and else changes nothing.

A deposit to a known key adds to the balance of that validator.

From Electra the amount of a deposit waits in a queue instead.

A deposit that the execution layer requests waits there too.

A voluntary exit starts the exit of an active validator that has been active for long enough.

From Electra its validator must have no pending partial withdrawal.

Where a later fork changes a rule, the step fails as not yet specified there.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-! ## Attestations -/

/-- Before Electra, the bits of an attestation fit the bits of a pending attestation. -/
theorem aggregationBits_size_le (attestation : Attestation preset fork)
    (before : fork < .pectra) :
    attestation.aggregationBits.bits.size ≤ preset.MAX_VALIDATORS_PER_COMMITTEE.toNat := by
  have bound := attestation.aggregationBits.bound (Nat.lt_trans before (by decide))
  have notElectra : ¬Fork.pectra ≤ fork := fun le =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simpa [maxAttesters, notElectra] using bound

/-- Before Altair: the state with a pending attestation appended to those of an epoch.

The epoch is the current one when the flag is set, and the previous one otherwise.

A list at its limit is an error. -/
def recordPendingAttestation (state : BeaconState preset fork) (before : fork < .altair)
    (current : Bool) (pending : PendingAttestation preset) :
    Except TransitionError (BeaconState preset fork) :=
  let list := if current then state.currentEpochAttestations before
    else state.previousEpochAttestations before
  if fits : list.data.size < preset.MAX_ATTESTATIONS.toNat * preset.SLOTS_PER_EPOCH.toNat then
    let list : SszList (PendingAttestation preset) _ :=
      ⟨list.data.push pending, by simp only [Array.size_push]; omega⟩
    if current then .ok { state with currentEpochAttestations := fun _ => list }
    else .ok { state with previousEpochAttestations := fun _ => list }
  else .error .tooManyPendingAttestations

/-- From Altair: one flag of one attester, set if the attestation earns it and it is not yet set.

A newly set flag adds the attester's base reward times the flag's weight to the numerator. -/
def addFlagReward (state : BeaconState preset fork) (total : Gwei) (earned : List UInt64)
    (index : ValidatorIndex) (step : ParticipationFlags × Gwei)
    (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length) :
    Except TransitionError (ParticipationFlags × Gwei) := do
  let (flags, numerator) := step
  let flagIndex := flag.val.toUInt64
  if flagIndex ∈ earned ∧ hasFlag flags flagIndex = false then
    let reward ← liftAccessor (getBaseReward state total index)
    let weighted ← liftAccessor (liftArith (mulChecked reward PARTICIPATION_FLAG_WEIGHTS[flag]))
    return (addFlag flags flagIndex, ← liftAccessor (liftArith (addChecked numerator weighted)))
  else return (flags, numerator)

/-- From Altair: the flags of the epoch with those of one attester set, and the numerator. -/
def addAttesterFlags (state : BeaconState preset fork) (total : Gwei) (earned : List UInt64)
    (step : EpochParticipation preset fork × Gwei) (index : ValidatorIndex) :
    Except TransitionError (EpochParticipation preset fork × Gwei) := do
  let (participation, numerator) := step
  if inside : index.toNat < participation.data.size then
    let (flags, numerator) ← (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).foldlM
      (addFlagReward state total earned index) (participation.data[index.toNat], numerator)
    return (⟨participation.data.set index.toNat flags inside,
      fun before => by simpa using participation.bound before⟩, numerator)
  else throw (.accessor (.indexOutOfRange index))

/-- From Altair: the state with the flags of the current epoch, or else of the previous epoch.
-/
def setEpochParticipation (state : BeaconState preset fork) (current : Bool)
    (participation : EpochParticipation preset fork) : BeaconState preset fork :=
  if current then { state with currentEpochParticipation := fun _ => participation }
  else { state with previousEpochParticipation := fun _ => participation }

/-- Before Deneb: an attestation must be included at most one epoch after its slot.

A 64-bit overflow of that last slot is an error.

From Deneb there is no such bound, as [EIP-7045] says, and nothing is computed.

[EIP-7045]: https://eips.ethereum.org/EIPS/eip-7045#specification
-/
def checkInclusionDeadline (state : BeaconState preset fork) (slot : Slot) :
    Except TransitionError Unit :=
  if fork < .dencun then do
    let latest ← liftAccessor (liftArith (addChecked slot preset.SLOTS_PER_EPOCH))
    ensure (state.slot ≤ latest) (.attestationTooLate slot state.slot)
  else pure ()

/-- From Electra: the total size of some committees of a slot, each with an attester.

The committees are cut from the given active validators and shuffle.

Each index must be below the given bound.

Each committee is cut with the given count of committees per slot. -/
def attestationCommitteesSizeOf (preset : Preset) (slot : Slot) (bits : Array Bool)
    (count perSlot : UInt64) (active : Array ValidatorIndex) (shuffled : Array UInt64) :
    List CommitteeIndex → Nat → Except TransitionError Nat
  | [], offset => pure offset
  | index :: rest, offset => do
    ensure (index < count) (.committeeIndexOutOfRange index count)
    let committee ← liftAccessor (beaconCommitteeOf preset slot index perSlot active shuffled)
    let attesters ← liftAccessor (committeeAttesters bits offset committee)
    ensure (attesters ≠ []) (.noCommitteeAttester index)
    attestationCommitteesSizeOf preset slot bits count perSlot active shuffled rest
      (offset + committee.size)

/-- From Electra: the total size of some committees of a slot, each with an attester.

Each committee must be one of the slot, and must have a bit set for at least one member.

The bits of each committee follow those of the committees before it.

The bits must reach past each committee, else the attestation is invalid.

The committees share one shuffle of the active validators, computed once for the list.

A list that names no committee computes no shuffle. -/
def attestationCommitteesSize (state : BeaconState preset fork) (data : AttestationData)
    (bits : Array Bool) : List CommitteeIndex → Nat → Except TransitionError Nat
  | [], offset => pure offset
  | index :: rest, offset => do
    let count := getCommitteeCountPerSlot state data.target.epoch
    -- A first index out of range fails here, before the shuffle is computed.
    ensure (index < count) (.committeeIndexOutOfRange index count)
    let epoch := computeEpochAtSlot preset data.slot
    let (active, shuffled) ← liftAccessor (attesterShuffle state epoch)
    -- The walk checks the first index again, and that check never fails.
    attestationCommitteesSizeOf preset data.slot bits count (getCommitteeCountPerSlot state epoch)
      active shuffled (index :: rest) offset

/-- The check that an attestation has one bit for each member of its committees.

Before Electra it names one committee of its slot by its index.

From Electra its index must be zero, and its committee bits name the committees, as [EIP-7549] says.

Each of them must then have an attester.

From Gloas its index is its vote on the payload, so it may also be one.

[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
-/
def checkAttestationCommittees (state : BeaconState preset fork)
    (attestation : Attestation preset fork) : Except TransitionError Unit := do
  let data := attestation.data
  let bits := attestation.aggregationBits.bits
  if electra : .pectra ≤ fork then
    if .glamsterdam ≤ fork then ensure (data.index < 2) (.attestationIndexAboveOne data.index)
    else ensure (data.index = 0) (.attestationIndexNotZero data.index)
    let size ← attestationCommitteesSize state data bits
      (getCommitteeIndices (attestation.committeeBits electra)) 0
    ensure (bits.size = size) (.aggregationBitsLength bits.size size)
  else
    let count := getCommitteeCountPerSlot state data.target.epoch
    ensure (data.index < count) (.committeeIndexOutOfRange data.index count)
    let committee ← liftAccessor (getBeaconCommittee state data.slot data.index)
    ensure (bits.size = committee.size) (.aggregationBitsLength bits.size committee.size)

/-- From Gloas: the position of the pending payment of the block at a slot.

A slot of the current epoch pays in the second half, and a slot of the previous epoch in the first.
-/
def attestationPaymentPosition (preset : Preset) (current : Bool) (slot : Slot) : Nat :=
  ((if current then preset.SLOTS_PER_EPOCH else 0) + slot % preset.SLOTS_PER_EPOCH).toNat

/-- From Gloas: the weight of a payment after the attesters of an attestation.

An attester adds its effective balance if it had no flag in the epoch and now has one.

A sum that reaches `2^64` is an error. -/
def addPaymentWeight (state : BeaconState preset fork)
    (before after : EpochParticipation preset fork) (weight : Gwei) (index : ValidatorIndex) :
    Except TransitionError Gwei := do
  let some old := before.data[index.toNat]? | throw (.accessor (.indexOutOfRange index))
  let some new := after.data[index.toNat]? | throw (.accessor (.indexOutOfRange index))
  if old = 0 ∧ new ≠ old then
    let validator ← liftAccessor (getValidator state index)
    liftAccessor (liftArith (addChecked weight validator.effectiveBalance))
  else return weight

/-- From Gloas: the state with the payment of an attested block weighed by its new attesters.

Only an attestation for the block of its own slot weighs, and only a payment of a positive amount.

Otherwise the payment is written back unchanged. -/
def recordPaymentWeight (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (data : AttestationData) (current : Bool) (before after : EpochParticipation preset fork)
    (attesters : List ValidatorIndex) : Except TransitionError (BeaconState preset fork) := do
  let position := attestationPaymentPosition preset current data.slot
  let payments := state.builderPendingPayments gloas
  if inside : position < payments.elements.size then
    let payment := payments[position]
    let sameSlot ← liftAccessor (isAttestationSameSlot state data)
    let weight ← (if sameSlot ∧ 0 < payment.withdrawal.amount then
        attesters.foldlM (addPaymentWeight state before after) payment.weight
      else pure payment.weight)
    let payments := payments.set position { payment with weight } inside
    return { state with builderPendingPayments := fun _ => payments }
  else throw (.accessor (.paymentIndexOutOfRange position.toUInt64))

/-- From Altair: the state after an attestation.

Its target must be the current or the previous epoch, and the epoch of its slot.

It must be included at least the least inclusion delay after its slot.

Before Deneb it must also be included at most one epoch after its slot, as [EIP-7045] removes.

It must have one bit for each member of its committees, which from Electra may be several.

Its source, target and head earn flags by its inclusion delay, and its source must be justified.

Its signature must be the aggregate signature of the members whose bit is set.

Each attester gets the flags it earned in the epoch of the target.

The proposer earns a share of the base rewards of the flags newly set.

From Gloas the head flag also needs the payload vote to match, at the slot of the parent block.

The new attesters of a vote for the block of its own slot add weight to the payment of its builder.

Both rules are from [EIP-7732].

[EIP-7045]: https://eips.ethereum.org/EIPS/eip-7045#specification
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/
def processAttestationAltair (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (attestation : Attestation preset fork)
    (altair : .altair ≤ fork) (parentSlot : Slot) :
    Except TransitionError (BeaconState preset fork) := do
    let data := attestation.data
    let currentEpoch := getCurrentEpoch state
    ensure (data.target.epoch = getPreviousEpoch state ∨ data.target.epoch = currentEpoch)
      (.attestationTargetNotRecent data.target.epoch currentEpoch)
    ensure (data.target.epoch = computeEpochAtSlot preset data.slot)
      (.attestationTargetNotSlotEpoch data.target.epoch (computeEpochAtSlot preset data.slot))
    let earliest ←
      liftAccessor (liftArith (addChecked data.slot preset.MIN_ATTESTATION_INCLUSION_DELAY))
    ensure (earliest ≤ state.slot) (.attestationTooEarly data.slot state.slot)
    checkInclusionDeadline state data.slot
    checkAttestationCommittees state attestation
    let earned ← liftAccessor
      (getAttestationParticipationFlagIndices state data (state.slot - data.slot) parentSlot)
    let indexed ← liftAccessor (getIndexedAttestation state attestation)
    let valid ← isValidIndexedAttestation config checks state indexed
    ensure (valid = true) .invalidAttestation
    let current := data.target.epoch == currentEpoch
    let participation := if current then state.currentEpochParticipation altair
      else state.previousEpochParticipation altair
    let total ← liftAccessor (getTotalActiveBalance state)
    let attesters ← liftAccessor (getAttestingIndices state attestation)
    let (updated, numerator) ←
      attesters.foldlM (addAttesterFlags state total earned) (participation, 0)
    let state := setEpochParticipation state current updated
    let denominator := (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT
    let proposer ← liftAccessor (getBeaconProposerIndex state)
    let state ← liftAccessor (increaseBalance state proposer (numerator / denominator))
    if gloas : .glamsterdam ≤ fork then
      recordPaymentWeight state gloas data current participation updated attesters
    else pure state

/-- The state after an attestation.

Its target must be the current or the previous epoch, and the epoch of its slot.

It must be included at least the least inclusion delay after its slot, and at most one epoch after.

It must name a committee of its slot, with one bit for each member.

Its source must be the justified checkpoint that the state holds for its target epoch.

It then joins the pending attestations of that epoch, with its delay and the current proposer.

Its signature must be the aggregate signature of the members whose bit is set.

A 64-bit overflow is an error.

From Altair the rule records participation flags instead.

From Gloas the slot of the parent block decides the payload vote. -/
def processAttestation (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (parentSlot : Slot) (attestation : Attestation preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then
    processAttestationAltair config checks state attestation altair parentSlot
  else do
    have before : fork < .altair := Nat.lt_of_not_le altair
    let data := attestation.data
    let currentEpoch := getCurrentEpoch state
    ensure (data.target.epoch = getPreviousEpoch state ∨ data.target.epoch = currentEpoch)
      (.attestationTargetNotRecent data.target.epoch currentEpoch)
    ensure (data.target.epoch = computeEpochAtSlot preset data.slot)
      (.attestationTargetNotSlotEpoch data.target.epoch (computeEpochAtSlot preset data.slot))
    let earliest ←
      liftAccessor (liftArith (addChecked data.slot preset.MIN_ATTESTATION_INCLUSION_DELAY))
    ensure (earliest ≤ state.slot) (.attestationTooEarly data.slot state.slot)
    let latest ← liftAccessor (liftArith (addChecked data.slot preset.SLOTS_PER_EPOCH))
    ensure (state.slot ≤ latest) (.attestationTooLate data.slot state.slot)
    let count := getCommitteeCountPerSlot state data.target.epoch
    ensure (data.index < count) (.committeeIndexOutOfRange data.index count)
    let committee ← liftAccessor (getBeaconCommittee state data.slot data.index)
    let bits := attestation.aggregationBits.bits
    ensure (bits.size = committee.size) (.aggregationBitsLength bits.size committee.size)
    let proposer ← liftAccessor (getBeaconProposerIndex state)
    let pending : PendingAttestation preset :=
      ⟨⟨bits, aggregationBits_size_le attestation (Nat.lt_trans before (by decide))⟩, data,
        state.slot - data.slot, proposer⟩
    let current := data.target.epoch == currentEpoch
    let justified :=
      if current then state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint
    ensure (data.source = justified) .wrongAttestationSource
    let updated ← recordPendingAttestation state before current pending
    let indexed ← liftAccessor (getIndexedAttestation updated attestation)
    let valid ← isValidIndexedAttestation config checks updated indexed
    ensure (valid = true) .invalidAttestation
    return updated

/-! ## Deposits -/

/-- The validator that a deposit creates.

Its effective balance is the amount rounded down to a whole increment, and at most the largest.

From Electra the largest depends on its credentials, as [EIP-7251] specifies.

It is not slashed, not yet eligible for activation, and has no exit.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def getValidatorFromDeposit (preset : Preset) (fork : Base.Fork) (pubkey : BLSPubkey)
    (withdrawalCredentials : Bytes32) (amount : Gwei) : Validator :=
  let validator : Validator :=
    { pubkey, withdrawalCredentials, effectiveBalance := 0, slashed := false
      activationEligibilityEpoch := FAR_FUTURE_EPOCH, activationEpoch := FAR_FUTURE_EPOCH
      exitEpoch := FAR_FUTURE_EPOCH, withdrawableEpoch := FAR_FUTURE_EPOCH }
  { validator with
    effectiveBalance := min (amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT)
      (withdrawalMaxEffectiveBalance preset fork validator) }

/-- From Altair: the state with a new validator at the index for a new validator.

It gets its balance, no participation flag in either epoch, and an inactivity score of zero.

A list at its limit is an error, and so is a registry of `2^64` validators or more. -/
def addValidatorToRegistryAltair (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (pubkey : BLSPubkey) (withdrawalCredentials : Bytes32) (amount : Gwei) :
    Except TransitionError (BeaconState preset fork) :=
  liftAccessor do
    let index ← getIndexForNewValidator state
    let validator := getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount
    let validators ← setOrAppendRooted state.validators index validator
    let balances ← setOrAppendList state.balances index amount
    let previous ← setOrAppendList (state.previousEpochParticipation altair) index 0
    let current ← setOrAppendList (state.currentEpochParticipation altair) index 0
    let scores ← setOrAppendList (state.inactivityScores altair) index 0
    return { state with
      validators, balances
      previousEpochParticipation := fun _ => previous
      currentEpochParticipation := fun _ => current
      inactivityScores := fun _ => scores }

/-- The state with a new validator at the end of the registry, and its balance.

A registry at its limit is an error.

From Altair a new validator also gets participation flags and an inactivity score. -/
def addValidatorToRegistry (state : BeaconState preset fork) (pubkey : BLSPubkey)
    (withdrawalCredentials : Bytes32) (amount : Gwei) :
    Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then
    addValidatorToRegistryAltair state altair pubkey withdrawalCredentials amount
  else
    if fits : state.validators.data.size < preset.VALIDATOR_REGISTRY_LIMIT.toNat ∧
        state.balances.data.size < preset.VALIDATOR_REGISTRY_LIMIT.toNat then
      .ok { state with
        validators :=
          state.validators.push
            (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount)
            fun _ => fits.1
        balances :=
          ⟨state.balances.data.push amount, fun _ => by simp only [Array.size_push]; omega⟩ }
    else .error .registryFull

/-- The state after a deposit is credited.

A key that no validator has gets a new validator, if the deposit carries its signature.

A deposit to a new key with an invalid signature changes nothing.

A key that a validator has adds the amount to the balance of the first such validator.

A known key at a position of `2^64` or more has no validator index, an overflow.

Before Electra a deposit is credited at once; from Electra it waits in the pending deposits.

From Heze a deposit to a new key with BLS withdrawal credentials changes nothing.

It is not refunded, as [EIP-8365] specifies.

[EIP-8365]: https://eips.ethereum.org/EIPS/eip-8365#deposit-processing
-/
def applyPendingDeposit (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (deposit : PendingDeposit) :
    Except TransitionError (BeaconState preset fork) :=
  match state.validators.data.findIdx? (·.pubkey == deposit.pubkey) with
  | none =>
    if .hegota ≤ fork ∧ deposit.withdrawalCredentials[0] = BLS_WITHDRAWAL_PREFIX[0] then
      pure state
    else do
      if ← isValidDepositSignature config checks deposit.pubkey deposit.withdrawalCredentials
          deposit.amount deposit.signature then
        addValidatorToRegistry state deposit.pubkey deposit.withdrawalCredentials deposit.amount
      else return state
  | some position => liftAccessor do
    increaseBalance state (← liftArith (ofNatChecked position)) deposit.amount

/-- From Electra: the state after the deposit of an amount to a key, as [EIP-7251] specifies.

A new key with a valid signature gets a new validator with no balance.

A deposit to a new key with an invalid signature changes nothing.

Otherwise the deposit joins the pending deposits, at the genesis slot.

That slot tells it apart from a deposit that comes as a request.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def applyDepositElectra (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork) (pubkey : BLSPubkey)
    (withdrawalCredentials : Bytes32) (amount : Gwei) (signature : BLSSignature) :
    Except TransitionError (BeaconState preset fork) := do
  let deposit : PendingDeposit := ⟨pubkey, withdrawalCredentials, amount, signature, GENESIS_SLOT⟩
  match state.validators.data.findIdx? (·.pubkey == pubkey) with
  | none =>
    if ← isValidDepositSignature config checks pubkey withdrawalCredentials amount signature then
      let state ← addValidatorToRegistry state pubkey withdrawalCredentials 0
      liftAccessor (addPendingDeposit state electra deposit)
    else return state
  | some _ => liftAccessor (addPendingDeposit state electra deposit)

/-- The state after the deposit of an amount to a key.

Before Electra the deposit is credited at once.

From Electra it waits in the pending deposits. -/
def applyDeposit (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (pubkey : BLSPubkey) (withdrawalCredentials : Bytes32) (amount : Gwei)
    (signature : BLSSignature) : Except TransitionError (BeaconState preset fork) :=
  if electra : .pectra ≤ fork then
    applyDepositElectra config checks state electra pubkey withdrawalCredentials amount signature
  else
    applyPendingDeposit config checks state
      ⟨pubkey, withdrawalCredentials, amount, signature, GENESIS_SLOT⟩

/-- The state after a deposit of a block.

Its Merkle branch must lead from the deposit to the deposit root, at the next deposit index.

The branch has one node more than the depth of the tree, for the number of deposits in the root.

The next deposit index then grows by one, and the deposit applies.

The step exists only before Heze, which removes deposits from blocks. -/
def processDeposit (config : Config) (checks : SignatureChecks) (before : fork < .hegota)
    (state : BeaconState preset fork) (deposit : Deposit) :
    Except TransitionError (BeaconState preset fork) := do
  let leaf ← liftSsz (hashTreeRoot deposit.data)
  let index := state.eth1DepositIndex before
  ensure (isValidMerkleBranch leaf deposit.proof.toList (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
    index.toNat (state.eth1Data before).depositRoot = true) .invalidDepositProof
  let next ← liftAccessor (liftArith (addChecked index 1))
  applyDeposit config checks { state with eth1DepositIndex := fun _ => next } deposit.data.pubkey
    deposit.data.withdrawalCredentials deposit.data.amount deposit.data.signature

/-- In Electra: the state that records the index of the first deposit request.

A state that holds such an index already keeps it.

From Fulu nothing is recorded. -/
def recordDepositRequestsStart (state : BeaconState preset fork) (index : UInt64) :
    BeaconState preset fork :=
  if electra : .pectra ≤ fork ∧ fork < .fusaka then
    if state.depositRequestsStartIndex ⟨electra.1, Nat.lt_trans electra.2 (by decide)⟩ =
        UNSET_DEPOSIT_REQUESTS_START_INDEX then
      { state with depositRequestsStartIndex := fun _ => index }
    else state
  else state

/-- From Electra: the state after a deposit that the execution layer requests, as [EIP-6110] adds.

The deposit joins the pending deposits, at the current slot.

In Electra the first such request also records its index as the start of the requests.

From Fulu nothing is recorded.

[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer
-/
def processDepositRequest (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (request : DepositRequest) : Except TransitionError (BeaconState preset fork) :=
  let state := recordDepositRequestsStart state request.index
  liftAccessor (addPendingDeposit state electra
    ⟨request.pubkey, request.withdrawalCredentials, request.amount, request.signature, state.slot⟩)

/-! ## Voluntary exits -/

/-- From Electra: the check that a validator has no pending partial withdrawal.

Before Electra there is no such withdrawal, and nothing is checked. -/
def checkNoPendingWithdrawal (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except TransitionError Unit :=
  if electra : .pectra ≤ fork then do
    let pending ← liftAccessor (getPendingBalanceToWithdraw state electra index)
    ensure (pending = 0) (.exitPendingWithdrawal index)
  else pure ()

/-- The domain under which a validator signs a voluntary exit for an epoch.

Before Deneb it is the domain of the fork at that epoch.

From Deneb it is fixed on the fork version of Capella, as [EIP-7044] specifies.

So an exit signed once stays valid at every later fork.

[EIP-7044]: https://eips.ethereum.org/EIPS/eip-7044#specification
-/
def voluntaryExitDomain (config : Config) (state : BeaconState preset fork) (epoch : Epoch) :
    Except TransitionError Domain :=
  if .dencun ≤ fork then
    liftSsz (computeDomain config DOMAIN_VOLUNTARY_EXIT config.CAPELLA_FORK_VERSION
      state.genesisValidatorsRoot)
  else liftAccessor (getDomain config state DOMAIN_VOLUNTARY_EXIT (some epoch))

/-- The state after a voluntary exit.

Its validator must be active, and must not have started to exit.

It must have been active for long enough.

The exit must not be for a later epoch than the current one.

From Electra the validator must have no pending partial withdrawal, as [EIP-7251] specifies.

The validator must sign the exit, under the domain of a voluntary exit.

The validator then starts to exit.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def processVoluntaryExit (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedVoluntaryExit) :
    Except TransitionError (BeaconState preset fork) := do
    let exit := signed.message
    let validator ← liftAccessor (getValidator state exit.validatorIndex)
    let epoch := getCurrentEpoch state
    ensure (isActiveValidator validator epoch = true)
      (.exitingValidatorNotActive exit.validatorIndex)
    ensure (validator.exitEpoch = FAR_FUTURE_EPOCH) (.exitAlreadyInitiated exit.validatorIndex)
    ensure (exit.epoch ≤ epoch) (.exitNotYetValid exit.epoch epoch)
    let eligible ←
      liftAccessor (liftArith (addChecked validator.activationEpoch config.SHARD_COMMITTEE_PERIOD))
    ensure (eligible ≤ epoch) (.exitTooSoon exit.validatorIndex)
    checkNoPendingWithdrawal state exit.validatorIndex
    let domain ← voluntaryExitDomain config state exit.epoch
    let signingRoot ← liftSsz (computeSigningRoot exit domain)
    ensure (checks.verify (packBytes validator.pubkey) (packBytes signingRoot)
      (packBytes signed.signature) = true) .invalidExitSignature
    liftAccessor (initiateValidatorExit config state exit.validatorIndex)

/-! ## All the operations of a block -/

/-- The number of deposits that a block must hold, before Heze.

Before Electra it is every deposit that the state has not processed, up to the most per block.

In Electra the deposits of the contract stop at the first deposit request, as [EIP-6110] specifies.

So it counts only the deposits before that request, up to the most per block.

From Fulu a block holds no deposit.

Before Electra, a deposit index past the deposit count is a 64-bit underflow, and an error.

[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer
-/
def expectedDepositCount (state : BeaconState preset fork) (before : fork < .hegota) :
    Except TransitionError Nat :=
  let index := state.eth1DepositIndex before
  let count := (state.eth1Data before).depositCount
  if .fusaka ≤ fork then pure 0
  else if electra : .pectra ≤ fork then
    let limit := min count (state.depositRequestsStartIndex ⟨electra, before⟩)
    pure (if index < limit then (min preset.MAX_DEPOSITS (limit - index)).toNat else 0)
  else do
    let outstanding ← liftAccessor (liftArith (subChecked count index))
    return (min preset.MAX_DEPOSITS outstanding).toNat

/-- From Electra to Fulu: the state after the requests of the execution layer in a block.

The deposit requests run first, then the withdrawal requests and the consolidation requests. -/
def processExecutionRequests (config : Config) (state : BeaconState preset fork)
    (body : BeaconBlockBody preset fork) (electra : .pectra ≤ fork ∧ fork < .glamsterdam) :
    Except TransitionError (BeaconState preset fork) := do
  let requests := body.executionRequests electra
  let state ← requests.deposits.data.foldlM (processDepositRequest · electra.1 ·) state
  let state ← requests.withdrawals.data.foldlM (processWithdrawalRequest config · electra.1 ·) state
  requests.consolidations.data.foldlM (processConsolidationRequest config · electra.1 ·) state

/-- From Capella: the state after the changes of BLS credentials of a block.

Before Capella the state stays the same. -/
def processBlsToExecutionChanges (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (body : BeaconBlockBody preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if capella : .shapella ≤ fork then
    (body.blsToExecutionChanges capella).data.foldlM (processBlsToExecutionChange config checks)
      state
  else pure state

/-- From Gloas: the state after the operations of a block.

Each list of operations must hold no more than its most per block, since it has no type bound.

Before Heze the block must hold no deposit.

The proposer slashings run first, then the attester slashings and the attestations.

The attestations read the slot of the parent block, for their payload vote.

The voluntary exits and the changes of BLS credentials follow, and the payload attestations last.

The requests of the execution layer run with the parent payload instead. -/
def processOperationsGloas (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (body : BeaconBlockBody preset fork)
    (gloas : .glamsterdam ≤ fork) (parentSlot : Slot) :
    Except TransitionError (BeaconState preset fork) := do
  (if before : fork < .hegota then
      ensure ((body.deposits before).data.size = 0)
        (.wrongDepositCount (body.deposits before).data.size 0)
    else pure ())
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) gloas
  let changes := (body.blsToExecutionChanges capella).data
  let payloadAttestations := (body.payloadAttestations gloas).data
  checkCount body.proposerSlashings.data.size preset.MAX_PROPOSER_SLASHINGS
  checkCount body.attesterSlashings.data.size preset.MAX_ATTESTER_SLASHINGS_ELECTRA
  checkCount body.attestations.data.size preset.MAX_ATTESTATIONS_ELECTRA
  checkCount body.voluntaryExits.data.size preset.MAX_VOLUNTARY_EXITS
  checkCount changes.size preset.MAX_BLS_TO_EXECUTION_CHANGES
  checkCount payloadAttestations.size preset.MAX_PAYLOAD_ATTESTATIONS
  let state ← body.proposerSlashings.data.foldlM (processProposerSlashing config checks) state
  let state ← body.attesterSlashings.data.foldlM (processAttesterSlashing config checks) state
  let state ← body.attestations.data.foldlM (processAttestation config checks · parentSlot ·) state
  let state ← body.voluntaryExits.data.foldlM (processVoluntaryExit config checks) state
  let state ← changes.foldlM (processBlsToExecutionChange config checks) state
  payloadAttestations.foldlM (processPayloadAttestation config checks · gloas ·) state

/-- The state after the operations of a block.

The block must hold the number of deposits that the state expects.

The proposer slashings run first, then the attester slashings, attestations, deposits and exits.

From Capella the changes of BLS credentials follow.

From Electra the requests of the execution layer run last.

From Fulu a block holds no deposit, so no deposit runs.

From Gloas the operations change, and the attestations read the slot of the parent block. -/
def processOperations (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (body : BeaconBlockBody preset fork) (parentSlot : Slot) :
    Except TransitionError (BeaconState preset fork) :=
  if gloas : .glamsterdam ≤ fork then
    processOperationsGloas config checks state body gloas parentSlot
  else do
    have before : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le gloas) (by decide)
    let expected ← expectedDepositCount state before
    let deposits := (body.deposits before).data
    ensure (deposits.size = expected) (.wrongDepositCount deposits.size expected)
    let state ← body.proposerSlashings.data.foldlM (processProposerSlashing config checks) state
    let state ← body.attesterSlashings.data.foldlM (processAttesterSlashing config checks) state
    let state ←
      body.attestations.data.foldlM (processAttestation config checks · parentSlot ·) state
    let state ← deposits.foldlM (processDeposit config checks before) state
    let state ← body.voluntaryExits.data.foldlM (processVoluntaryExit config checks) state
    let state ← processBlsToExecutionChanges config checks state body
    if electra : .pectra ≤ fork then
      processExecutionRequests config state body ⟨electra, Nat.lt_of_not_le gloas⟩
    else return state

end EthLib.Consensus
