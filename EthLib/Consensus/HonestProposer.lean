module

public import EthLib.Consensus.HonestValidator
public import EthLib.Consensus.Transition.StateTransition
public import EthLib.Cryptography.Bls.Signatures

/-!
# `Consensus.HonestProposer`

What an honest validator computes to propose a block.

Before Heze, the block carries a vote on the Eth1 data, the state of the deposit contract.

The proposer votes for the data of a recent Eth1 block.

It prefers the data that most proposers of the voting period voted for already.

The block commits to the root of the state after it.

The proposer computes that root by running the state transition without the checks of the result.

In Electra, the block holds the deposits of the deposit contract up to the first deposit request.

From Altair, the proposer joins the contributions of the sync subcommittees into one aggregate.

From Electra, the proposer joins the network aggregates of one vote into one attestation.

It also reads the requests of the execution layer from their bytes, as [EIP-7685] gives them.

From Fulu, a node with validators custodies more data columns, by the balance of its validators.

[EIP-7685]: https://eips.ethereum.org/EIPS/eip-7685#execution-layer

The Eth1 data of an Eth1 block is not specified, and neither is the type of an Eth1 block.

So the vote takes the timestamp and the Eth1 data of a block as functions.

The steps that read the network or the execution layer are not specified here.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Why a step of an honest proposer has no result. -/
inductive ProposerError where
  /-- A 64-bit operation has no result. -/
  | arith (error : ArithError)
  /-- A state accessor fails. -/
  | accessor (error : AccessorError)
  /-- A value cannot be encoded, decoded or hashed. -/
  | ssz (error : Err)
  /-- The aggregate of the signatures fails. -/
  | bls (error : BlsError)
  /-- The state transition fails. -/
  | transition (error : TransitionError)
  /-- There is no network aggregate to join. -/
  | noAggregates
  /-- A network aggregate has no committee bit set.

  The error gives the data of that aggregate. -/
  | noCommittee (data : AttestationData)
  /-- The joined aggregation bits exceed the limit of an attestation. -/
  | tooManyBits (count limit : Nat)
  /-- A request has no type byte, or a type byte that names no request. -/
  | unknownRequestType (request : ByteArray)
  /-- A request has a type byte and nothing after it. -/
  | emptyRequest (type : UInt8)
  /-- A request type does not come after the type before it. -/
  | requestTypeOrder (previous type : UInt8)
  /-- A contribution names a subcommittee that is not below the number of subnets. -/
  | subcommitteeOutOfRange (index : UInt64)
  /-- Two contributions name the same subcommittee. -/
  | repeatedSubcommittee (index : UInt64)
  /-- From Bellatrix: a block of proof of work names a parent that the chain does not hold. -/
  | unknownPowBlock (hash : Hash32)
  /-- From Gloas: a step of the fork choice fails. -/
  | forkChoice (error : ForkChoiceError)
  /-- From Heze: the inclusion lists of the payload cannot be read. -/
  | duty (error : ValidatorDutyError)

/-- The code of an error at the C boundary, one for each constructor. -/
def ProposerError.code : ProposerError → UInt32
  | .arith _ => 1
  | .accessor _ => 2
  | .ssz _ => 3
  | .bls _ => 4
  | .transition _ => 5
  | .noAggregates => 6
  | .noCommittee _ => 7
  | .tooManyBits .. => 8
  | .unknownRequestType _ => 9
  | .emptyRequest _ => 10
  | .requestTypeOrder .. => 11
  | .subcommitteeOutOfRange _ => 12
  | .repeatedSubcommittee _ => 13
  | .unknownPowBlock _ => 14
  | .forkChoice _ => 15
  | .duty _ => 16

/-- The message of an error, with the values that its check compared. -/
instance : ToString ProposerError where
  toString
    | .arith error => s!"arithmetic: {reprStr error}"
    | .accessor error => s!"a state accessor fails: {reprStr error}"
    | .ssz error => s!"a value cannot be encoded, decoded or hashed: {reprStr error}"
    | .bls error => s!"BLS: {error.message}"
    | .transition error => s!"the state transition fails: {reprStr error}"
    | .noAggregates => "there is no network aggregate to join"
    | .noCommittee data =>
      s!"the network aggregate at slot {data.slot} for block " ++
        s!"{hexString data.beaconBlockRoot.toList} has no committee bit set"
    | .tooManyBits count limit => s!"{count} joined aggregation bits exceed the limit {limit}"
    | .unknownRequestType request =>
      s!"a request of {request.size} bytes has no type byte that names a request"
    | .emptyRequest type => s!"the request of type {type} has nothing after its type byte"
    | .requestTypeOrder previous type =>
      s!"request type {type} does not come after the type before it, {previous}"
    | .subcommitteeOutOfRange index =>
      s!"subcommittee {index} is not below the number of subnets"
    | .repeatedSubcommittee index => s!"two contributions name subcommittee {index}"
    | .unknownPowBlock hash => s!"no known proof-of-work block has hash {hexString hash.toList}"
    | .forkChoice error => s!"fork choice: {error}"
    | .duty error => s!"validator duty: {error}"

/-! ## The Eth1 vote -/

/-- Before Heze: the time at the start of the Eth1 voting period of the slot of a state.

It fails when the period has no slot, and when a 64-bit operation overflows. -/
def votingPeriodStartTime (config : Config) (state : BeaconState preset fork) :
    Except ProposerError UInt64 := do
  -- A period lasts `P = EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH` slots.
  let periodSlots ←
    (mulChecked preset.EPOCHS_PER_ETH1_VOTING_PERIOD preset.SLOTS_PER_EPOCH).mapError .arith
  -- A period of no slot is a division by zero.
  if periodSlots = 0 then throw (.arith .divisionByZero)
  -- It starts at slot `s - (s mod P)`, for the slot `s` of the state.
  --
  -- The remainder is at most the slot, so the difference cannot underflow.
  let startSlot := state.slot - state.slot % periodSlots
  -- The time of that slot, from the genesis time.
  (computeTimeAtSlot config state.genesisTime startSlot).mapError .arith

/-- Before Heze: whether an Eth1 block with a timestamp is a candidate for a voting period.

The bound of two follow distances is computed only once the bound of one follow distance holds.

It fails when a 64-bit operation overflows. -/
def isCandidateBlock (config : Config) (timestamp periodStart : UInt64) :
    Except ProposerError Bool := do
  -- A follow distance is `d = SECONDS_PER_ETH1_BLOCK * ETH1_FOLLOW_DISTANCE` seconds.
  let distance ←
    (mulChecked config.SECONDS_PER_ETH1_BLOCK config.ETH1_FOLLOW_DISTANCE).mapError .arith
  -- Let `t` be the timestamp and `p` the start of the period.
  --
  -- The block is a candidate when `t + d ≤ p ≤ t + 2 * d`.
  if (← (addChecked timestamp distance).mapError .arith) ≤ periodStart then
    let twice ← (mulChecked distance 2).mapError .arith
    return periodStart ≤ (← (addChecked timestamp twice).mapError .arith)
  else return false

/-- Before Heze: the Eth1 data of the blocks of a chain that a proposer may vote for, in order.

It fails when a 64-bit operation overflows. -/
def votesToConsider {Block : Type} (config : Config) (state : BeaconState preset fork)
    (before : fork < .hegota) (timestamp : Block → UInt64) (getEth1Data : Block → Eth1Data)
    (periodStart : UInt64) : List Block → Except ProposerError (List Eth1Data)
  | [] => return []
  | block :: rest => do
    -- A block counts when it is a candidate for the period.
    let candidate ← isCandidateBlock config (timestamp block) periodStart
    let others ← votesToConsider config state before timestamp getEth1Data periodStart rest
    -- Its deposit count is at least that of the state, so that the vote never moves back.
    if candidate ∧ (state.eth1Data before).depositCount ≤ (getEth1Data block).depositCount then
      return getEth1Data block :: others
    else return others

/-- Whether a vote beats another among a list of votes. -/
def beatsVote (votes : List Eth1Data) (vote best : Eth1Data) : Bool :=
  -- Let `c(v)` be the number of copies of `v` in the list, and `i(v)` the place of its first copy.
  --
  -- The vote `v` beats `b` when `c(b) < c(v)`, or `c(b) = c(v)` and `i(v) < i(b)`.
  votes.count best < votes.count vote ||
    (votes.count best == votes.count vote && votes.idxOf vote < votes.idxOf best)

/-- The vote with the most copies in a list, the earliest one on a tie, or a default when empty.

It walks the list once and keeps the first vote that no later vote beats. -/
def mostVoted (votes : List Eth1Data) (default : Eth1Data) : Eth1Data :=
  match votes with
  -- An empty list gives the default.
  | [] => default
  -- From the first vote, each later vote that beats the best one replaces it.
  | first :: rest => rest.foldl (fun best vote => if beatsVote votes vote best then vote else best)
      first

/-- Before Heze: the Eth1 data that an honest proposer votes for in its block.

The Eth1 chain lists the blocks by increasing height.

Each block has a timestamp and the Eth1 data that the deposit contract held after it.

It fails when the voting period has no slot, and when a 64-bit operation overflows. -/
def getEth1Vote {Block : Type} (config : Config) (state : BeaconState preset fork)
    (before : fork < .hegota) (timestamp : Block → UInt64) (getEth1Data : Block → Eth1Data)
    (eth1Chain : List Block) : Except ProposerError Eth1Data := do
  -- From Electra, the vote is the data of the state once the deposits of the contract are all in.
  --
  -- They are all in when the next deposit index is the start index of the requests.
  if electra : .pectra ≤ fork then
    if state.eth1DepositIndex before = state.depositRequestsStartIndex ⟨electra, before⟩ then
      return state.eth1Data before
  -- The data of the blocks that count, in the order of the chain.
  let periodStart ← votingPeriodStartTime config state
  let votes ← votesToConsider config state before timestamp getEth1Data periodStart eth1Chain
  -- The votes already cast in this period for a block that counts.
  let validVotes := (state.eth1DataVotes before).data.toList.filter (· ∈ votes)
  -- The default is the data of the last block that counts, or with none the data of the state.
  let defaultVote := votes.getLast?.getD (state.eth1Data before)
  -- The cast vote with the most copies, the one first cast on a tie, or else the default.
  return mostVoted validVotes defaultVote

/-- In Electra: the number of deposits of the deposit contract that a proposer includes.

[EIP-6110] ends these deposits at the first deposit request, so only the deposits before it count.

From Fulu a block holds no deposit of the contract, so the count is not defined there.

[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer -/
def getEth1PendingDepositCount (state : BeaconState preset fork)
    (electra : .pectra ≤ fork ∧ fork < .fusaka) : UInt64 :=
  have before : fork < .hegota := Nat.lt_trans electra.2 (by decide)
  -- Let `n` be the deposit count of the Eth1 data, and `r` the start index of the requests.
  --
  -- The deposits of the contract end at `L = min(n, r)`.
  let limit := min (state.eth1Data before).depositCount
    (state.depositRequestsStartIndex ⟨electra.1, before⟩)
  -- Let `i` be the next deposit index; for `i < L` the count is `min(MAX_DEPOSITS, L - i)`.
  if state.eth1DepositIndex before < limit then
    min preset.MAX_DEPOSITS (limit - state.eth1DepositIndex before)
  -- Else those deposits are all in, and the count is 0.
  else 0

/-! ## The state root -/

/-- The root of the state after a block, to set as the state root of that block.

The checks of the result, the signature of the block and its state root, do not run.

The signatures of the operations go through the signature checks that it takes.

It fails when the transition rejects the block, and when the state after it has no root. -/
def computeNewStateRoot (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except ProposerError Root := do
  -- The block with an empty signature, 96 zero bytes.
  let signed : SignedBeaconBlock preset fork := ⟨block, Vector.replicate 96 0⟩
  -- The state transition on it, without the checks of the result.
  let post ← (stateTransition config checks engine state signed false).mapError .transition
  -- The root of the state after it.
  (SszType.hashTreeRoot post).mapError .ssz

/-! ## Attestations -/

/-- From Electra: the first committee whose bit a network aggregate sets, with the aggregate.

It fails when the aggregate sets no committee bit. -/
def committeeOfAggregate (electra : .pectra ≤ fork) (aggregate : Attestation preset fork) :
    Except ProposerError (CommitteeIndex × Attestation preset fork) :=
  -- The least committee index whose bit is set; with no bit set, it is an error.
  match (getCommitteeIndices (aggregate.committeeBits electra)).head? with
  | some index => .ok (index, aggregate)
  | none => .error (.noCommittee aggregate.data)

/-- From Electra: one attestation on chain from network aggregates of the same data.

It fails on an aggregate without a committee bit, and on an empty list.

Before Gloas it fails when the aggregation bits exceed the limit of an attestation.

It also fails when a signature does not decode. -/
def computeOnChainAggregate (electra : .pectra ≤ fork)
    (networkAggregates : List (Attestation preset fork)) :
    Except ProposerError (Attestation preset fork) := do
  -- Each network aggregate covers one committee, the first one whose bit it sets.
  let keyed ← networkAggregates.mapM (committeeOfAggregate electra)
  -- The aggregates sorted by that committee, in their order on a tie.
  let aggregates := keyed.mergeSort fun a b => a.1 ≤ b.1
  -- The data is that of the first aggregate.
  let some first := aggregates.head? | throw .noAggregates
  -- The aggregation bits are those of each aggregate in turn.
  let bits := (aggregates.map (·.2.aggregationBits.bits)).foldl (· ++ ·) #[]
  -- Before Gloas they fit in the limit of an attestation.
  if bound : fork < .glamsterdam → bits.size ≤ maxAttesters preset fork then
    -- The signature is the aggregate of their signatures.
    let signature ← (Signatures.aggregate
      (aggregates.map (·.2.signature)).toArray).mapError .bls
    -- The committees of the aggregates, in order.
    let committees := aggregates.map (·.1)
    return {
      aggregationBits := ⟨bits, bound⟩
      data := first.2.data
      signature
      -- Committee bit `i` is set when `i` is among them.
      committeeBits := fun _ =>
        ⟨Vector.ofFn fun index : Fin preset.MAX_COMMITTEES_PER_SLOT.toNat =>
          committees.contains index.val.toUInt64⟩ }
  else throw (.tooManyBits bits.size (maxAttesters preset fork))

/-! ## The sync aggregate -/

/-- From Altair: the sync aggregate of a block, from the contributions of some subcommittees.

It fails on a subcommittee that is not below the number of subnets, and on one named twice.

It also fails on an empty list, and when a signature does not decode. -/
def processSyncCommitteeContributions (contributions : List (SyncCommitteeContribution preset)) :
    Except ProposerError (SyncAggregate preset) := do
  -- Each subcommittee is below `SYNC_COMMITTEE_SUBNET_COUNT`.
  --
  -- The source fails on a larger one only when its contribution sets a bit.
  match contributions.find? fun contribution =>
      Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT ≤ contribution.subcommitteeIndex.toNat with
  | some other => throw (.subcommitteeOutOfRange other.subcommitteeIndex)
  | none =>
  -- No two contributions name the same subcommittee, as the rule requires of its input.
  let indices := contributions.map (·.subcommitteeIndex)
  match indices.find? fun index => 1 < indices.count index with
  | some index => throw (.repeatedSubcommittee index)
  | none =>
  -- A subcommittee has `k = floor(SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT)` seats.
  let size := syncSubcommitteeSize preset
  -- Seat `j` of the committee is seat `j mod k` of subcommittee `floor(j / k)`.
  --
  -- Its bit is set when the contribution of that subcommittee sets the bit of that seat.
  let bits := Vector.ofFn fun participant : Fin preset.SYNC_COMMITTEE_SIZE.toNat =>
    contributions.any fun contribution =>
      contribution.subcommitteeIndex.toNat = participant.val / size &&
        contribution.aggregationBits.bits.toArray.getD (participant.val % size) false
  -- The signature is the aggregate of the signatures of the contributions.
  let signatures := contributions.map (·.signature)
  let signature ← (Signatures.aggregate signatures.toArray).mapError .bls
  return { syncCommitteeBits := ⟨bits⟩, syncCommitteeSignature := signature }

/-! ## Execution requests -/

/-- From Electra: the types of the request lists, in their order: three, and from Gloas five. -/
def requestTypes (fork : Fork) : List UInt8 :=
  -- The deposit, withdrawal and consolidation types, then from Gloas the two builder types.
  [DEPOSIT_REQUEST_TYPE[0], WITHDRAWAL_REQUEST_TYPE[0], CONSOLIDATION_REQUEST_TYPE[0]] ++
    if .glamsterdam ≤ fork then [BUILDER_DEPOSIT_REQUEST_TYPE[0], BUILDER_EXIT_REQUEST_TYPE[0]]
    else []

/-- From Electra: the requests with the list of one type decoded from its SSZ bytes.

A type that is not a request type leaves the requests as they are. -/
def setRequestList (requests : ExecutionRequests preset fork) (type : UInt8) (data : ByteArray) :
    Except ProposerError (ExecutionRequests preset fork) := do
  -- The bytes decode, as SSZ, into the list of the field of the type.
  if type = DEPOSIT_REQUEST_TYPE[0] then
    return { requests with deposits := ← (SszType.deserialize _ data).mapError .ssz }
  else if type = WITHDRAWAL_REQUEST_TYPE[0] then
    return { requests with withdrawals := ← (SszType.deserialize _ data).mapError .ssz }
  else if type = CONSOLIDATION_REQUEST_TYPE[0] then
    return { requests with consolidations := ← (SszType.deserialize _ data).mapError .ssz }
  -- From Gloas the builder deposits and the builder exits have a type too.
  else if gloas : .glamsterdam ≤ fork then
    if type = BUILDER_DEPOSIT_REQUEST_TYPE[0] then
      let builderDeposits ← (SszType.deserialize _ data).mapError .ssz
      return { requests with builderDeposits := fun _ => builderDeposits }
    else if type = BUILDER_EXIT_REQUEST_TYPE[0] then
      let builderExits ← (SszType.deserialize _ data).mapError .ssz
      return { requests with builderExits := fun _ => builderExits }
    else return requests
  else return requests

/-- From Electra: the requests after reading a list of typed requests, after the type before. -/
def getExecutionRequestsFrom (previous : Option UInt8) (requests : ExecutionRequests preset fork) :
    List ByteArray → Except ProposerError (ExecutionRequests preset fork)
  | [] => return requests
  | request :: rest => do
    -- The first byte is the type, and it is a request type of the fork.
    let some type := request.data[0]? | throw (.unknownRequestType request)
    unless type ∈ requestTypes fork do throw (.unknownRequestType request)
    -- The data after it is not empty.
    let data := request.extract 1 request.size
    if data.size = 0 then throw (.emptyRequest type)
    -- The type is above the type before it, so that the types strictly increase.
    if let some previous := previous then
      unless previous < type do throw (.requestTypeOrder previous type)
    -- The data sets the list of the type, then the next entries are read.
    getExecutionRequestsFrom (some type) (← setRequestList requests type data) rest

/-- From Electra: the requests of an execution block, from the list the execution layer gives.

Each entry is a type byte, then the SSZ bytes of the list of that type, as in [EIP-7685].

It fails on an entry whose type names no request, and on one with nothing after its type.

It fails when a type does not come strictly after the type before it.

It fails when the bytes of a list do not decode.

[EIP-7685]: https://eips.ethereum.org/EIPS/eip-7685#execution-layer -/
def getExecutionRequests (executionRequestsList : List ByteArray) :
    Except ProposerError (ExecutionRequests preset fork) :=
  -- Every list starts empty, so a type that has no entry keeps an empty list.
  getExecutionRequestsFrom none (.empty preset fork) executionRequestsList

/-! ## Custody -/

/-- The sum of the effective balances of some validators.

It fails on an index outside the registry, and on a sum that overflows. -/
def totalEffectiveBalance (state : BeaconState preset fork)
    (validatorIndices : List ValidatorIndex) :
    Except ProposerError Gwei :=
  -- The sum of the effective balances of the validators, below `2^64`.
  validatorIndices.foldlM (fun total index => do
    let validator ← (getValidator state index).mapError .accessor
    (addChecked total validator.effectiveBalance).mapError .arith) 0

/-- From Fulu: the number of custody groups of a node, from the validators attached to it.

It fails on an index outside the registry, on a sum that overflows, and on an increment of zero. -/
def getValidatorsCustodyRequirement (config : Config) (state : BeaconState preset fork)
    (validatorIndices : List ValidatorIndex) : Except ProposerError UInt64 := do
  -- Let `B` be the sum of the effective balances of the validators of the node.
  let totalNodeBalance ← totalEffectiveBalance state validatorIndices
  -- One group for each increment: `c = floor(B / BALANCE_PER_ADDITIONAL_CUSTODY_GROUP)`.
  let count ←
    (divChecked totalNodeBalance config.BALANCE_PER_ADDITIONAL_CUSTODY_GROUP).mapError .arith
  -- The count is `min(max(c, VALIDATOR_CUSTODY_REQUIREMENT), NUMBER_OF_CUSTODY_GROUPS)`.
  return min (max count config.VALIDATOR_CUSTODY_REQUIREMENT) config.NUMBER_OF_CUSTODY_GROUPS

end EthLib.Consensus
