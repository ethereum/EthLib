module

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
  /-- A network aggregate has no committee bit set. -/
  | noCommittee
  /-- The joined aggregation bits exceed the limit of an attestation. -/
  | tooManyBits (count limit : Nat)
  /-- A request has no type byte, or a type byte that names no request. -/
  | unknownRequestType (request : ByteArray)
  /-- A request has a type byte and nothing after it. -/
  | emptyRequest (type : UInt8)
  /-- A request type does not come after the type before it. -/
  | requestTypeOrder (previous type : UInt8)

/-- The code of an error at the C boundary, one for each constructor. -/
def ProposerError.code : ProposerError → UInt32
  | .arith _ => 1
  | .accessor _ => 2
  | .ssz _ => 3
  | .bls _ => 4
  | .transition _ => 5
  | .noAggregates => 6
  | .noCommittee => 7
  | .tooManyBits .. => 8
  | .unknownRequestType _ => 9
  | .emptyRequest _ => 10
  | .requestTypeOrder .. => 11

/-! ## The Eth1 vote -/

/-- Before Heze: the time at the start of the Eth1 voting period of the slot of a state.

It fails when the period has no slot, and when a 64-bit operation overflows. -/
def votingPeriodStartTime (config : Config) (state : BeaconState preset fork) :
    Except ProposerError UInt64 := do
  let periodSlots ←
    (mulChecked preset.EPOCHS_PER_ETH1_VOTING_PERIOD preset.SLOTS_PER_EPOCH).mapError .arith
  if periodSlots = 0 then throw (.arith .divisionByZero)
  -- The remainder is at most the slot, so the difference cannot underflow.
  let startSlot := state.slot - state.slot % periodSlots
  (computeTimeAtSlot config state.genesisTime startSlot).mapError .arith

/-- Before Heze: whether an Eth1 block with a timestamp is a candidate for a voting period.

Its timestamp must lie between one and two follow distances before the start of the period.

A follow distance is the number of Eth1 blocks to wait times the time of one Eth1 block.

The bound of two follow distances is computed only once the first bound holds.

It fails when a 64-bit operation overflows. -/
def isCandidateBlock (config : Config) (timestamp periodStart : UInt64) :
    Except ProposerError Bool := do
  let distance ←
    (mulChecked config.SECONDS_PER_ETH1_BLOCK config.ETH1_FOLLOW_DISTANCE).mapError .arith
  if (← (addChecked timestamp distance).mapError .arith) ≤ periodStart then
    let twice ← (mulChecked distance 2).mapError .arith
    return periodStart ≤ (← (addChecked timestamp twice).mapError .arith)
  else return false

/-- Before Heze: the Eth1 data of the blocks of a chain that a proposer may vote for, in order.

A block counts when it is a candidate for the period.

Its deposit count must also be at least that of the state, so that the vote never moves back.

It fails when a 64-bit operation overflows. -/
def votesToConsider {Block : Type} (config : Config) (state : BeaconState preset fork)
    (before : fork < .hegota) (timestamp : Block → UInt64) (getEth1Data : Block → Eth1Data)
    (periodStart : UInt64) : List Block → Except ProposerError (List Eth1Data)
  | [] => return []
  | block :: rest => do
    let candidate ← isCandidateBlock config (timestamp block) periodStart
    let others ← votesToConsider config state before timestamp getEth1Data periodStart rest
    if candidate ∧ (state.eth1Data before).depositCount ≤ (getEth1Data block).depositCount then
      return getEth1Data block :: others
    else return others

/-- Whether a vote beats another among a list of votes.

It has more copies, or as many and a first copy that comes earlier. -/
def beatsVote (votes : List Eth1Data) (vote best : Eth1Data) : Bool :=
  votes.count best < votes.count vote ||
    (votes.count best == votes.count vote && votes.idxOf vote < votes.idxOf best)

/-- The vote with the most copies in a list, the earliest one on a tie, or a default when empty.

It walks the list once and keeps the first vote that no later vote beats. -/
def mostVoted (votes : List Eth1Data) (default : Eth1Data) : Eth1Data :=
  match votes with
  | [] => default
  | first :: rest => rest.foldl (fun best vote => if beatsVote votes vote best then vote else best)
      first

/-- Before Heze: the Eth1 data that an honest proposer votes for in its block.

The Eth1 chain lists the blocks by increasing height.

Each block has a timestamp and the Eth1 data that the deposit contract held after it.

From Electra, once the deposits of the contract are all processed, the vote is the state's data.

Otherwise the proposer considers the data of the candidate blocks.

Among them it takes the one with the most votes in the state, the earliest one on a tie.

When no vote of the state is among them, it takes the data of the last candidate.

With no candidate at all, the vote is the data of the state.

It fails when the voting period has no slot, and when a 64-bit operation overflows. -/
def getEth1Vote {Block : Type} (config : Config) (state : BeaconState preset fork)
    (before : fork < .hegota) (timestamp : Block → UInt64) (getEth1Data : Block → Eth1Data)
    (eth1Chain : List Block) : Except ProposerError Eth1Data := do
  if electra : .pectra ≤ fork then
    if state.eth1DepositIndex before = state.depositRequestsStartIndex ⟨electra, before⟩ then
      return state.eth1Data before
  let periodStart ← votingPeriodStartTime config state
  let votes ← votesToConsider config state before timestamp getEth1Data periodStart eth1Chain
  -- The votes already cast in this period for a block that counts.
  let validVotes := (state.eth1DataVotes before).data.toList.filter (· ∈ votes)
  let defaultVote := votes.getLast?.getD (state.eth1Data before)
  return mostVoted validVotes defaultVote

/-- In Electra: the number of deposits of the deposit contract that a proposer includes.

[EIP-6110] ends these deposits at the first deposit request, so only the deposits before it count.

The count is at most the most deposits per block, and zero once those deposits are all in.

From Fulu a block holds no deposit of the contract, so the count is not defined there.

[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer -/
def getEth1PendingDepositCount (state : BeaconState preset fork)
    (electra : .pectra ≤ fork ∧ fork < .fusaka) : UInt64 :=
  have before : fork < .hegota := Nat.lt_trans electra.2 (by decide)
  let limit := min (state.eth1Data before).depositCount
    (state.depositRequestsStartIndex ⟨electra.1, before⟩)
  if state.eth1DepositIndex before < limit then
    min preset.MAX_DEPOSITS (limit - state.eth1DepositIndex before)
  else 0

/-! ## The state root -/

/-- The root of the state after a block, to set as the state root of that block.

It runs the state transition on the block with an empty signature.

The checks of the result, the signature of the block and its state root, do not run.

The signatures of the operations go through the signature checks that it takes.

It fails when the transition rejects the block, and when the state after it has no root. -/
def computeNewStateRoot (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except ProposerError Root := do
  let signed : SignedBeaconBlock preset fork := ⟨block, Vector.replicate 96 0⟩
  let post ← (stateTransition config checks engine state signed false).mapError .transition
  (SszType.hashTreeRoot post).mapError .ssz

/-! ## Attestations -/

/-- From Electra: the first committee whose bit a network aggregate sets, with the aggregate.

It fails when the aggregate sets no committee bit. -/
def committeeOfAggregate (electra : .pectra ≤ fork) (aggregate : Attestation preset fork) :
    Except ProposerError (CommitteeIndex × Attestation preset fork) :=
  match (getCommitteeIndices (aggregate.committeeBits electra)).head? with
  | some index => .ok (index, aggregate)
  | none => .error .noCommittee

/-- From Electra: one attestation on chain from network aggregates of the same data.

Each network aggregate covers one committee, the first one whose bit it sets.

The aggregates are sorted by that committee, and keep their order on a tie.

The aggregation bits are those of each aggregate in turn, and the signature is their aggregate.

The committee bits mark the committee of each aggregate.

The data is that of the first aggregate.

It fails on an aggregate without a committee bit, and on an empty list.

Before Gloas it fails when the aggregation bits exceed the limit of an attestation.

It also fails when a signature does not decode. -/
def computeOnChainAggregate (electra : .pectra ≤ fork)
    (networkAggregates : List (Attestation preset fork)) :
    Except ProposerError (Attestation preset fork) := do
  let keyed ← networkAggregates.mapM (committeeOfAggregate electra)
  let aggregates := keyed.mergeSort fun a b => a.1 ≤ b.1
  let some first := aggregates.head? | throw .noAggregates
  let bits := (aggregates.map (·.2.aggregationBits.bits)).foldl (· ++ ·) #[]
  if bound : fork < .glamsterdam → bits.size ≤ maxAttesters preset fork then
    let signature ← (Signatures.aggregate
      (aggregates.map fun entry => Base.packBytes entry.2.signature).toArray).mapError .bls
    let committees := aggregates.map (·.1)
    return {
      aggregationBits := ⟨bits, bound⟩
      data := first.2.data
      signature
      committeeBits := fun _ =>
        ⟨Vector.ofFn fun index : Fin preset.MAX_COMMITTEES_PER_SLOT.toNat =>
          committees.contains index.val.toUInt64⟩ }
  else throw (.tooManyBits bits.size (maxAttesters preset fork))

/-! ## Execution requests -/

/-- From Electra: the types of the request lists, in their order: three, and from Gloas five. -/
def requestTypes (fork : Fork) : List UInt8 :=
  [DEPOSIT_REQUEST_TYPE[0], WITHDRAWAL_REQUEST_TYPE[0], CONSOLIDATION_REQUEST_TYPE[0]] ++
    if .glamsterdam ≤ fork then [BUILDER_DEPOSIT_REQUEST_TYPE[0], BUILDER_EXIT_REQUEST_TYPE[0]]
    else []

/-- From Electra: the requests with the list of one type decoded from its SSZ bytes.

A type that is not a request type leaves the requests as they are. -/
def setRequestList (requests : ExecutionRequests preset fork) (type : UInt8) (data : ByteArray) :
    Except ProposerError (ExecutionRequests preset fork) := do
  if type = DEPOSIT_REQUEST_TYPE[0] then
    return { requests with deposits := ← (SszType.deserialize _ data).mapError .ssz }
  else if type = WITHDRAWAL_REQUEST_TYPE[0] then
    return { requests with withdrawals := ← (SszType.deserialize _ data).mapError .ssz }
  else if type = CONSOLIDATION_REQUEST_TYPE[0] then
    return { requests with consolidations := ← (SszType.deserialize _ data).mapError .ssz }
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
    let some type := request.data[0]? | throw (.unknownRequestType request)
    unless type ∈ requestTypes fork do throw (.unknownRequestType request)
    let data := request.extract 1 request.size
    if data.size = 0 then throw (.emptyRequest type)
    if let some previous := previous then
      unless previous < type do throw (.requestTypeOrder previous type)
    getExecutionRequestsFrom (some type) (← setRequestList requests type data) rest

/-- From Electra: the requests of an execution block, from the list the execution layer gives.

Each entry is a type byte, then the SSZ bytes of the list of that type, as in [EIP-7685].

A type that has no entry has an empty list.

It fails on an entry whose type names no request, and on one with nothing after its type.

It fails when a type does not come strictly after the type before it.

It fails when the bytes of a list do not decode.

[EIP-7685]: https://eips.ethereum.org/EIPS/eip-7685#execution-layer -/
def getExecutionRequests (executionRequestsList : List ByteArray) :
    Except ProposerError (ExecutionRequests preset fork) :=
  getExecutionRequestsFrom none (.empty preset fork) executionRequestsList

/-! ## Custody -/

/-- The sum of the effective balances of some validators.

It fails on an index outside the registry, and on a sum that overflows. -/
def totalEffectiveBalance (state : BeaconState preset fork)
    (validatorIndices : List ValidatorIndex) :
    Except ProposerError Gwei :=
  validatorIndices.foldlM (fun total index => do
    let validator ← (getValidator state index).mapError .accessor
    (addChecked total validator.effectiveBalance).mapError .arith) 0

/-- From Fulu: the number of custody groups of a node, from the validators attached to it.

The node custodies one group for each increment of effective balance of its validators.

That count is at least the minimum for a node with validators, and at most the number of groups.

It fails on an index outside the registry, on a sum that overflows, and on an increment of zero. -/
def getValidatorsCustodyRequirement (config : Config) (state : BeaconState preset fork)
    (validatorIndices : List ValidatorIndex) : Except ProposerError UInt64 := do
  let totalNodeBalance ← totalEffectiveBalance state validatorIndices
  let count ←
    (divChecked totalNodeBalance config.BALANCE_PER_ADDITIONAL_CUSTODY_GROUP).mapError .arith
  return min (max count config.VALIDATOR_CUSTODY_REQUIREMENT) config.NUMBER_OF_CUSTODY_GROUPS

end EthLib.Consensus
