module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.ForkSchedule
public import EthLib.Consensus.Transition.Basic
public import EthLib.Cryptography.Kzg.VersionedHash

/-!
# `Consensus.Transition.Execution`

From Bellatrix to Fulu: the execution payload of a block, and the execution layer that checks it.

The payload must extend the latest payload, read the current RANDAO mix and carry the slot's time.

The execution layer then checks the payload, and the state keeps the header of the payload.

The execution layer is an argument of the step, as the signature checks are.

A test gives one fixed answer, and a node asks its execution client.

Before the first payload, the state holds a header with every field zero.

Until Capella, a block may then carry a zero payload, and no execution runs.

Deneb passes the versioned hashes of the blobs and the parent beacon block root.

Electra passes the requests of the payload too.

[EIP-3675] makes the beacon chain carry the execution blocks.

[EIP-4399] puts the RANDAO mix in the payload, and [EIP-4788] the parent beacon block root.

[EIP-7685] gives the requests to the execution layer as typed byte lists.

[EIP-7691] raises the blob limit at Electra, and from Fulu [EIP-7892] sets it by epoch.

[EIP-3675]: https://eips.ethereum.org/EIPS/eip-3675#block-structure
[EIP-4399]: https://eips.ethereum.org/EIPS/eip-4399#block-structure
[EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788#block-structure-and-validity
[EIP-7685]: https://eips.ethereum.org/EIPS/eip-7685#consensus-layer
[EIP-7691]: https://eips.ethereum.org/EIPS/eip-7691#parameters
[EIP-7892]: https://eips.ethereum.org/EIPS/eip-7892#consensus-layer-configuration
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-! ## Empty payloads -/

/-- Two fields from a fork are equal when they hold equal values, or when the fork has neither. -/
local instance {f fork : Base.Fork} {α : Type} [DecidableEq α] : DecidableEq (Since f fork α) :=
  fun a b =>
    if present : f ≤ fork then
      if same : a present = b present then .isTrue (funext fun _ => same)
      else .isFalse fun eq => same (eq ▸ rfl)
    else .isTrue (funext fun later => absurd later present)

deriving instance DecidableEq for ExecutionPayloadHeader
deriving instance DecidableEq for ExecutionPayload

/-- The payload with every field zero and every list empty. -/
def ExecutionPayload.empty (preset : Preset) (fork : Base.Fork) :
    ExecutionPayload preset fork where
  parentHash := Vector.replicate 32 0
  feeRecipient := Vector.replicate 20 0
  stateRoot := Vector.replicate 32 0
  receiptsRoot := Vector.replicate 32 0
  logsBloom := Vector.replicate _ 0
  prevRandao := Vector.replicate 32 0
  blockNumber := 0
  gasLimit := 0
  gasUsed := 0
  timestamp := 0
  extraData := ⟨#[], Nat.zero_le _⟩
  baseFeePerGas := 0
  blockHash := Vector.replicate 32 0
  transactions := ⟨#[], fun _ => Nat.zero_le _⟩
  withdrawals _ := ⟨#[], fun _ => Nat.zero_le _⟩
  blobGasUsed _ := 0
  excessBlobGas _ := 0
  blockAccessList _ := ⟨#[]⟩
  slotNumber _ := 0

/-! ## The merge -/

/-- From Bellatrix: whether the state holds a payload, so the chain has passed the merge.

It holds one once its header is not the empty header. -/
def isMergeTransitionComplete (state : BeaconState preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) : Bool :=
  state.latestExecutionPayloadHeader bellatrix != .empty preset fork

/-- From Bellatrix: whether a block carries the first payload of the chain.

The state holds no payload yet, and the payload of the block is not the empty payload. -/
def isMergeTransitionBlock (state : BeaconState preset fork) (body : BeaconBlockBody preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) : Bool :=
  !isMergeTransitionComplete state bellatrix &&
    body.executionPayload bellatrix != .empty preset fork

/-- From Bellatrix: whether a block runs its payload, once the merge is complete or at its block.
-/
def isExecutionEnabled (state : BeaconState preset fork) (body : BeaconBlockBody preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) : Bool :=
  isMergeTransitionBlock state body bellatrix || isMergeTransitionComplete state bellatrix

/-! ## The execution layer -/

/-- From Electra: the request lists of a payload request, each with its type byte. -/
def NewPayloadRequest.requestsList (request : NewPayloadRequest preset fork) :
    Except Err (Since .pectra fork (List ByteArray)) :=
  if electra : .pectra ≤ fork then do
    let lists ← getExecutionRequestsList (request.executionRequests electra)
    pure fun _ => lists
  else pure fun later => absurd later electra

/-- Whether a payload holds a transaction with no bytes. -/
def ExecutionPayload.hasEmptyTransaction (payload : ExecutionPayload preset fork) : Bool :=
  payload.transactions.data.any (·.data.isEmpty)

/-- A check of a payload by the execution layer.

From Deneb it also reads the parent beacon block root, and from Electra the request lists. -/
abbrev PayloadCheck (preset : Preset) (fork : Base.Fork) :=
  ExecutionPayload preset fork → Since .dencun fork Root → Since .pectra fork (List ByteArray) →
    Bool

/-- Whether the execution layer accepts a payload request, from its three checks.

A payload with a transaction of no bytes is invalid.

The block hash of the payload must be the hash of its block, and the payload must be valid.

From Deneb, the versioned hashes must also be those of the blob transactions of the payload. -/
def verifyAndNotify (isValidBlockHash : PayloadCheck preset fork)
    (isValidVersionedHashes : NewPayloadRequest preset fork → Bool)
    (notifyNewPayload : PayloadCheck preset fork) (request : NewPayloadRequest preset fork) :
    Except Err Bool := do
  let payload := request.executionPayload
  let requests ← request.requestsList
  return !payload.hasEmptyTransaction &&
    isValidBlockHash payload request.parentBeaconBlockRoot requests &&
    (decide (fork < .dencun) || isValidVersionedHashes request) &&
    notifyNewPayload payload request.parentBeaconBlockRoot requests

/-- From Bellatrix: the execution layer, as the beacon chain sees it.

Its checks read the state of the execution layer, which the beacon chain never sees.

An execution layer may answer a payload request in its own way.

By default it answers from its three checks. -/
structure ExecutionEngine (preset : Preset) (fork : Base.Fork) where
  /-- Whether the block hash of a payload is the hash of its block. -/
  isValidBlockHash : PayloadCheck preset fork
  /-- From Deneb: whether the versioned hashes of a request are those of its blob transactions. -/
  isValidVersionedHashes : NewPayloadRequest preset fork → Bool
  /-- Whether a payload is valid on the state of the execution layer. -/
  notifyNewPayload : PayloadCheck preset fork
  /-- Whether the execution layer accepts a payload request. -/
  verifyAndNotifyNewPayload : NewPayloadRequest preset fork → Except Err Bool :=
    verifyAndNotify isValidBlockHash isValidVersionedHashes notifyNewPayload

/-- An execution layer that gives one answer to every payload request.

The test vectors use it, since they fix the answer of the execution layer. -/
def ExecutionEngine.constant (valid : Bool) : ExecutionEngine preset fork where
  isValidBlockHash _ _ _ := valid
  isValidVersionedHashes _ := valid
  notifyNewPayload _ _ _ := valid
  verifyAndNotifyNewPayload _ := .ok valid

/-! ## The payload of a block -/

/-- From Deneb: the versioned hash of a KZG commitment, as 32 bytes.

It is the version byte of KZG, then the last 31 bytes of the SHA-256 hash of the commitment. -/
def commitmentVersionedHash (commitment : Cryptography.Kzg.KZGCommitment) : VersionedHash :=
  Cryptography.Kzg.kzgCommitmentToVersionedHash ⟨commitment.toArray⟩

/-- The blob commitments of a block, of which there are none before Deneb. -/
def BeaconBlockBody.blobCommitments (body : BeaconBlockBody preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    Array Cryptography.Kzg.KZGCommitment :=
  if deneb : .dencun ≤ fork then (body.blobKzgCommitments ⟨deneb, bellatrix.2⟩).data else #[]

/-- From Deneb: the most blobs that a block may commit to, at the current epoch of a state.

Electra raises the limit, and from Fulu the blob schedule of the configuration sets it. -/
def maxBlobsPerBlock (config : Config) (state : BeaconState preset fork) : UInt64 :=
  if .fusaka ≤ fork then (config.getBlobParameters (getCurrentEpoch state)).maxBlobsPerBlock
  else if .pectra ≤ fork then config.MAX_BLOBS_PER_BLOCK_ELECTRA
  else config.MAX_BLOBS_PER_BLOCK

/-- The payload request of a block, for the execution layer.

From Deneb it holds the versioned hashes of the blobs and the parent root of the latest header.

From Electra it holds the requests of the block. -/
def BeaconBlockBody.newPayloadRequest (state : BeaconState preset fork)
    (body : BeaconBlockBody preset fork) (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    NewPayloadRequest preset fork where
  executionPayload := body.executionPayload bellatrix
  versionedHashes deneb :=
    let commitments := body.blobKzgCommitments ⟨deneb, bellatrix.2⟩
    ⟨commitments.data.map commitmentVersionedHash, by simpa using commitments.bound bellatrix.2⟩
  parentBeaconBlockRoot _ := state.latestBlockHeader.parentRoot
  executionRequests electra := body.executionRequests ⟨electra, bellatrix.2⟩

/-- From Bellatrix to Fulu: the state after the execution payload of a block.

Once the merge is complete, and always from Capella, the payload must extend the latest payload.

It must read the RANDAO mix of the current epoch, and carry the time of the slot of the state.

From Deneb, the block must commit to at most the blobs that a block may hold.

The execution layer must accept the payload request of the block.

The state then keeps the header of the payload. -/
def processExecutionPayload (config : Config) (engine : ExecutionEngine preset fork)
    (state : BeaconState preset fork) (body : BeaconBlockBody preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    Except TransitionError (BeaconState preset fork) := do
  let payload := body.executionPayload bellatrix
  let latest := state.latestExecutionPayloadHeader bellatrix
  ensure ((.shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true) →
    payload.parentHash = latest.blockHash) .wrongPayloadParentHash
  let mix ← liftAccessor (getRandaoMix state (getCurrentEpoch state))
  ensure (payload.prevRandao = mix) .wrongPayloadRandao
  let time ← liftAccessor (liftArith (computeTimeAtSlot config state.genesisTime state.slot))
  ensure (payload.timestamp = time) (.wrongPayloadTimestamp payload.timestamp time)
  let blobs := (body.blobCommitments bellatrix).size
  ensure (blobs ≤ (maxBlobsPerBlock config state).toNat) .tooManyBlobCommitments
  let valid ← liftSsz (engine.verifyAndNotifyNewPayload (body.newPayloadRequest state bellatrix))
  ensure (valid = true) .invalidExecutionPayload
  let header ← liftSsz payload.header
  return { state with latestExecutionPayloadHeader := fun _ => header }

end EthLib.Consensus
