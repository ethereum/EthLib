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

[EIP-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#block-structure
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
  -- The latest payload header differs from the header whose fields are all zero or empty.
  state.latestExecutionPayloadHeader bellatrix != .empty preset fork

/-- From Bellatrix: whether a block carries the first payload of the chain. -/
def isMergeTransitionBlock (state : BeaconState preset fork) (body : BeaconBlockBody preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) : Bool :=
  -- The state holds no payload yet, and the payload of the block is not the empty payload.
  !isMergeTransitionComplete state bellatrix &&
    body.executionPayload bellatrix != .empty preset fork

/-- From Bellatrix: whether a block runs its payload, once the merge is complete or at its block.
-/
def isExecutionEnabled (state : BeaconState preset fork) (body : BeaconBlockBody preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) : Bool :=
  -- The block is the merge block, or the state already holds a payload.
  isMergeTransitionBlock state body bellatrix || isMergeTransitionComplete state bellatrix

/-! ## The execution layer -/

/-- From Electra: the request lists of a payload request, each with its type byte. -/
def NewPayloadRequest.requestsList (request : NewPayloadRequest preset fork) :
    Except Err (Since .pectra fork (List ByteArray)) :=
  -- EIP-7685: each nonempty list of requests, as its type byte then its data.
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

/-- Whether the execution layer accepts a payload request, from its three checks. -/
def verifyAndNotify (isValidBlockHash : PayloadCheck preset fork)
    (isValidVersionedHashes : NewPayloadRequest preset fork → Bool)
    (notifyNewPayload : PayloadCheck preset fork) (request : NewPayloadRequest preset fork) :
    Except Err Bool := do
  let payload := request.executionPayload
  let requests ← request.requestsList
  -- A payload with a transaction of no bytes is invalid.
  --
  -- The block hash of the payload is the hash of its block.
  --
  -- From Deneb, the versioned hashes are those of the blob transactions of the payload.
  --
  -- The payload is valid on the state of the execution layer.
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
  Cryptography.Kzg.kzgCommitmentToVersionedHash commitment

/-- The blob commitments of a block, of which there are none before Deneb. -/
def BeaconBlockBody.blobCommitments (body : BeaconBlockBody preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    Array Cryptography.Kzg.KZGCommitment :=
  -- From Deneb the commitments of the body, before it none.
  if deneb : .dencun ≤ fork then (body.blobKzgCommitments ⟨deneb, bellatrix.2⟩).data else #[]

/-- From Deneb: the most blobs that a block may commit to, at the current epoch of a state. -/
def maxBlobsPerBlock (config : Config) (state : BeaconState preset fork) : UInt64 :=
  -- From Fulu the blob schedule sets it for the epoch, as EIP-7892 specifies.
  if .fusaka ≤ fork then (config.getBlobParameters (getCurrentEpoch state)).maxBlobsPerBlock
  -- Electra raises it, as EIP-7691 specifies.
  else if .pectra ≤ fork then config.MAX_BLOBS_PER_BLOCK_ELECTRA
  -- Deneb sets `MAX_BLOBS_PER_BLOCK`.
  else config.MAX_BLOBS_PER_BLOCK

/-- The payload request of a block, for the execution layer. -/
def BeaconBlockBody.newPayloadRequest (state : BeaconState preset fork)
    (body : BeaconBlockBody preset fork) (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    NewPayloadRequest preset fork where
  executionPayload := body.executionPayload bellatrix
  -- From Deneb, the versioned hash of each blob commitment, in order.
  versionedHashes deneb :=
    let commitments := body.blobKzgCommitments ⟨deneb, bellatrix.2⟩
    ⟨commitments.data.map commitmentVersionedHash, by simpa using commitments.bound bellatrix.2⟩
  -- From Deneb, the parent root of the latest block header, as EIP-4788 asks.
  --
  -- The header is that of this block, so the root is that of its parent.
  parentBeaconBlockRoot _ := state.latestBlockHeader.parentRoot
  -- From Electra, the requests of the block.
  executionRequests electra := body.executionRequests ⟨electra, bellatrix.2⟩

/-- From Bellatrix to Fulu: the state after the execution payload of a block. -/
def processExecutionPayload (config : Config) (engine : ExecutionEngine preset fork)
    (state : BeaconState preset fork) (body : BeaconBlockBody preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    Except TransitionError (BeaconState preset fork) := do
  let payload := body.executionPayload bellatrix
  let latest := state.latestExecutionPayloadHeader bellatrix
  -- Once the merge is complete, and always from Capella, the payload extends the latest payload.
  --
  -- Its parent hash is the block hash of the latest payload header.
  ensure ((.shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true) →
    payload.parentHash = latest.blockHash)
    (.wrongPayloadParentHash payload.parentHash latest.blockHash)
  -- EIP-4399: its previous RANDAO is the latest RANDAO mix before the reveal of this block.
  --
  -- That is the mix of the current epoch, since the reveal of this block runs later.
  let mix ← liftAccessor (getRandaoMix state (getCurrentEpoch state))
  ensure (payload.prevRandao = mix) (.wrongPayloadRandao payload.prevRandao mix)
  -- Its timestamp is the time of the slot of the state.
  let time ← liftAccessor (liftArith (computeTimeAtSlot config state.genesisTime state.slot))
  ensure (payload.timestamp = time) (.wrongPayloadTimestamp payload.timestamp time)
  -- From Deneb the block commits to at most the blobs that a block may hold.
  let blobs := (body.blobCommitments bellatrix).size
  ensure (blobs ≤ (maxBlobsPerBlock config state).toNat)
    (.tooManyBlobCommitments blobs (maxBlobsPerBlock config state).toNat)
  -- The execution layer accepts the payload request of the block.
  let valid ← liftSsz (engine.verifyAndNotifyNewPayload (body.newPayloadRequest state bellatrix))
  ensure (valid = true) (.invalidExecutionPayload payload.blockHash)
  -- The state keeps the header of the payload.
  let header ← liftSsz payload.header
  return { state with latestExecutionPayloadHeader := fun _ => header }

end EthLib.Consensus
