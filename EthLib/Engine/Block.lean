module

public import EthLib.Engine.Payload
public import EthLib.Execution.Blocks.BlockAccessList
public import EthLib.Execution.Blocks.Requests
public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Blocks.Validate
public import EthLib.Execution.Transactions.Envelope

/-!
# `Engine.Block`

The execution block of a payload, and the payload of a block.

The block hash of a payload is checked by step 2 of [`engine_newPayloadV1`][v1].

Step 2 of [`engine_newPayloadV4`][v4] adds the commitment to the requests to it.

Step 3 of [`engine_newPayloadV5`][v5] requires the RLP encoding of a block access list.

The blob hashes follow step 3 of [`engine_newPayloadV3`][v3].

A step comment names the version of the method, as in version 3, step 3.

The header takes the constants of [EIP-3675][eip-3675] and the mix digest of [EIP-4399][eip-4399].

From Glamsterdam, it takes the fields of [EIP-7928][eip-7928] and [EIP-7843][eip-7843].

[eip-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#block-structure
[eip-4399]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-4399.md#block-structure
[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#specification
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#specification
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#specification
[v5]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#specification
[eip-7928]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7928.md#engine-api
[eip-7843]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7843.md#header-extension
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

variable {fork : Fork}

/-- A field from fork `f` on, computed by a step that may fail, only when the fork has the field. -/
def sinceM {ε α : Type} {f : Fork} (g : f ≤ fork → Except ε α) : Except ε (Since f fork α) :=
  if h : f ≤ fork then (fun a _ => a) <$> g h else pure fun h' => absurd h' h

/-- Transactions decoded at the fork, in order, the first one at an index from 0. -/
def decodeTransactions (fork : Fork) (index : Nat) :
    List ByteArray → Except PayloadError (List Transaction)
  | [] => pure []
  | bytes :: rest => do
    -- Each transaction decodes at the fork, or the payload is invalid at its index.
    let tx ← (decodeTransaction fork bytes).mapError (.invalidTransaction index)
    return tx :: (← decodeTransactions fork (index + 1) rest)

namespace ExecutionPayload

/-- The header of a payload.

The transactions root, the hash of the block access list and the method's parameters are inputs.
-/
def toHeader (p : ExecutionPayload fork) (transactionsRoot : Hash32)
    (parentBeaconBlockRoot : Since .dencun fork Hash32)
    (requests : Since .pectra fork (List ByteArray))
    (blockAccessListHash : Since .glamsterdam fork Hash32)
    (slotNumber : Since .glamsterdam fork UInt64) :
    Except PayloadError (Header fork) := do
  -- EIP-4895: from Shapella, the trie root of the withdrawals of the payload.
  let withdrawalsRoot ← sinceM fun h =>
    (Execution.Blocks.withdrawalsRoot (p.withdrawals h)).mapError fun _ => .noEncoding
  -- Version 1, step 2: `ExecutionBlockHeader`, with the payload's values and the constants.
  --
  -- A field of the payload enters as it is, under the name of the header.
  return {
    parentHash := p.parentHash
    -- EIP-3675: the ommers hash is `Keccak256(RLP([]))`.
    ommersHash := EMPTY_OMMER_HASH
    coinbase := p.feeRecipient
    stateRoot := p.stateRoot
    -- The trie root of the transactions of the payload.
    transactionsRoot
    receiptRoot := p.receiptsRoot
    bloom := p.logsBloom
    -- EIP-3675: the difficulty is `0`.
    difficulty := 0
    number := p.blockNumber.toNat
    gasLimit := p.gasLimit.toNat
    gasUsed := p.gasUsed.toNat
    timestamp := BitVec.ofNat 256 p.timestamp.toNat
    extraData := p.extraData
    -- EIP-4399: the mix hash holds the RANDAO mix of the payload, in place of the zero of EIP-3675.
    prevRandao := p.prevRandao
    -- EIP-3675: the nonce is `0x0000000000000000`.
    nonce := Vector.replicate 8 0
    baseFeePerGas := fun _ => p.baseFeePerGas.toNat
    withdrawalsRoot
    -- EIP-4844: from Dencun, the blob gas used and the excess blob gas of the payload.
    blobGasUsed := p.blobGasUsed
    excessBlobGas := p.excessBlobGas
    -- From Dencun, version 3 passes the parent beacon block root beside the payload.
    parentBeaconBlockRoot
    -- Version 4, step 2: from Pectra, the commitment of EIP-7685 to the request lists.
    --
    -- A wrong commitment then fails the check of the block hash.
    requestsHash := fun h => requestsHash (requests h)
    -- EIP-7928: from Glamsterdam, the hash of the block access list.
    blockAccessListHash
    -- EIP-7843: from Glamsterdam, the slot number of the payload.
    slotNumber }

/-- The hash of a block access list, which must be the RLP encoding of one. -/
def blockAccessListHashOf (bytes : ByteArray) : Except PayloadError Hash32 :=
  match (Serialization.Rlp.Codec.decode bytes : Except _ BlockAccessList) with
  -- EIP-7928: the header holds the Keccak-256 hash of the bytes as given.
  --
  -- Whether the list matches the execution of the block is a check of the state transition.
  | .ok _ => .ok (keccak256 bytes)
  -- Version 5, step 3: bytes that are not the RLP encoding of a block access list are `INVALID`.
  | .error _ => .error .invalidBlockAccessList

/-- The block of a payload, before the check of its block hash. -/
def toBlockUnchecked (p : ExecutionPayload fork) (parentBeaconBlockRoot : Since .dencun fork Hash32)
    (requests : Since .pectra fork (List ByteArray))
    (blockAccessList : Since .glamsterdam fork ByteArray)
    (slotNumber : Since .glamsterdam fork UInt64) :
    Except PayloadError (Block fork Transaction) := do
  -- Version 1, step 1: each transaction has at least 1 byte, and an empty one does not decode.
  --
  -- Step 6: an invalid entry is `INVALID` too, so each transaction decodes at the fork.
  let transactions ← decodeTransactions fork 0 p.transactions
  -- Yellow Paper §4.4.2: `H_t` is the trie root of the bytes of each transaction, as given.
  let root ← (indexedRoot p.transactions).mapError fun _ => .noEncoding
  -- Version 5, step 3, from Glamsterdam: the list decodes, and its hash enters the header.
  --
  -- It runs before the block hash check of version 1, step 2, since the header needs that hash.
  let accessListHash ← sinceM fun h => blockAccessListHashOf (blockAccessList h)
  let header ← p.toHeader root parentBeaconBlockRoot requests accessListHash slotNumber
  -- EIP-3675: the block has no ommers, `[]`.
  return ⟨header, transactions, [], p.withdrawals⟩

/-- Check that the block hash of a payload is the hash of a header. -/
def checkBlockHash (p : ExecutionPayload fork) (header : Header fork) :
    Except PayloadError Unit := do
  -- Version 1, step 2: the hash is `Keccak256(RLP(ExecutionBlockHeader))`.
  --
  -- A header without an RLP encoding makes the payload invalid.
  let computed ← header.hash.mapError fun _ => .noEncoding
  -- Step 2: the block hash of the payload equals that hash, or the payload fails the check.
  if computed = p.blockHash then pure () else throw (.wrongBlockHash p.blockHash computed)

/-- The block of a payload, whose block hash must be the hash of its header. -/
def toBlock (p : ExecutionPayload fork) (parentBeaconBlockRoot : Since .dencun fork Hash32)
    (requests : Since .pectra fork (List ByteArray))
    (blockAccessList : Since .glamsterdam fork ByteArray)
    (slotNumber : Since .glamsterdam fork UInt64) :
    Except PayloadError (Block fork Transaction) := do
  -- Version 1, step 1, and version 5, step 3, then version 1, step 2.
  let block ← p.toBlockUnchecked parentBeaconBlockRoot requests blockAccessList slotNumber
  p.checkBlockHash block.header
  return block

/-- The payload of a block from Paris on, with the hash of its header. -/
def ofBlock (hParis : .paris ≤ fork) (b : Block fork Transaction) :
    Option (ExecutionPayload fork) := do
  let h := b.header
  let baseFee := h.baseFeePerGas (Nat.le_trans (by decide) hParis)
  -- EIP-2718: each transaction as its bytes, or none when one has no encoding.
  let transactions ← (b.transactions.mapM encodeTransaction).toOption
  -- `Keccak256(RLP(ExecutionBlockHeader))`, or none when the header has no encoding.
  let blockHash ← h.hash.toOption
  -- `ExecutionPayloadV1`: the number, the gas limit, the gas used and the timestamp have 64 bits.
  --
  -- The base fee is a 256-bit quantity, and a number that does not fit gives none.
  if h.number < 2 ^ 64 ∧ h.gasLimit < 2 ^ 64 ∧ h.gasUsed < 2 ^ 64 ∧
      h.timestamp.toNat < 2 ^ 64 ∧ baseFee < 2 ^ 256 then
    -- The fields of the header, back under the names of the payload.
    return {
      parentHash := h.parentHash
      feeRecipient := h.coinbase
      stateRoot := h.stateRoot
      receiptsRoot := h.receiptRoot
      logsBloom := h.bloom
      prevRandao := h.prevRandao
      blockNumber := h.number.toUInt64
      gasLimit := h.gasLimit.toUInt64
      gasUsed := h.gasUsed.toUInt64
      timestamp := h.timestamp.toNat.toUInt64
      extraData := h.extraData
      baseFeePerGas := BitVec.ofNat 256 baseFee
      blockHash
      transactions
      withdrawals := b.withdrawals
      blobGasUsed := h.blobGasUsed
      excessBlobGas := h.excessBlobGas }
  else none

/-- The versioned hashes of the blob transactions of a list, in order. -/
def blobVersionedHashes (transactions : List Transaction) : List Bytes32 :=
  -- Version 3, step 3.1: the versioned hashes of each blob transaction, in the order of inclusion.
  transactions.flatMap fun
    | .blob tx => tx.blobVersionedHashes
    -- Another transaction adds none, so without blob transactions the actual array is `[]`.
    --
    -- Step 3.1 requires the expected array to be `[]` then, and step 3.2 enforces it.
    | _ => []

end ExecutionPayload

end EthLib.Engine
