module

public import EthLib.Engine.Payload
public import EthLib.Execution.Blocks.Requests
public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Blocks.Validate
public import EthLib.Execution.Transactions.Envelope

/-!
# `Engine.Block`

The execution block of a payload, and the payload of a block.

The header takes most fields of the payload as they are.

[EIP-3675][eip-3675] fixes the ommers hash to the hash of the empty list from Paris.

It also fixes the difficulty and the nonce to zero.

[EIP-4399][eip-4399] puts the RANDAO mix of the payload in the mix digest.

The header commits to the lists of the payload by their roots.

From Dencun, the method passes the parent beacon block root beside the payload.

From Pectra, it passes the request lists, and the header holds their requests hash.

The block hash of the payload must be the hash of that header.

Step 2 of [`engine_newPayloadV1`][v1] states the check.

Step 2 of [`engine_newPayloadV4`][v4] adds the requests to it.

The conversions hold up to BPO5, since Glamsterdam adds fields to the header.

[eip-3675]: https://eips.ethereum.org/EIPS/eip-3675#block-structure
[eip-4399]: https://eips.ethereum.org/EIPS/eip-4399#block-structure
[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#specification
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#specification
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions

variable {fork : Fork}

/-- A field from fork `f` on, computed by a step that may fail, only when the fork has the field. -/
def sinceM {ε α : Type} {f : Fork} (g : f ≤ fork → Except ε α) : Except ε (Since f fork α) :=
  if h : f ≤ fork then (fun a _ => a) <$> g h else pure fun h' => absurd h' h

/-- The requests hash of request lists, as the 32 bytes of a header field. -/
def requestsCommitment (requests : List ByteArray) : Hash32 :=
  Vector.ofFn fun i => (requestsHash requests)[i.val]!

/-- Transactions decoded at the fork, in order, the first one at an index from 0. -/
def decodeTransactions (fork : Fork) (index : Nat) :
    List ByteArray → Except PayloadError (List Transaction)
  | [] => pure []
  | bytes :: rest => do
    let tx ← (decodeTransaction fork bytes).mapError (.invalidTransaction index)
    return tx :: (← decodeTransactions fork (index + 1) rest)

namespace ExecutionPayload

/-- The header of a payload.

The transactions root and the method's parameters are inputs. -/
def toHeader (p : ExecutionPayload fork) (transactionsRoot : Hash32)
    (parentBeaconBlockRoot : Since .dencun fork Hash32)
    (requests : Since .pectra fork (List ByteArray)) (hFork : fork < .glamsterdam) :
    Except PayloadError (Header fork) := do
  let withdrawalsRoot ← sinceM fun h =>
    (Execution.Blocks.withdrawalsRoot (p.withdrawals h)).mapError fun _ => .noEncoding
  return {
    parentHash := p.parentHash
    ommersHash := EMPTY_OMMER_HASH
    coinbase := p.feeRecipient
    stateRoot := p.stateRoot
    transactionsRoot
    receiptRoot := p.receiptsRoot
    bloom := p.logsBloom
    difficulty := 0
    number := p.blockNumber.toNat
    gasLimit := p.gasLimit.toNat
    gasUsed := p.gasUsed.toNat
    timestamp := BitVec.ofNat 256 p.timestamp.toNat
    extraData := p.extraData
    prevRandao := p.prevRandao
    nonce := Vector.replicate 8 0
    baseFeePerGas := fun _ => p.baseFeePerGas.toNat
    withdrawalsRoot
    blobGasUsed := p.blobGasUsed
    excessBlobGas := p.excessBlobGas
    parentBeaconBlockRoot
    requestsHash := fun h => requestsCommitment (requests h)
    blockAccessListHash := fun h => absurd (Nat.lt_of_lt_of_le hFork h) (Nat.lt_irrefl _)
    slotNumber := fun h => absurd (Nat.lt_of_lt_of_le hFork h) (Nat.lt_irrefl _) }

/-- The block of a payload, before the check of its block hash.

Each transaction must decode at the fork, and the block has no ommers. -/
def toBlockUnchecked (p : ExecutionPayload fork) (parentBeaconBlockRoot : Since .dencun fork Hash32)
    (requests : Since .pectra fork (List ByteArray)) (hFork : fork < .glamsterdam) :
    Except PayloadError (Block fork Transaction) := do
  let transactions ← decodeTransactions fork 0 p.transactions
  let root ← (indexedRoot p.transactions).mapError fun _ => .noEncoding
  let header ← p.toHeader root parentBeaconBlockRoot requests hFork
  return ⟨header, transactions, [], p.withdrawals⟩

/-- Check that the block hash of a payload is the hash of a header. -/
def checkBlockHash (p : ExecutionPayload fork) (header : Header fork) :
    Except PayloadError Unit := do
  let computed ← header.hash.mapError fun _ => .noEncoding
  if computed = p.blockHash then pure () else throw (.wrongBlockHash p.blockHash computed)

/-- The block of a payload, whose block hash must be the hash of its header. -/
def toBlock (p : ExecutionPayload fork) (parentBeaconBlockRoot : Since .dencun fork Hash32)
    (requests : Since .pectra fork (List ByteArray)) (hFork : fork < .glamsterdam) :
    Except PayloadError (Block fork Transaction) := do
  let block ← p.toBlockUnchecked parentBeaconBlockRoot requests hFork
  p.checkBlockHash block.header
  return block

/-- The payload of a block from Paris on, with the hash of its header.

It has none when a transaction or the header has no encoding.

It also has none when a number does not fit its field in the payload. -/
def ofBlock (hParis : .paris ≤ fork) (b : Block fork Transaction) :
    Option (ExecutionPayload fork) := do
  let h := b.header
  let baseFee := h.baseFeePerGas (Nat.le_trans (by decide) hParis)
  let transactions ← (b.transactions.mapM encodeTransaction).toOption
  let blockHash ← h.hash.toOption
  if h.number < 2 ^ 64 ∧ h.gasLimit < 2 ^ 64 ∧ h.gasUsed < 2 ^ 64 ∧
      h.timestamp.toNat < 2 ^ 64 ∧ baseFee < 2 ^ 256 then
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
  transactions.flatMap fun
    | .blob tx => tx.blobVersionedHashes
    | _ => []

end ExecutionPayload

end EthLib.Engine
