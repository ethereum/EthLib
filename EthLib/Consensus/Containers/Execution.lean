module

public import EthLib.Base.Hash32
public import EthLib.Base.Fork
public import EthLib.Consensus.Preset
public import EthLib.Serialization.Ssz.Typed.Basic
public import EthLib.Serialization.Ssz.Typed.Collections
public import EthLib.Serialization.Ssz.Typed.Since

/-!
# `Consensus.Containers.Execution`

The execution payload of a beacon block from Bellatrix on, its withdrawals, and its header.

The payload is one type for every fork, and so is its header.

A field that a later fork adds holds nothing at the forks before it, and its codec skips it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- From Capella: a withdrawal of a validator's balance to an address on the execution layer. -/
structure Withdrawal where
  /-- The index of the withdrawal, counted over all withdrawals. -/
  index : WithdrawalIndex
  /-- The validator whose balance is withdrawn. -/
  validatorIndex : ValidatorIndex
  /-- The address that receives the amount. -/
  address : ExecutionAddress
  /-- The amount withdrawn. -/
  amount : Gwei
  deriving DecidableEq, Repr

instance : SszType Withdrawal :=
  .container ["index", "validator_index", "address", "amount"]
    (fun w => (w.index, w.validatorIndex, w.address, w.amount))
    (fun (index, validatorIndex, address, amount) => ⟨index, validatorIndex, address, amount⟩)

/-- From Bellatrix: a transaction of the execution layer, as opaque bytes. -/
abbrev Transaction (preset : Preset) := SszList UInt8 preset.MAX_BYTES_PER_TRANSACTION.toNat

/-- From Bellatrix: the execution block that a beacon block carries.

Capella adds the withdrawals of [EIP-4895].

Deneb adds the two fields of blob gas of [EIP-4844].

This type does not yet have the changes of Gloas, so from Glamsterdam on it keeps the shape of Fulu.

[EIP-4895]: https://eips.ethereum.org/EIPS/eip-4895#new-field-in-the-execution-payload-withdrawals
[EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844#header-extension
-/
structure ExecutionPayload (preset : Preset) (fork : Fork) where
  /-- The hash of the parent execution block. -/
  parentHash : Hash32
  /-- The address that receives the priority fees. -/
  feeRecipient : ExecutionAddress
  /-- The root of the execution state after the block. -/
  stateRoot : Bytes32
  /-- The root of the receipts of the block. -/
  receiptsRoot : Bytes32
  /-- The Bloom filter of the logs of the block. -/
  logsBloom : Vector UInt8 preset.BYTES_PER_LOGS_BLOOM.toNat
  /-- The RANDAO mix of the beacon chain that the block reads. -/
  prevRandao : Bytes32
  /-- The number of the block. -/
  blockNumber : UInt64
  /-- The gas limit of the block. -/
  gasLimit : UInt64
  /-- The gas that the block uses. -/
  gasUsed : UInt64
  /-- The time of the block, in seconds since the Unix epoch. -/
  timestamp : UInt64
  /-- Extra data of the block. -/
  extraData : SszList UInt8 preset.MAX_EXTRA_DATA_BYTES.toNat
  /-- The base fee per gas of the block. -/
  baseFeePerGas : U256
  /-- The hash of the block. -/
  blockHash : Hash32
  /-- The transactions of the block. -/
  transactions : SszList (Transaction preset) preset.MAX_TRANSACTIONS_PER_PAYLOAD.toNat
  /-- From Capella: the withdrawals that the block applies. -/
  withdrawals : Since .shapella fork (SszList Withdrawal preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat)
  /-- From Deneb: the blob gas that the transactions of the block use. -/
  blobGasUsed : Since .dencun fork UInt64
  /-- From Deneb: the blob gas above the target, summed over the blocks before this one. -/
  excessBlobGas : Since .dencun fork UInt64

namespace ExecutionPayload

variable {preset : Preset} {fork : Fork}

/-- The names of the fields of a payload at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom", "prev_randao",
    "block_number", "gas_limit", "gas_used", "timestamp", "extra_data", "base_fee_per_gas",
    "block_hash", "transactions"] ++
  sinceNames .shapella fork ["withdrawals"] ++
  sinceNames .dencun fork ["blob_gas_used", "excess_blob_gas"]

instance : SszType (ExecutionPayload preset fork) :=
  .container (names fork)
    (fun p => (p.parentHash, p.feeRecipient, p.stateRoot, p.receiptsRoot, p.logsBloom,
      p.prevRandao, p.blockNumber, p.gasLimit, p.gasUsed, p.timestamp, p.extraData,
      p.baseFeePerGas, p.blockHash, p.transactions, p.withdrawals, p.blobGasUsed,
      p.excessBlobGas))
    (fun (parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao, blockNumber,
        gasLimit, gasUsed, timestamp, extraData, baseFeePerGas, blockHash, transactions,
        withdrawals, blobGasUsed, excessBlobGas) =>
      ⟨parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao, blockNumber,
        gasLimit, gasUsed, timestamp, extraData, baseFeePerGas, blockHash, transactions,
        withdrawals, blobGasUsed, excessBlobGas⟩)

end ExecutionPayload

/-- From Bellatrix: an execution payload with each list replaced by its root.

The beacon state keeps the header of the latest payload.

The header has the root of the payload, so the state commits to the whole payload. -/
structure ExecutionPayloadHeader (preset : Preset) (fork : Fork) where
  /-- The hash of the parent execution block. -/
  parentHash : Hash32
  /-- The address that receives the priority fees. -/
  feeRecipient : ExecutionAddress
  /-- The root of the execution state after the block. -/
  stateRoot : Bytes32
  /-- The root of the receipts of the block. -/
  receiptsRoot : Bytes32
  /-- The Bloom filter of the logs of the block. -/
  logsBloom : Vector UInt8 preset.BYTES_PER_LOGS_BLOOM.toNat
  /-- The RANDAO mix of the beacon chain that the block reads. -/
  prevRandao : Bytes32
  /-- The number of the block. -/
  blockNumber : UInt64
  /-- The gas limit of the block. -/
  gasLimit : UInt64
  /-- The gas that the block uses. -/
  gasUsed : UInt64
  /-- The time of the block, in seconds since the Unix epoch. -/
  timestamp : UInt64
  /-- Extra data of the block. -/
  extraData : SszList UInt8 preset.MAX_EXTRA_DATA_BYTES.toNat
  /-- The base fee per gas of the block. -/
  baseFeePerGas : U256
  /-- The hash of the block. -/
  blockHash : Hash32
  /-- The root of the transactions of the block. -/
  transactionsRoot : Root
  /-- From Capella: the root of the withdrawals of the block. -/
  withdrawalsRoot : Since .shapella fork Root
  /-- From Deneb: the blob gas that the transactions of the block use. -/
  blobGasUsed : Since .dencun fork UInt64
  /-- From Deneb: the blob gas above the target, summed over the blocks before this one. -/
  excessBlobGas : Since .dencun fork UInt64

namespace ExecutionPayloadHeader

/-- The names of the fields of a header at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom", "prev_randao",
    "block_number", "gas_limit", "gas_used", "timestamp", "extra_data", "base_fee_per_gas",
    "block_hash", "transactions_root"] ++
  sinceNames .shapella fork ["withdrawals_root"] ++
  sinceNames .dencun fork ["blob_gas_used", "excess_blob_gas"]

instance {preset : Preset} {fork : Fork} : SszType (ExecutionPayloadHeader preset fork) :=
  .container (names fork)
    (fun h => (h.parentHash, h.feeRecipient, h.stateRoot, h.receiptsRoot, h.logsBloom,
      h.prevRandao, h.blockNumber, h.gasLimit, h.gasUsed, h.timestamp, h.extraData,
      h.baseFeePerGas, h.blockHash, h.transactionsRoot, h.withdrawalsRoot, h.blobGasUsed,
      h.excessBlobGas))
    (fun (parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao, blockNumber,
        gasLimit, gasUsed, timestamp, extraData, baseFeePerGas, blockHash, transactionsRoot,
        withdrawalsRoot, blobGasUsed, excessBlobGas) =>
      ⟨parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao, blockNumber,
        gasLimit, gasUsed, timestamp, extraData, baseFeePerGas, blockHash, transactionsRoot,
        withdrawalsRoot, blobGasUsed, excessBlobGas⟩)

end ExecutionPayloadHeader

/-- The header of a payload: its fields, with the transactions and withdrawals as their roots. -/
def ExecutionPayload.header {preset : Preset} {fork : Fork}
    (payload : ExecutionPayload preset fork) : Except Err (ExecutionPayloadHeader preset fork) := do
  let transactionsRoot ← SszType.hashTreeRoot payload.transactions
  let withdrawalsRoot : Since .shapella fork Root ←
    if present : .shapella ≤ fork then do
      let root ← SszType.hashTreeRoot (payload.withdrawals present)
      pure fun _ => root
    else pure fun later => absurd later present
  return ⟨payload.parentHash, payload.feeRecipient, payload.stateRoot, payload.receiptsRoot,
    payload.logsBloom, payload.prevRandao, payload.blockNumber, payload.gasLimit,
    payload.gasUsed, payload.timestamp, payload.extraData, payload.baseFeePerGas,
    payload.blockHash, transactionsRoot, withdrawalsRoot, payload.blobGasUsed,
    payload.excessBlobGas⟩

end EthLib.Consensus
