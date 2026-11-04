module

public import EthLib.Consensus.Containers.Execution
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
public import EthLib.Serialization.Proofs.Ssz.Typed.Since
public import EthLib.Serialization.Proofs.Ssz.Type.Legality

/-!
# Proofs: the execution payload encodes as the fields of its fork

At every fork, the payload is a lawful SSZ container, so its bytes decode back to it.

Its SSZ type is the container of the fields that exist at that fork, in their order.

So its bytes and its root are those of that plain list of fields.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz SszType

instance : LawfulSszType Withdrawal :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

namespace ExecutionPayload

variable {preset : Preset} {fork : Fork}

/-- The SSZ types of the fields that exist at a fork, in their order. -/
def fieldDescs (preset : Preset) (fork : Fork) : List Desc :=
  [desc Hash32, desc ExecutionAddress, desc Bytes32, desc Bytes32,
    desc (Vector UInt8 preset.BYTES_PER_LOGS_BLOOM.toNat), desc Bytes32, desc UInt64,
    desc UInt64, desc UInt64, desc UInt64, desc (SszList UInt8 preset.MAX_EXTRA_DATA_BYTES.toNat),
    desc U256, desc Hash32,
    desc (SszList (Transaction preset) preset.MAX_TRANSACTIONS_PER_PAYLOAD.toNat)] ++
  (if .shapella ≤ fork then [desc (SszList Withdrawal preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat)]
    else []) ++
  (if .dencun ≤ fork then [desc UInt64, desc UInt64] else [])

/-- The untyped values of the fields that exist at a fork, in their order. -/
def fieldValues (payload : ExecutionPayload preset fork) : List Value :=
  [toValue payload.parentHash, toValue payload.feeRecipient, toValue payload.stateRoot,
    toValue payload.receiptsRoot, toValue payload.logsBloom, toValue payload.prevRandao,
    toValue payload.blockNumber, toValue payload.gasLimit, toValue payload.gasUsed,
    toValue payload.timestamp, toValue payload.extraData, toValue payload.baseFeePerGas,
    toValue payload.blockHash, toValue payload.transactions] ++
  (if present : .shapella ≤ fork then [toValue (payload.withdrawals present)] else []) ++
  (if present : .dencun ≤ fork then
    [toValue (payload.blobGasUsed present), toValue (payload.excessBlobGas present)] else [])

/-- At every fork, the SSZ type of a payload is the container of the fields of that fork. -/
theorem desc_eq :
    desc (ExecutionPayload preset fork) = .container (names fork) (fieldDescs preset fork) := by
  by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
    simp [desc, SszFields.descs, fieldDescs, capella, deneb]

/-- At every fork, a payload stands for the values of the fields of that fork, in their order. -/
theorem toValue_eq (payload : ExecutionPayload preset fork) :
    toValue payload = .seq (fieldValues payload) := by
  by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
    simp [toValue, SszFields.toValues, fieldValues, capella, deneb]

/-- At every fork, the bytes of a payload are those of the plain list of its fields. -/
theorem serialize_eq (payload : ExecutionPayload preset fork) :
    SszType.serialize payload = (do
      return ⟨← Serialization.Ssz.serialize (.container (names fork) (fieldDescs preset fork))
        (.seq (fieldValues payload))⟩) := by
  rw [SszType.serialize, desc_eq, toValue_eq]

/-- At every fork, the root of a payload is the root of the plain list of its fields. -/
theorem hashTreeRoot_eq (payload : ExecutionPayload preset fork) :
    SszType.hashTreeRoot payload = (do
      toChunk (← Serialization.Ssz.hashTreeRoot
        (.container (names fork) (fieldDescs preset fork)) (.seq (fieldValues payload)))) := by
  rw [SszType.hashTreeRoot, desc_eq, toValue_eq]

/-- The field names of a payload are distinct at every fork. -/
theorem names_nodup : (names fork).Nodup := by
  have all : (["parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom",
      "prev_randao", "block_number", "gas_limit", "gas_used", "timestamp", "extra_data",
      "base_fee_per_gas", "block_hash", "transactions", "withdrawals", "blob_gas_used",
      "excess_blob_gas"] : List String).Nodup := by decide
  refine all.sublist ?_
  unfold names
  exact (((List.Sublist.refl _).append (sinceNames_sublist _)).append
    (sinceNames_sublist _))

/-- At every fork, the payload is a lawful SSZ container, when its logs bloom has a byte. -/
instance [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] :
    LawfulSszType (ExecutionPayload preset fork) :=
  .container
    ⟨by
      by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
        simp [names, sinceNames, SszFields.descs, capella, deneb],
     by simp [names],
     firstDuplicate_of_nodup _ names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

/-- At every fork, the bytes of a payload decode back to it. -/
theorem deserialize_serialize [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    {payload : ExecutionPayload preset fork} {data : ByteArray}
    (wrote : SszType.serialize payload = .ok data) :
    SszType.deserialize (ExecutionPayload preset fork) data = .ok payload :=
  SszType.deserialize_serialize wrote

end ExecutionPayload

end EthLib.Consensus
