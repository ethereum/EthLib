module

public import EthLib.Consensus.Containers.Execution
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.ForkKind
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
public import EthLib.Serialization.Proofs.Ssz.Typed.Since
public import EthLib.Serialization.Proofs.Ssz.Type.Legality
public import EthLib.Serialization.Proofs.Ssz.Codec.RootUnfold
public import EthLib.Serialization.Proofs.Ssz.Codec.Summary

/-!
# Proofs: the execution payload encodes as the fields of its fork

At every fork, the payload is a lawful SSZ container, so its bytes decode back to it.

Its SSZ type holds the fields that exist at that fork, in their order.

Before Gloas it is a container, with the field types of Fulu, so Gloas changes nothing before it.

From Gloas it is a progressive container, whose lists have no limit.

So its bytes and its root are those of that plain list of fields.

Before Gloas, the header of a payload has the root of the payload.

Each list gives way to its own root, which leaves the root unchanged.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz SszType

instance : LawfulSszType Withdrawal :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

namespace ExecutionPayload

variable {preset : Preset} {fork : Fork}

/-- The SSZ types of the fields that exist at a fork, in their order.

Before Gloas the lists have the limits of the preset, and from Gloas they are progressive. -/
def fieldDescs (preset : Preset) (fork : Fork) : List Desc :=
  [desc Hash32, desc ExecutionAddress, desc Bytes32, desc Bytes32,
    desc (Vector UInt8 preset.BYTES_PER_LOGS_BLOOM.toNat), desc Bytes32, desc UInt64,
    desc UInt64, desc UInt64, desc UInt64, desc (SszList UInt8 preset.MAX_EXTRA_DATA_BYTES.toNat),
    desc U256, desc Hash32,
    if .glamsterdam ≤ fork then desc (ProgressiveList (ProgressiveList UInt8))
    else desc (SszList (SszList UInt8 preset.MAX_BYTES_PER_TRANSACTION.toNat)
      preset.MAX_TRANSACTIONS_PER_PAYLOAD.toNat)] ++
  (if .shapella ≤ fork then
    [if .glamsterdam ≤ fork then desc (ProgressiveList Withdrawal)
      else desc (SszList Withdrawal preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat)]
    else []) ++
  (if .dencun ≤ fork then [desc UInt64, desc UInt64] else []) ++
  (if .glamsterdam ≤ fork then [desc BlockAccessList, desc UInt64] else [])

/-- The untyped values of the fields that exist at a fork, in their order. -/
def fieldValues (payload : ExecutionPayload preset fork) : List Value :=
  [toValue payload.parentHash, toValue payload.feeRecipient, toValue payload.stateRoot,
    toValue payload.receiptsRoot, toValue payload.logsBloom, toValue payload.prevRandao,
    toValue payload.blockNumber, toValue payload.gasLimit, toValue payload.gasUsed,
    toValue payload.timestamp, toValue payload.extraData, toValue payload.baseFeePerGas,
    toValue payload.blockHash, toValue payload.transactions] ++
  (if present : .shapella ≤ fork then [toValue (payload.withdrawals present)] else []) ++
  (if present : .dencun ≤ fork then
    [toValue (payload.blobGasUsed present), toValue (payload.excessBlobGas present)] else []) ++
  (if present : .glamsterdam ≤ fork then
    [toValue (payload.blockAccessList present), toValue (payload.slotNumber present)] else [])

/-- The SSZ type of a payload at a fork: the container of its fields, progressive from Gloas. -/
def fieldsDesc (preset : Preset) (fork : Fork) : Desc :=
  if .glamsterdam ≤ fork then
    .progressiveContainer activeFields (names fork) (fieldDescs preset fork)
  else .container (names fork) (fieldDescs preset fork)

/-- Before Gloas, the SSZ type of a payload is the container of the fields of that fork. -/
theorem fieldsDesc_of_lt (before : fork < .glamsterdam) :
    fieldsDesc preset fork = .container (names fork) (fieldDescs preset fork) := by
  simp [fieldsDesc, not_switch_of_lt before]

/-- At every fork, the SSZ type of a payload is the type of the fields of that fork. -/
theorem desc_eq : desc (ExecutionPayload preset fork) = fieldsDesc preset fork := by
  unfold desc instSszType SszType.forkContainer
  by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
    by_cases gloas : Fork.glamsterdam ≤ fork <;>
    simp [desc, SszType.progressiveContainer, SszType.container, SszFields.descs, fieldDescs,
      fieldsDesc, capella, deneb,
      gloas]

/-- At every fork, a payload stands for the values of the fields of that fork, in their order. -/
theorem toValue_eq (payload : ExecutionPayload preset fork) :
    toValue payload = .seq (fieldValues payload) := by
  unfold toValue instSszType SszType.forkContainer
  by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
    by_cases gloas : Fork.glamsterdam ≤ fork <;>
    simp [toValue, SszType.progressiveContainer, SszType.container, SszFields.toValues,
      fieldValues, capella, deneb, gloas]

/-- At every fork, the bytes of a payload are those of the plain list of its fields. -/
theorem serialize_eq (payload : ExecutionPayload preset fork) :
    SszType.serialize payload = (do
      return ⟨← Serialization.Ssz.serialize (fieldsDesc preset fork)
        (.seq (fieldValues payload))⟩) := by
  rw [SszType.serialize, desc_eq, toValue_eq]

/-- At every fork, the root of a payload is the root of the plain list of its fields. -/
theorem hashTreeRoot_eq (payload : ExecutionPayload preset fork) :
    SszType.hashTreeRoot payload = (do
      toChunk (← Serialization.Ssz.hashTreeRoot (fieldsDesc preset fork)
        (.seq (fieldValues payload)))) := by
  rw [SszType.hashTreeRoot, desc_eq, toValue_eq]

/-- The field names of a payload are distinct at every fork. -/
theorem names_nodup : (names fork).Nodup := by
  have all : (["parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom",
      "prev_randao", "block_number", "gas_limit", "gas_used", "timestamp", "extra_data",
      "base_fee_per_gas", "block_hash", "transactions", "withdrawals", "blob_gas_used",
      "excess_blob_gas", "block_access_list", "slot_number"] : List String).Nodup := by decide
  refine all.sublist ?_
  unfold names
  exact ((((List.Sublist.refl _).append (sinceNames_sublist _)).append
    (sinceNames_sublist _)).append (sinceNames_sublist _))

/-- At every fork, the payload is a lawful SSZ container, when its logs bloom has a byte. -/
instance [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] :
    LawfulSszType (ExecutionPayload preset fork) :=
  .forkContainer
    (fun gloas => by
      have deneb : Fork.dencun ≤ fork := Nat.le_trans (by decide) gloas
      have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) gloas
      exact ⟨rfl, by decide, by simp [activeFields, SszFields.descs, capella, deneb, gloas]⟩)
    ⟨by
      by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
        by_cases gloas : Fork.glamsterdam ≤ fork <;>
        simp [names, sinceNames, SszFields.descs, capella, deneb, gloas],
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

namespace ExecutionPayloadHeader

variable {preset : Preset} {fork : Fork}

/-- The field names of a header are distinct at every fork. -/
theorem names_nodup : (names fork).Nodup := by
  have all : (["parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom",
      "prev_randao", "block_number", "gas_limit", "gas_used", "timestamp", "extra_data",
      "base_fee_per_gas", "block_hash", "transactions_root", "withdrawals_root",
      "blob_gas_used", "excess_blob_gas"] : List String).Nodup := by decide
  refine all.sublist ?_
  unfold names
  exact (((List.Sublist.refl _).append (sinceNames_sublist _)).append
    (sinceNames_sublist _))

/-- At every fork, the header is a lawful SSZ container, when its logs bloom has a byte. -/
instance [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] :
    LawfulSszType (ExecutionPayloadHeader preset fork) :=
  .container
    ⟨by
      by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
        simp [names, sinceNames, SszFields.descs, capella, deneb],
     by simp [names],
     firstDuplicate_of_nodup _ names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

end ExecutionPayloadHeader

/-- Before Gloas, the transactions have the SSZ type of Fulu: lists of bytes, with limits. -/
theorem desc_transactions_of_lt {preset : Preset} {fork : Fork} (before : fork < .glamsterdam) :
    desc (Transactions preset fork) =
      desc (SszList (SszList UInt8 preset.MAX_BYTES_PER_TRANSACTION.toNat)
        preset.MAX_TRANSACTIONS_PER_PAYLOAD.toNat) := by
  rw [desc_forkList before]
  show Desc.list (desc (Transaction preset fork)) _ = Desc.list (desc (SszList UInt8 _)) _
  rw [desc_forkList_uint8 before]

/-- Before Gloas, the withdrawals have the SSZ type of Fulu: a list with a limit. -/
theorem desc_withdrawals_of_lt {preset : Preset} {fork : Fork} (before : fork < .glamsterdam) :
    desc (Withdrawals preset fork) =
      desc (SszList Withdrawal preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat) :=
  desc_forkList before

/-- At every fork, every payload has a header. -/
theorem ExecutionPayload.header_total {preset : Preset} {fork : Fork}
    (payload : ExecutionPayload preset fork) : ∃ header, payload.header = .ok header := by
  obtain ⟨txRoot, tx⟩ := SszType.hashTreeRoot_total payload.transactions
  by_cases capella : Fork.shapella ≤ fork
  · obtain ⟨wRoot, w⟩ := SszType.hashTreeRoot_total (payload.withdrawals capella)
    simp [ExecutionPayload.header, tx, w, capella, bind, Except.bind, pure, Except.pure]
  · simp [ExecutionPayload.header, tx, capella, bind, Except.bind, pure, Except.pure]

/-- Before Gloas, the header of a payload has the root of the payload.

Each list of the payload gives way to its root, which leaves the root of the payload unchanged. -/
theorem ExecutionPayload.hashTreeRoot_header {preset : Preset} {fork : Fork}
    (before : fork < .glamsterdam)
    {payload : ExecutionPayload preset fork} {header : ExecutionPayloadHeader preset fork}
    (made : payload.header = .ok header) :
    SszType.hashTreeRoot header = SszType.hashTreeRoot payload := by
  have gloas : ¬Fork.glamsterdam ≤ fork := not_switch_of_lt before
  obtain ⟨txRoot, tx⟩ : ∃ r, SszType.hashTreeRoot payload.transactions = .ok r := by
    cases h : SszType.hashTreeRoot payload.transactions with
    | error e => simp [ExecutionPayload.header, h, bind, Except.bind] at made
    | ok r => exact ⟨r, rfl⟩
  -- The transactions sit at position 13, and from Capella the withdrawals at position 14.
  by_cases capella : Fork.shapella ≤ fork
  · obtain ⟨wRoot, w⟩ : ∃ r, SszType.hashTreeRoot (payload.withdrawals capella) = .ok r := by
      cases h : SszType.hashTreeRoot (payload.withdrawals capella) with
      | error e => simp [ExecutionPayload.header, tx, h, capella, bind, Except.bind] at made
      | ok r => exact ⟨r, rfl⟩
    simp [ExecutionPayload.header, tx, w, capella, bind, Except.bind, pure, Except.pure] at made
    subst made
    rw [SszType.hashTreeRoot_ok_iff] at tx w
    simp only [SszType.hashTreeRoot]
    rw [ExecutionPayload.desc_eq, ExecutionPayload.fieldsDesc_of_lt before,
      ExecutionPayload.toValue_eq]
    have one := hashTreeRoot_summary (names := ExecutionPayload.names fork) (position := 13)
      (fields := ExecutionPayload.fieldDescs preset fork)
      (values := ExecutionPayload.fieldValues payload)
      (by by_cases deneb : Fork.dencun ≤ fork <;>
        simp [ExecutionPayload.fieldDescs, ExecutionPayload.fieldValues, capella, deneb,
          gloas])
      (by simpa [ExecutionPayload.fieldDescs, gloas] using
        (desc_transactions_of_lt before).symm) (by simp [ExecutionPayload.fieldValues]) tx
    have two := hashTreeRoot_summary (names := ExecutionPayload.names fork) (position := 14)
      (fields := (ExecutionPayload.fieldDescs preset fork).set 13 (.byteVector bytesPerChunk))
      (values := (ExecutionPayload.fieldValues payload).set 13 (.bytes txRoot.toArray))
      (by by_cases deneb : Fork.dencun ≤ fork <;>
        simp [ExecutionPayload.fieldDescs, ExecutionPayload.fieldValues, capella, deneb,
          gloas])
      (by simpa [ExecutionPayload.fieldDescs, capella, gloas] using
        (desc_withdrawals_of_lt before).symm)
      (by simp [ExecutionPayload.fieldValues, capella]) w
    rw [← one, ← two, hashTreeRoot_container_names (ExecutionPayload.names fork)
      (ExecutionPayloadHeader.names fork)]
    by_cases deneb : Fork.dencun ≤ fork <;>
      simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues,
        ExecutionPayload.fieldDescs, ExecutionPayload.fieldValues, capella, deneb,
          gloas]
  · have deneb : ¬Fork.dencun ≤ fork := fun later => capella (Nat.le_trans (by decide) later)
    simp [ExecutionPayload.header, tx, capella, bind, Except.bind, pure, Except.pure] at made
    subst made
    rw [SszType.hashTreeRoot_ok_iff] at tx
    simp only [SszType.hashTreeRoot]
    rw [ExecutionPayload.desc_eq, ExecutionPayload.fieldsDesc_of_lt before,
      ExecutionPayload.toValue_eq]
    have one := hashTreeRoot_summary (names := ExecutionPayload.names fork) (position := 13)
      (fields := ExecutionPayload.fieldDescs preset fork)
      (values := ExecutionPayload.fieldValues payload)
      (by simp [ExecutionPayload.fieldDescs, ExecutionPayload.fieldValues, capella, deneb,
          gloas])
      (by simpa [ExecutionPayload.fieldDescs, gloas] using
        (desc_transactions_of_lt before).symm) (by simp [ExecutionPayload.fieldValues]) tx
    rw [← one, hashTreeRoot_container_names (ExecutionPayload.names fork)
      (ExecutionPayloadHeader.names fork)]
    simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues,
      ExecutionPayload.fieldDescs, ExecutionPayload.fieldValues, capella, deneb,
          gloas]

end EthLib.Consensus
