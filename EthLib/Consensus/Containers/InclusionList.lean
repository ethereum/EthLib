module

public import EthLib.Consensus.Containers.Misc

/-!
# `Consensus.Containers.InclusionList`

From Heze: the inclusion lists of [EIP-7805], which force transactions into the next payload.

In each slot a small committee of validators sends lists of transactions from the mempool.

Attesters then vote only for a payload that satisfies these lists.

EIP-7805 is a Draft on 2026-11-03, so these containers can still change.

[EIP-7805]: https://eips.ethereum.org/EIPS/eip-7805
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- From Heze: one bit for each member of an inclusion list committee, in committee order. -/
abbrev InclusionListBits (preset : Preset) :=
  Bitvector preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat

/-- From Heze: the validators of the inclusion list committee of a slot, in committee order.

A validator can hold more than one seat. -/
abbrev InclusionListCommittee (preset : Preset) :=
  Vector ValidatorIndex preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat

/-- From Heze: the transactions that one committee member asks the next payload to include.

[EIP-7805](https://eips.ethereum.org/EIPS/eip-7805#new-containers) adds it.

The EIP names its third field `inclusion_list_committee_root`, and bounds its lists.

Heze replaces that field by the root of the block that fixes the committees of the slot. -/
structure InclusionList where
  /-- The slot of the committee. -/
  slot : Slot
  /-- The committee member that sends the list. -/
  validatorIndex : ValidatorIndex
  /-- The root of the block whose state fixes the committees of the slot. -/
  dependentRoot : Root
  /-- The transactions, each as opaque bytes.

  From Gloas, neither the list nor a transaction has a limit, as EIP-7688 asks. -/
  transactions : ProgressiveList (ProgressiveList UInt8)
  deriving DecidableEq

instance : SszType InclusionList :=
  .container ["slot", "validator_index", "dependent_root", "transactions"]
    (fun l => (l.slot, l.validatorIndex, l.dependentRoot, l.transactions))
    (fun (slot, validatorIndex, dependentRoot, transactions) =>
      ⟨slot, validatorIndex, dependentRoot, transactions⟩)

/-- From Heze: an inclusion list with the signature of the member that sends it. -/
structure SignedInclusionList where
  /-- The list. -/
  message : InclusionList
  /-- The signature of the list by the member. -/
  signature : BLSSignature
  deriving DecidableEq

instance : SszType SignedInclusionList :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

end EthLib.Consensus
