module

public import EthLib.Consensus.Containers.Misc

/-!
# `Consensus.Containers.ProposerPreferences`

From Gloas: the preferences that a proposer sends to builders before its slot.

A proposer names the address that receives the payment of the builder, and a target gas limit.

Builders read these preferences to bid for the slot.

Gossip forwards no bid for a slot whose proposer sent no preferences.

The preferences also name the block whose state fixes the proposer of the slot.

[EIP-7732] adds these containers; on 2026-11-03 the EIP was in Last Call.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#p2p-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- The fee recipient and the target gas limit that a proposer asks for at a slot. -/
structure ProposerPreferences where
  /-- The root of the block whose state fixes the proposer of the slot. -/
  dependentRoot : Root
  /-- The slot of the proposal. -/
  proposalSlot : Slot
  /-- The proposer. -/
  validatorIndex : ValidatorIndex
  /-- The address that receives the payment of the builder. -/
  feeRecipient : ExecutionAddress
  /-- The gas limit that the proposer asks the payload to move toward. -/
  targetGasLimit : UInt64
  deriving DecidableEq

instance : SszType ProposerPreferences :=
  .container
    ["dependent_root", "proposal_slot", "validator_index", "fee_recipient", "target_gas_limit"]
    (fun p => (p.dependentRoot, p.proposalSlot, p.validatorIndex, p.feeRecipient,
      p.targetGasLimit))
    (fun (dependentRoot, proposalSlot, validatorIndex, feeRecipient, targetGasLimit) =>
      ⟨dependentRoot, proposalSlot, validatorIndex, feeRecipient, targetGasLimit⟩)

/-- Preferences with the signature of their proposer. -/
structure SignedProposerPreferences where
  /-- The preferences. -/
  message : ProposerPreferences
  /-- The signature of the preferences by the proposer. -/
  signature : BLSSignature
  deriving DecidableEq

instance : SszType SignedProposerPreferences :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

end EthLib.Consensus
