module

public import EthLib.Consensus.Containers.Misc

/-!
# `Consensus.Containers.Operations`

The block operations that every fork shares: proposer slashings, deposits and voluntary exits.

Each one encodes as an SSZ container of its fields, in declaration order.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- Evidence that a proposer signed two different headers for one slot. -/
structure ProposerSlashing where
  /-- The first signed header. -/
  signedHeader1 : SignedBeaconBlockHeader
  /-- The second signed header. -/
  signedHeader2 : SignedBeaconBlockHeader
  deriving DecidableEq, Repr

instance : SszType ProposerSlashing :=
  .container ["signed_header_1", "signed_header_2"]
    (fun s => (s.signedHeader1, s.signedHeader2))
    (fun (signedHeader1, signedHeader2) => ⟨signedHeader1, signedHeader2⟩)

/-- A deposit, with its Merkle proof against the deposit root that the state holds. -/
structure Deposit where
  /-- The sibling nodes from the leaf of the deposit up to the root.

  There is one node for each level of the deposit tree.

  One more node stands for the level where the root mixes in the number of deposits. -/
  proof : Vector Bytes32 (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
  /-- The deposit. -/
  data : DepositData
  deriving DecidableEq, Repr

instance : SszType Deposit :=
  .container ["proof", "data"] (fun d => (d.proof, d.data))
    (fun (proof, data) => ⟨proof, data⟩)

/-- A request of a validator to stop validating, from an epoch on. -/
structure VoluntaryExit where
  /-- The earliest epoch at which the exit may be processed. -/
  epoch : Epoch
  /-- The validator that exits. -/
  validatorIndex : ValidatorIndex
  deriving DecidableEq, Repr

instance : SszType VoluntaryExit :=
  .container ["epoch", "validator_index"] (fun e => (e.epoch, e.validatorIndex))
    (fun (epoch, validatorIndex) => ⟨epoch, validatorIndex⟩)

/-- A voluntary exit with the signature of the validator that exits. -/
structure SignedVoluntaryExit where
  /-- The exit. -/
  message : VoluntaryExit
  /-- The signature of the exit by the validator. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType SignedVoluntaryExit :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

/-- From Capella: a request to replace the BLS withdrawal credentials of a validator by an address.

The address receives the withdrawals of the validator from then on. -/
structure BLSToExecutionChange where
  /-- The validator. -/
  validatorIndex : ValidatorIndex
  /-- The BLS key that the current credentials commit to. -/
  fromBlsPubkey : BLSPubkey
  /-- The address of the new credentials. -/
  toExecutionAddress : ExecutionAddress
  deriving DecidableEq, Repr

instance : SszType BLSToExecutionChange :=
  .container ["validator_index", "from_bls_pubkey", "to_execution_address"]
    (fun c => (c.validatorIndex, c.fromBlsPubkey, c.toExecutionAddress))
    (fun (validatorIndex, fromBlsPubkey, toExecutionAddress) =>
      ⟨validatorIndex, fromBlsPubkey, toExecutionAddress⟩)

/-- From Capella: a change of credentials with the signature of the BLS key it names. -/
structure SignedBLSToExecutionChange where
  /-- The change. -/
  message : BLSToExecutionChange
  /-- The signature of the change by the BLS key. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType SignedBLSToExecutionChange :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

end EthLib.Consensus
