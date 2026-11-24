module

public import EthLib.Base.Address
public import EthLib.Base.Bytes
public import EthLib.Base.Hex
public import EthLib.Cryptography.Kzg.Types
public import EthLib.Serialization.Ssz.Typed.Basic

/-!
# `Consensus.Types`

The integers and byte strings that name the values of the beacon chain.

Each integer is a 64-bit unsigned integer, and each byte string has a fixed length.
-/

@[expose] public section

namespace EthLib.Consensus

/-- A slot: one fixed span of time, numbered from genesis. -/
abbrev Slot := UInt64

/-- An epoch: a fixed number of consecutive slots, numbered from genesis. -/
abbrev Epoch := UInt64

/-- The index of a committee among the committees of one slot. -/
abbrev CommitteeIndex := UInt64

/-- The index of a validator in the registry of validators. -/
abbrev ValidatorIndex := UInt64

/-- An amount in Gwei.

One ether is 10^9 Gwei, and one Gwei is 10^9 wei. -/
abbrev Gwei := UInt64

/-- A Merkle root, usually the hash tree root of an object. -/
abbrev Root := Base.Bytes32

/-- The version of a fork. -/
abbrev Version := Vector UInt8 4

/-- The type of a signature domain, which names the kind of message that is signed. -/
abbrev DomainType := Vector UInt8 4

/-- A short digest of the data of a fork. -/
abbrev ForkDigest := Vector UInt8 4

/-- A signature domain. -/
abbrev Domain := Base.Bytes32

/-- A 20-byte address on the execution layer. -/
abbrev ExecutionAddress := Base.Address

/-- From Altair: the flags of one validator for one epoch, one bit for each timely duty. -/
abbrev ParticipationFlags := UInt8

/-- From Capella: the index of a withdrawal, counted over all withdrawals. -/
abbrev WithdrawalIndex := UInt64

/-- An amount in ether, which the weak subjectivity period counts in. -/
abbrev Ether := UInt64

/-- From Bellatrix: the identifier of a payload that the execution engine is building. -/
abbrev PayloadId := Base.Bytes8

/-- From Bellatrix: what a node knows of the execution payload of a block, as one byte. -/
abbrev PayloadValidationStatus := UInt8

/-- From Deneb: the index of a blob in a block. -/
abbrev BlobIndex := UInt64

/-- From Deneb: the versioned hash of a KZG commitment, which names a blob.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#type-aliases) defines it.

It is the type of KZG itself, so the consensus layer needs no conversion.

The execution layer keeps it as 32 bytes, so the Engine API reads its bytes. -/
abbrev VersionedHash := Cryptography.Kzg.VersionedHash

/-- From Deneb: a versioned hash is a `Bytes32` in SSZ.

Source: "Type aliases" of [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#type-aliases). -/
instance : Serialization.Ssz.SszType Cryptography.Kzg.VersionedHash :=
  .wrapper Cryptography.Kzg.VersionedHash.mk Cryptography.Kzg.VersionedHash.bytes

/-- From Deneb: a KZG commitment is a `Bytes48` in SSZ.

Source: "Type aliases" of [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#type-aliases). -/
instance : Serialization.Ssz.SszType Cryptography.Kzg.KZGCommitment :=
  .wrapper Cryptography.Kzg.KZGCommitment.mk Cryptography.Kzg.KZGCommitment.bytes

/-- From Fulu: the index of a cell in an extended blob, below the number of cells. -/
abbrev CellIndex := UInt64

/-- From Fulu: the index of a row, one blob, in the matrix of cells of a block. -/
abbrev RowIndex := UInt64

/-- From Gloas: the index of a builder in the registry of builders.

[EIP-7732](https://eips.ethereum.org/EIPS/eip-7732#types) defines it. -/
abbrev BuilderIndex := UInt64

namespace HexRepr

/-- Bytes in an error, such as a root, as hex digits behind `0x`, which keeps its message short.

An error type opens this namespace where it derives its rendering, for the rest of its file. -/
scoped instance (priority := high) instReprBytesHex {n : Nat} : Repr (Vector UInt8 n) where
  reprPrec bytes _ := Base.hexString bytes.toList

end HexRepr

end EthLib.Consensus
