module

public import EthLib.Base.Address
public import EthLib.Base.Bytes

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

/-- From Deneb: the index of a blob in a block. -/
abbrev BlobIndex := UInt64

end EthLib.Consensus
