module

public import EthLib.Base.Fork
public import EthLib.Networking.Enr.Record
public import EthLib.Serialization.Ssz.Typed.Basic
public import EthLib.Serialization.Ssz.Typed.Collections
public import EthLib.Serialization.Ssz.Typed.Container

/-!
# `Networking.Enr.Consensus`

The entries that a consensus-layer node adds to its node record.

- `eth2`: the SSZ bytes of the fork digest now, and the version and epoch of the next fork.
- `attnets`: one bit for each attestation subnet that the node subscribes to.
- `syncnets`: one bit for each sync committee subnet, from Altair on.
- `cgc`: the number of custody groups of the node, from Fulu on.
- `nfd`: the fork digest of the next fork, from Fulu on.

A node reads only the entries of its fork, and it ignores the others.

[EIP-7892][eip-7892] adds the next fork digest, in its section ENR.

[eip-7892]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7892.md#enr
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Base (Fork)
open EthLib.Serialization
open EthLib.Serialization.Ssz

/-- The value of `eth2`: the fork digest now, and the fork that comes next. -/
structure EnrForkId where
  /-- The fork digest of the current epoch. -/
  forkDigest : Vector UInt8 4
  /-- The fork version at the next fork epoch, or the current one if no fork is planned. -/
  nextForkVersion : Vector UInt8 4
  /-- The epoch of the next fork, or 2^64 - 1 if no fork is planned. -/
  nextForkEpoch : UInt64
  deriving DecidableEq, Repr

/-- `eth2` is the SSZ container of its three fields, 16 bytes in all. -/
instance : SszType EnrForkId :=
  -- The fields in order: the fork digest and the next fork version, 4 bytes each.
  --
  -- Then the next fork epoch, a `uint64` of 8 bytes.
  .container ["fork_digest", "next_fork_version", "next_fork_epoch"]
    (fun e => (e.forkDigest, e.nextForkVersion, e.nextForkEpoch)) (fun (d, v, e) => ⟨d, v, e⟩)

/-- The number of sync committee subnets. -/
def SYNC_COMMITTEE_SUBNET_COUNT : Nat := 4

/-- The attestation subnets of a node, one bit for each of the `count` subnets.

The count is the number of attestation subnets of the configuration. -/
abbrev Attnets (count : UInt64) := Bitvector count.toNat

/-- The sync committee subnets of a node, one bit each. -/
abbrev Syncnets := Bitvector SYNC_COMMITTEE_SUBNET_COUNT

/-- An entry that the consensus layer adds to a node record. -/
inductive ConsensusKey where
  /-- The current fork digest and the next fork. -/
  | eth2
  /-- The attestation subnets. -/
  | attnets
  /-- The sync committee subnets. -/
  | syncnets
  /-- The custody group count. -/
  | cgc
  /-- The next fork digest. -/
  | nfd
  deriving DecidableEq, Repr

namespace ConsensusKey

/-- The key in the record, as ASCII bytes. -/
def name : ConsensusKey → String
  | .eth2 => "eth2"
  | .attnets => "attnets"
  | .syncnets => "syncnets"
  | .cgc => "cgc"
  | .nfd => "nfd"

/-- The first fork at which the entry exists. -/
def since : ConsensusKey → Fork
  -- `eth2` and the attestation subnets exist from Phase 0.
  | .eth2 | .attnets => .phase0
  -- Altair adds the bitfield of the sync committee subnets.
  | .syncnets => .altair
  -- Fulu adds the custody group count, and EIP-7892 adds the next fork digest.
  --
  -- The fork of the consensus layer is Fulu, which the timeline names Fusaka.
  | .cgc | .nfd => .fusaka

end ConsensusKey

/-- The consensus entries that exist at a fork. -/
def keysAt (fork : Fork) : List ConsensusKey :=
  [.eth2, .attnets, .syncnets, .cgc, .nfd].filter (·.since ≤ fork)

/-- Why a consensus entry of a record was refused. -/
inductive EntryError where
  /-- A required entry is absent. -/
  | missing (key : ConsensusKey)
  /-- The value is an RLP list, not a byte string. -/
  | notBytes (key : ConsensusKey)
  /-- The value is not the SSZ encoding of its type. -/
  | ssz (key : ConsensusKey) (e : Ssz.Err)
  /-- The custody group count is not an RLP scalar below 2^64. -/
  | cgc (e : Rlp.RlpError)
  deriving DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

The codes start at 101, above every code of a record error, so that the two never meet.

A new constructor takes a new code, so that each code keeps its meaning. -/
def EntryError.code : EntryError → UInt32
  | .missing _ => 101
  | .notBytes _ => 102
  | .ssz .. => 103
  | .cgc _ => 104

/-- The value of a key in a record, if the record has the key. -/
def lookup (r : Enr) (key : ConsensusKey) : Option Rlp.Item :=
  -- Each key is an ASCII name, whose UTF-8 bytes are its ASCII bytes.
  (r.pairs.find? (·.1 = key.name.toUTF8)).map (·.2)

/-- The bytes of a key in a record, if the record has the key. -/
def lookupBytes (r : Enr) (key : ConsensusKey) : Except EntryError (Option ByteArray) :=
  match lookup r key with
  | none => return none
  -- Every consensus entry holds a byte string: an SSZ encoding, or the custody group count.
  | some (.bytes value) => return some value
  -- So an RLP list in its place is refused.
  | some (.list _) => throw (.notBytes key)

/-- The SSZ value of a key in a record, if the record has the key. -/
def readSsz (α : Type) [SszType α] (r : Enr) (key : ConsensusKey) :
    Except EntryError (Option α) := do
  match ← lookupBytes r key with
  | none => return none
  -- The bytes are the SSZ encoding of a value of the type of the entry.
  | some value => return some (← (SszType.deserialize α value).mapError (.ssz key))

/-- The custody group count of a record, if the record has the key. -/
def readCgc (r : Enr) : Except EntryError (Option UInt64) := do
  match ← lookupBytes r .cgc with
  | none => return none
  -- The count is a 64-bit big-endian integer with no leading zero byte.
  --
  -- Zero is the empty byte string, so the value is an RLP scalar below 2^64.
  | some value => return some (← (Rlp.Codec.ofItem (.bytes value)).mapError .cgc)

/-- The consensus entries of a record, as a node at one fork reads them.

`count` is the number of attestation subnets, which fixes the length of `attnets`. -/
structure ConsensusEntries (count : UInt64) where
  /-- The current and next forks, which every node record of the consensus layer carries. -/
  eth2 : EnrForkId
  /-- The attestation subnets, which a node may leave out when it subscribes to none. -/
  attnets : Option (Attnets count)
  /-- The sync committee subnets, read from Altair on. -/
  syncnets : Option Syncnets
  /-- The custody group count, read and required from Fulu on. -/
  cgc : Option UInt64
  /-- The next fork digest, read and required from Fulu on. -/
  nfd : Option (Vector UInt8 4)
  deriving DecidableEq

/-- The value of a key that exists at the fork, and nothing for a key that does not. -/
def readAt {α : Type} (fork : Fork) (key : ConsensusKey) (read : Except EntryError (Option α)) :
    Except EntryError (Option α) :=
  -- A node of an earlier fork does not know the key, so it ignores the entry.
  if key.since ≤ fork then read else return none

/-- The value of a key that the fork requires, and nothing for a key that does not exist yet. -/
def readRequiredAt {α : Type} (fork : Fork) (key : ConsensusKey)
    (read : Except EntryError (Option α)) : Except EntryError (Option α) :=
  if key.since ≤ fork then do
    match ← read with
    | some a => return some a
    -- From its fork on, a record must carry the entry.
    | none => throw (.missing key)
  -- A node of an earlier fork does not know the key, so it ignores the entry.
  else return none

/-- The consensus entries of a record at a fork, with `count` attestation subnets. -/
def readEntries (count : UInt64) (fork : Fork) (r : Enr) :
    Except EntryError (ConsensusEntries count) := do
  -- Every record carries `eth2` at every fork, the SSZ encoding of its three fields.
  let some eth2 ← readSsz EnrForkId r .eth2 | throw (.missing .eth2)
  -- `attnets` is a bitvector of `count` bits, and a node subscribed to no subnet may omit it.
  --
  -- A node subscribed to a subnet carries it, a rule for the writer that a reader cannot check.
  let attnets ← readSsz (Attnets count) r .attnets
  -- From Altair, `syncnets`: a bitvector of 4 bits, one per sync committee subnet.
  --
  -- The source states no rule that a record carries it, so EthLib reads it as optional.
  let syncnets ← readAt fork .syncnets (readSsz Syncnets r .syncnets)
  -- A node adds `cgc` once the Fulu epoch is scheduled, so it may precede the fork.
  --
  -- EthLib requires it from the fork on, and a node of an earlier fork ignores it.
  let cgc ← readRequiredAt fork .cgc (readCgc r)
  -- `nfd`: the SSZ `ForkDigest` of the next scheduled fork, 4 bytes.
  --
  -- Like `cgc`, a node adds it once the Fulu epoch is scheduled.
  --
  -- EthLib requires it from the fork on.
  --
  -- With no next fork scheduled, it holds four zero bytes.
  --
  -- EIP-7892: nodes must evaluate it alongside the next fork fields of `eth2`.
  --
  -- That comparison is left to the caller, which knows its own next fork.
  let nfd ← readRequiredAt fork .nfd (readSsz (Vector UInt8 4) r .nfd)
  return ⟨eth2, attnets, syncnets, cgc, nfd⟩

end EthLib.Networking.Enr
