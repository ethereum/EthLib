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
  .container ["fork_digest", "next_fork_version", "next_fork_epoch"]
    (fun e => (e.forkDigest, e.nextForkVersion, e.nextForkEpoch)) (fun (d, v, e) => ⟨d, v, e⟩)

/-- The number of attestation subnets, 64 in the mainnet and minimal configurations. -/
def ATTESTATION_SUBNET_COUNT : Nat := 64

/-- The number of sync committee subnets. -/
def SYNC_COMMITTEE_SUBNET_COUNT : Nat := 4

/-- The attestation subnets of a node, one bit each. -/
abbrev Attnets := Bitvector ATTESTATION_SUBNET_COUNT

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

/-- The first fork at which the entry exists.

The next fork digest comes from [EIP-7892](https://eips.ethereum.org/EIPS/eip-7892#enr), "ENR".
-/
def since : ConsensusKey → Fork
  | .eth2 | .attnets => .phase0
  | .syncnets => .altair
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

/-- The value of a key in a record, if the record has the key. -/
def lookup (r : Enr) (key : ConsensusKey) : Option Rlp.Item :=
  (r.pairs.find? (·.1 = key.name.toUTF8)).map (·.2)

/-- The bytes of a key in a record, if the record has the key. -/
def lookupBytes (r : Enr) (key : ConsensusKey) : Except EntryError (Option ByteArray) :=
  match lookup r key with
  | none => return none
  | some (.bytes value) => return some value
  | some (.list _) => throw (.notBytes key)

/-- The SSZ value of a key in a record, if the record has the key. -/
def readSsz (α : Type) [SszType α] (r : Enr) (key : ConsensusKey) :
    Except EntryError (Option α) := do
  match ← lookupBytes r key with
  | none => return none
  | some value => return some (← (SszType.deserialize α value).mapError (.ssz key))

/-- The custody group count, a big-endian integer with no leading zero byte.

Zero is the empty byte string, so the value is an RLP scalar below 2^64. -/
def readCgc (r : Enr) : Except EntryError (Option UInt64) := do
  match ← lookupBytes r .cgc with
  | none => return none
  | some value => return some (← (Rlp.Codec.ofItem (.bytes value)).mapError .cgc)

/-- The consensus entries of a record, as a node at one fork reads them. -/
structure ConsensusEntries where
  /-- The current and next forks, which every node record of the consensus layer carries. -/
  eth2 : EnrForkId
  /-- The attestation subnets, which a node may leave out when it subscribes to none. -/
  attnets : Option Attnets
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
  if key.since ≤ fork then read else return none

/-- The value of a key that the fork requires, and nothing for a key that does not exist yet. -/
def readRequiredAt {α : Type} (fork : Fork) (key : ConsensusKey)
    (read : Except EntryError (Option α)) : Except EntryError (Option α) :=
  if key.since ≤ fork then do
    match ← read with
    | some a => return some a
    | none => throw (.missing key)
  else return none

/-- The consensus entries of a record at a fork.

`eth2` is required at every fork, and `cgc` and `nfd` from Fulu on.

A node does not read an entry of a later fork, since it does not know the key. -/
def readEntries (fork : Fork) (r : Enr) : Except EntryError ConsensusEntries := do
  let some eth2 ← readSsz EnrForkId r .eth2 | throw (.missing .eth2)
  let attnets ← readSsz Attnets r .attnets
  let syncnets ← readAt fork .syncnets (readSsz Syncnets r .syncnets)
  let cgc ← readRequiredAt fork .cgc (readCgc r)
  let nfd ← readRequiredAt fork .nfd (readSsz (Vector UInt8 4) r .nfd)
  return ⟨eth2, attnets, syncnets, cgc, nfd⟩

end EthLib.Networking.Enr
