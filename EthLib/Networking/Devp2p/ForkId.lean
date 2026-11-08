module

public import EthLib.Base.BigEndian
public import EthLib.Base.ChainConfig
public import EthLib.Base.Hash32
public import EthLib.Cryptography.Hash.Crc32
public import EthLib.Serialization.Rlp.Codec

/-!
# `Networking.Devp2p.ForkId`

The fork identifier of [EIP-2124][eip2124], with the forks by timestamp of [EIP-6122][eip6122].

A node announces how far its chain has come, and a peer checks that against its own forks.

- `FORK_HASH` is the CRC-32 of the genesis hash, then of each passed fork as a big-endian `uint64`.
- `FORK_NEXT` is the block number or timestamp of the next fork, or 0 when no next fork is known.
- The identifier is the RLP list `[FORK_HASH, FORK_NEXT]`.

The forks by block come first, then the forks by time, each in ascending order and each value once.

A fork at genesis is not a fork.

The identifier reads only when forks activate, never their rules.

So it holds for every fork of the timeline, Glamsterdam and Hegotá included.

[eip2124]: https://eips.ethereum.org/EIPS/eip-2124#specification
[eip6122]: https://eips.ethereum.org/EIPS/eip-6122#specification
-/

@[expose] public section

namespace EthLib.Networking.Devp2p

open EthLib.Base
open EthLib.Cryptography.Hash
open EthLib.Serialization.Rlp

/-- The fork identifier `[FORK_HASH, FORK_NEXT]`. -/
structure ForkId where
  /-- `FORK_HASH`: the CRC-32 of the genesis hash and the passed forks, as 4 big-endian bytes. -/
  hash : Vector UInt8 4
  /-- `FORK_NEXT`: the block number or timestamp of the next fork, or 0 when none is known. -/
  next : UInt64
  deriving DecidableEq, Repr

namespace ForkId

/-- An identifier as the RLP list `[FORK_HASH, FORK_NEXT]`.

The hash is a byte string of 4 bytes, and the next fork is a scalar. -/
def toItem (id : ForkId) : Item :=
  .list [Codec.toItem id.hash, Codec.toItem id.next]

/-- The identifier in the RLP list `[FORK_HASH, FORK_NEXT]`.

The hash must have 4 bytes, and the next fork must be a scalar below 2^64. -/
def ofItem (item : Item) : Except RlpError ForkId := do
  match ← item.fields 2 with
  | [hash, next] => return ⟨← hash.field 0, ← next.field 1⟩
  | items => throw (.wrongFieldCount 2 items.length)

instance : Codec ForkId := ⟨toItem, ofItem⟩

end ForkId

/-- The block number or timestamp of an activation. -/
def activationValue : Activation → Nat
  | .block n => n
  | .time t => t

/-- What a node needs to know about its chain to compute its fork identifier. -/
structure Schedule where
  /-- The hash of the genesis block. -/
  genesisHash : Hash32
  /-- The timestamp of the genesis block. -/
  genesisTime : Nat
  /-- The forks of the chain, with their activations. -/
  config : ChainConfig
  /-- `FORK_NEXT_VALUE` of EIP-3675, the block that stands for Paris, if the chain sets one. -/
  mergeForkBlock : Option Nat
  deriving DecidableEq, Repr

namespace Schedule

/--
The fork blocks of a chain, in ascending order, each block once.

A fork at block 0 is part of the genesis rules, so it is not a fork.

Paris activates when the chain reaches a total difficulty, so no one knows its block in advance.

[EIP-3675][eip-3675] puts its `FORK_NEXT_VALUE` in its place.

That value is a block that the chain configuration sets.

So the block of Paris is not a fork block, and `FORK_NEXT_VALUE` is one when the chain sets it.

[eip-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#fork-identifier
-/
def blocks (s : Schedule) : List Nat :=
  let listed := s.config.activations.filterMap fun (fork, activation) =>
    match activation with
    | .block n => if fork = .paris then none else some n
    | .time _ => none
  ((listed ++ s.mergeForkBlock.toList).filter (0 < ·)).mergeSort.eraseDups

/--
The fork timestamps of a chain, in ascending order, each timestamp once.

A fork at or before the genesis time is part of the genesis rules, so it is not a fork.
-/
def times (s : Schedule) : List Nat :=
  let listed := s.config.activations.filterMap fun (_, activation) =>
    match activation with
    | .block _ => none
    | .time t => some t
  (listed.filter (s.genesisTime < ·)).mergeSort.eraseDups

/-- The forks of a chain: the forks by block, then the forks by time.

[EIP-6122][eip-6122] puts the forks by time after the forks by block.

[eip-6122]: https://eips.ethereum.org/EIPS/eip-6122#additional-rules
-/
def forks (s : Schedule) : List Activation :=
  s.blocks.map .block ++ s.times.map .time

/-- The bytes that `FORK_HASH` checksums: the genesis hash, then each fork as 8 bytes.

Each block number or timestamp is a big-endian `uint64`. -/
def checksumInput (genesisHash : Hash32) (forks : List Activation) : ByteArray :=
  ⟨(genesisHash.toList ++ forks.flatMap fun a => natToBytes 8 (activationValue a)).toArray⟩

/-- `FORK_HASH` after some forks: the CRC-32 of the genesis hash and of those forks.

The CRC is a number, and `FORK_HASH` holds it as 4 big-endian bytes. -/
def checksum (genesisHash : Hash32) (forks : List Activation) : Vector UInt8 4 :=
  ⟨(natToBytes 4 (Crc32.crc32 (checksumInput genesisHash forks)).toNat).toArray,
    by simp [natToBytes_length]⟩

/--
The passed forks at a head with a block number and a timestamp.

They are the forks up to the first one that the head has not reached.

A fork by block is reached by the block number, and a fork by time by the timestamp.
-/
def passed (s : Schedule) (number timestamp : Nat) : List Activation :=
  s.forks.takeWhile (·.reached number timestamp)

/-- The fork identifier of a node at a head with a block number and a timestamp.

`FORK_NEXT` is the first fork that the head has not reached.

It is 0 if the head has passed every fork. -/
def forkId (s : Schedule) (number timestamp : Nat) : ForkId where
  hash := checksum s.genesisHash (s.passed number timestamp)
  next :=
    match s.forks.dropWhile (·.reached number timestamp) with
    | [] => 0
    | a :: _ => UInt64.ofNat (activationValue a)

/-- `FORK_HASH` after each number of forks, from none to all of them. -/
def checksums (s : Schedule) : List (Vector UInt8 4) :=
  (List.range (s.forks.length + 1)).map fun k => checksum s.genesisHash (s.forks.take k)

end Schedule

/-- Why a node refuses the fork identifier of a peer. -/
inductive ForkIdError where
  /-- The peer is on an earlier fork of this chain, but it announces a different next fork.

  It needs a software update. -/
  | remoteStale
  /-- The two chains differ, or this node needs a software update. -/
  | localIncompatibleOrStale
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

A new constructor takes a new code, so that each code keeps its meaning. -/
def ForkIdError.code : ForkIdError → UInt32
  | .remoteStale => 1
  | .localIncompatibleOrStale => 2

/--
The value above which a `FORK_NEXT` is a timestamp, and at or below which it is a block number.

EIP-6122 says that a node need not tell the two apart.

Rule 1a must, since it compares a peer's next fork with the local head.

EthLib fixes the bound as a choice of its own: the time 2015-07-30 15:26:13 UTC.

Every block number of a real chain is far below it, and every fork timestamp far above it.
-/
def TIMESTAMP_THRESHOLD : Nat := 1438269973

/-- Whether the local head has passed the next fork `next` that a peer announces.

A next fork of 0 announces nothing, so it is never passed. -/
def passedNext (number timestamp next : Nat) : Bool :=
  0 < next && (next ≤ number || (TIMESTAMP_THRESHOLD < next && next ≤ timestamp))

namespace Schedule

/--
Whether a node at a head accepts the fork identifier of a peer, by the rules of EIP-2124.

They are the validation rules of [EIP-2124][eip-2124].

- 1: the two hashes match, so the nodes are at one fork.
  The node refuses only if it has passed the next fork that the peer announces (1a).
- 2: the hash of the peer is one of the node's earlier hashes, so the peer is syncing.
  The node accepts if the peer announces the fork that follows that hash, and refuses otherwise.
- 3: the hash of the peer is one of the node's later hashes, so the node is syncing, and it accepts.
- 4: the node refuses in every other case.

[EIP-6122][eip-6122] checks the forks by block before the forks by time, as the order of forks does.

The node compares its earlier hashes from the first one, so the first match decides rule 2.

[eip-2124]: https://eips.ethereum.org/EIPS/eip-2124#validation-rules
[eip-6122]: https://eips.ethereum.org/EIPS/eip-6122#additional-rules
-/
def validate (s : Schedule) (number timestamp : Nat) (remote : ForkId) :
    Except ForkIdError Unit :=
  let i := (s.passed number timestamp).length
  if (s.forkId number timestamp).hash = remote.hash then
    if passedNext number timestamp remote.next.toNat then throw .localIncompatibleOrStale
    else pure ()
  else
    match (s.checksums.take i).findIdx? (· = remote.hash) with
    | some j =>
      if (s.forks[j]?.map activationValue) = some remote.next.toNat then pure ()
      else throw .remoteStale
    | none =>
      if (s.checksums.drop (i + 1)).contains remote.hash then pure ()
      else throw .localIncompatibleOrStale

/--
The schedule of Ethereum mainnet: its chain configuration from Frontier to BPO2.

[EIP-1898][eip-1898] gives the hash of its genesis block.

The header of that block has the timestamp 0, as [`genesishashestest.json`][genesis] holds it.

That file is part of the Ethereum tests.

EIP-3675 sets no `FORK_NEXT_VALUE` for mainnet, so Paris adds no fork block.

[eip-1898]: https://eips.ethereum.org/EIPS/eip-1898#specification
[genesis]: https://github.com/ethereum/tests/blob/c67e485ff8b5be9abc8ad15345ec21aa22e290d9/BasicTests/genesishashestest.json
-/
def mainnet : Schedule where
  genesisHash := ⟨#[0xd4, 0xe5, 0x67, 0x40, 0xf8, 0x76, 0xae, 0xf8, 0xc0, 0x10, 0xb8, 0x6a,
    0x40, 0xd5, 0xf5, 0x67, 0x45, 0xa1, 0x18, 0xd0, 0x90, 0x6a, 0x34, 0xe6, 0x9a, 0xec, 0x8c,
    0x0d, 0xb1, 0xcb, 0x8f, 0xa3], rfl⟩
  genesisTime := 0
  config := ChainConfig.mainnet
  mergeForkBlock := none

end Schedule

end EthLib.Networking.Devp2p
