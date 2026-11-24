module

public import EthLib.Base.ByteOrder
public import EthLib.Base.ChainConfig
public import EthLib.Base.Hash32
public import EthLib.Cryptography.Hash.Crc.Crc32
public import EthLib.Serialization.Rlp.Codec

/-!
# `Networking.Devp2p.ForkId`

The fork identifier of [EIP-2124][eip2124], with the forks by timestamp of [EIP-6122][eip6122].

A node announces how far its chain has come, and a peer checks that against its own forks.

The identifier reads only when forks activate, never their rules.

So it holds for every fork of the timeline, Glamsterdam and Hegotá included.

[eip2124]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-2124.md#specification
[eip6122]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-6122.md#specification
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

/-- An identifier as the RLP list `[FORK_HASH, FORK_NEXT]`. -/
def toItem (id : ForkId) : Item :=
  -- The fork identifier is defined as `RLP([FORK_HASH, FORK_NEXT])`.
  --
  -- `FORK_HASH` is a 4 byte binary, so a byte string, and `FORK_NEXT` a `uint64`, so a scalar.
  .list [Codec.toItem id.hash, Codec.toItem id.next]

/-- The identifier in the RLP list `[FORK_HASH, FORK_NEXT]`.

The hash must have 4 bytes, and the next fork must be a scalar below 2^64. -/
def ofItem (item : Item) : Except RlpError ForkId := do
  match ← item.fields 2 with
  -- `[FORK_HASH, FORK_NEXT]`: a `[4]byte` and a `uint64`.
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

Paris takes the `FORK_NEXT_VALUE` of [EIP-3675][eip-3675] as its block, when the chain sets one.

[eip-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#fork-identifier
-/
def blocks (s : Schedule) : List Nat :=
  -- The forks by block of the chain configuration.
  --
  -- Paris activates at a total difficulty, so no one knows its block in advance: it is left out.
  let listed := s.config.activations.filterMap fun (fork, activation) =>
    match activation with
    | .block n => if fork = .paris then none else some n
    | .time _ => none
  -- EIP-3675 sets `FORK_NEXT` to `FORK_NEXT_VALUE`, a block number that the chain sets.
  --
  -- So EthLib counts that block as a fork.
  --
  -- A non-Frontier ruleset already in the genesis is NOT considered a fork, so block 0 is dropped.
  --
  -- The fork block numbers are in ascending order, and a block of several forks appears once.
  ((listed ++ s.mergeForkBlock.toList).filter (0 < ·)).mergeSort.eraseDups

/-- The fork timestamps of a chain, in ascending order, each timestamp once. -/
def times (s : Schedule) : List Nat :=
  -- The forks by timestamp of the chain configuration.
  let listed := s.config.activations.filterMap fun (_, activation) =>
    match activation with
    | .block _ => none
    | .time t => some t
  -- A non-Frontier ruleset already in the genesis is NOT considered a fork.
  --
  -- EthLib reads that as a fork at or before the genesis time, which the genesis block runs.
  --
  -- The timestamps are in ascending order, and a time of several forks appears once.
  (listed.filter (s.genesisTime < ·)).mergeSort.eraseDups

/-- The forks of a chain: the forks by block, then the forks by time.

[EIP-6122][eip-6122] puts the forks by time after the forks by block.

[eip-6122]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-6122.md#additional-rules
-/
def forks (s : Schedule) : List Activation :=
  -- EIP-6122: forks by timestamp MUST be scheduled at or after the forks by block.
  --
  -- So the forks by time come after the forks by block.
  s.blocks.map .block ++ s.times.map .time

/-- The bytes that `FORK_HASH` checksums: the genesis hash, then each fork as 8 bytes. -/
def checksumInput (genesisHash : Hash32) (forks : List Activation) : ByteArray :=
  -- `<genesis-hash> || uint64(f_1) || ... || uint64(f_k)`, each value big endian.
  --
  -- A value of 2^64 or more loses its high bytes, so only a bounded schedule checksums exactly.
  ⟨(genesisHash.toList
    ++ forks.flatMap fun a => (ByteOrder.toBE 8 (activationValue a)).toList).toArray⟩

/-- `FORK_HASH` after some forks: the CRC-32 of the genesis hash and of those forks. -/
def checksum (genesisHash : Hash32) (forks : List Activation) : Vector UInt8 4 :=
  -- `FORK_HASH = CRC32(<genesis-hash> || uint64(f_1) || ... || uint64(f_k))`, the IEEE CRC-32.
  --
  -- EIP-2124 writes `[4]byte` with no byte order.
  --
  -- Its RLP test vectors write the CRC big endian, so EthLib does too.
  ByteOrder.toBE 4 (Crc32.crc32 (checksumInput genesisHash forks)).toNat

/-- The passed forks at a head with a block number and a timestamp. -/
def passed (s : Schedule) (number timestamp : Nat) : List Activation :=
  -- The fork block numbers or timestamps that already passed.
  --
  -- A fork by block is passed at its block number, and a fork by time at its timestamp.
  --
  -- EthLib stops at the first fork not reached, so no later fork counts as passed.
  s.forks.takeWhile (·.reached number timestamp)

/-- The fork identifier of a node at a head with a block number and a timestamp. -/
def forkId (s : Schedule) (number timestamp : Nat) : ForkId where
  -- `FORK_HASH`: the checksum of the genesis hash and of the forks that already passed.
  hash := checksum s.genesisHash (s.passed number timestamp)
  -- `FORK_NEXT`: the block number or timestamp of the next upcoming fork.
  --
  -- That is the first fork that the head has not reached.
  next :=
    match s.forks.dropWhile (·.reached number timestamp) with
    -- `0` if no next fork is known: the head has passed every fork.
    | [] => 0
    -- A `uint64`: the value wraps modulo 2^64 unless the schedule is bounded.
    | a :: _ => UInt64.ofNat (activationValue a)

/-- `FORK_HASH` after each number of forks, from none to all of them. -/
def checksums (s : Schedule) : List (Vector UInt8 4) :=
  -- `forkhash_k = CRC32(<genesis-hash> || uint64(f_1) || ... || uint64(f_k))`.
  --
  -- Here `k` runs from 0 to the number of forks.
  (List.range (s.forks.length + 1)).map fun k => checksum s.genesisHash (s.forks.take k)

/--
Whether each fork of a schedule has a block number or timestamp below 2^64.

[EIP-2124][eip-2124] hashes each fork as a big-endian `uint64`, and `FORK_NEXT` is a `uint64`.

[EIP-6122][eip-6122] does the same for the forks by time.

The block of `FORK_NEXT_VALUE` of [EIP-3675][eip-3675] is one of these forks.

So only such a schedule has fork identifiers that hold its forks whole.

The schedule reader of the exports refuses any fork of 2^64 or more.

[eip-2124]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-2124.md#specification
[eip-6122]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-6122.md#specification
[eip-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#fork-identifier
-/
def Bounded (s : Schedule) : Prop :=
  ∀ a ∈ s.forks, activationValue a < ACTIVATION_BOUND

instance (s : Schedule) : Decidable s.Bounded :=
  inferInstanceAs (Decidable (∀ a ∈ s.forks, _))

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

/-- Whether the local head has passed the next fork `next` that a peer announces. -/
def passedNext (number timestamp next : Nat) : Bool :=
  -- Rule 1a: a remotely announced fork that is already passed locally.
  --
  -- A `FORK_NEXT` of 0 announces no fork, so it is never passed.
  --
  -- Every value is compared with the block number.
  --
  -- EthLib's bound: a value above the threshold is also a timestamp, passed at the head's time.
  0 < next && (next ≤ number || (TIMESTAMP_THRESHOLD < next && next ≤ timestamp))

namespace Schedule

/--
Whether a node at a head accepts the fork identifier of a peer, by the rules of EIP-2124.

They are the validation rules of [EIP-2124][eip-2124].

[EIP-6122][eip-6122] checks the forks by block before the forks by time, as the order of forks does.

[eip-2124]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-2124.md#validation-rules
[eip-6122]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-6122.md#additional-rules
-/
def validate (s : Schedule) (number timestamp : Nat) (remote : ForkId) :
    Except ForkIdError Unit :=
  -- The number of local past forks.
  let i := (s.passed number timestamp).length
  -- Rule 1: the local and remote `FORK_HASH` match, so the nodes are in the same fork state.
  if (s.forkId number timestamp).hash = remote.hash then
    -- Rule 1a: a remotely announced fork is already passed locally, so disconnect.
    if passedNext number timestamp remote.next.toNat then throw .localIncompatibleOrStale
    -- Rule 1b: no remotely announced fork, or not yet passed locally, so connect.
    else pure ()
  else
    -- Rule 2: the remote `FORK_HASH` is a subset of the local past forks.
    --
    -- That is the checksum of the first `j` forks, for some `j < i`: the remote node is syncing.
    --
    -- EthLib compares from the first checksum, so the first match decides.
    match (s.checksums.take i).findIdx? (· = remote.hash) with
    | some j =>
      -- Rule 2: connect if the remote `FORK_NEXT` matches the locally following fork, fork `j + 1`.
      if (s.forks[j]?.map activationValue) = some remote.next.toNat then pure ()
      -- Rule 4 otherwise: the remote node needs a software update.
      else throw .remoteStale
    | none =>
      -- Rule 3: the remote `FORK_HASH` is a superset of the local past forks.
      --
      -- It is completed with locally known future forks: the checksum of more than `i` forks.
      if (s.checksums.drop (i + 1)).contains remote.hash then pure ()
      -- Rule 4: reject in all other cases.
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
