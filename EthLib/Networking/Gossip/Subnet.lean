module

public import EthLib.Base.LittleEndian
public import EthLib.Base.U256
public import EthLib.Base.Uint64
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Networking.Gossip.Parameters
public import EthLib.Networking.Gossip.Topic
public import EthLib.Serialization.Ssz.Merkle.Merkleize

/-!
# `Networking.Gossip.Subnet`

The attestation subnets that a node stays subscribed to, for a period of epochs.

Its node ID and the period choose them, so any peer can compute them.

The parameters and the shuffle are inputs, since the consensus layer defines them.
-/

@[expose] public section

namespace EthLib.Networking.Gossip

/-- The ID of a node on the discovery network, a number below 2^256. -/
abbrev NodeID := Base.U256

/-- The number of bits of a node ID. -/
def NODE_ID_BITS : Nat := 256

/-- Every way the choice of subnets can fail.

`ε` is the error type of the shuffle. -/
inductive SubnetError (ε : Type) where
  /-- There are no subnets of the kind asked for. -/
  | zeroSubnetCount
  /-- A subscription lasts zero epochs. -/
  | zeroEpochsPerSubscription
  /-- The epoch `epoch` plus the offset `offset` of the node is 2^64 or more. -/
  | epochOverflow (epoch offset : UInt64)
  /-- The prefix has 64 bits or more, so the number of prefixes is not below 2^64. -/
  | prefixBitsTooLarge (bits : Nat)
  /-- A sum or a product on the way to a subnet, of `left` and `right`, is 2^64 or more.

  For the subnets of a node, it is the permuted prefix plus the index of the subnet. -/
  | subnetOverflow (left right : UInt64)
  /-- The shuffle failed. -/
  | shuffle (error : ε)
  deriving Repr, DecidableEq

/--
The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning.

The codes start at 101, since the consensus errors of the bindings share one class.
-/
def SubnetError.code {ε : Type} : SubnetError ε → UInt32
  | .zeroSubnetCount => 101
  | .zeroEpochsPerSubscription => 102
  | .epochOverflow .. => 103
  | .prefixBitsTooLarge _ => 104
  | .subnetOverflow .. => 105
  | .shuffle _ => 106

variable {ε : Type}

/-- The number of node ID bits in the prefix. -/
def computeAttestationSubnetPrefixBits (config : SubnetParameters) :
    Except (SubnetError ε) Nat :=
  -- The base-2 logarithm of zero is not defined, so a count of zero subnets is an error.
  if config.ATTESTATION_SUBNET_COUNT = 0 then throw .zeroSubnetCount
  else
    -- `b = c + e`, for `n` subnets and `e` extra bits, where `c` is the least with `2^c >= n`.
    return Serialization.Ssz.depthFor config.ATTESTATION_SUBNET_COUNT.toNat +
      config.ATTESTATION_SUBNET_EXTRA_BITS.toNat

/-- The shuffled prefix of a node in an epoch, which every index of the node shares.

The prefix is the top bits of the node ID, and a shuffle seeded by the period permutes it.

`shuffle i n seed` is the position of `i` in a permutation of `0, …, n - 1` that the seed selects.

The shuffle permutes the prefix of the node among all prefixes of its length.
-/
def computeShuffledPrefix (config : SubnetParameters)
    (shuffle : UInt64 → UInt64 → Base.Bytes32 → Except ε UInt64)
    (nodeId : NodeID) (epoch : UInt64) : Except (SubnetError ε) UInt64 := do
  -- The prefix is the top `b` bits of the 256-bit node ID `id`: `floor(id / 2^(256 - b))`.
  let bits ← computeAttestationSubnetPrefixBits config
  let nodePrefix := nodeId.toNat >>> (NODE_ID_BITS - bits)
  -- The period length `E` is the epochs per subscription, and `E = 0` is an error.
  if config.EPOCHS_PER_SUBNET_SUBSCRIPTION = 0 then throw .zeroEpochsPerSubscription
  -- The offset of the node is `id mod E`, below `E`, so it fits 64 bits.
  --
  -- The offset shifts the start of each period, so nodes do not all change their subnets at once.
  let nodeOffset := (nodeId.toNat % config.EPOCHS_PER_SUBNET_SUBSCRIPTION.toNat).toUInt64
  -- The epoch plus the offset is a 64-bit integer, and an overflow is an error.
  let shifted ← (Base.Uint64.addChecked epoch nodeOffset).mapError
    fun _ => .epochOverflow epoch nodeOffset
  -- The period is `floor((epoch + offset) / E)`.
  let period := shifted / config.EPOCHS_PER_SUBNET_SUBSCRIPTION
  -- The seed is SHA-256 of the period as eight little-endian bytes.
  let seed := Cryptography.Hash.Sha256.hash32 ⟨(Base.uintToBytes 8 period.toNat).toArray⟩
  -- The `2^b` prefixes are counted by a 64-bit integer, so `b >= 64` is an error.
  --
  -- It is checked after the seed, where the count `2^b` is first needed.
  if 64 ≤ bits then throw (.prefixBitsTooLarge bits)
  -- The position of the prefix in the permutation of `0, ..., 2^b - 1` that the seed selects.
  (shuffle nodePrefix.toUInt64 (2 ^ bits).toUInt64 seed).mapError .shuffle

/-- The subnet with a given index among the subnets of a node in an epoch.

The node takes the subnets that start at its shuffled prefix.

The subnet is the shuffled prefix plus the index, modulo the number of subnets.
-/
def computeSubscribedSubnet (config : SubnetParameters)
    (shuffle : UInt64 → UInt64 → Base.Bytes32 → Except ε UInt64)
    (nodeId : NodeID) (epoch index : UInt64) : Except (SubnetError ε) SubnetID := do
  let permuted ← computeShuffledPrefix config shuffle nodeId epoch
  -- The subnet is `(p + i) mod n`, for the shuffled prefix `p`, the index `i` and `n` subnets.
  --
  -- The sum `p + i` is a 64-bit integer, and an overflow is an error.
  let subnet ← (Base.Uint64.addChecked permuted index).mapError
    fun _ => .subnetOverflow permuted index
  return subnet % config.ATTESTATION_SUBNET_COUNT

/-- The subnets of a node in an epoch, one for each index below the subnets per node. -/
def computeSubscribedSubnets (config : SubnetParameters)
    (shuffle : UInt64 → UInt64 → Base.Bytes32 → Except ε UInt64)
    (nodeId : NodeID) (epoch : UInt64) : Except (SubnetError ε) (List SubnetID) :=
  -- The subnets of the indices `0, ..., k - 1`, in order, for `k` subnets per node.
  (List.range config.SUBNETS_PER_NODE.toNat).mapM fun index =>
    computeSubscribedSubnet config shuffle nodeId epoch index.toUInt64

end EthLib.Networking.Gossip
