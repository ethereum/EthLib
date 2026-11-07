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

A node stays subscribed to a few attestation subnets for a period of epochs.

Its node ID and the period choose the subnets, so any peer can compute them.

The top bits of the node ID give a prefix, and a shuffle seeded by the period permutes it.

The node takes the subnets that start at the permuted prefix, modulo the number of subnets.

The node ID modulo the period length shifts the start of each period.

So nodes do not all change their subnets at once.

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
  /-- The epoch plus the offset of the node is 2^64 or more. -/
  | epochOverflow
  /-- The prefix has 64 bits or more, so the number of prefixes is not below 2^64. -/
  | prefixBitsTooLarge (bits : Nat)
  /-- The permuted prefix plus the index of the subnet is 2^64 or more. -/
  | subnetOverflow
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
  | .epochOverflow => 103
  | .prefixBitsTooLarge _ => 104
  | .subnetOverflow => 105
  | .shuffle _ => 106

variable {ε : Type}

/-- The number of node ID bits in the prefix.

It is the smallest `b` with `2^b` at least the number of subnets, plus the extra bits. -/
def computeAttestationSubnetPrefixBits (config : SubnetParameters) :
    Except (SubnetError ε) Nat :=
  if config.ATTESTATION_SUBNET_COUNT = 0 then throw .zeroSubnetCount
  else
    return Serialization.Ssz.depthFor config.ATTESTATION_SUBNET_COUNT.toNat +
      config.ATTESTATION_SUBNET_EXTRA_BITS.toNat

/-- The shuffled prefix of a node in an epoch, which every index of the node shares.

`shuffle i n seed` is the position of `i` in a permutation of `0, …, n - 1` that the seed selects.

`b` is the number of prefix bits, and the prefix is the top `b` bits of the node ID.

The shuffle permutes the prefix among all `2^b` prefixes.

The offset is the node ID modulo the epochs per subscription.

The period is `(epoch + offset) / epochs per subscription`.

The seed is the SHA-256 hash of the period as eight little-endian bytes.
-/
def computeShuffledPrefix (config : SubnetParameters)
    (shuffle : UInt64 → UInt64 → Base.Bytes32 → Except ε UInt64)
    (nodeId : NodeID) (epoch : UInt64) : Except (SubnetError ε) UInt64 := do
  let bits ← computeAttestationSubnetPrefixBits config
  let nodePrefix := nodeId.toNat >>> (NODE_ID_BITS - bits)
  if config.EPOCHS_PER_SUBNET_SUBSCRIPTION = 0 then throw .zeroEpochsPerSubscription
  let nodeOffset := (nodeId.toNat % config.EPOCHS_PER_SUBNET_SUBSCRIPTION.toNat).toUInt64
  let shifted ← (Base.Uint64.addChecked epoch nodeOffset).mapError fun _ => .epochOverflow
  let period := shifted / config.EPOCHS_PER_SUBNET_SUBSCRIPTION
  let seed := Cryptography.Hash.Sha256.hash32 ⟨(Base.uintToBytes 8 period.toNat).toArray⟩
  if 64 ≤ bits then throw (.prefixBitsTooLarge bits)
  (shuffle nodePrefix.toUInt64 (2 ^ bits).toUInt64 seed).mapError .shuffle

/-- The subnet with a given index among the subnets of a node in an epoch.

The subnet is the shuffled prefix plus the index, modulo the number of subnets.
-/
def computeSubscribedSubnet (config : SubnetParameters)
    (shuffle : UInt64 → UInt64 → Base.Bytes32 → Except ε UInt64)
    (nodeId : NodeID) (epoch index : UInt64) : Except (SubnetError ε) SubnetID := do
  let permuted ← computeShuffledPrefix config shuffle nodeId epoch
  let subnet ← (Base.Uint64.addChecked permuted index).mapError fun _ => .subnetOverflow
  return subnet % config.ATTESTATION_SUBNET_COUNT

/-- The subnets of a node in an epoch, one for each index below the subnets per node. -/
def computeSubscribedSubnets (config : SubnetParameters)
    (shuffle : UInt64 → UInt64 → Base.Bytes32 → Except ε UInt64)
    (nodeId : NodeID) (epoch : UInt64) : Except (SubnetError ε) (List SubnetID) :=
  (List.range config.SUBNETS_PER_NODE.toNat).mapM fun index =>
    computeSubscribedSubnet config shuffle nodeId epoch index.toUInt64

end EthLib.Networking.Gossip
