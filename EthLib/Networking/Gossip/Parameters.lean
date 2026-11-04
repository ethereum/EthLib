module

/-!
# `Networking.Gossip.Parameters`

The parameters of the attestation subnets, which a configuration of the consensus layer sets.

Each one has the name it has in that configuration.

The gossip subnets and the node record both read them, so they are defined once, here.
-/

@[expose] public section

namespace EthLib.Networking.Gossip

/-- The parameters of the attestation subnets that a node subscribes to and announces. -/
structure SubnetParameters where
  /-- The number of epochs that a subscription to a subnet lasts. -/
  EPOCHS_PER_SUBNET_SUBSCRIPTION : UInt64
  /-- The number of long-lived subnets that a node subscribes to. -/
  SUBNETS_PER_NODE : UInt64
  /-- The number of attestation subnets. -/
  ATTESTATION_SUBNET_COUNT : UInt64
  /-- The number of extra bits of a node ID that choose its subnets. -/
  ATTESTATION_SUBNET_EXTRA_BITS : UInt64
  deriving DecidableEq, Repr

end EthLib.Networking.Gossip
