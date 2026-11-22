module

public import EthLib.Base.Uint64

/-!
# `Networking.Gossip.Parameters`

The parameters of gossip on the consensus layer.

The parameters of the attestation subnets come from a configuration of the consensus layer.

Each one has the name it has in that configuration.

The gossip subnets and the node record both read them, so they are defined once, here.

The gossipsub parameters are fixed, except the lifetime of seen message IDs.

That lifetime is two epochs, so it follows the slot duration and the slots per epoch.
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

/-- The gossipsub parameters of the consensus layer, with times in milliseconds or seconds. -/
structure GossipsubParameters where
  /-- The target number of peers in the mesh of a topic. -/
  D : Nat
  /-- The fewest peers in the mesh of a topic before a node adds more. -/
  D_low : Nat
  /-- The most peers in the mesh of a topic before a node prunes some. -/
  D_high : Nat
  /-- The number of peers outside the mesh that a node tells of the messages it has. -/
  D_lazy : Nat
  /-- The time between two heartbeats, in milliseconds. -/
  heartbeat_interval_ms : Nat
  /-- How long a node keeps the peers of a topic it publishes to without joining, in seconds. -/
  fanout_ttl : Nat
  /-- The number of heartbeat windows for which a node keeps whole messages. -/
  mcache_len : Nat
  /-- The number of recent heartbeat windows whose messages a node tells peers of. -/
  mcache_gossip : Nat
  /-- How long a node keeps the ID of a message it has seen, in seconds. -/
  seen_ttl : Nat
  deriving DecidableEq, Repr

/--
The gossipsub parameters, given the slot duration in milliseconds and the slots per epoch.

A seen message ID lasts two epochs, in whole seconds, with the remainder dropped.

The slot duration and the slots per epoch are 64-bit configuration values.

So two epochs in milliseconds must fit 64 bits, and an overflow is an error.

Provenance: the [phase 0 networking text][p2p] of consensus-specs states these parameters.

[p2p]: https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/phase0/p2p-interface.md#the-gossip-domain-gossipsub
-/
def gossipsubParameters (slotDurationMs slotsPerEpoch : UInt64) :
    Except Base.ArithError GossipsubParameters := do
  -- `SLOT_DURATION_MS * SLOTS_PER_EPOCH * 2`, on `uint64`, where an overflow fails.
  let epochMs ← Base.Uint64.mulChecked slotDurationMs slotsPerEpoch
  let twoEpochsMs ← Base.Uint64.mulChecked epochMs 2
  return {
    D := 8
    D_low := 6
    D_high := 12
    D_lazy := 6
    heartbeat_interval_ms := 700
    fanout_ttl := 60
    mcache_len := 6
    mcache_gossip := 3
    -- `seen_ttl = milliseconds_to_seconds(...)`: whole seconds, with the remainder dropped.
    seen_ttl := (twoEpochsMs / 1000).toNat }

end EthLib.Networking.Gossip
