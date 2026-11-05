module

public import EthLib.Consensus.Gossip.Topics
public import EthLib.Consensus.Proofs.ShufflePermutation
public import EthLib.Networking.Proofs.Gossip.Subnet
public import EthLib.Networking.Proofs.Gossip.Topic

/-!
# `Consensus.Proofs.Gossip.Topics`

Properties of the gossip topics and of the subnets of messages.

- Each topic name parses back to its topic, so no two topics share a name.
- Every subnet of a topic of a fork is below the number of subnets of its kind.
- Each subnet that a message is sent on is below that number.
- A node subscribes to as many attestation subnets as the configuration says.
- The topics of Gloas are those of Fulu, then the four topics that Gloas adds.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.Gossip.Topics

open EthLib.Base
open EthLib.Consensus
open EthLib.Networking.Gossip
open EthLib.Networking.Proofs.Gossip.Topic

/-- The name of a subnet topic holds a decimal digit, from its subnet ID. -/
theorem exists_digit_subnetTopicName (base : String) (subnet : SubnetID) :
    ∃ c ∈ (subnetTopicName base subnet).toList, c.isDigit = true := by
  obtain ⟨c, member⟩ :=
    List.exists_mem_of_ne_nil _ (Nat.toDigits_ne_nil (b := 10) (n := subnet.toNat))
  refine ⟨c, ?_, Nat.isDigit_of_mem_toDigits (by decide) (by decide) member⟩
  simp [subnetTopicName, member]

/-- No name of a topic with no subnet holds a decimal digit. -/
theorem no_digit_global : ∀ topic ∈ GossipTopic.global, ∀ c ∈ topic.name.toList,
    c.isDigit = false := by
  decide

/-- The name of a subnet topic is not the name of a topic with no subnet. -/
theorem find?_global_subnetTopicName {t : GossipTopic} {base : String} {subnet : SubnetID}
    (named : t.name = subnetTopicName base subnet) :
    GossipTopic.global.find? (·.name == t.name) = none := by
  rw [List.find?_eq_none]
  intro topic member same
  obtain ⟨c, inside, digit⟩ := exists_digit_subnetTopicName base subnet
  rw [← named, ← (beq_iff_eq.mp same)] at inside
  simp [no_digit_global topic member c inside] at digit

/--
A base name reads no subnet in the names of another base name.

Neither base, followed by `_`, may start the other.
-/
theorem parseSubnetTopicName_other {base other : String} (subnet : SubnetID)
    (differ : (base ++ "_").toList.isPrefixOf (other ++ "_").toList = false ∧
      (other ++ "_").toList.isPrefixOf (base ++ "_").toList = false) :
    parseSubnetTopicName base (subnetTopicName other subnet) = none := by
  have shape : (subnetTopicName other subnet).toList =
      (other ++ "_").toList ++ Nat.toDigits 10 subnet.toNat := by
    simp [subnetTopicName]
  -- Two prefixes of one list are comparable, and the two base names are not.
  have notPrefix : ¬ ((base ++ "_").toList <+: (other ++ "_").toList ++
      Nat.toDigits 10 subnet.toNat) := by
    intro prefixed
    rcases List.prefix_or_prefix_of_prefix prefixed (List.prefix_append _ _) with left | right
    · rw [← List.isPrefixOf_iff_prefix, differ.1] at left
      cases left
    · rw [← List.isPrefixOf_iff_prefix, differ.2] at right
      cases right
  have fails : ((base ++ "_").toList.isPrefixOf
      ((other ++ "_").toList ++ Nat.toDigits 10 subnet.toNat)) = false := by
    rwa [Bool.eq_false_iff, ne_eq, List.isPrefixOf_iff_prefix]
  simp only [parseSubnetTopicName, dropPrefix?, shape, fails]
  rfl

/-- The name of every topic parses back to the topic. -/
theorem ofName?_name (topic : GossipTopic) : GossipTopic.ofName? topic.name = some topic := by
  cases topic <;>
    first
    | rfl
    | (rename_i subnet
       rw [GossipTopic.ofName?, find?_global_subnetTopicName rfl]
       simp (disch := decide) only [GossipTopic.name, GossipTopic.subnetBases,
         List.findSome?_cons, parseSubnetTopicName_subnetTopicName, Option.map_some,
         parseSubnetTopicName_other, Option.map_none])

/-- Two topics with one name are one topic. -/
theorem name_injective : Function.Injective GossipTopic.name := fun a b same => by
  have := ofName?_name a
  rw [same, ofName?_name b] at this
  exact (Option.some.inj this).symm

/-- A number below a 64-bit count is the same number as a 64-bit integer. -/
theorem ofNat_lt {a : Nat} {count : UInt64} (lt : a < count.toNat) : UInt64.ofNat a < count := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_trans lt count.toNat_lt)]
  exact lt

/-- Every attestation subnet topic of a fork is below the number of attestation subnets. -/
theorem gossipTopics_beaconAttestation {config : Config} {fork : Fork}
    {topics : List GossipTopic} (listed : config.gossipTopics fork = some topics)
    {subnet : SubnetID} (member : .beaconAttestation subnet ∈ topics) :
    subnet < config.ATTESTATION_SUBNET_COUNT := by
  unfold Config.gossipTopics at listed
  split at listed
  · cases listed
  · cases listed
    -- Only the attestation subnets hold an attestation topic.
    simp only [subnetTopics, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.mem_nil_iff, reduceCtorEq, or_false, false_or] at member
    rcases member with ((((⟨a, lt, same⟩ | other) | other) | other) | other) | other
    · cases same
      exact ofNat_lt lt
    all_goals
      first
      | simp [GossipTopic.gloas] at other
      | (split at other <;> simp [List.mem_append, List.mem_cons, List.mem_map] at other)

/-- The topics of Gloas are those of Fulu, then the four topics that Gloas adds. -/
theorem gossipTopics_gloas {config : Config} {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (beforeHeze : fork < .hegota) :
    config.gossipTopics fork = (config.gossipTopics .fusaka).map (· ++ GossipTopic.gloas) := by
  have notHeze : ¬ (.hegota ≤ fork) := Nat.not_le_of_lt beforeHeze
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) gloas
  have shapella : Fork.shapella ≤ fork := Nat.le_trans (by decide) gloas
  have fusaka : Fork.fusaka ≤ fork := Nat.le_trans (by decide) gloas
  have blobs : config.blobSidecarSubnetCount fork = config.blobSidecarSubnetCount .fusaka := by
    simp (config := { decide := true }) [Config.blobSidecarSubnetCount, fusaka]
  simp only [Config.gossipTopics, notHeze, altair, shapella, fusaka, gloas, blobs,
    ↓reduceIte, List.append_assoc]
  simp (config := { decide := true }) [List.append_assoc]

/-- An attestation is sent on a subnet below the number of attestation subnets. -/
theorem computeSubnetForAttestation_lt {preset : Preset} {config : Config}
    {committeesPerSlot : UInt64} {slot : Slot} {committeeIndex : CommitteeIndex}
    {subnet : SubnetID}
    (computed : computeSubnetForAttestation preset config committeesPerSlot slot committeeIndex =
      .ok subnet) :
    subnet < config.ATTESTATION_SUBNET_COUNT := by
  unfold computeSubnetForAttestation at computed
  by_cases zero : config.ATTESTATION_SUBNET_COUNT = 0
  · simp [zero, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at computed
  · simp only [zero, ite_false, bind, Except.bind, Except.mapError, pure, Except.pure] at computed
    repeat' split at computed
    all_goals try (cases computed; done)
    cases computed
    exact UInt64.mod_lt _ (UInt64.pos_iff_ne_zero.mpr zero)

/-- A blob sidecar is sent on a subnet below the number of blob subnets of its fork. -/
theorem computeSubnetForBlobSidecar_lt {config : Config} {fork : Fork} {blobIndex : BlobIndex}
    {subnet : SubnetID}
    (computed : computeSubnetForBlobSidecar config fork blobIndex = .ok subnet) :
    subnet < config.blobSidecarSubnetCount fork := by
  unfold computeSubnetForBlobSidecar at computed
  by_cases zero : config.blobSidecarSubnetCount fork = 0
  · simp [zero, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at computed
  · simp only [zero, ite_false, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at computed
    subst computed
    exact UInt64.mod_lt _ (UInt64.pos_iff_ne_zero.mpr zero)

/-- A data column sidecar is sent on a subnet below the number of column subnets. -/
theorem computeSubnetForDataColumnSidecar_lt {config : Config} {columnIndex : UInt64}
    {subnet : SubnetID}
    (computed : computeSubnetForDataColumnSidecar config columnIndex = .ok subnet) :
    subnet < config.DATA_COLUMN_SIDECAR_SUBNET_COUNT := by
  unfold computeSubnetForDataColumnSidecar at computed
  by_cases zero : config.DATA_COLUMN_SIDECAR_SUBNET_COUNT = 0
  · simp [zero, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at computed
  · simp only [zero, ite_false, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at computed
    subst computed
    exact UInt64.mod_lt _ (UInt64.pos_iff_ne_zero.mpr zero)

/-- The shuffle of the preset places every index below the count at a position below it. -/
theorem computeShuffledIndex_bounded (preset : Preset) :
    ∀ i n (seed : ByteArray), i < n → ∃ p,
      computeShuffledIndex preset i n (seedOfDigest seed) = .ok p ∧ p < n := by
  intro i n seed lt
  refine ⟨_, computeShuffledIndex_eq lt, ?_⟩
  have bound := Shuffle.shuffledIndex_lt (rounds := preset.SHUFFLE_ROUND_COUNT.toNat)
    (seed := seedOfDigest seed) (UInt64.lt_iff_toNat_lt.mp lt)
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans bound n.toNat_lt)]
  exact bound

/--
A node gets the subnets per node, each below the number of attestation subnets.

The counts must be positive, and the prefix must have fewer than 64 bits.

The epoch must leave room for one subscription period.

The subnets per node must be at most 2^63.
-/
theorem computeSubscribedSubnets_ok {preset : Preset} {config : Config}
    {nodeId : NodeID} {epoch : Epoch}
    (count : config.ATTESTATION_SUBNET_COUNT ≠ 0)
    (epochs : config.EPOCHS_PER_SUBNET_SUBSCRIPTION ≠ 0)
    (bits : Serialization.Ssz.depthFor config.ATTESTATION_SUBNET_COUNT.toNat +
      config.ATTESTATION_SUBNET_EXTRA_BITS.toNat < 64)
    (period : epoch.toNat + config.EPOCHS_PER_SUBNET_SUBSCRIPTION.toNat ≤ 2 ^ 64)
    (perNode : config.SUBNETS_PER_NODE.toNat ≤ 2 ^ 63) :
    ∃ subnets, computeSubscribedSubnets preset config nodeId epoch = .ok subnets ∧
      subnets.length = config.SUBNETS_PER_NODE.toNat ∧
      ∀ subnet ∈ subnets, subnet < config.ATTESTATION_SUBNET_COUNT := by
  obtain ⟨subnets, chosen⟩ := Networking.Proofs.Gossip.Subnet.computeSubscribedSubnets_exists
    (config := config.toSubnetParameters) (nodeId := nodeId) (epoch := epoch)
    count epochs bits period (computeShuffledIndex_bounded preset) perNode
  exact ⟨subnets, chosen, Networking.Proofs.Gossip.Subnet.computeSubscribedSubnets_ok chosen⟩

end EthLib.Consensus.Proofs.Gossip.Topics
