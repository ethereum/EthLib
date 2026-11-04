module

public import EthLib.Networking.Gossip.Subnet

/-!
# `Networking.Proofs.Gossip.Subnet`

What the choice of attestation subnets returns.

- A node gets as many subnets as the subnets per node, each below the number of subnets.
- The choice succeeds when the parameters are nonzero and small enough, and the shuffle succeeds.

These facts hold for every shuffle, so they do not depend on how the consensus layer shuffles.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Subnet

open EthLib.Networking.Gossip

variable {ε : Type} {config : AttestationSubnetConfig}
  {shuffle : UInt64 → UInt64 → ByteArray → Except ε UInt64} {nodeId : NodeID} {epoch : UInt64}

/-- A traversal that succeeds has one output per input, and each output comes from an input. -/
private theorem mapM_ok {α β : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) : ys.length = xs.length ∧ ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x <;> cases hxs : xs.mapM f <;>
      simp only [hx, hxs, bind, Except.bind, pure, Except.pure, reduceCtorEq,
        Except.ok.injEq] at h
    subst h
    obtain ⟨length, from_input⟩ := ih hxs
    refine ⟨by simp [length], ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, hx⟩
    · obtain ⟨x', hx', hf⟩ := from_input y hy
      exact ⟨x', List.mem_cons_of_mem x hx', hf⟩

/-- Every subnet is below the number of subnets. -/
theorem computeSubscribedSubnet_lt {index : UInt64} {subnet : SubnetID}
    (h : computeSubscribedSubnet config shuffle nodeId epoch index = .ok subnet) :
    subnet < config.subnetCount := by
  have count : config.subnetCount ≠ 0 := by
    intro zero
    simp [computeSubscribedSubnet, computeAttestationSubnetPrefixBits, zero, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at h
  have positive : 0 < config.subnetCount.toNat :=
    Nat.pos_of_ne_zero fun zero => count (UInt64.toNat_inj.mp (by simpa using zero))
  unfold computeSubscribedSubnet at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    Except.mapError] at h
  repeat' split at h
  all_goals try (cases h; done)
  simp only [Except.ok.injEq] at h
  subst h
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_mod]
  exact Nat.mod_lt _ positive

/-- A traversal succeeds when the function succeeds on every input. -/
private theorem mapM_exists_ok {α β : Type} {f : α → Except ε β} {xs : List α}
    (h : ∀ x ∈ xs, ∃ y, f x = .ok y) : ∃ ys, xs.mapM f = .ok ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := ih fun x' hx' => h x' (List.mem_cons_of_mem x hx')
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys, bind, Except.bind, pure, Except.pure]⟩

/-- A node gets as many subnets as the subnets per node, each below the number of subnets. -/
theorem computeSubscribedSubnets_ok {subnets : List SubnetID}
    (h : computeSubscribedSubnets config shuffle nodeId epoch = .ok subnets) :
    subnets.length = config.subnetsPerNode.toNat ∧
      ∀ subnet ∈ subnets, subnet < config.subnetCount := by
  obtain ⟨length, from_index⟩ := mapM_ok h
  refine ⟨by simpa using length, fun subnet member => ?_⟩
  obtain ⟨_, _, ok⟩ := from_index subnet member
  exact computeSubscribedSubnet_lt ok

/-- A sum below `2^64` does not overflow. -/
private theorem addChecked_of_lt {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    Base.Uint64.addChecked a b = .ok (a + b) := by
  simp [Base.Uint64.addChecked, h]

/-- A prefix of `b` bits of a node ID is below `2^b`. -/
theorem nodePrefix_lt (nodeId : NodeID) {bits : Nat} (h : bits ≤ NODE_ID_BITS) :
    nodeId.toNat >>> (NODE_ID_BITS - bits) < 2 ^ bits := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
    Nat.add_sub_cancel' h]
  exact nodeId.isLt

/-- The choice of one subnet succeeds when the parameters fit and the shuffle succeeds.

The shuffle must succeed on every index below the count, with a position below the count. -/
theorem computeSubscribedSubnet_exists {index : UInt64}
    (count : config.subnetCount ≠ 0) (epochs : config.epochsPerSubscription ≠ 0)
    (bits : Serialization.Ssz.depthFor config.subnetCount.toNat + config.extraBits.toNat < 64)
    (period : epoch.toNat + config.epochsPerSubscription.toNat ≤ 2 ^ 64)
    (shuffled : ∀ i n seed, i < n → ∃ p, shuffle i n seed = .ok p ∧ p < n)
    (small : index.toNat ≤ 2 ^ 63) :
    ∃ subnet, computeSubscribedSubnet config shuffle nodeId epoch index = .ok subnet := by
  have prefixBits : computeAttestationSubnetPrefixBits (ε := ε) config =
      .ok (Serialization.Ssz.depthFor config.subnetCount.toNat + config.extraBits.toNat) := by
    simp [computeAttestationSubnetPrefixBits, count, pure, Except.pure]
  generalize Serialization.Ssz.depthFor config.subnetCount.toNat + config.extraBits.toNat = b
    at prefixBits bits
  have below : 2 ^ b < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) bits
  have nodePrefix : nodeId.toNat >>> (NODE_ID_BITS - b) < 2 ^ b :=
    nodePrefix_lt nodeId (by unfold NODE_ID_BITS; omega)
  have offset :
      nodeId.toNat % config.epochsPerSubscription.toNat < config.epochsPerSubscription.toNat :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero fun zero => epochs (UInt64.toNat_inj.mp (by simpa using zero)))
  have toNat_of_lt {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]
  have key := fun seed => shuffled (nodeId.toNat >>> (NODE_ID_BITS - b)).toUInt64
    (2 ^ b).toUInt64 seed (by
      rw [UInt64.lt_iff_toNat_lt, toNat_of_lt (by omega), toNat_of_lt below]
      exact nodePrefix)
  have bitsFit : ¬64 ≤ b := by omega
  have half : 2 ^ b ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  have shifted := addChecked_of_lt (a := epoch)
    (b := (nodeId.toNat % config.epochsPerSubscription.toNat).toUInt64)
    (by rw [toNat_of_lt (by omega)]; omega)
  unfold computeSubscribedSubnet
  simp only [prefixBits, bind, Except.bind, pure, Except.pure, Except.mapError, epochs, bitsFit,
    shifted, ↓reduceIte]
  split
  · rename_i e he
    split at he
    · rename_i e' he'
      obtain ⟨p, hp, _⟩ := key _
      rw [hp] at he'
      cases he'
    · cases he
  · rename_i p hp
    split at hp
    · cases hp
    · rename_i p' hp'
      cases hp
      obtain ⟨q, hq, hqn⟩ := key _
      rw [hq] at hp'
      cases hp'
      rw [UInt64.lt_iff_toNat_lt, toNat_of_lt below] at hqn
      rw [addChecked_of_lt (by omega)]
      exact ⟨_, rfl⟩

/-- The choice of the subnets of a node succeeds when the parameters fit and the shuffle succeeds.

The shuffle must succeed on every index below the count, with a position below the count. -/
theorem computeSubscribedSubnets_exists
    (count : config.subnetCount ≠ 0) (epochs : config.epochsPerSubscription ≠ 0)
    (bits : Serialization.Ssz.depthFor config.subnetCount.toNat + config.extraBits.toNat < 64)
    (period : epoch.toNat + config.epochsPerSubscription.toNat ≤ 2 ^ 64)
    (shuffled : ∀ i n seed, i < n → ∃ p, shuffle i n seed = .ok p ∧ p < n)
    (perNode : config.subnetsPerNode.toNat ≤ 2 ^ 63) :
    ∃ subnets, computeSubscribedSubnets config shuffle nodeId epoch = .ok subnets :=
  mapM_exists_ok fun index member =>
    computeSubscribedSubnet_exists count epochs bits period shuffled (by
      have := List.mem_range.mp member
      have := config.subnetsPerNode.toNat_lt
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      omega)

end EthLib.Networking.Proofs.Gossip.Subnet
