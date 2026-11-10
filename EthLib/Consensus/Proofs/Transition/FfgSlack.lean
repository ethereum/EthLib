module

public import EthLib.Consensus.Proofs.Transition.FfgJustification

/-!
# Proofs: justification keeps the justified checkpoints slack-justified in Casper FFG

The bound that the epoch step gives for a link, up to churn, is a slack link of the model.

So the step keeps the two justified checkpoints of a state slack-justified in the model.

This is the step of an induction over the epochs of a chain, from the genesis checkpoint.

Each checkpoint of the model has its own weights, here the effective balances of one state.

A target is read at the step of its epoch and again at the next step, with new balances between.

So the sets and weights of a checkpoint need to match only the step that first justifies it.

Along one chain that step is unique.

Two branches can justify one checkpoint from two different states.

One set and one weights for that checkpoint then need the two states to agree on them.

No theorem shows that yet.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

The slack is the stake of the set `E(V t, U t)` of Gasper §8.6, Definition 8.1.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.Ffg

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {β : Type*} [Preorder β]
  {V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex}
  {w : Models.Ffg.Checkpoint β → ValidatorIndex → ℕ} {genesis : β}
  {votes : Set (Vote ValidatorIndex β)}

/-- The two justified checkpoints of the state are slack-justified in the model.

Each root maps to a block of the model. -/
def SlackJustifiedCheckpoints (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (w : Models.Ffg.Checkpoint β → ValidatorIndex → ℕ) (genesis : β)
    (votes : Set (Vote ValidatorIndex β)) (block : Root → β)
    (state : BeaconState preset fork) : Prop :=
  SlackJustified V U w genesis votes (state.previousJustifiedCheckpoint.toFfg block) ∧
    SlackJustified V U w genesis votes (state.currentJustifiedCheckpoint.toFfg block)

/-- The sets of the model match the state for the checkpoint of an epoch.

That checkpoint has the block of the root that the state records for the start of the epoch.

Its validator set is the active set of the epoch.

Under its weights, each of its validators weighs its effective balance in the state.

Each of its validators in its second set is active in the current epoch.

For the current epoch that always holds.

As the second set, the active set of the next epoch meets it for both recent epochs. -/
def TargetSetsMatch (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (w : Models.Ffg.Checkpoint β → ValidatorIndex → ℕ) (block : Root → β)
    (state : BeaconState preset fork)
    (epoch : Epoch) : Prop :=
  ∀ root, getBlockRoot state epoch = .ok root →
    V ⟨block root, epoch.toNat⟩ = (getActiveValidatorIndices state epoch).toFinset ∧
      (∀ index ∈ V ⟨block root, epoch.toNat⟩,
        w ⟨block root, epoch.toNat⟩ index = balanceAt state index.toNat) ∧
      V ⟨block root, epoch.toNat⟩ ∩ U ⟨block root, epoch.toNat⟩ ⊆
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset

/-- The bound of a link up to churn gives a slack link of the model.

The sets of the model must match the state for the checkpoint of the epoch.

The source must come before the target, in epoch and in the chain of the target. -/
theorem LinkWithChurn.slackLink {block : Root → β} {epoch : Epoch} {root : Root}
    {s : Models.Ffg.Checkpoint β}
    (link : LinkWithChurn state votes epoch s ⟨block root, epoch.toNat⟩)
    (sets : TargetSetsMatch V U w block state epoch) (rootOk : getBlockRoot state epoch = .ok root)
    (epochs : s.epoch < epoch.toNat) (chain : s.block ≤ block root) :
    SlackLink V U w votes s ⟨block root, epoch.toNat⟩ := by
  classical
  obtain ⟨set, weights, later⟩ := sets root rootOk
  set t : Models.Ffg.Checkpoint β := ⟨block root, epoch.toNat⟩
  refine ⟨epochs, chain, ?_⟩
  -- Each set in the bound lies in the target set, where the two stakes agree.
  have agree : ∀ S ⊆ V t, stake (w t) S = stake (fun index => balanceAt state index.toNat) S :=
    fun S sub => stake_congr fun index member => weights index (sub member)
  have exited : V t \ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ⊆
      V t \ U t := by
    intro index member
    simp only [Finset.mem_sdiff] at member ⊢
    exact ⟨member.1, fun inU => member.2 (later (Finset.mem_inter.mpr ⟨member.1, inU⟩))⟩
  have slack := stake_mono (w := w t) exited
  unfold LinkWithChurn at link
  rw [← set, ← agree _ subset_rfl, ← agree (signers (V t) votes s t) (Finset.filter_subset _ _),
    ← agree _ Finset.sdiff_subset] at link
  convert link.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 slack) _)

/-- Justification keeps the two justified checkpoints slack-justified in the model.

The hypotheses on the signed votes and the stake are those of the bound of a link up to churn.

The current justified epoch must be at most the previous epoch.

Once justification runs, the previous justified epoch must be below the previous epoch.

The step may make the checkpoint of the previous or the current epoch the current justified one.

If that changes the current justified checkpoint, the sets and weights of the model must match.

They must match the state for the epoch of the new checkpoint.

Otherwise they need not match.

Take each of the two recent epochs and the source of its link.

The block of that source must be in the chain of the block of the epoch.

That block is the block of the root that the state records for the start of the epoch.

For the genesis state, choose the block of the zero root as the genesis block of the model.

The hypothesis on the chain then needs that block below the block of each recent epoch. -/
theorem processJustificationAndFinalization_slackJustifiedCheckpoints
    (flagsSigned : TargetFlagsSigned config checks state)
    (pendingSigned : PendingSigned config checks state)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β)
    (contains : ffgVotes block {vote | SignedVote config checks state vote} ⊆ votes)
    (settled : JustifiedSettled state)
    (separated : GENESIS_EPOCH + 1 < getCurrentEpoch state →
      state.previousJustifiedCheckpoint.epoch < getPreviousEpoch state)
    (sets : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint →
      TargetSetsMatch V U w block state after.currentJustifiedCheckpoint.epoch)
    (chain : ∀ (current : Bool) (root : Root),
      getBlockRoot state (if current then getCurrentEpoch state else getPreviousEpoch state) =
          .ok root →
        block (if current then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint).root ≤ block root)
    (holds : SlackJustifiedCheckpoints V U w genesis votes block state)
    (computed : processJustificationAndFinalization state = .ok after) :
    SlackJustifiedCheckpoints V U w genesis votes block after := by
  by_cases early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1
  · exact processJustificationAndFinalization_early_eq early computed ▸ holds
  have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by decide
  have late : 1 < (getCurrentEpoch state).toNat := by
    have := mt UInt64.le_iff_toNat_le.mpr early
    omega
  rcases processJustificationAndFinalization_ok computed with same | ⟨_, _, _, weighed⟩
  · exact same ▸ holds
  refine ⟨?_, ?_⟩
  · -- The old current justified checkpoint becomes the previous one.
    rw [(weighJustificationAndFinalization_checkpoints weighed).1]
    exact holds.2
  rcases processJustificationAndFinalization_linkWithChurn flagsSigned pendingSigned large block
    contains computed with same | ⟨current, epoch, rootOk, link⟩
  · rw [same]
    exact holds.2
  by_cases kept : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
  · rw [kept]
    exact holds.2
  have targetSets := sets kept
  rw [epoch] at rootOk targetSets
  have before := chain current _ rootOk
  have settled' := UInt64.le_iff_toNat_le.mp settled
  have previous := getPreviousEpoch_toNat state
  -- The new checkpoint is the checkpoint of its epoch, with the root of its first slot.
  have target : after.currentJustifiedCheckpoint.toFfg block =
      ⟨block after.currentJustifiedCheckpoint.root,
        (if current then getCurrentEpoch state else getPreviousEpoch state).toNat⟩ := by
    simp only [Checkpoint.toFfg, epoch]
  rw [target] at link ⊢
  cases current
  · -- The previous epoch: its source is the previous justified checkpoint.
    simp only [Bool.false_eq_true, ↓reduceIte] at link before rootOk targetSets ⊢
    have below := UInt64.lt_iff_toNat_lt.mp
      (separated (UInt64.lt_iff_toNat_lt.mpr (by rw [one]; exact late)))
    exact .link holds.1 (link.slackLink targetSets rootOk below before)
  · -- The current epoch: its source is the current justified checkpoint.
    simp only [↓reduceIte] at link before rootOk targetSets ⊢
    exact .link holds.2 (link.slackLink targetSets rootOk (by simp only [Checkpoint.toFfg]; omega)
      before)

end EthLib.Consensus
