module

public import EthLib.Consensus.Proofs.Models.Ffg.Monotonicity
public import EthLib.Consensus.Proofs.Transition.FfgFinalityChain

/-!
# Proofs: a chain's finalized checkpoint in larger vote and weight sets

The chain theorem uses the votes of its block steps and the balances of its justifying states.

Adding votes and allowed weights keeps its finalized checkpoint slack-finalized.

Its validator sets and second sets stay those of the chain theorem.

This result does not identify validator indices or establish root ancestry across two chains.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {ν β : Type*} {block : Root → β}

/-- Adding attestation data adds votes to the model. -/
theorem ffgVotes_mono {attested more : Set (ν × AttestationData)} (included : attested ⊆ more) :
    ffgVotes block attested ⊆ ffgVotes block more :=
  Set.image_mono included

variable {preset : Preset} {config : Config} {checks : SignatureChecks} [Preorder β]
  {attested : Set (ValidatorIndex × AttestationData)}
  {W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)}

/-- A chain's finalized checkpoint remains slack-finalized with more votes and allowed weights.

The validator sets are the active sets read in the last state, as in the chain theorem.

The larger sets must contain the votes and justifying balances of the run.

The preset, stake and root-order hypotheses of the chain theorem are unchanged. -/
theorem slackFinalized_activeSetAt_of_chainSteps_of_subset
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state)
    {last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ last)
    (meets : ∀ forked after,
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last →
      SlackStepBounds block forked after)
    (weights : ∀ c, justifyingBalances config checks block ⟨fork, state⟩ last c ⊆ W c)
    (votes : runVotes config checks ⟨fork, state⟩ last ⊆ attested) :
    SlackFinalized (fun c => activeSetAt last.state c.epoch)
      (fun c => activeSetAt last.state (c.epoch + 1)) W (block (Vector.replicate 32 0))
      (ffgVotes block attested) (last.state.finalizedCheckpoint.toFfg block) :=
  (slackFinalized_activeSetAt_of_chainSteps positive window apart computed steps meets).mono
    weights (ffgVotes_mono votes)

end EthLib.Consensus
