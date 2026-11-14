module

public import EthLib.Consensus.Proofs.Models.Network.Model
public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties

/-!
# Network assumptions for Ethereum fork choice

The generic network execution is specialized to honest Ethereum fork-choice duties.

SignsTarget describes signing witnesses inside the honest target-vote count hypothesis.

DelayFits, Prompt and BlocksAdmitted are separate assumptions of the duty/head endpoints.

Synchrony alone supplies neither timely processing nor successful block handling.

Separate handler-totality proofs could discharge BlocksAdmitted.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz Uint64

variable {preset : Preset} {fork : Fork}
variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- A validator signs a vote with a target, in a message sent by the time `last`. -/
def SignsTarget
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (v : ValidatorIndex) (target : Checkpoint) (last : ℕ) : Prop :=
  ∃ k, (e.world k).time ≤ last ∧ ∃ m ∈ (e.world k).sent, ∃ data,
    (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.target = target

variable (fork) in
/-- A vote sent at its deadline arrives before the next slot starts. -/
def DelayFits (config : Config) (genesisTimeMs : UInt64) (Δ : ℕ) : Prop :=
  (∃ due, getAttestationDueMs config fork = .ok due) ∧
  ∀ slot next start due following, addChecked slot 1 = .ok next →
    computeTimeAtSlotMs config genesisTimeMs slot = .ok start →
    getAttestationDueMs config fork = .ok due →
    computeTimeAtSlotMs config genesisTimeMs next = .ok following →
    start.toNat + due.toNat + Δ < following.toNat

/-- Honest receivers process messages immediately before and at slot boundaries up to `last`.

This is a processing hypothesis, not a consequence of synchrony. -/
def Prompt
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (last : ℕ) : Prop :=
  ∀ w ∈ J, ∀ slot start, computeTimeAtSlotMs config genesisTimeMs slot = .ok start →
    e.startTime ≤ start.toNat → start.toNat ≤ last →
    (∃ k, (e.world k).time = start.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w)) ∧
    (e.startTime < start.toNat → ∃ k, (e.world k).time + 1 = start.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w))

/-- Validated delayed blocks pass the receiver's remaining handler checks.

Synchrony supplies view membership, not success of carried votes inside onBlockWithVotes. -/
def BlocksAdmitted
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (GST Δ last : ℕ) : Prop :=
  ∀ v ∈ J, ∀ u ∈ J, ∀ n k, (e.world k).time ≤ last → ∀ signedBlock blockRoot state,
    .block signedBlock ∈ (e.world n).view v →
    ((e.world n).state v).blocks[blockRoot]? = some signedBlock.message →
    max (e.world n).time GST + Δ ≤ (e.world k).time →
    UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u) →
    SszType.hashTreeRoot signedBlock.message = .ok blockRoot →
    ((e.world k).state u).validateOnBlock config checks sources signedBlock blockRoot =
      .ok state →
    ∃ after, ((e.world k).state u).onBlockWithVotes config checks sources signedBlock = .ok after

end EthLib.Consensus.Models.Network
