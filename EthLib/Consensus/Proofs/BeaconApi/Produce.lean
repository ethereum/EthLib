module

public import EthLib.Consensus.BeaconApi.Produce
public import EthLib.Consensus.Proofs.BeaconApi.Rewards

/-!
# Proofs: the value of a produced block

The consensus value of a block is the total of its block rewards, at 10^9 Wei per Gwei.

Under the hypotheses of the block rewards, it is the rise of the proposer's balance in Wei.

That rise is over the operations and the sync aggregate of the block.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork} {state : BeaconState preset fork}

/-- The consensus value of a block is the total of its block rewards, in Wei. -/
theorem consensusBlockValue_ok_iff {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork} {value : Nat} :
    consensusBlockValue config checks engine state block = .ok value ↔
      ∃ rewards, blockRewards config checks engine state block = .ok rewards ∧
        value = rewards.total.toNat * GWEI_TO_WEI := by
  unfold consensusBlockValue
  cases blockRewards config checks engine state block with
  | error error => simp [bind, Except.bind]
  | ok rewards =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    exact ⟨fun valued => ⟨rewards, rfl, valued.symm⟩, fun ⟨_, same, valued⟩ => by
      cases same
      exact valued.symm⟩

/-- The consensus value of a block is the rise of the proposer's balance, in Wei.

The rise is over the operations and the sync aggregate of the block.

The hypotheses are those under which the block rewards give that rise. -/
theorem consensusBlockValue_balance {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork} {value : Nat}
    {after : BeaconState preset fork} {validator : Validator}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (applied : processBlock config checks engine state block = .ok after)
    (valued : consensusBlockValue config checks engine state block = .ok value)
    (found : state.validators.data[block.proposerIndex.toNat]? = some validator)
    (held : block.proposerIndex.toNat < state.balances.data.size)
    (unslashedByProposers : ∀ slashing ∈ block.body.proposerSlashings.data,
      slashing.signedHeader1.message.proposerIndex ≠ block.proposerIndex)
    (unslashedByAttesters : ∀ slashing ∈ block.body.attesterSlashings.data,
      block.proposerIndex ∉ slashingIndices slashing)
    (undeposited : ∀ before : fork < .pectra,
      ∀ deposit ∈ (block.body.deposits (Nat.lt_trans before (by decide))).data,
        deposit.data.pubkey ≠ validator.pubkey)
    (unswitched : ∀ electra : .pectra ≤ fork ∧ fork < .glamsterdam,
      ∀ request ∈ (block.body.executionRequests electra).consolidations.data,
        request.sourcePubkey ≠ validator.pubkey)
    (unseated : ∀ altair : .altair ≤ fork,
      validator.pubkey ∉ (state.currentSyncCommittee altair).value.pubkeys.toList) :
    ∃ start balance final, stateBeforeOperations config checks engine state block = .ok start ∧
      start.balances.data[block.proposerIndex.toNat]? = some balance ∧
      after.balances.data[block.proposerIndex.toNat]? = some final ∧
      final.toNat * GWEI_TO_WEI = balance.toNat * GWEI_TO_WEI + value := by
  obtain ⟨rewards, answered, rfl⟩ := consensusBlockValue_ok_iff.mp valued
  obtain ⟨start, balance, final, startOk, balanceOk, finalOk, risen⟩ :=
    blockRewards_balance apart applied answered found held unslashedByProposers
      unslashedByAttesters undeposited unswitched unseated
  exact ⟨start, balance, final, startOk, balanceOk, finalOk, by rw [risen, Nat.add_mul]⟩

end EthLib.Consensus.BeaconApi
