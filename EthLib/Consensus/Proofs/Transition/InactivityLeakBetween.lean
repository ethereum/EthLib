module

public import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.ValidatorKeys

/-!
# Proofs: the slots and blocks between two epochs of a leak

The trace bound of an inactivity leak reads one validator before each epoch transition.

Between two epoch transitions, the chain runs blocks and slots that end no epoch.

A slot that runs no epoch keeps every balance, every score and the registry.

A block keeps each score and each effective balance of the registry before it.

It raises no balance of a validator that it does not credit.

The module follows the validator through any sequence of such steps.

After them the validator keeps its position, its key, its effective balance and its score.

It still has a balance, and that balance is no higher.

The steps stay within one fork.

The slot that runs an epoch transition, and an upgrade, are not among them.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- One step between two epoch transitions that credits nothing to one validator.

The validator is named by its position and by its key, given separately.

A slot step is one slot that does not end an epoch, so it runs no epoch transition.

A block step is a successful block whose proposer sits at another position.

From Altair no member that signs its sync aggregate has the key.

No deposit of the block carries the key; there are none from Heze. -/
inductive QuietStep (config : Config) (checks : SignatureChecks) (index : Nat)
    (key : Cryptography.Bls.BLSPubkey) :
    BeaconState preset fork → BeaconState preset fork → Prop where
  | slot {state after : BeaconState preset fork}
      (ok : advanceSlot config checks state = .ok after)
      (inside : (state.slot + 1) % preset.SLOTS_PER_EPOCH ≠ 0) :
      QuietStep config checks index key state after
  | block {state after : BeaconState preset fork} (engine : ExecutionEngine preset fork)
      (block : BeaconBlock preset fork)
      (ok : processBlock config checks engine state block = .ok after)
      (notProposer : block.proposerIndex.toNat ≠ index)
      (unsigned : ∀ altair : .altair ≤ fork,
        ∀ member ∈ ((state.currentSyncCommittee altair).value.pubkeys.toArray.zip
          (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray).toList,
          member.2 = true → member.1 ≠ key)
      (undeposited : ∀ before : fork < .hegota, ∀ deposit ∈ (block.body.deposits before).data,
        deposit.data.pubkey ≠ key) :
      QuietStep config checks index key state after

/-- A slot that ends no epoch keeps the registry, the balances and the scores. -/
theorem advanceSlot_quiet (ok : advanceSlot config checks state = .ok after)
    (inside : (state.slot + 1) % preset.SLOTS_PER_EPOCH ≠ 0) :
    after.validators = state.validators ∧ after.balances = state.balances ∧
      after.inactivityScores = state.inactivityScores := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  have same : next = state.slot + 1 := by
    apply UInt64.toNat_inj.mp
    have bound := next.toNat_lt_size
    rw [sum, UInt64.toNat_add, UInt64.toNat_one]
    simp only [UInt64.size] at bound
    omega
  unfold epochIfLast at epochedOk
  split at epochedOk
  · exact absurd (same ▸ ‹next % preset.SLOTS_PER_EPOCH = 0›) inside
  cases epochedOk
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  exact ⟨rfl, rfl, rfl⟩

/-- Steps that credit nothing to a validator keep what the trace bound reads of it.

The validator has a balance and the given key before the steps.

After them it keeps its position, its key, its effective balance and its score.

It still has a balance, and that balance is no higher.

The mixes must span more than the seed lookahead plus two epochs. -/
theorem quietSteps_kept
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {index : Nat} {key : Cryptography.Bls.BLSPubkey}
    (steps : Relation.ReflTransGen (QuietStep config checks index key) state after)
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (keyed : validator.pubkey = key) (held : index < state.balances.data.size) :
    ∃ now, after.validators.data[index]? = some now ∧ now.pubkey = key ∧
      now.effectiveBalance = validator.effectiveBalance ∧
      index < after.balances.data.size ∧ BalanceNotRaised index state after ∧
      ScoreKept index state after := by
  induction steps with
  | refl => exact ⟨validator, found, keyed, rfl, held, .refl _ _, .refl _ _⟩
  | tail _ step kept => ?_
  obtain ⟨now, atNow, nowKey, nowBalance, nowHeld, raised, scored⟩ := kept
  cases step with
  | slot ok inside =>
    obtain ⟨validators, balances, scores⟩ := advanceSlot_quiet ok inside
    refine ⟨now, by rw [validators]; exact atNow, nowKey, nowBalance,
      by rw [balances]; exact nowHeld,
      raised.trans (.of_balances balances index), scored.trans (.of_scores scores index)⟩
  | block engine block ok notProposer unsigned undeposited =>
    obtain ⟨later, atLater, laterKey⟩ :=
      validators_getElem?_of_validatorKeys_prefix (frame_processBlock ok).pubkeysPrefix atNow
    have inside := (Array.getElem?_eq_some_iff.mp atNow).1
    have effective := effectiveKept_processBlock ok index inside
    simp only [effectiveAt, atNow, atLater, Option.map_some, Option.getD_some] at effective
    rw [← nowKey] at unsigned undeposited
    exact ⟨later, atLater, laterKey.trans nowKey,
      (UInt64.toNat_inj.mp effective).trans nowBalance,
      balance_lt_size_processBlock apart ok atNow nowHeld notProposer unsigned undeposited,
      raised.trans
        (balanceNotRaised_processBlock apart ok atNow nowHeld notProposer unsigned undeposited),
      scored.trans (scoreKept_processBlock ok inside)⟩

end EthLib.Consensus
