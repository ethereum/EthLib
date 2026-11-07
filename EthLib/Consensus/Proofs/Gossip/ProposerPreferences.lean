module

public import EthLib.Consensus.Gossip.ProposerPreferences
public import EthLib.Consensus.Proofs.HonestValidator
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the topic of the preferences of proposers

The topic checks preferences in a fixed order, so its outcome is a chain of checks.

The chain reads the clock, the dependent block, its advanced state and the signature.

Once these are computed, preferences are valid exactly when every check passes.

Valid preferences record their key, and preferences with the same key are then ignored.

A state names a validator as the proposer of each of its upcoming proposal slots.

So the validator passes the proposer check for that slot, with the lookahead of that state.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {seen : Seen} {store : Store preset fork} {gloas : .glamsterdam ≤ fork}
  {signed : SignedProposerPreferences} {currentTimeMs : UInt64}

/-- Preferences whose proposal slot and dependent root have valid preferences already are ignored.
-/
theorem validateProposerPreferences_of_seen {earlier : ProposerPreferences}
    (known : seen.proposerPreferencesFor
      (signed.message.proposalSlot, signed.message.dependentRoot) = some earlier) :
    validateProposerPreferences config checks seen store gloas signed currentTimeMs =
      .ok (.ignore "already seen preferences for this dependent root and proposal slot") := by
  simp [validateProposerPreferences, known, ignoreUnless, andThenM, pure, Except.pure]

/-- Valid preferences record their key, so preferences with the same key are then ignored. -/
theorem validateProposerPreferences_recordProposerPreferences
    {other : SignedProposerPreferences}
    (sameSlot : other.message.proposalSlot = signed.message.proposalSlot)
    (sameRoot : other.message.dependentRoot = signed.message.dependentRoot) :
    validateProposerPreferences config checks (seen.recordProposerPreferences signed) store gloas
        other currentTimeMs =
      .ok (.ignore "already seen preferences for this dependent root and proposal slot") :=
  validateProposerPreferences_of_seen (earlier := signed.message) (by
    simp [Seen.proposerPreferencesFor, Seen.recordProposerPreferences, sameSlot, sameRoot])

section Accept

variable {past future possible valid : Bool} {start dependentSlot : Slot}
  {block : BeaconBlock preset fork} {dependentState state : BeaconState preset fork}
  {proposer : ValidatorIndex}

/-- Once its inputs are computed, preferences are valid exactly when every check passes.

The inputs are the clock at the proposal slot and at the start of the lookahead.

They also include the dependent block with its state, and that state at the start of the lookahead.

The last ones are the proposer of the slot in that state, and the check of the signature. -/
theorem validateProposerPreferences_eq_accept
    (clockPast : store.isPastSlot config signed.message.proposalSlot currentTimeMs = .ok past)
    (started : computeShufflingLookaheadStartSlot preset
      (computeEpochAtSlot preset signed.message.proposalSlot) = .ok start)
    (clockFuture : store.isFutureSlot config start currentTimeMs = .ok future)
    (known : store.blocks[signed.message.dependentRoot]? = some block)
    (held : store.blockStates[signed.message.dependentRoot]? = some dependentState)
    (dependent : computeShufflingDependentSlot preset
      (computeEpochAtSlot preset signed.message.proposalSlot) = .ok dependentSlot)
    (checked : store.isValidDependentRoot config signed.message.dependentRoot dependentSlot =
      .ok possible)
    (advanced : lookaheadState config checks dependentState start = .ok state)
    (named : lookaheadProposer state (Nat.le_trans (by decide) gloas) start
      signed.message.proposalSlot = .ok proposer)
    (signature : isValidProposerPreferencesSignature config checks state signed = .ok valid) :
    validateProposerPreferences config checks seen store gloas signed currentTimeMs = .ok accept ↔
      seen.proposerPreferencesFor
          (signed.message.proposalSlot, signed.message.dependentRoot) = none ∧
        config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset signed.message.proposalSlot ∧
        past = false ∧ future = false ∧ block.slot ≤ dependentSlot ∧ possible = true ∧
        proposer = signed.message.validatorIndex ∧ valid = true := by
  unfold validateProposerPreferences
  simp only [clockPast, started, clockFuture, known, held, dependent, checked, advanced, named,
    signature, bind, Except.bind, pure, Except.pure, Except.mapError]
  simp only [ignoreUnless, rejectUnless, andThenM]
  repeat' split
  all_goals simp_all [Option.isNone_iff_eq_none, pure, Except.pure]

end Accept

/-! ## The proposer check and the upcoming proposal slots -/

/-- A slot that a validator proposes, among the upcoming slots of a state, names it as proposer.

The lookahead is that of the state, from the first slot of its current epoch. -/
theorem lookaheadProposer_of_mem_getUpcomingProposalSlots {state : BeaconState preset fork}
    {validatorIndex : ValidatorIndex} {slots : List Slot} {start slot : Slot}
    (upcoming : getUpcomingProposalSlots state gloas validatorIndex = .ok slots)
    (started : computeStartSlotAtEpoch preset (getCurrentEpoch state) = .ok start)
    (proposes : slot ∈ slots) :
    lookaheadProposer state (Nat.le_trans (by decide) gloas) start slot = .ok validatorIndex := by
  obtain ⟨offset, atOffset, -, named⟩ :=
    ((getUpcomingProposalSlots_spec upcoming started).1 slot).mp proposes
  have noBorrow : start ≤ slot := by
    rw [UInt64.le_iff_toNat_le]
    omega
  have difference : (slot - start).toNat = offset.val := by
    rw [UInt64.toNat_sub_of_le _ _ noBorrow]
    omega
  unfold lookaheadProposer
  simp only [subChecked, noBorrow, ite_true, Except.mapError, bind, Except.bind, difference,
    pure, Except.pure]
  rw [Vector.getElem?_eq_getElem offset.isLt]
  simp only [Fin.getElem_fin] at named
  rw [named]

end EthLib.Consensus
