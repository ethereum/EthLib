module

public import EthLib.Consensus.Gossip.InclusionList
public import EthLib.Base.Proofs.Uint64
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the topic of inclusion lists

The topic checks a list in a fixed order, so its outcome is a chain of checks.

Once the computed inputs are fixed, the outcome is that chain.

A list is valid exactly when every check passes.

Each valid list counts once for its slot, dependent root and member.

So gossip forwards at most two valid lists of a member for a slot and a dependent root.

A list that gossip accepts in its slot is accepted by the fork choice in that slot too.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {seen : Seen} {store : Store preset fork} {signed : SignedInclusionList}
  {currentTimeMs : UInt64}

/-- A list whose member has two valid lists for its slot and dependent root already is ignored. -/
theorem validateInclusionList_of_seen_twice
    (twice : 2 ≤ seen.inclusionListKeys.count
      (signed.message.slot, signed.message.dependentRoot, signed.message.validatorIndex)) :
    validateInclusionList config checks seen store signed currentTimeMs =
      .ok (.ignore "already seen two valid inclusion lists from this validator") := by
  have notBelow : ¬ seen.inclusionListKeys.count
      (signed.message.slot, signed.message.dependentRoot, signed.message.validatorIndex) < 2 := by
    omega
  simp [validateInclusionList, notBelow, pure, Except.pure]

/-- After two valid lists of a member for a slot and a dependent root, a third is ignored.

The three lists may differ in every other field. -/
theorem validateInclusionList_recordInclusionList_twice {first second : SignedInclusionList}
    (firstSlot : first.message.slot = signed.message.slot)
    (firstRoot : first.message.dependentRoot = signed.message.dependentRoot)
    (firstMember : first.message.validatorIndex = signed.message.validatorIndex)
    (secondSlot : second.message.slot = signed.message.slot)
    (secondRoot : second.message.dependentRoot = signed.message.dependentRoot)
    (secondMember : second.message.validatorIndex = signed.message.validatorIndex) :
    validateInclusionList config checks
        ((seen.recordInclusionList first).recordInclusionList second) store signed currentTimeMs =
      .ok (.ignore "already seen two valid inclusion lists from this validator") := by
  apply validateInclusionList_of_seen_twice
  simp [Seen.recordInclusionList, firstSlot, firstRoot, firstMember, secondSlot, secondRoot,
    secondMember]

section Chain

variable {current possible valid : Bool} {block : BeaconBlock preset fork}
  {dependentState state : BeaconState preset fork} {dependentSlot start : Slot}
  {committee : InclusionListCommittee preset}

/-- The outcome of a list is its chain of checks, in order.

It holds once the clock, the dependent block with its state and the dependent slot are fixed.

The test of the dependent block, the advanced state, the committee and the signature are fixed too.
-/
theorem validateInclusionList_eq
    (clock : store.isCurrentSlot config signed.message.slot currentTimeMs = .ok current)
    (known : store.blocks[signed.message.dependentRoot]? = some block)
    (held : store.blockStates[signed.message.dependentRoot]? = some dependentState)
    (dependent : computeShufflingDependentSlot preset
      (computeEpochAtSlot preset signed.message.slot) = .ok dependentSlot)
    (checked : store.isValidDependentRoot config signed.message.dependentRoot dependentSlot =
      .ok possible)
    (started : computeShufflingLookaheadStartSlot preset
      (computeEpochAtSlot preset signed.message.slot) = .ok start)
    (advanced : lookaheadState config checks dependentState start = .ok state)
    (seated : getInclusionListCommittee state signed.message.slot = .ok committee)
    (signature : isValidInclusionListSignature config state signed = .ok valid) :
    validateInclusionList config checks seen store signed currentTimeMs =
      .ok ((ignoreUnless (decide (seen.inclusionListKeys.count (signed.message.slot,
            signed.message.dependentRoot, signed.message.validatorIndex) < 2))
          "already seen two valid inclusion lists from this validator").andThen fun _ =>
        (ignoreUnless current "inclusion list is not for the current slot").andThen fun _ =>
        (ignoreUnless (signed.message.transactionsSize != 0)
          "inclusion list contains no transactions").andThen fun _ =>
        (rejectUnless (decide (signed.message.transactionsSize ≤
            config.MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST.toNat))
          "inclusion list transactions exceed the maximum size").andThen fun _ =>
        (rejectUnless (signed.message.transactions.data.toList.all (·.data.size != 0))
          "inclusion list contains an empty transaction").andThen fun _ =>
        (rejectUnless (decide (block.slot ≤ dependentSlot))
          "dependent block is after the shuffling dependent slot").andThen fun _ =>
        (ignoreUnless possible "dependent block is not a possible dependent block").andThen
          fun _ =>
        (rejectUnless (committee.toList.contains signed.message.validatorIndex)
          "includer is not a member of the committee").andThen fun _ =>
        rejectUnless valid "invalid inclusion list signature") := by
  unfold validateInclusionList
  simp only [clock, known, held, dependent, checked, started, advanced, seated, signature, bind,
    Except.bind, pure, Except.pure, Except.mapError, ignoreUnless_andThenM, ignoreUnless_andThen,
    rejectUnless_andThenM, rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- A list is valid exactly when every check passes, once its inputs are computed. -/
theorem validateInclusionList_eq_accept
    (clock : store.isCurrentSlot config signed.message.slot currentTimeMs = .ok current)
    (known : store.blocks[signed.message.dependentRoot]? = some block)
    (held : store.blockStates[signed.message.dependentRoot]? = some dependentState)
    (dependent : computeShufflingDependentSlot preset
      (computeEpochAtSlot preset signed.message.slot) = .ok dependentSlot)
    (checked : store.isValidDependentRoot config signed.message.dependentRoot dependentSlot =
      .ok possible)
    (started : computeShufflingLookaheadStartSlot preset
      (computeEpochAtSlot preset signed.message.slot) = .ok start)
    (advanced : lookaheadState config checks dependentState start = .ok state)
    (seated : getInclusionListCommittee state signed.message.slot = .ok committee)
    (signature : isValidInclusionListSignature config state signed = .ok valid) :
    validateInclusionList config checks seen store signed currentTimeMs = .ok accept ↔
      seen.inclusionListKeys.count (signed.message.slot, signed.message.dependentRoot,
          signed.message.validatorIndex) < 2 ∧
        current = true ∧ signed.message.transactionsSize ≠ 0 ∧
        signed.message.transactionsSize ≤ config.MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST.toNat ∧
        signed.message.transactions.data.toList.all (·.data.size != 0) = true ∧
        block.slot ≤ dependentSlot ∧ possible = true ∧
        signed.message.validatorIndex ∈ committee.toList ∧ valid = true := by
  rw [validateInclusionList_eq clock known held dependent checked started advanced seated
    signature]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept,
    decide_eq_true_eq, bne_iff_ne, ne_eq, List.contains_iff_mem]

/-- A list that gossip accepts passes the checks of the fork choice in the same store.

The clock of the store must be in the slot of the list.

The window, the due time and the time into the slot must compute. -/
theorem checkInclusionList_ok_of_validateInclusionList
    (clock : store.isCurrentSlot config signed.message.slot currentTimeMs = .ok current)
    (known : store.blocks[signed.message.dependentRoot]? = some block)
    (held : store.blockStates[signed.message.dependentRoot]? = some dependentState)
    (dependent : computeShufflingDependentSlot preset
      (computeEpochAtSlot preset signed.message.slot) = .ok dependentSlot)
    (checked : store.isValidDependentRoot config signed.message.dependentRoot dependentSlot =
      .ok possible)
    (started : computeShufflingLookaheadStartSlot preset
      (computeEpochAtSlot preset signed.message.slot) = .ok start)
    (advanced : lookaheadState config checks dependentState start = .ok state)
    (seated : getInclusionListCommittee state signed.message.slot = .ok committee)
    (signature : isValidInclusionListSignature config state signed = .ok valid)
    (inSlot : store.getCurrentSlot config = .ok signed.message.slot)
    {lastSlot : Slot}
    (window : addChecked signed.message.slot config.MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS =
      .ok lastSlot)
    {due : UInt64} (deadline : getInclusionListDueMs config = .ok due)
    {timeIntoSlot : UInt64} (into : store.getTimeIntoSlotMs config = .ok timeIntoSlot)
    (accepted : validateInclusionList config checks seen store signed currentTimeMs =
      .ok accept) :
    store.checkInclusionList config checks signed = .ok (decide (timeIntoSlot < due)) := by
  obtain ⟨-, -, nonempty, small, filled, early, isPossible, member, isValid⟩ :=
    (validateInclusionList_eq_accept clock known held dependent checked started advanced seated
      signature).mp accepted
  have notBefore : signed.message.slot ≤ lastSlot := by
    have := (addChecked_ok_iff.mp window).2
    rw [UInt64.le_iff_toNat_le]
    omega
  have sized : 0 < signed.message.transactionsSize := Nat.pos_of_ne_zero nonempty
  have allFilled : signed.message.transactions.data.toList.all (0 < ·.data.size) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at filled ⊢
    intro transaction mem
    exact Nat.pos_of_ne_zero (filled transaction mem)
  unfold Store.checkInclusionList
  simp only [inSlot, window, Store.block, known, Store.blockState, held, dependent, checked,
    started, advanced, seated, signature, deadline, into, isPossible, isValid, bind, Except.bind,
    pure, Except.pure, Except.mapError, ensure, UInt64.le_refl, notBefore, early, member,
    allFilled, ite_true]
  simp_all [InclusionList.transactionsSize]

end Chain

end EthLib.Consensus
