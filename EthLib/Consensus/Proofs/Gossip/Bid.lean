module

public import EthLib.Consensus.Gossip.Bid
public import EthLib.Base.Proofs.Uint64
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the topic of bids

The topic checks a bid in a fixed order, so its outcome is a chain of checks.

Once the computed inputs are fixed, the outcome is that chain.

A bid is valid exactly when every check passes.

A valid bid records its key, and a bid with the same key is then ignored.

Each valid bid beats the best value before it, for its slot and parents.

So the best value recorded for a slot and its parents only grows.

A compatible gas limit moves from the parent's limit by less than a 1024th of it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {seen : Seen} {store : Store preset fork} {gloas : .glamsterdam ≤ fork}
  {signed : SignedExecutionPayloadBid preset fork} {currentTimeMs : UInt64}

/-! ## The gas limit -/

/-- A compatible gas limit is within the bounds that the parent's limit sets.

The bounds are the parent's limit minus and plus a 1024th of it, less one. -/
theorem isGasLimitTargetCompatible_bounds {parent gasLimit target : UInt64}
    (compatible : isGasLimitTargetCompatible parent gasLimit target = .ok true) :
    parent.toNat - (parent.toNat / 1024 - 1) ≤ gasLimit.toNat ∧
      gasLimit.toNat ≤ parent.toNat + (parent.toNat / 1024 - 1) := by
  unfold isGasLimitTargetCompatible at compatible
  have difference : (saturatingSub (parent / 1024) 1).toNat = parent.toNat / 1024 - 1 := by
    rw [toNat_saturatingSub, UInt64.toNat_div]
    rfl
  have below : saturatingSub (parent / 1024) 1 ≤ parent := by
    rw [UInt64.le_iff_toNat_le, difference]
    omega
  cases sum : addChecked parent (saturatingSub (parent / 1024) 1) with
  | error e => simp [sum, bind, Except.bind] at compatible
  | ok high =>
    have highNat := (addChecked_ok_iff.mp sum).2
    rw [difference] at highNat
    have lowNat : (parent - saturatingSub (parent / 1024) 1).toNat =
        parent.toNat - (parent.toNat / 1024 - 1) := by
      rw [UInt64.toNat_sub_of_le _ _ below, difference]
    simp only [sum, bind, Except.bind, pure, Except.pure] at compatible
    split at compatible
    · simp only [Except.ok.injEq, beq_iff_eq] at compatible
      rw [compatible, lowNat]
      omega
    · split at compatible
      · simp only [Except.ok.injEq, beq_iff_eq] at compatible
        rw [compatible, highNat]
        omega
      · rename_i notLow notHigh
        simp only [Except.ok.injEq, beq_iff_eq] at compatible
        subst compatible
        rw [UInt64.lt_iff_toNat_lt, lowNat] at notLow
        rw [UInt64.lt_iff_toNat_lt, highNat] at notHigh
        omega

/-- A compatible gas limit differs from a parent's limit of at least 1024 by less than its 1024th.
-/
theorem isGasLimitTargetCompatible_close {parent gasLimit target : UInt64}
    (large : 1024 ≤ parent.toNat)
    (compatible : isGasLimitTargetCompatible parent gasLimit target = .ok true) :
    gasLimit.toNat < parent.toNat + parent.toNat / 1024 ∧
      parent.toNat < gasLimit.toNat + parent.toNat / 1024 := by
  have := isGasLimitTargetCompatible_bounds compatible
  omega

/-! ## Seen keys -/

/-- A bid whose slot, parents and builder have a valid bid already is ignored. -/
theorem validateExecutionPayloadBid_of_seen
    (known : (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot,
      signed.message.builderIndex) ∈ seen.executionPayloadBids) :
    validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok (.ignore "already seen valid bid for this slot, parent, and builder") := by
  simp [validateExecutionPayloadBid, known, pure, Except.pure]

/-- After a valid bid, a bid of the same builder for the same slot and parents is ignored. -/
theorem validateExecutionPayloadBid_recordExecutionPayloadBid
    {other : SignedExecutionPayloadBid preset fork}
    (sameSlot : other.message.slot = signed.message.slot)
    (sameHash : other.message.parentBlockHash = signed.message.parentBlockHash)
    (sameRoot : other.message.parentBlockRoot = signed.message.parentBlockRoot)
    (sameBuilder : other.message.builderIndex = signed.message.builderIndex) :
    validateExecutionPayloadBid config checks (seen.recordExecutionPayloadBid signed) store gloas
        other currentTimeMs =
      .ok (.ignore "already seen valid bid for this slot, parent, and builder") :=
  validateExecutionPayloadBid_of_seen (by
    simp [Seen.recordExecutionPayloadBid, sameSlot, sameHash, sameRoot, sameBuilder])

/-- After a valid bid, the best value for its slot and parents is its own value. -/
theorem bestExecutionPayloadBidFor_recordExecutionPayloadBid :
    (seen.recordExecutionPayloadBid signed).bestExecutionPayloadBidFor
        (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot) =
      some signed.message.value := by
  simp [Seen.recordExecutionPayloadBid, Seen.bestExecutionPayloadBidFor]

/-- A bid whose value does not beat the best value for its slot and parents is ignored.

That check comes after the check of the seen key. -/
theorem validateExecutionPayloadBid_of_not_best {best : Gwei}
    (fresh : (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot,
      signed.message.builderIndex) ∉ seen.executionPayloadBids)
    (recorded : seen.bestExecutionPayloadBidFor
      (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot) =
        some best)
    (low : signed.message.value ≤ best) :
    validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok (.ignore "bid is not the highest value bid seen for this slot and parent") := by
  have notBelow : ¬best < signed.message.value := by
    rw [UInt64.lt_iff_toNat_lt]
    rw [UInt64.le_iff_toNat_le] at low
    omega
  simp [validateExecutionPayloadBid, fresh, recorded, notBelow, pure, Except.pure]

/-- A valid bid beats the best value recorded for its slot and parents, if there is one. -/
theorem lt_value_of_validateExecutionPayloadBid_eq_accept {best : Gwei}
    (valid : validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok accept)
    (recorded : seen.bestExecutionPayloadBidFor
      (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot) =
        some best) :
    best < signed.message.value := by
  by_cases seenKey : (signed.message.slot, signed.message.parentBlockHash,
      signed.message.parentBlockRoot, signed.message.builderIndex) ∈ seen.executionPayloadBids
  · rw [validateExecutionPayloadBid_of_seen seenKey] at valid
    cases valid
  · by_cases below : best < signed.message.value
    · exact below
    · have low : signed.message.value ≤ best := by
        rw [UInt64.lt_iff_toNat_lt] at below
        rw [UInt64.le_iff_toNat_le]
        omega
      rw [validateExecutionPayloadBid_of_not_best seenKey recorded low] at valid
      cases valid

/-! ## The chain of checks -/

section Chain

variable {timely onHead compatible active covered exiting valid : Bool}
  {parent : BeaconBlock preset fork} {state advanced : BeaconState preset fork}
  {lookahead : Epoch} {dependentRoot : Root} {preferences : ProposerPreferences}
  {parentGasLimit : UInt64} {randao : Bytes32} {builder : Builder}

/-- The outcome of a bid is its chain of checks, in order.

It holds once the clock, the parent block, its state, the lookahead and the dependent root are set.

The preferences, the parent gas limit and the head test must be fixed too.

So must the RANDAO mix, the advanced state, the builder and the tests on the builder. -/
theorem validateExecutionPayloadBid_eq
    (clock : store.isCurrentOrNextSlot config signed.message.slot currentTimeMs = .ok timely)
    (known : store.blocks[signed.message.parentBlockRoot]? = some parent)
    (held : store.blockStates[signed.message.parentBlockRoot]? = some state)
    (reach : addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD = .ok lookahead)
    (dependent : store.getShufflingDependentRoot signed.message.parentBlockRoot
      (computeEpochAtSlot preset signed.message.slot) = .ok dependentRoot)
    (preferred : seen.proposerPreferencesFor (signed.message.slot, dependentRoot) =
      some preferences)
    (payload : seen.executionPayloadGasLimitFor signed.message.parentBlockHash =
      some parentGasLimit)
    (gas : isGasLimitTargetCompatible parentGasLimit signed.message.gasLimit
      preferences.targetGasLimit = .ok compatible)
    (branch : store.isBidCompatibleWithHead config gloas signed.message = .ok onHead)
    (mix : getRandaoMix state (getCurrentEpoch state) = .ok randao)
    (slots : processSlots config checks state signed.message.slot = .ok advanced)
    (found : (advanced.builders gloas).data[signed.message.builderIndex.toNat]? = some builder)
    (activity : isActiveBuilder advanced gloas signed.message.builderIndex = .ok active)
    (funds : canBuilderCoverBid advanced gloas signed.message.builderIndex signed.message.value =
      .ok covered)
    (exit : builderMayExit store gloas advanced signed.message builder = .ok exiting)
    (signature : verifyExecutionPayloadBidSignature config checks advanced gloas signed =
      .ok valid) :
    validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok ((ignoreUnless (!seen.executionPayloadBids.contains (signed.message.slot,
            signed.message.parentBlockHash, signed.message.parentBlockRoot,
            signed.message.builderIndex))
          "already seen valid bid for this slot, parent, and builder").andThen fun _ =>
        (ignoreUnless ((seen.bestExecutionPayloadBidFor (signed.message.slot,
            signed.message.parentBlockHash, signed.message.parentBlockRoot)).all
            (· < signed.message.value))
          "bid is not the highest value bid seen for this slot and parent").andThen fun _ =>
        (ignoreUnless timely "bid's slot is not the current or next slot").andThen fun _ =>
        (rejectUnless (signed.message.executionPayment == 0)
          "bid's execution payment must be zero").andThen fun _ =>
        (rejectUnless (signed.message.blockHash != signed.message.parentBlockHash)
          "bid's block hash equals its parent block hash").andThen fun _ =>
        (rejectUnless (signed.message.blobKzgCommitments.data.size ≤
            (config.getBlobParameters
              (computeEpochAtSlot preset signed.message.slot)).maxBlobsPerBlock.toNat)
          "too many blob kzg commitments").andThen fun _ =>
        (rejectUnless (parent.slot < signed.message.slot)
          "bid's slot is not higher than its parent's slot").andThen fun _ =>
        (ignoreUnless (computeEpochAtSlot preset signed.message.slot ≤ lookahead)
          "bid's slot is past the parent's proposer lookahead").andThen fun _ =>
        (ignoreUnless (signed.message.feeRecipient == preferences.feeRecipient)
          "bid's fee recipient does not match the proposer's preference").andThen fun _ =>
        (ignoreUnless compatible
          "bid's gas limit is not compatible with the proposer's target").andThen fun _ =>
        (ignoreUnless onHead "bid is not compatible with the current head branch").andThen
          fun _ =>
        (rejectUnless (signed.message.prevRandao == randao)
          "bid's previous randao is incorrect").andThen fun _ =>
        (rejectUnless (builder.version == PAYLOAD_BUILDER_VERSION)
          "builder is not a payload builder").andThen fun _ =>
        (rejectUnless active "builder is not active").andThen fun _ =>
        (ignoreUnless covered "builder cannot cover bid value").andThen fun _ =>
        (ignoreUnless (!exiting) "builder may exit").andThen fun _ =>
        rejectUnless valid "invalid bid signature") := by
  unfold validateExecutionPayloadBid
  simp only [clock, known, held, reach, dependent, preferred, payload, gas, branch, mix, slots,
    found, activity, funds, exit, signature, bind, Except.bind, pure, Except.pure,
    Except.mapError, ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM,
    rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, a bid is valid exactly when every check passes. -/
theorem validateExecutionPayloadBid_eq_accept
    (clock : store.isCurrentOrNextSlot config signed.message.slot currentTimeMs = .ok timely)
    (known : store.blocks[signed.message.parentBlockRoot]? = some parent)
    (held : store.blockStates[signed.message.parentBlockRoot]? = some state)
    (reach : addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD = .ok lookahead)
    (dependent : store.getShufflingDependentRoot signed.message.parentBlockRoot
      (computeEpochAtSlot preset signed.message.slot) = .ok dependentRoot)
    (preferred : seen.proposerPreferencesFor (signed.message.slot, dependentRoot) =
      some preferences)
    (payload : seen.executionPayloadGasLimitFor signed.message.parentBlockHash =
      some parentGasLimit)
    (gas : isGasLimitTargetCompatible parentGasLimit signed.message.gasLimit
      preferences.targetGasLimit = .ok compatible)
    (branch : store.isBidCompatibleWithHead config gloas signed.message = .ok onHead)
    (mix : getRandaoMix state (getCurrentEpoch state) = .ok randao)
    (slots : processSlots config checks state signed.message.slot = .ok advanced)
    (found : (advanced.builders gloas).data[signed.message.builderIndex.toNat]? = some builder)
    (activity : isActiveBuilder advanced gloas signed.message.builderIndex = .ok active)
    (funds : canBuilderCoverBid advanced gloas signed.message.builderIndex signed.message.value =
      .ok covered)
    (exit : builderMayExit store gloas advanced signed.message builder = .ok exiting)
    (signature : verifyExecutionPayloadBidSignature config checks advanced gloas signed =
      .ok valid) :
    validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs = .ok accept ↔
      (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot,
          signed.message.builderIndex) ∉ seen.executionPayloadBids ∧
        (seen.bestExecutionPayloadBidFor (signed.message.slot, signed.message.parentBlockHash,
          signed.message.parentBlockRoot)).all (· < signed.message.value) = true ∧
        timely = true ∧ signed.message.executionPayment = 0 ∧
        signed.message.blockHash ≠ signed.message.parentBlockHash ∧
        signed.message.blobKzgCommitments.data.size ≤
          (config.getBlobParameters
            (computeEpochAtSlot preset signed.message.slot)).maxBlobsPerBlock.toNat ∧
        parent.slot < signed.message.slot ∧
        computeEpochAtSlot preset signed.message.slot ≤ lookahead ∧
        signed.message.feeRecipient = preferences.feeRecipient ∧ compatible = true ∧
        onHead = true ∧ signed.message.prevRandao = randao ∧
        builder.version = PAYLOAD_BUILDER_VERSION ∧ active = true ∧ covered = true ∧
        exiting = false ∧ valid = true := by
  rw [validateExecutionPayloadBid_eq clock known held reach dependent preferred payload gas branch
    mix slots found activity funds exit signature]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept]
  simp

/-- Once its inputs are computed, a bid is ignored only when an ignore check fails. -/
theorem validateExecutionPayloadBid_ignored {reason : String}
    (clock : store.isCurrentOrNextSlot config signed.message.slot currentTimeMs = .ok timely)
    (known : store.blocks[signed.message.parentBlockRoot]? = some parent)
    (held : store.blockStates[signed.message.parentBlockRoot]? = some state)
    (reach : addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD = .ok lookahead)
    (dependent : store.getShufflingDependentRoot signed.message.parentBlockRoot
      (computeEpochAtSlot preset signed.message.slot) = .ok dependentRoot)
    (preferred : seen.proposerPreferencesFor (signed.message.slot, dependentRoot) =
      some preferences)
    (payload : seen.executionPayloadGasLimitFor signed.message.parentBlockHash =
      some parentGasLimit)
    (gas : isGasLimitTargetCompatible parentGasLimit signed.message.gasLimit
      preferences.targetGasLimit = .ok compatible)
    (branch : store.isBidCompatibleWithHead config gloas signed.message = .ok onHead)
    (mix : getRandaoMix state (getCurrentEpoch state) = .ok randao)
    (slots : processSlots config checks state signed.message.slot = .ok advanced)
    (found : (advanced.builders gloas).data[signed.message.builderIndex.toNat]? = some builder)
    (activity : isActiveBuilder advanced gloas signed.message.builderIndex = .ok active)
    (funds : canBuilderCoverBid advanced gloas signed.message.builderIndex signed.message.value =
      .ok covered)
    (exit : builderMayExit store gloas advanced signed.message builder = .ok exiting)
    (signature : verifyExecutionPayloadBidSignature config checks advanced gloas signed =
      .ok valid)
    (ignored : validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok (.ignore reason)) :
    (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot,
          signed.message.builderIndex) ∈ seen.executionPayloadBids ∨
        (seen.bestExecutionPayloadBidFor (signed.message.slot, signed.message.parentBlockHash,
          signed.message.parentBlockRoot)).all (· < signed.message.value) = false ∨
        timely = false ∨ lookahead < computeEpochAtSlot preset signed.message.slot ∨
        signed.message.feeRecipient ≠ preferences.feeRecipient ∨ compatible = false ∨
        onHead = false ∨ covered = false ∨ exiting = true := by
  rw [validateExecutionPayloadBid_eq clock known held reach dependent preferred payload gas branch
    mix slots found activity funds exit signature] at ignored
  refine Classical.byContradiction fun none => ?_
  simp only [not_or, Bool.not_eq_false, Bool.not_eq_true, ne_eq, Decidable.not_not,
    UInt64.not_lt] at none
  obtain ⟨fresh, best, current, inside, fee, gasOk, branchOk, coveredOk, staying⟩ := none
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen, best, current,
    inside, fee, gasOk, branchOk, coveredOk, staying, beq_self_eq_true, decide_true, Bool.not_false,
    Bool.not_eq_true', ite_true] at ignored
  repeat' split at ignored
  all_goals cases valid <;> simp_all

end Chain

end EthLib.Consensus
