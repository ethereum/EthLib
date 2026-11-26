module

public import EthLib.Consensus.ForkChoice.PayloadVotes

/-!
# Proofs: the votes of the payload committee

A vote of the committee never has two winning sides.

So no payload is both on time and late, and no blob data is both available and missing.

A payload that the store has not verified always loses: it is late, and its data is missing.

The rule that extends the payload of the previous slot has one theorem per branch, errors included.

The tiebreaker of two nodes of one block is 0, 1 or 2.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

/-- No vote has two winning sides when the threshold is half of the committee. -/
theorem ptcMajority_not_both {n : Nat} (votes : Vector (Option Bool) n) :
    ¬ (ptcMajority (n / 2) votes true = true ∧ ptcMajority (n / 2) votes false = true) := by
  rintro ⟨yes, no⟩
  simp only [ptcMajority, decide_eq_true_eq] at yes no
  -- The members that vote false are among those that do not vote true.
  have total := List.length_eq_countP_add_countP (l := votes.toList) (· == some true)
  have apart : votes.toList.countP (· == some false) ≤
      votes.toList.countP (fun vote => decide ¬(vote == some true) = true) :=
    List.countP_mono_left fun vote _ isFalse => by
      simp only [beq_iff_eq] at isFalse
      simp [isFalse]
  simp only [Vector.length_toList] at total
  omega

namespace Store

variable {config : Config} {store : Store preset fork}

/-- Without the votes of a block, its payload has no timeliness. -/
theorem payloadTimeliness_of_unknown {gloas : .glamsterdam ≤ fork} {root : Root} {timely : Bool}
    (missing : (store.payloadTimelinessVote gloas)[root]? = none) :
    store.payloadTimeliness gloas root timely = .error (.unknownPayloadVotes root) := by
  simp [payloadTimeliness, ptcVotes, missing, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- A payload that the store has not verified is late, whatever the votes. -/
theorem payloadTimeliness_of_not_verified {gloas : .glamsterdam ≤ fork} {root : Root}
    {timely : Bool} {votes : Vector (Option Bool) preset.PTC_SIZE.toNat}
    (found : (store.payloadTimelinessVote gloas)[root]? = some votes)
    (unverified : store.isPayloadVerified gloas root = false) :
    store.payloadTimeliness gloas root timely = .ok !timely := by
  simp [payloadTimeliness, ptcVotes, found, unverified, bind, Except.bind, pure, Except.pure]

/-- For a verified payload, the side of the vote with more than half of the committee wins. -/
theorem payloadTimeliness_of_verified {gloas : .glamsterdam ≤ fork} {root : Root}
    {timely : Bool} {votes : Vector (Option Bool) preset.PTC_SIZE.toNat}
    (found : (store.payloadTimelinessVote gloas)[root]? = some votes)
    (verified : store.isPayloadVerified gloas root = true) :
    store.payloadTimeliness gloas root timely =
      .ok (ptcMajority (ptcThreshold preset) votes timely) := by
  simp [payloadTimeliness, ptcVotes, found, verified, bind, Except.bind, pure, Except.pure]

/-- No payload is both on time and late. -/
theorem payloadTimeliness_not_both {gloas : .glamsterdam ≤ fork} {root : Root}
    {onTime late : Bool} (timelyOk : store.payloadTimeliness gloas root true = .ok onTime)
    (lateOk : store.payloadTimeliness gloas root false = .ok late) : ¬ (onTime ∧ late) := by
  cases found : (store.payloadTimelinessVote gloas)[root]? with
  | none => simp [payloadTimeliness_of_unknown found] at timelyOk
  | some votes =>
    cases verified : store.isPayloadVerified gloas root
    · rw [payloadTimeliness_of_not_verified found verified, Except.ok.injEq] at timelyOk
      simp [← timelyOk]
    · rw [payloadTimeliness_of_verified found verified, Except.ok.injEq] at timelyOk lateOk
      subst timelyOk lateOk
      exact ptcMajority_not_both votes

/-- Without the votes of a block, its blob data has no availability. -/
theorem payloadDataAvailability_of_unknown {gloas : .glamsterdam ≤ fork} {root : Root}
    {available : Bool} (missing : (store.payloadDataAvailabilityVote gloas)[root]? = none) :
    store.payloadDataAvailability gloas root available = .error (.unknownPayloadVotes root) := by
  simp [payloadDataAvailability, ptcVotes, missing, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- The data of a payload that the store has not verified is missing, whatever the votes. -/
theorem payloadDataAvailability_of_not_verified {gloas : .glamsterdam ≤ fork} {root : Root}
    {available : Bool} {votes : Vector (Option Bool) preset.PTC_SIZE.toNat}
    (found : (store.payloadDataAvailabilityVote gloas)[root]? = some votes)
    (unverified : store.isPayloadVerified gloas root = false) :
    store.payloadDataAvailability gloas root available = .ok !available := by
  simp [payloadDataAvailability, ptcVotes, found, unverified, bind, Except.bind, pure,
    Except.pure]

/-- For a verified payload, the side of the data vote with more than half of the committee wins. -/
theorem payloadDataAvailability_of_verified {gloas : .glamsterdam ≤ fork} {root : Root}
    {available : Bool} {votes : Vector (Option Bool) preset.PTC_SIZE.toNat}
    (found : (store.payloadDataAvailabilityVote gloas)[root]? = some votes)
    (verified : store.isPayloadVerified gloas root = true) :
    store.payloadDataAvailability gloas root available =
      .ok (ptcMajority (ptcThreshold preset) votes available) := by
  simp [payloadDataAvailability, ptcVotes, found, verified, bind, Except.bind, pure, Except.pure]

/-- No blob data is both available and missing. -/
theorem payloadDataAvailability_not_both {gloas : .glamsterdam ≤ fork} {root : Root}
    {present missing : Bool}
    (presentOk : store.payloadDataAvailability gloas root true = .ok present)
    (missingOk : store.payloadDataAvailability gloas root false = .ok missing) :
    ¬ (present ∧ missing) := by
  cases found : (store.payloadDataAvailabilityVote gloas)[root]? with
  | none => simp [payloadDataAvailability_of_unknown found] at presentOk
  | some votes =>
    cases verified : store.isPayloadVerified gloas root
    · rw [payloadDataAvailability_of_not_verified found verified, Except.ok.injEq] at presentOk
      simp [← presentOk]
    · rw [payloadDataAvailability_of_verified found verified, Except.ok.injEq] at presentOk
      rw [payloadDataAvailability_of_verified found verified, Except.ok.injEq] at missingOk
      subst presentOk missingOk
      exact ptcMajority_not_both votes

/-- A proposer never asks the pending node of its head whether to build on the full node. -/
theorem shouldBuildOnFull_of_pending {gloas : .glamsterdam ≤ fork} {head : ForkChoiceNode}
    {slot : Slot} (pending : head.payloadStatus = .pending) :
    store.shouldBuildOnFull gloas head slot = .error (.pendingNode head.root) := by
  simp [shouldBuildOnFull, pending, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A payload of the previous slot that the store has not verified is not extended. -/
theorem shouldExtendPayload_of_not_verified {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (unverified : store.isPayloadVerified gloas root = false) :
    store.shouldExtendPayload config gloas root = .ok false := by
  simp [shouldExtendPayload, Store.block, found, nextOk, current, unverified, Except.mapError,
    bind, Except.bind, pure, Except.pure]

/-- From Heze: a payload of the previous slot that failed its inclusion lists is not extended. -/
theorem shouldExtendPayload_of_not_satisfied {gloas : .glamsterdam ≤ fork}
    (heze : .hegota ≤ fork) {root : Root} {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (unsatisfied : store.isPayloadInclusionListSatisfied heze root = .ok false) :
    store.shouldExtendPayload config gloas root = .ok false := by
  by_cases verified : store.isPayloadVerified gloas root = true
  · simp [shouldExtendPayload, Store.block, found, nextOk, current, verified, heze, unsatisfied,
      Except.mapError, bind, Except.bind, pure, Except.pure]
  · exact shouldExtendPayload_of_not_verified found nextOk current (by simpa using verified)

/-- From Heze: without a recorded answer for a block, its inclusion lists have no answer. -/
theorem isPayloadInclusionListSatisfied_of_unknown (heze : .hegota ≤ fork) {root : Root}
    (missing : (store.payloadInclusionListSatisfaction heze)[root]? = none) :
    store.isPayloadInclusionListSatisfied heze root =
      .error (.unknownInclusionListSatisfaction root) := by
  simp [isPayloadInclusionListSatisfied, missing, throw, throwThe, MonadExceptOf.throw]

/-- From Heze: a payload that the store has not verified does not satisfy its inclusion lists. -/
theorem isPayloadInclusionListSatisfied_of_not_verified {gloas : .glamsterdam ≤ fork}
    (heze : .hegota ≤ fork) {root : Root} {satisfied : Bool}
    (recorded : (store.payloadInclusionListSatisfaction heze)[root]? = some satisfied)
    (unverified : store.isPayloadVerified gloas root = false) :
    store.isPayloadInclusionListSatisfied heze root = .ok false := by
  simp [isPayloadInclusionListSatisfied, recorded, unverified, pure, Except.pure]

/-- From Heze: for a verified payload, the answer is the one that the store recorded. -/
theorem isPayloadInclusionListSatisfied_of_verified {gloas : .glamsterdam ≤ fork}
    (heze : .hegota ≤ fork) {root : Root} {satisfied : Bool}
    (recorded : (store.payloadInclusionListSatisfaction heze)[root]? = some satisfied)
    (verified : store.isPayloadVerified gloas root = true) :
    store.isPayloadInclusionListSatisfied heze root = .ok satisfied := by
  simp [isPayloadInclusionListSatisfied, recorded, verified, pure, Except.pure]

/-- A block that the store does not hold has no payload to extend. -/
theorem shouldExtendPayload_of_unknown {gloas : .glamsterdam ≤ fork} {root : Root}
    (missing : store.blocks[root]? = none) :
    store.shouldExtendPayload config gloas root = .error (.unknownBlock root) := by
  simp [shouldExtendPayload, Store.block, missing, throw, throwThe, MonadExceptOf.throw, bind,
    Except.bind]

/-- A block at the last slot has no next slot, so the rule overflows before it reads the clock. -/
theorem shouldExtendPayload_of_last_slot {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (last : block.slot.toNat = 2 ^ 64 - 1) :
    store.shouldExtendPayload config gloas root = .error (.arith .overflow) := by
  have overflow : addChecked block.slot 1 = .error .overflow := by
    simp [addChecked, last]
  simp [shouldExtendPayload, Store.block, found, overflow, Except.mapError, bind, Except.bind,
    pure, Except.pure]

/-- For a held block whose next slot fits, an error of the clock is the error of the rule. -/
theorem shouldExtendPayload_of_clock_error {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} {next : Slot} {e : ForkChoiceError}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (clock : store.getCurrentSlot config = .error e) :
    store.shouldExtendPayload config gloas root = .error e := by
  simp [shouldExtendPayload, Store.block, found, nextOk, clock, Except.mapError, bind,
    Except.bind, pure, Except.pure]

/-- A block whose next slot is not the current slot is an error: it is not of the previous slot. -/
theorem shouldExtendPayload_of_not_previous_slot {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} {next current : Slot}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (clock : store.getCurrentSlot config = .ok current) (other : next ≠ current) :
    store.shouldExtendPayload config gloas root =
      .error (.notPreviousSlot root block.slot current) := by
  simp [shouldExtendPayload, Store.block, found, nextOk, clock, other, Except.mapError, bind,
    Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- From Heze: a verified payload without a recorded answer for its inclusion lists is an error. -/
theorem shouldExtendPayload_of_unknown_satisfaction {gloas : .glamsterdam ≤ fork}
    (heze : .hegota ≤ fork) {root : Root} {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    (missing : (store.payloadInclusionListSatisfaction heze)[root]? = none) :
    store.shouldExtendPayload config gloas root =
      .error (.unknownInclusionListSatisfaction root) := by
  simp [shouldExtendPayload, Store.block, found, nextOk, current, verified, heze,
    isPayloadInclusionListSatisfied_of_unknown heze missing, Except.mapError, bind, Except.bind,
    pure, Except.pure]

/-- A payload that passes the first checks but has no timeliness votes is an error. -/
theorem shouldExtendPayload_of_unknown_timeliness {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    -- From Heze the payload satisfies its inclusion lists.
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (missing : (store.payloadTimelinessVote gloas)[root]? = none) :
    store.shouldExtendPayload config gloas root = .error (.unknownPayloadVotes root) := by
  by_cases heze : .hegota ≤ fork <;>
    simp [shouldExtendPayload, Store.block, found, nextOk, current, verified, heze, satisfied,
      payloadTimeliness_of_unknown missing, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A payload that passes the first checks but has no availability votes is an error. -/
theorem shouldExtendPayload_of_unknown_availability {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} {next : Slot}
    {timelyVotes : Vector (Option Bool) preset.PTC_SIZE.toNat}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    -- From Heze the payload satisfies its inclusion lists.
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (timelyFound : (store.payloadTimelinessVote gloas)[root]? = some timelyVotes)
    (missing : (store.payloadDataAvailabilityVote gloas)[root]? = none) :
    store.shouldExtendPayload config gloas root = .error (.unknownPayloadVotes root) := by
  by_cases heze : .hegota ≤ fork <;>
    simp [shouldExtendPayload, Store.block, found, nextOk, current, verified, heze, satisfied,
      payloadTimeliness_of_verified timelyFound verified,
      payloadDataAvailability_of_unknown missing, Except.mapError, bind, Except.bind, pure,
      Except.pure]

/-- Once the votes are read, the rule is the votes, then the boosted block.

The answers `timely` and `available` are those of the two votes of the committee. -/
theorem shouldExtendPayload_of_votes {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} {next : Slot} {timely available : Bool}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    -- From Heze the payload satisfies its inclusion lists.
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (timelyOk : store.payloadTimeliness gloas root true = .ok timely)
    (availableOk : store.payloadDataAvailability gloas root true = .ok available) :
    store.shouldExtendPayload config gloas root =
      -- Votes that both pass, or no boosted block, extend the payload.
      if (timely && available) = true ∨ store.proposerBoostRoot = Vector.replicate 32 0 then
        .ok true
      else (do
        -- So does a boosted block that does not build on this block.
        let proposerBlock ← store.block store.proposerBoostRoot
        if proposerBlock.parentRoot ≠ root then return true
        -- Else the boosted block decides, by whether it builds on the full node.
        store.isParentNodeFull proposerBlock) := by
  by_cases heze : .hegota ≤ fork <;>
    by_cases votes : (timely && available) = true <;>
    simp [shouldExtendPayload, Store.block, found, nextOk, current, verified, heze, satisfied,
      timelyOk, availableOk, votes, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Votes that both pass, or no boosted block, extend a payload that passes the first checks. -/
theorem shouldExtendPayload_of_votes_or_no_boost {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} {next : Slot} {timely available : Bool}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    -- From Heze the payload satisfies its inclusion lists.
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (timelyOk : store.payloadTimeliness gloas root true = .ok timely)
    (availableOk : store.payloadDataAvailability gloas root true = .ok available)
    (passed : (timely && available) = true ∨ store.proposerBoostRoot = Vector.replicate 32 0) :
    store.shouldExtendPayload config gloas root = .ok true := by
  rw [shouldExtendPayload_of_votes found nextOk current verified satisfied timelyOk availableOk,
    ite_eq_left_of_eq_true _ _ (eq_true passed)]

/-- A boosted block that the store does not hold is an error, once the votes do not decide. -/
theorem shouldExtendPayload_of_unknown_boost {gloas : .glamsterdam ≤ fork} {root : Root}
    {block : BeaconBlock preset fork} {next : Slot} {timely available : Bool}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    -- From Heze the payload satisfies its inclusion lists.
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (timelyOk : store.payloadTimeliness gloas root true = .ok timely)
    (availableOk : store.payloadDataAvailability gloas root true = .ok available)
    (failed : (timely && available) = false)
    (boosted : store.proposerBoostRoot ≠ Vector.replicate 32 0)
    (missing : store.blocks[store.proposerBoostRoot]? = none) :
    store.shouldExtendPayload config gloas root =
      .error (.unknownBlock store.proposerBoostRoot) := by
  rw [shouldExtendPayload_of_votes found nextOk current verified satisfied timelyOk availableOk]
  simp [failed, boosted, Store.block, missing, throw, throwThe, MonadExceptOf.throw, bind,
    Except.bind]

/-- A payload that passes the first checks is extended when the boosted block builds elsewhere. -/
theorem shouldExtendPayload_of_boost_elsewhere {gloas : .glamsterdam ≤ fork} {root : Root}
    {block proposerBlock : BeaconBlock preset fork} {next : Slot} {timely available : Bool}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    -- From Heze the payload satisfies its inclusion lists.
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (timelyOk : store.payloadTimeliness gloas root true = .ok timely)
    (availableOk : store.payloadDataAvailability gloas root true = .ok available)
    (proposerFound : store.blocks[store.proposerBoostRoot]? = some proposerBlock)
    (elsewhere : proposerBlock.parentRoot ≠ root) :
    store.shouldExtendPayload config gloas root = .ok true := by
  rw [shouldExtendPayload_of_votes found nextOk current verified satisfied timelyOk availableOk]
  split
  · rfl
  · simp [Store.block, proposerFound, elsewhere, bind, Except.bind, pure, Except.pure]

/-- When the votes do not decide and a boosted child exists, it decides by its parent's status. -/
theorem shouldExtendPayload_of_boost_child {gloas : .glamsterdam ≤ fork} {root : Root}
    {block proposerBlock : BeaconBlock preset fork} {next : Slot} {timely available : Bool}
    (found : store.blocks[root]? = some block) (nextOk : addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    -- From Heze the payload satisfies its inclusion lists.
    (satisfied : ∀ heze : .hegota ≤ fork,
      store.isPayloadInclusionListSatisfied heze root = .ok true)
    (timelyOk : store.payloadTimeliness gloas root true = .ok timely)
    (availableOk : store.payloadDataAvailability gloas root true = .ok available)
    (failed : (timely && available) = false)
    (boosted : store.proposerBoostRoot ≠ Vector.replicate 32 0)
    (proposerFound : store.blocks[store.proposerBoostRoot]? = some proposerBlock)
    (child : proposerBlock.parentRoot = root) :
    store.shouldExtendPayload config gloas root = store.isParentNodeFull proposerBlock := by
  rw [shouldExtendPayload_of_votes found nextOk current verified satisfied timelyOk availableOk]
  simp [failed, boosted, Store.block, proposerFound, child, bind, Except.bind, pure, Except.pure]

/-- From Heze: a payload that is extended satisfied its inclusion lists, and is verified. -/
theorem isPayloadInclusionListSatisfied_of_shouldExtendPayload {gloas : .glamsterdam ≤ fork}
    (heze : .hegota ≤ fork) {root : Root}
    (extends_ : store.shouldExtendPayload config gloas root = .ok true) :
    store.isPayloadInclusionListSatisfied heze root = .ok true := by
  unfold shouldExtendPayload at extends_
  simp only [heze, dite_true, bind, Except.bind, Except.mapError, pure, Except.pure] at extends_
  repeat' split at extends_
  all_goals simp_all

/-- Outside a decision on the previous slot's payload, the tiebreaker is the status number. -/
theorem getPayloadStatusTiebreaker_of_not_decision {gloas : .glamsterdam ≤ fork}
    {node : ForkChoiceNode}
    (notDecision : store.isPreviousSlotPayloadDecision config node = .ok false) :
    store.getPayloadStatusTiebreaker config gloas node = .ok node.payloadStatus.code := by
  simp [getPayloadStatusTiebreaker, notDecision, bind, Except.bind, pure, Except.pure]

/-- The tiebreaker of a node is at most 2. -/
theorem getPayloadStatusTiebreaker_le {gloas : .glamsterdam ≤ fork} {node : ForkChoiceNode}
    {tiebreaker : UInt8}
    (computed : store.getPayloadStatusTiebreaker config gloas node = .ok tiebreaker) :
    tiebreaker ≤ 2 := by
  unfold getPayloadStatusTiebreaker at computed
  cases decision : store.isPreviousSlotPayloadDecision config node with
  | error e => simp [decision, bind, Except.bind] at computed
  | ok isDecision =>
    cases isDecision
    · simp only [decision, bind, Except.bind, Bool.false_eq_true, ↓reduceIte, pure,
        Except.pure, Except.ok.injEq] at computed
      subst computed
      cases node.payloadStatus <;> decide
    · simp only [decision, bind, Except.bind, ↓reduceIte] at computed
      split at computed
      · simp only [pure, Except.pure, Except.ok.injEq] at computed
        subst computed
        decide
      · cases extend : store.shouldExtendPayload config gloas node.root with
        | error e => simp [extend] at computed
        | ok extendIt =>
          cases extendIt <;>
            simp only [extend, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
              Except.ok.injEq] at computed <;> subst computed <;> decide

end Store

end EthLib.Consensus
