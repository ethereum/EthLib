module

public import EthLib.Consensus.ForkChoice.PayloadVotes

/-!
# Proofs: the votes of the payload committee

A vote of the committee never has two winning sides.

So no payload is both on time and late, and no blob data is both available and missing.

A payload that the store has not verified always loses: it is late, and its data is missing.

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
