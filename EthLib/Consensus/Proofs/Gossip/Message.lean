module

public import EthLib.Base.Except
public import EthLib.Consensus.Gossip.Message
public import EthLib.Consensus.Proofs.Gossip.Sidecar

/-!
# Proofs: the dispatch of a gossip message to the rules of its topic

The outcome of the dispatch is the outcome of the validator of the topic.

A message that is ignored or rejected leaves the messages seen as they were.

A valid message adds its keys, and those keys can always be computed.

So the dispatch fails only when the validator of the topic fails.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Networking.Gossip Cryptography.Kzg

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {setup : TrustedSetup} {seen : Seen} {store : Store preset fork} {statuses : PayloadStatuses}
  {currentTimeMs : UInt64} {message : GossipMessage preset fork}

/-- The outcome of the dispatch is the outcome of the validator of the topic. -/
theorem validateGossipMessage_outcome {outcome : ValidationResult} {after : Seen}
    (dispatched : validateGossipMessage config checks setup seen store statuses currentTimeMs
      message = .ok (outcome, after)) :
    message.validate config checks setup seen store statuses currentTimeMs = .ok outcome := by
  unfold validateGossipMessage at dispatched
  cases h : message.validate config checks setup seen store statuses currentTimeMs with
  | error e => simp [h, bind, Except.bind] at dispatched
  | ok o =>
    simp only [h, bind, Except.bind] at dispatched
    split at dispatched
    · cases r : message.record config store seen <;>
        simp_all [pure, Except.pure]
    · simp_all [pure, Except.pure]

/-- A message that its topic ignores or rejects leaves the messages seen as they were. -/
theorem validateGossipMessage_of_not_accept {outcome : ValidationResult}
    (validated : message.validate config checks setup seen store statuses currentTimeMs =
      .ok outcome)
    (notAccepted : outcome.isAccept = false) :
    validateGossipMessage config checks setup seen store statuses currentTimeMs message =
      .ok (outcome, seen) := by
  simp [validateGossipMessage, validated, notAccepted, bind, Except.bind, pure, Except.pure]

/-- A message that its topic accepts adds its keys to the messages seen. -/
theorem validateGossipMessage_of_accept {after : Seen}
    (validated : message.validate config checks setup seen store statuses currentTimeMs =
      .ok .accept)
    (recorded : message.record config store seen = .ok after) :
    validateGossipMessage config checks setup seen store statuses currentTimeMs message =
      .ok (.accept, after) := by
  simp [validateGossipMessage, validated, recorded, ValidationResult.isAccept, bind, Except.bind,
    pure, Except.pure]

/-- A chain of checks that accepts runs its next checks, and they accept. -/
private theorem next_of_andThenM {ε : Type} {first : ValidationResult}
    {next : Unit → Except ε ValidationResult}
    (accepted : first.andThenM next = .ok .accept) : next () = .ok .accept :=
  (andThenM_eq_ok_accept.mp accepted).2

/-- The keys of a message that its topic accepts can always be recorded.

Before Electra an accepted attestation has an attester, since its checks find one.

The root of the data of an accepted aggregate was computed by its checks. -/
theorem GossipMessage.record_of_accept
    (validated : message.validate config checks setup seen store statuses currentTimeMs =
      .ok .accept) :
    ∃ after, message.record config store seen = .ok after := by
  cases message with
  | beaconAttestation early attestation subnetId =>
    simp only [GossipMessage.validate, validateBeaconAttestation] at validated
    have h1 := next_of_andThenM validated
    obtain ⟨state, head, h2⟩ := bind_ok_iff.mp h1
    obtain ⟨_, -, h3⟩ := bind_ok_iff.mp (next_of_andThenM h2)
    obtain ⟨_, -, h4⟩ := bind_ok_iff.mp (next_of_andThenM h3)
    obtain ⟨committee, committeeOf, h5⟩ := bind_ok_iff.mp (next_of_andThenM
      (next_of_andThenM (next_of_andThenM h4)))
    have h6 := next_of_andThenM h5
    cases attesterOf : firstAttester committee attestation.aggregationBits.bits with
    | none => rw [attesterOf] at h6; cases h6
    | some attester =>
      refine ⟨seen.recordAttestation attestation.data.target.epoch attester, ?_⟩
      simp only [GossipMessage.record, beaconAttestationAttester, head, bind, Except.bind]
      cases h : getBeaconCommittee state attestation.data.slot attestation.data.index with
      | error e => rw [h] at committeeOf; cases committeeOf
      | ok c =>
        rw [h] at committeeOf
        cases committeeOf
        simp only [Except.mapError, attesterOf]
        rfl
  | aggregateAndProof signed =>
    simp only [GossipMessage.record]
    cases rootOf : Serialization.Ssz.SszType.hashTreeRoot signed.message.aggregate.data with
    | ok root => exact ⟨seen.recordAggregateAndProof signed root, rfl⟩
    | error e =>
      exfalso
      have inCommittee : ∀ index, validateAggregateInCommittee config checks seen store statuses
          signed index currentTimeMs ≠ .ok .accept := by
        intro index accepted
        simp only [validateAggregateInCommittee] at accepted
        obtain ⟨root, hashed, -⟩ := bind_ok_iff.mp accepted
        rw [rootOf] at hashed
        cases hashed
      simp only [GossipMessage.validate, validateAggregateAndProof] at validated
      split at validated
      · have checked := next_of_andThenM validated
        split at checked
        · exact inCommittee _ checked
        · cases checked
      · exact inCommittee _ validated
  | dataColumnSidecar fulu sidecar subnetId =>
    simp only [GossipMessage.record]
    split <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-- The dispatch fails only when the validator of the topic fails, with the same error. -/
theorem validateGossipMessage_eq_error {e : ForkChoiceError}
    (failed : validateGossipMessage config checks setup seen store statuses currentTimeMs
      message = .error e) :
    message.validate config checks setup seen store statuses currentTimeMs = .error e := by
  unfold validateGossipMessage at failed
  cases validated : message.validate config checks setup seen store statuses currentTimeMs with
  | error e' => simp_all [bind, Except.bind]
  | ok outcome =>
    exfalso
    simp only [validated, bind, Except.bind] at failed
    split at failed
    · rename_i accepted
      have isAccept : outcome = .accept := by cases outcome <;> simp_all [ValidationResult.isAccept]
      subst isAccept
      obtain ⟨after, recorded⟩ := GossipMessage.record_of_accept validated
      simp [recorded, pure, Except.pure] at failed
    · simp [pure, Except.pure] at failed

end EthLib.Consensus
