module

public import EthLib.Networking.Exports.ForkId
public import EthLib.Networking.Proofs.Devp2p.ForkId
import all EthLib.Networking.Exports.ForkId
import all EthLib.Base.Exports.Result

/-!
# Proofs: the schedule that the fork identifier exports read

Each fork of a schedule that the exports read is below 2^64.

So the fork identifiers of that schedule hold its forks whole.
-/

@[expose] public section

namespace EthLib.Networking.Devp2p.Exports

open EthLib.Base
open EthLib.Exports (rejectArgument)

/-- A refused argument is never a result. -/
private theorem rejectArgument_ne_ok {α : Type} (context : Option String) (reason : String)
    (a : α) :
    rejectArgument context reason ≠ .ok a := by
  simp [rejectArgument, EthLib.Exports.toResult, Except.mapError]

/-- A fork that the reader of one fork returns is below 2^64. -/
theorem readActivation_lt {item : Serialization.Rlp.Item} {fork : Fork} {a : Activation}
    (h : readActivation item = .ok (fork, a)) : activationValue a < ACTIVATION_BOUND := by
  unfold readActivation at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  -- Every refusal contradicts the result, and an accepted fork passed the bound.
  all_goals first
    | exact absurd h (rejectArgument_ne_ok _ _ _)
    | cases h
  all_goals first
    | exact absurd ‹rejectArgument _ _ = _› (rejectArgument_ne_ok _ _ _)
    | exact ‹_ < ACTIVATION_BOUND›

/-- Each fork of a schedule that the exports read is below 2^64. -/
theorem readSchedule_bounded {bytes : ByteArray} {s : Schedule}
    (h : readSchedule bytes = .ok s) : s.Bounded := by
  unfold readSchedule at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  -- Every refusal contradicts the result.
  all_goals first
    | exact absurd h (rejectArgument_ne_ok _ _ _)
    | cases h
  all_goals first
    | exact absurd ‹rejectArgument _ _ = _› (rejectArgument_ne_ok _ _ _)
    | skip
  -- An accepted schedule takes each activation from the reader of one fork.
  all_goals refine Schedule.bounded_of_activations _ (fun p hp => ?_) (fun n hn => ?_)
  · obtain ⟨item, -, hitem⟩ := mapM_ok_mem ‹List.mapM readActivation _ = _› p hp
    exact readActivation_lt hitem
  -- A schedule without `FORK_NEXT_VALUE` has none to bound.
  · simp_all [pure, Except.pure]
  · obtain ⟨item, -, hitem⟩ := mapM_ok_mem ‹List.mapM readActivation _ = _› p hp
    exact readActivation_lt hitem
  -- The reader bounds `FORK_NEXT_VALUE` itself.
  · simp_all [pure, Except.pure]

end EthLib.Networking.Devp2p.Exports
