module

public import EthLib.Consensus.BeaconApi.StateQueries

/-!
# Proofs: the codes of answers written as JSON

Writing the value of an answer as JSON fails only with code 500.

So a versioned answer refuses with any other code exactly when its value does.

A versioned answer passes each refusal of its value on unchanged.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Serialization.Ssz

/-- Writing the value of an answer as JSON fails only with code 500. -/
theorem apiJsonOr500_error_code {α : Type} [SszType α] [ApiSpelling α] {x : α}
    {error : ErrorMessage} (failed : apiJsonOr500 x = .error error) : error.code = 500 := by
  unfold apiJsonOr500 at failed
  cases json : toApiJson x with
  | error fault =>
    simp only [json, Except.mapError, Except.error.injEq] at failed
    rw [← failed]
    rfl
  | ok _ => simp [json, Except.mapError] at failed

/-- Writing the value of an answer as JSON adds no refusal with a code other than 500.

It needs a code other than 500, the code of an internal error. -/
theorem apiJsonOr500_bind_error_iff {α β : Type} [SszType α] [ApiSpelling α]
    {answer : Except ErrorMessage α} {wrap : Lean.Json → β} {code : Nat}
    (notInternal : code ≠ 500) :
    (∃ error, (do return wrap (← apiJsonOr500 (← answer))) = .error error ∧ error.code = code) ↔
      ∃ error, answer = .error error ∧ error.code = code := by
  cases answer with
  | error fault => simp [bind, Except.bind]
  | ok value =>
    simp only [bind, Except.bind]
    cases json : apiJsonOr500 value with
    | error fault => simp [apiJsonOr500_error_code json, notInternal, @eq_comm _ 500 code]
    | ok _ => simp [pure, Except.pure]

/-- A versioned answer refuses with a code exactly when its value does.

It needs a code other than 500, the code of an internal error. -/
theorem versioned_error_iff {α : Type} [SszType α] [ApiSpelling α] {fork : Fork}
    {field : Except ErrorMessage α} {code : Nat} (notInternal : code ≠ 500) :
    (∃ error, versioned fork field = .error error ∧ error.code = code) ↔
      ∃ error, field = .error error ∧ error.code = code := by
  unfold versioned
  exact apiJsonOr500_bind_error_iff notInternal

/-- A versioned answer passes a refusal of its value on unchanged. -/
theorem versioned_of_error {α : Type} [SszType α] [ApiSpelling α] {fork : Fork}
    {field : Except ErrorMessage α} {error : ErrorMessage} (refused : field = .error error) :
    versioned fork field = .error error := by
  rw [versioned, refused]
  rfl

end EthLib.Consensus.BeaconApi
