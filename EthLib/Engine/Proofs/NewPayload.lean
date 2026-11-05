module

public import EthLib.Engine.NewPayload
public import EthLib.Engine.Proofs.Block

/-!
# Proofs: the checks of `engine_newPayload`

Each fork from Paris to BPO5 has a version of the method, and no other fork has one.

Request lists that pass the checks have distinct types, in increasing order.
-/

public section

namespace EthLib.Engine

open EthLib.Base

/-- Two errors with one code come from one constructor. -/
theorem EngineError.code_injective (e₁ e₂ : EngineError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [EngineError.code] at h; exact absurd h (by decide))

/-- Two reasons with one code come from one constructor. -/
theorem PayloadError.code_injective (e₁ e₂ : PayloadError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [PayloadError.code] at h; exact absurd h (by decide))

/-- Some version of the method takes a fork exactly when the fork is from Paris to BPO5. -/
theorem exists_acceptsFork_iff (fork : Fork) :
    (∃ version, acceptsFork version fork = true) ↔ .paris ≤ fork ∧ fork < .glamsterdam := by
  constructor
  · rintro ⟨version, h⟩
    revert h
    unfold acceptsFork
    split <;> cases fork <;> decide
  · intro ⟨hLow, hHigh⟩
    cases fork <;> first
      | exact absurd hLow (by decide)
      | exact absurd hHigh (by decide)
      | exact ⟨1, rfl⟩
      | exact ⟨2, rfl⟩
      | exact ⟨3, rfl⟩
      | exact ⟨4, rfl⟩

/-- Request lists that pass the check have strictly increasing types. -/
theorem pairwise_of_validRequests {requests : List ByteArray}
    (h : validRequests requests = true) :
    requests.Pairwise fun r s => r[0]! < s[0]! := by
  induction requests with
  | nil => exact .nil
  | cons r rest ih =>
    match rest, h with
    | [], _ => exact List.pairwise_singleton _ r
    | s :: rest', h =>
      simp only [validRequests, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨-, -⟩, hrs⟩, hRest⟩ := h
      have hTail := ih hRest
      refine List.Pairwise.cons (fun t ht => ?_) hTail
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hrs
      · exact UInt8.lt_trans hrs (List.rel_of_pairwise_cons hTail ht)

/-- Request lists that pass the check have distinct types. -/
theorem nodup_types_of_validRequests {requests : List ByteArray}
    (h : validRequests requests = true) : (requests.map fun r => r[0]!).Nodup :=
  List.Pairwise.map _ (fun _ _ hlt => UInt8.ne_of_lt hlt) (pairwise_of_validRequests h)

end EthLib.Engine
