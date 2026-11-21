module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FirstFinderForgery
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedClient
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderMarkFacts
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishFill

/-!
# The marked forgery experiment uses its own first finder

The sampled parameter and retained seed tables initialize the original conditioned experiment.

Completing its pending graph cells preserves every recorded search and physical reply.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig Constants OracleSpec OracleComp TwoLayerGraph Honest

attribute [local irreducible] caller chronicleGame observedGame

/-- A successful fresh forgery hits a registered target or a partner at the first search. -/
theorem actual_post_or_first (w : HashOutput) (A : Adversary) (left : Nat) :
    let pp := parameterOfWord w
    let r : ResidualCache pp :=
        SecretEncoding.Residual.localState _ _ (toKeyedState pp (afterWord w))
    ∀ (obs : Outcome) (out : ResidualCache pp) (rem : Nat) (s : State pp) (last : SharedState),
      ((some (obs,out),rem),s) ∈ support (observedGame pp A left r) →
      last ∈ support (RelabelState.endFill (FinderNotices.physical s.1.1)) →
      wins obs = true → ¬ (graph pp).Conflict last →
      ¬ (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project last) →
      s.1.1.2 = true ∨ Hit s.2 := by
  intro pp r obs out rem s last reached fill win clean safe
  have raw : (some (obs,out),s.1) ∈ support (chronicleGame pp A left r) := by
    rw [← erase_observedGame pp A left r, support_map]
    exact ⟨_,reached,rfl⟩
  refine post_or_first_of_marks pp A left r raw fill win clean safe
    (first_bookings A left r reached) (first_private_cold w A left obs out rem s reached) ?_ ?_
  · intro x hx
    obtain ⟨req,ans,member,issued⟩ := observed_issued pp A left r reached x hx
    exact ⟨req,ans,member,issued.mono (RelabelState.le_of_mem_support_endFill fill) (fun _ h => h)⟩
  · intro x hx
    exact ((completed_facts pp A left r reached) x hx).mono le_rfl
      (RelabelState.le_of_mem_support_endFill fill)

/-- The four priced events cover the actual filled game, including conflict on a refused prefix. -/
theorem filled_cover (w : HashOutput) (A : Adversary) (left : Nat) :
    let pp := parameterOfWord w
    let r : ResidualCache pp :=
        SecretEncoding.Residual.localState _ _ (toKeyedState pp (afterWord w))
    ∀ z ∈ support (observedFill pp A left r),
    (RealClient.accepted (z.1.1.1.map Prod.fst) ∨ (graph pp).Conflict z.2) →
      ((graph pp).Conflict z.2 ∨ (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project z.2)) ∨
      z.1.2.1.1.2 = true ∨ Hit z.1.2.2 := by
  classical
  intro pp r z reached
  unfold observedFill at reached
  rw [mem_support_bind_iff] at reached
  obtain ⟨⟨⟨ans,rem⟩,s⟩,actual,filled⟩ := reached
  rw [mem_support_bind_iff] at filled
  obtain ⟨last,fill,eq⟩ := filled
  rw [mem_support_pure_iff] at eq
  subst z
  intro bad
  by_cases clean : (graph pp).Conflict last
  · exact Or.inl (Or.inl clean)
  by_cases safe : (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project last)
  · exact Or.inl (Or.inr safe)
  obtain win | clash := bad
  · cases ans with
    | none => cases win
    | some p =>
      obtain ⟨obs,out⟩ := p
      exact Or.inr (actual_post_or_first w A left obs out rem s last actual fill win clean safe)
  · exact (clean clash).elim

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
