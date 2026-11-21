module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeOrigin

/-!
# Matching a registered signing digest on a first full-word response

The flag survives every later query, every notice and a refusal of the guard.

A real message recorded at its first public response sets the flag if its prior target matches.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleSpec OracleComp TrialGraphWatch

/-- A recorded word that matched its earlier target has already set the hit flag. -/
@[expose] def SeenPost (pp : PublicParam) (s : JointState × List Arrival) : Prop :=
  ∀ b w prior, Arrival.word b w prior ∈ s.2 → cold pp b prior.1.1.1.1.1 = true →
    target pp prior.1.1.1.1.2 b = some (halfOf 0 (ofOutput w)) → s.1.2 = true

private theorem seen_step (pp : PublicParam) (q : Nat) : (chronicle pp q).PreservesInv
    (SeenPost pp) := by
  rintro t ⟨s, xs⟩ before ⟨ans, s', xs'⟩ ran
  obtain ⟨hjoint, logEq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp ran
  obtain ⟨_, flag⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp hjoint
  change xs' = remember pp t s ans xs at logEq
  change s'.2 = (s.2 || (activePost pp (target pp) t s.1.1 && matchesPost (target pp) t s.1.1 ans))
    at flag
  subst xs'
  intro b w prior mem was matchWord
  change s'.2 = true
  rw [flag, Bool.or_eq_true]
  have old (earlier : Arrival.word b w prior ∈ xs) := before b w prior earlier was matchWord
  rcases t with ((u | a) | op) | n
  · exact Or.inl (old mem)
  · by_cases recorded : MessageAt pp a ∧ s.1.2.1.1 a = none
    · simp only [remember, ite_eq_left recorded, List.mem_cons] at mem
      rcases mem with same | earlier
      · cases same
        exact Or.inr (by simp [activePost, matchesPost, was, matchWord])
      · exact Or.inl (old earlier)
    · exact Or.inl (old (by simpa [remember, recorded] using mem))
  · exact Or.inl (old mem)
  · exact Or.inl (old (by simpa [remember] using mem))

/-- A later observed match sets the physical hit flag on the same run. -/
theorem seen_run {α : Type} (pp : PublicParam) (q : Nat) (p : OracleComp Queries α) (s : JointState)
    {z} (ran : z ∈ support ((simulateQ (chronicle pp q) p).run (s, []))) : SeenPost pp z.2 := by
  apply OracleComp.simulateQ_run_preservesInv _ _ (seen_step pp q) _ _ _ _ ran
  simp [SeenPost]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
