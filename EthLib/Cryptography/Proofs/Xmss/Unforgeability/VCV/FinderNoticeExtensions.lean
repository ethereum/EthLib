module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistrationProjection

/-!
# Earlier registration states in one common graph

A first response and a notice both store the state before their operation.

Every later supported prefix extends that earlier shared graph.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleSpec OracleComp TrialGraphWatch TwoLayerGraph

@[expose] def Arrival.prior : Arrival → JointState
  | .word _ _ s | .note _ s => s

private theorem advances (pp : PublicParam) (q : Nat) (t : Queries.Domain)
    (s : ChronicleState) {z} (hit : z ∈ support (((chronicle pp q) t).run s)) :
    (physical s.1).1 ≤ (physical z.2.1).1 := by
  let keep : ResidualCache pp := (∅, ∅)
  have step : Ran q (StateT.mk (fun u : ResidualCache pp =>
    (fun w => (w,u)) <$> (liftM (Queries.query t) : OracleComp Queries _)))
      keep s z.1 keep z.2 := by
    unfold Ran
    simp only [StateT.run_mk, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map]
    exact ⟨z, hit, rfl⟩
  exact step.graph_mono

/-- Every arrival's prior graph is an extension predecessor of the current execution state. -/
theorem arrivals_extend {α : Type} (pp : PublicParam) (q : Nat) (p : OracleComp Queries α)
    (s : JointState)
    {z} (ran : z ∈ support ((simulateQ (chronicle pp q) p).run (s, []))) :
    ∀ a ∈ z.2.2, (physical a.prior).1 ≤ (physical z.2.1).1 := by
  let inv (u : ChronicleState) := ∀ a ∈ u.2, (physical a.prior).1 ≤ (physical u.1).1
  apply simulateQ_run_preservesInv (chronicle pp q) inv _ p (s, []) (by simp [inv]) _ ran
  rintro t st prev ⟨w,next,xs⟩ step a member
  have grows := advances pp q t st step
  obtain ⟨_, eq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp step
  change xs = remember pp t st.1 w st.2 at eq
  change a ∈ xs at member
  rw [eq] at member
  have old (mem : a ∈ st.2) := (prev a mem).trans grows
  rcases t with ((coin | b) | op) | n
  · exact old member
  · by_cases fresh : MessageAt pp b ∧ st.1.1.2.1.1 b = none
    · simp only [remember, ite_eq_left fresh, List.mem_cons] at member
      rcases member with rfl | mem
      · exact grows
      · exact old mem
    · exact old (by simpa only [remember, ite_eq_right fresh] using member)
  · exact old member
  · simp only [remember, List.mem_cons] at member
    rcases member with rfl | mem
    · exact grows
    · exact old mem

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
