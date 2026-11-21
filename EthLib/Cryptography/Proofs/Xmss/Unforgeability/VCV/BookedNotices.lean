module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.BookingCuts

/-!
# A recorded signing notice has an occupied booking

The booking is made by the same query that emits a notice.

It survives the rest of the capped experiment.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleSpec OracleComp EarlierDigest EarlierDigest.Ledger TrialGraphWatch

private def HasBookings (s : ChronicleState) : Prop :=
  ∀ n p, Arrival.note n p ∈ s.2 → (bookings s n.key).isSome

/-- Every signing notice found in the chronological stream has its own occupied booking. -/
theorem noted_booked {pp q} {α : Type} {p : OracleComp Queries α} {s : JointState} {z}
    (ran : z ∈ support ((simulateQ (chronicle pp q) p).run (s,[]))) :
    ∀ n prior, Arrival.note n prior ∈ z.2.2 → (bookings z.2 n.key).isSome := by
  apply simulateQ_run_preservesInv _ HasBookings _ _ _ (fun n p h =>
    (List.not_mem_nil h).elim) _ ran
  intro op st old z step n prior seen
  have grow : (bookings st n.key).isSome → (bookings z.2 n.key).isSome := by
    intro was
    rw [booked_step op st step]
    cases op with
    | inl => exact was
    | inr note =>
      by_cases same : n.key = note.key
      · simp [begin,same]
      · simpa only [begin,Function.update_of_ne same] using was
  have add := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp step).2
  change z.2.2 = remember pp op st.1 z.1 st.2 at add
  rw [add] at seen
  rcases op with ((u | b) | g) | note
  · exact grow (old n prior seen)
  · by_cases fresh : MessageAt pp b ∧ st.1.1.2.1.1 b = none
    · simp only [remember,ite_eq_left fresh,List.mem_cons] at seen
      rcases seen with eq | priorMem
      · cases eq
      · exact grow (old n prior priorMem)
    · simp only [remember,ite_eq_right fresh] at seen
      exact grow (old n prior seen)
  · exact grow (old n prior seen)
  · change Arrival.note n prior ∈ Arrival.note note st.1 :: st.2 at seen
    rcases List.mem_cons.mp seen with eq | priorMem
    · obtain ⟨rfl,rfl⟩ := Arrival.note.inj eq
      rw [booked_step (.inr _) st step]
      simp [begin]
    · exact grow (old n prior priorMem)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
