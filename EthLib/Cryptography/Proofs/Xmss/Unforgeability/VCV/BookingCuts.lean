module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.BookingFrame

/-!
# Bookings outside a single signing operation

A physical word cannot open a new signing-key booking.

The original signer books its own key before it samples the private word.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig Constants EarlierDigest EarlierDigest.Ledger OracleSpec OracleComp

/-- Every physical call preserves the complete booking table. -/
theorem carry_bookings {pp q} {α : Type} {p : MixedLocal pp α} {r s a out t}
    (ran : ((a,out),t) ∈ support ((simulateQ (chronicle pp q) ((carry p).run r)).run s)) :
    bookings t = bookings s := by
  have calls : AllQueriesSatisfy ((carry p).run r) (fun t => match t with
      | .inl _ => True | .inr _ => False) :=
    (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) (p.run r)).simulateQ
      fun x _ =>
      (allQueriesSatisfy_query_iff _ _).2 (by trivial)
  apply calls.holds_of_mem_support_run_simulateQ (fun g => bookings g = bookings s) _ rfl ran
  rintro (x | n) physical g prior z step
  · exact (booked_step (.inl x) g step).trans prior
  · cases physical

/-- A notice can change only the booking at its named signing key. -/
theorem notice_other_booking {pp q} (n : FinderNotice) {r s a out t}
    (ran : ((a,out),t) ∈ support ((simulateQ (chronicle pp q) ((emit (pp := pp) n).run r)).run s))
    (k : Key) (other : k ≠ n.key) : bookings t k = bookings s k := by
  simp only [emit,StateT.run_mk,simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map]
    at ran
  obtain ⟨⟨_,mid⟩,step,eq⟩ := ran
  have same : mid = t := congrArg Prod.snd eq
  subst t
  rw [booked_step (.inr n) s step]
  simp only [begin, Function.update_of_ne other]

/-- A new booking for another key cannot originate in this finder's private or public calls. -/
theorem find_other_booking {pp q} (l : Layer) (e : UInt32) (msg : ByteArray)
    {r s a out t} (ran : ((a,out),t) ∈ support ((simulateQ (chronicle pp q)
      ((find pp l e msg).run r)).run s)) (k : Key) (other : k ≠ (l,e)) :
    bookings t k = bookings s k := by
  simp only [find, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at ran
  obtain ⟨⟨_,g⟩,first,rest⟩ := ran
  rw [carry_bookings rest]
  simp only [emit,StateT.run_mk,simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map]
    at first
  obtain ⟨⟨_,mid⟩,step,eq⟩ := first
  have same : mid = g := congrArg Prod.snd eq
  subst g
  rw [booked_step (.inr (.attempt l e msg)) s step]
  simp only [FinderNotice.key, begin, Function.update_of_ne other]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
