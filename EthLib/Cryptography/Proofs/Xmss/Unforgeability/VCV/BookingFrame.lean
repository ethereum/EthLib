module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderChronicleGame

/-!
# Persistence of first finder bookings

The first attempt books the signing key before any private randomizer lookup.

All later searches and public operations preserve that booking, including exhausted searches.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleSpec OracleComp EarlierDigest EarlierDigest.Ledger TrialGraphWatch

abbrev bookings (s : ChronicleState) : Snapshots := s.1.1.2.2

theorem booked_step {pp q} (t : Queries.Domain) (s : ChronicleState) {a out}
    (ran : (a,out) ∈ support (((chronicle pp q) t).run s)) :
    bookings out = match t with
      | .inr n => begin (bookings s) n.key s.1.1.2.1
      | _ => bookings s := by
  have joint := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp ran).1
  have watched := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp joint).1
  have h := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp watched).2
  change out.1.1.2 = update pp cut t a s.1.1.2 at h
  have eq := congrArg Prod.snd h
  rcases t with ((coin | b) | op) | n
  · exact eq
  · simpa [update, recordWordAt, apply_ite] using eq
  · exact eq
  · exact eq

/-- No ordinary operation or later notice can clear a booked key. -/
theorem booked_persists {pp q} {α : Type} {p : OracleComp Queries α} {s out a}
    (ran : (a,out) ∈ support ((simulateQ (chronicle pp q) p).run s))
    (k : Key) (was : (bookings s k).isSome) : (bookings out k).isSome := by
  apply simulateQ_run_preservesInv _ (fun g => (bookings g k).isSome) _ _ _ was _ ran
  intro t g old z actual
  rw [booked_step t g actual]
  cases t with
  | inl => exact old
  | inr n =>
    by_cases eq : k = n.key
    · simp [begin,eq]
    · simpa [begin,Function.update_of_ne eq] using old

/-- The incoming key of this concrete finder has a booking at its return on either outcome. -/
theorem find_booked {pp q} (l : Layer) (e : UInt32) (m : ByteArray)
    {r s a out t} (ran : ((a,out),t) ∈ support ((simulateQ (chronicle pp q)
      ((find pp l e m).run r)).run s)) : (bookings t (l,e)).isSome := by
  simp only [find, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at ran
  obtain ⟨⟨_,g⟩,start,tail⟩ := ran
  apply booked_persists tail
  simp only [emit, StateT.run_mk, simulateQ_map, simulateQ_spec_query,
    StateT.run_map, support_map] at start
  obtain ⟨⟨_, seen⟩,note,tie⟩ := start
  have eq : seen = g := congrArg Prod.snd tie
  subst g
  rw [booked_step (.inr (.attempt l e m)) s note]
  simp [begin, FinderNotice.key]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
