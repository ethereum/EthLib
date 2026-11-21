module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderChronicleGame

/-!
# Registrations along a physical signer execution

Only the signer's explicit success notices can extend the chronological registration list.

Each retained notice includes the physical and private-observer state immediately before it.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleSpec OracleComp TrialGraphWatch

abbrev Registered := FinderNotice × JointState

/-- Keep successful registrations in reverse execution order, with their incoming state. -/
@[expose] def registrations (xs : List Arrival) : List Registered :=
  xs.filterMap fun a => match a with
    | .note n@(.register ..) st => some (n, st)
    | _ => none

/-- Supported realization of an instrumented stateful computation. -/
@[expose] def Ran {pp : PublicParam} (q : Nat) {α : Type} (p : Program pp α)
    (r : ResidualCache pp) (s : ChronicleState) (a : α) (out : ResidualCache pp)
      (t : ChronicleState) :=
  ((a, out), t) ∈ support ((simulateQ (chronicle pp q) (p.run r)).run s)

protected theorem Ran.bind {pp q} {α β : Type} {p : Program pp α} {f : α → Program pp β}
    {r s a out t}
    (ran : Ran q (p >>= f) r s a out t) : ∃ b mid g, Ran q p r s b mid g ∧
      Ran q (f b) mid g a out t := by
  unfold Ran at ran ⊢
  simp only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at ran
  obtain ⟨⟨⟨b, mid⟩, g⟩, h, k⟩ := ran
  exact ⟨b, mid, g, h, k⟩

protected theorem Ran.pure_result {pp q} {α : Type} {r s a b out t}
    (ran : Ran q (pure a : Program pp α) r s b out t) : b = a ∧ out = r ∧ t = s := by
  unfold Ran at ran
  simpa [and_assoc] using ran

private theorem keep_raw (pp : PublicParam) (q : Nat) (xs : List Registered) :
    ((chronicle pp q) ∘ₛ raw).PreservesInv (fun st : ChronicleState =>
      registrations st.2 = xs) := by
  rintro t st old ⟨w, st', trace⟩ ran
  simp only [QueryImpl.compose, raw, simulateQ_spec_query] at ran
  obtain ⟨_, stored⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp ran
  change trace = remember pp (.inl t) st.1 w st.2 at stored
  change registrations trace = xs
  rw [stored]
  rcases t with (u | b) | g
  · exact old
  · by_cases fresh : MessageAt pp b ∧ st.1.1.2.1.1 b = none
    · simpa only [remember, ite_eq_left fresh, registrations, List.filterMap_cons] using old
    · simpa only [remember, ite_eq_right fresh] using old
  · exact old

/-- Raw graph computations, including key generation and verification, register nothing. -/
protected theorem Ran.carry_registers {pp q} {α : Type} {p : MixedLocal pp α} {r s a out t}
    (ran : Ran q (carry p) r s a out t) : registrations t.2 = registrations s.2 := by
  change ((a, out), t) ∈ support ((simulateQ (chronicle pp q) (simulateQ raw (p.run r))).run s)
    at ran
  rw [← QueryImpl.simulateQ_compose] at ran
  exact OracleComp.simulateQ_run_preservesInv _ _ (keep_raw pp q _) _ s rfl _ ran

/-- A notice captures the actual incoming state and keeps all preceding arrivals. -/
protected theorem Ran.emitted {pp q} {n} {r s a out t}
    (ran : Ran (pp := pp) q (emit n) r s a out t) :
    t.2 = .note n s.1 :: s.2 := by
  unfold Ran emit at ran
  simp only [StateT.run_mk, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at ran
  obtain ⟨z, reach, same⟩ := ran
  obtain ⟨_, logEq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp reach
  cases same
  exact logEq

/-- The attempt notice and its finder preserve the successful registrations. -/
protected theorem Ran.find_registers {pp q l e m r s a out t}
    (ran : Ran q (find pp l e m) r s a out t) :
    registrations t.2 = registrations s.2 := by
  unfold find at ran
  obtain ⟨_,_,_,note,scan⟩ := ran.bind
  rw [scan.carry_registers, note.emitted]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
