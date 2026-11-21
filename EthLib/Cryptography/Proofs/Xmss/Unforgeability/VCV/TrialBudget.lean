module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialSource

/-!
# Charging trials before and after signing to the same public calls

The leanXMSS draft in "Security" counts the full experiment, including warm hash calls.

An eligible fresh message input can have a registered target or be waiting for one.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials

open Constants HashSig OracleComp OracleSpec PostSigning

/-- Unregistered trials and registered trials spend disjoint physical hash calls. -/
theorem separate (pp : PublicParam) (q : Nat) :
    QueryImpl.PreservesInv (handler pp q) (fun st => st.2.1 + st.1.1.paid ≤ st.1.2) := by
  rintro t ⟨⟨s, physical⟩, n, v⟩ h z hz
  obtain ⟨base, trial⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp hz
  obtain ⟨base, cost⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp base
  change n + s.paid ≤ physical at h
  rcases t with (i | b) | notice
  · change (z.1, z.2.1.1) ∈ support ((fun w => (w, s)) <$> _) at base
    rw [support_map] at base
    obtain ⟨w, _, state⟩ := base
    have same : z.2.1.1 = s := (congrArg Prod.snd state).symm
    have equalCost : z.2.1.2 = physical := cost
    change z.2.2.1 + z.2.1.1.paid ≤ z.2.1.2
    rw [trial, same, equalCost]
    exact h
  · rw [randomOracle.Targets.public_run, support_map] at base
    obtain ⟨row, _, eqn⟩ := base
    have next : z.2.1.1 = randomOracle.Targets.update (messageKey pp) low s b row.1 row.2 :=
      (congrArg Prod.snd eqn).symm
    have budget : z.2.1.2 = physical + 1 := cost
    change z.2.2.1 + z.2.1.1.paid ≤ z.2.1.2
    rw [budget, trial, next]
    simp only [BernoulliMoment.update, eligible, randomOracle.Targets.update]
    cases present : s.cache b with
    | some old => simp; omega
    | none =>
      cases key : messageKey pp b with
      | none => simp; omega
      | some k =>
        cases watched : s.target k with
        | some d => simp [watched]; omega
        | none =>
          by_cases room : n < q <;> simp [watched, room] <;> omega
  · change (z.1, z.2.1.1) ∈ support (pure ((), {s with target := record pp notice s.cache s.target})
      : ProbComp _) at base
    rw [support_pure, Set.mem_singleton_iff] at base
    have same : z.2.1.1.paid = s.paid :=
      congrArg (fun t : Unit × WatchState => t.2.paid) base
    have equalCost : z.2.1.2 = physical := cost
    change z.2.2.1 + z.2.1.1.paid ≤ z.2.1.2
    rw [trial, same, equalCost]
    exact h

/-- From the real key generation state, the distinct trial charges fit in the original meter. -/
theorem charged (A : Adversary) (q : Nat) {z} (hz : z ∈ support (game A q)) :
    z.2.2.1 + z.2.1.1.paid ≤ z.2.1.2 := by
  rw [game, mem_support_bind_iff] at hz
  obtain ⟨⟨raw, pk, cache, paid⟩, _, hz⟩ := hz
  exact simulateQ_run_preservesInv _ _ (separate pk.publicParam q) _ _
    (show 0 + 0 ≤ paid by omega) z hz

/-- A bounded native adversary can spend at most q on both sets of trials together. -/
theorem charged_le (A : Adversary) (q : Nat) (bounded : HasHashQueryBound A q)
    {z} (hz : z ∈ support (game A q)) : z.2.2.1 + z.2.1.1.paid ≤ q := by
  have watched : (z.1, z.2.1) ∈ support (countedGame A) := by
    rw [← erase_game A q, support_map]
    exact ⟨_, hz, rfl⟩
  have physical : (z.1, z.2.1.2) ∈ support (countedObservation A) := by
    rw [← countedGame_projection, support_map]
    exact ⟨_, watched, rfl⟩
  exact (charged A q hz).trans (((hashQueryBound_iff A q).1 bounded) _ physical)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials
