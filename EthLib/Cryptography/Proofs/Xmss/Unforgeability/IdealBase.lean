module

public import EthLib.Cryptography.Proofs.DerivationTable

/-!
# Proofs: a run of the ideal game of a derivation table

The ideal game holds a cache of public answers and a table of derivations.

A run only adds entries to both.

A program with public queries only runs in it as in the random oracle, and keeps the table.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleSpec OracleComp

variable {ι : Type} {pub : OracleSpec ι} [DecidableEq ι] [∀ t, SampleableType (pub.Range t)]
  {X R : Type} [DecidableEq X] [SampleableType R]

/-- A step of the ideal game only adds entries to its cache and to its table. -/
theorem le_of_mem_support_idealImpl {t : (pub.withDerivations X R).Domain}
    {st : SecretEncoding.SplitCache pub X R}
    {w : (pub.withDerivations X R).Range t × SecretEncoding.SplitCache pub X R}
    (hw : w ∈ support ((SecretEncoding.idealImpl pub X R t).run st)) :
    st.1 ≤ w.2.1 ∧ st.2 ≤ w.2.2 := by
  rcases t with (n | t) | x
  · simp only [SecretEncoding.idealImpl, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨u, -, rfl⟩ := hw
    exact ⟨le_rfl, le_rfl⟩
  · cases h : st.1 t with
    | some v =>
      rw [SecretEncoding.idealImpl_run_pub_some h] at hw
      simp only [support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨le_rfl, le_rfl⟩
    | none =>
      rw [SecretEncoding.idealImpl_run_pub_none h] at hw
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨u, -, rfl⟩ := hw
      exact ⟨QueryCache.le_cacheQuery _ h, le_rfl⟩
  · cases h : st.2 x with
    | some v =>
      rw [SecretEncoding.idealImpl_run_derive_some h] at hw
      simp only [support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨le_rfl, le_rfl⟩
    | none =>
      rw [SecretEncoding.idealImpl_run_derive_none h] at hw
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨u, -, rfl⟩ := hw
      exact ⟨le_rfl, QueryCache.le_cacheQuery _ h⟩

/-- A run of the ideal game only adds entries to its cache and to its table. -/
theorem le_of_mem_support_run_idealImpl {α : Type} (oa : OracleComp (pub.withDerivations X R) α)
    {st : SecretEncoding.SplitCache pub X R} {z : α × SecretEncoding.SplitCache pub X R}
    (hz : z ∈ support ((simulateQ (SecretEncoding.idealImpl pub X R) oa).run st)) :
    st.1 ≤ z.2.1 ∧ st.2 ≤ z.2.2 :=
  simulateQ_run_preservesInv _ (fun s => st.1 ≤ s.1 ∧ st.2 ≤ s.2)
    (fun _ _ hs _ hw => ⟨hs.1.trans (le_of_mem_support_idealImpl hw).1,
      hs.2.trans (le_of_mem_support_idealImpl hw).2⟩) oa st ⟨le_rfl, le_rfl⟩ z hz

/-- A program with public queries only runs in the ideal game as in the random oracle.

The table stays as it was. -/
theorem run_simulateQ_idealImpl_withDerivationsLift {α : Type}
    (oa : OracleComp (unifSpec + pub) α) (C : pub.QueryCache) (T : (X →ₒ R).QueryCache) :
    (simulateQ (SecretEncoding.idealImpl pub X R)
        (simulateQ (pub.withDerivationsLift X R) oa)).run (C, T) =
      (fun z => (z.1, (z.2, T))) <$> (simulateQ pub.romImpl oa).run C := by
  induction oa using OracleComp.inductionOn generalizing C with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [show (simulateQ (SecretEncoding.idealImpl pub X R) (pub.withDerivationsLift X R t)).run
      (C, T) = (fun z => (z.1, (z.2, T))) <$> (pub.romImpl t).run C from by
        simpa [OracleSpec.withDerivationsLift] using idealImpl_run_inl t C T, bind_map_left]
    exact bind_congr fun z => ih z.1 z.2

end EthLib.Cryptography
