module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchReserve
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialGraphErase

/-!
# Physical message words and first-search snapshots on the shared graph

A full message call reads two tagged ordinary rows and returns their combined word.

The ledger remembers this returned word at the same physical input.

A first-search notice saves this table before the private randomizer is read.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger

open HashSig OracleComp OracleSpec PostSigning TwoLayerGraph CanonicalGraph.PairedQueries
open RealClient.GraphPrefix RealClient.GraphPrefix.TrialGraphWatch
open scoped Classical

abbrev History := Entry × Snapshots

/-- Forward each original mixed graph operation and erase a first-search notice to unit. -/
noncomputable def backend {Note : Type} (pp : PublicParam) : QueryImpl (Spec Note)
    (StateT D ProbComp)
  | .inl t => simulateQ (graph pp).deferredImpl (expand PairedHashWord.halves t)
  | .inr _ => pure ()

/-- Record the first physical response and retain its full input in the finite footprint. -/
noncomputable def recordWordAt (b : HashInput) (w : HashOutput) (h : History) : History :=
  ((h.1.1.cacheQuery b w, insert b h.1.2), h.2)

/-- Observe only genuine message calls and explicit first-search notices. -/
noncomputable def update {Note : Type} (pp : PublicParam) (cut : Note → Option Key) :
    (t : (Spec Note).Domain) → (Spec Note).Range t → History → History
  | .inl (.inl (.inr b)), w, h =>
    if MessageAt pp b ∧ h.1.1 b = none then recordWordAt b w h else h
  | .inr note, _, h => match cut note with
    | some key => (h.1, begin h.2 key h.1)
    | none => h
  | _, _, h => h

/-- The ledger observes the same graph on returns, budget refusals and failed signatures. -/
noncomputable def handler {Note : Type} (pp : PublicParam) (cut : Note → Option Key) :=
  (backend (Note := Note) pp).extendState fun t _ w _ h => update pp cut t w h

/-- Erasing the other observer's counters leaves exactly the same path and first-search ledger. -/
theorem project_watch {Note R α : Type} (pp : PublicParam) (cut : Note → Option Key)
    (notice : Note → R → R) (registered : R → HashInput → Bool) (q : Nat) (test : HashOutput → Bool)
    (p : OracleComp (Spec Note) α) (s : Observed R × History) :
    let record := (observe pp notice registered q test).extendState fun t _ w _ h =>
      update pp cut t w h
    let proj := fun state : Observed R × History => (state.1.1.1.1, state.2)
    Prod.map id proj <$> (simulateQ record p).run s
      = (simulateQ (handler pp cut) p).run (proj s) := by
  apply map_run_simulateQ_eq_of_query_map_eq
  rintro (t | n) state <;>
    simp [observe, withPost, BernoulliMoment.observe, base, QueryImpl.extendState_apply, backend,
      handler,
      bind_pure_comp, Functor.map_map]

def Covered (s : Entry) := ∀ b w, s.1 b = some w → b ∈ s.2

/-- Every stored full word agrees with both ordinary public rows.

Every current or saved word lookup has an entry in its finite physical footprint.
-/
structure Sound (pp : PublicParam) (s : D × History) : Prop where
  rows : ∀ b, MessageAt pp b →
    s.1.1.1 (.inl b) = (s.2.1.1 b).map (fun w => (PairedHashWord.halves w).1) ∧
    s.1.1.1 (.inr b) = (s.2.1.1 b).map (fun w => (PairedHashWord.halves w).2)
  live : Covered s.2.1
  stored : ∀ b, b ∈ s.2.1.2 → (s.2.1.1 b).isSome
  saved : ∀ k, ∀ h, s.2.2 k = some h → Covered h

/-- At a cold shared graph and empty first-search table all readback conditions hold. -/
theorem sound_empty (pp : PublicParam) :
    Sound pp (((∅, ∅), []), ((∅, ∅), fun _ => none)) := by
  constructor <;> simp [Covered]

private theorem begin_sound {pp : PublicParam} {s : D × History} (prior : Sound pp s) (k : Key) :
    Sound pp (s.1, s.2.1, begin s.2.2 k s.2.1) := by
  refine ⟨prior.rows, prior.live, prior.stored, ?_⟩
  intro j snapshot found
  by_cases same : j = k
  · subst j
    simp only [begin, Function.update_self, Option.some.injEq] at found
    subst snapshot
    cases h : s.2.2 k with
    | none => simpa only [entry, h, Option.getD_none] using prior.live
    | some old => simpa only [entry, h, Option.getD_some] using prior.saved k old h
  · exact prior.saved j snapshot (by simpa only [begin, Function.update_of_ne same] using found)

private theorem record_sound {pp : PublicParam} {st : D} {h : History} (prior : Sound pp (st, h))
    (a : HashInput) (w : HashOutput) :
    Sound pp (recordWord PairedHashWord.halves a w st, recordWordAt a w h) := by
  refine ⟨?_, ?_, ?_, prior.saved⟩
  · intro b trial
    by_cases same : b = a
    · subst b
      simp [recordWordAt, recordWord, QueryCache.cacheQuery_of_ne]
    · simpa [recordWordAt, recordWord, QueryCache.cacheQuery_of_ne, same] using prior.rows b trial
  · intro b v existsWord
    by_cases same : b = a
    · exact Finset.mem_insert.mpr (Or.inl same)
    · exact Finset.mem_insert_of_mem (prior.live b v (by simpa [recordWordAt,
        same] using existsWord))

  · intro b hb
    rcases Finset.mem_insert.mp hb with eq | earlier
    · subst b
      simp [recordWordAt]
    · by_cases eq : b = a
      · subst b
        simp [recordWordAt]
      · simpa [recordWordAt, eq] using prior.stored b earlier

private theorem unchanged {pp : PublicParam} {st next : D} {h : History} (prior : Sound pp (st, h))
    (same : ∀ b, MessageAt pp b → next.1.1 (.inl b) = st.1.1 (.inl b) ∧
      next.1.1 (.inr b) = st.1.1 (.inr b)) : Sound pp (next, h) := by
  refine ⟨?_, prior.live, prior.stored, prior.saved⟩
  exact fun b hb => ⟨(same b hb).1.trans (prior.rows b hb).1, (same b hb).2.trans
      (prior.rows b hb).2⟩

/-- Readback and finite coverage hold after each actual oracle response, including cache hits. -/
theorem sound_step {Note : Type} (pp : PublicParam) (cut : Note → Option Key) :
    (handler pp cut).PreservesInv (Sound pp) := by
  rintro t ⟨st, h⟩ prior ⟨x, st', h'⟩ hz
  obtain ⟨ran, upd⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp hz
  change h' = update pp cut t x h at upd
  change (x, st') ∈ support ((backend pp t).run st) at ran
  subst h'
  rcases t with ((coin | a) | op) | note
  · apply unchanged prior
    intro b _
    exact mixed_rows_away (graph pp) PairedHashWord.halves b _ st (by simp) ran
  · by_cases actual : MessageAt pp a
    · obtain ⟨l, e, msg, r, encoded⟩ := actual
      have trial : IsTrial a := encoded ▸ isTrial_message pp l e msg r
      have ha : MessageAt pp a := ⟨l, e, msg, r, encoded⟩
      obtain ⟨hl, hh⟩ := prior.rows a ha
      cases present : h.1.1 a with
      | none =>
        simp only [present, Option.map_none] at hl hh
        simp only [backend] at ran
        rw [← support_eq_of_evalDistEq (trial_fresh pp a trial st hl hh), support_map] at ran
        obtain ⟨w, _, eq⟩ := ran
        cases eq
        simpa only [update, ha, present, and_self, ite_true] using record_sound prior a x
      | some w =>
        simp only [present, Option.map_some] at hl hh
        simp only [backend] at ran
        rw [trial_warm pp a trial st w hl hh, mem_support_pure_iff] at ran
        cases ran
        simpa only [update, present, reduceCtorEq, and_false, ite_false] using prior
    · simp only [update, actual, false_and, ite_false]
      apply unchanged prior
      intro b hb
      exact mixed_rows_away (graph pp) PairedHashWord.halves b _ st (by
        intro eq
        exact actual ((Sum.inr.inj (Sum.inl.inj eq)) ▸ hb)) ran
  · apply unchanged prior
    intro b _
    exact mixed_rows_away (graph pp) PairedHashWord.halves b _ st (by simp) ran
  · change (x, st') ∈ support (pure ((), st) : ProbComp _) at ran
    rw [mem_support_pure_iff] at ran
    cases ran
    cases key : cut note with
    | none => simpa only [update, key] using prior
    | some k => simpa only [update, key] using begin_sound prior k

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger
