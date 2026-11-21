module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeJoint

/-!
# First physical reads on the observed finder path

Each message word has one first response, with both tagged rows cold beforehand.

The transcript retains the incoming registry, first-search ledger and hit flag at that call.

The final pending fill preserves both ordinary halves.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig CachedCodeword OracleSpec OracleComp EarlierDigest EarlierDigest.Ledger TrialGraphWatch
open scoped Classical

abbrev JointState := WatchedState × Bool

inductive Arrival where
  | word (b : HashInput) (w : HashOutput) (prior : JointState)
  | note (n : FinderNotice) (prior : JointState)

/-- Record the incoming state on each first message answer and each finder notice. -/
@[expose] noncomputable def remember (pp : PublicParam) :
    (t : Queries.Domain) → JointState → Queries.Range t → List Arrival → List Arrival
  | .inl (.inl (.inr b)), s, w, xs =>
    if MessageAt pp b ∧ s.1.2.1.1 b = none then .word b w s :: xs else xs
  | .inr n, s, _, xs => .note n s :: xs
  | _, _, _, xs => xs

/-- The transcript observes a realized joint path without changing the real response. -/
@[expose] noncomputable def chronicle (pp : PublicParam) (q : Nat) :=
  (joint pp q).extendState fun t s w _ xs => remember pp t s w xs

theorem chronicle_joint {α : Type} (pp : PublicParam) (q : Nat) (p : OracleComp Queries α)
    (s : JointState) (xs : List Arrival) :
    Prod.map id Prod.fst <$> (simulateQ (chronicle pp q) p).run (s, xs) =
      (simulateQ (joint pp q) p).run s :=
  extendState_run_proj_eq _ _ p s xs

/-- Every live message word has a first response before either half is cached. -/
structure Origin (pp : PublicParam) (s : JointState × List Arrival) : Prop where
  sound : Sound pp (s.1.1.1.1.1.1, s.1.1.2)
  first : ∀ b w, s.1.1.2.1.1 b = some w →
    ∃ prior, Arrival.word b w prior ∈ s.2 ∧ cold pp b prior.1.1.1.1.1 = true

private theorem watched_sound {pp : PublicParam} {q : Nat} (t : Queries.Domain) (s : WatchedState)
    (pre : Sound pp (s.1.1.1.1, s.2)) {x next}
    (ran : (x, next) ∈ support
      (((watched pp cut register (fun r b => (target pp r b).isSome) q) t).run s)) :
    Sound pp (next.1.1.1.1, next.2) := by
  let h := Ledger.project_watch pp cut register (fun r b => (target pp r b).isSome) q
    (fun w => (digits w).isSome) (liftM (Queries.query t) : OracleComp Queries _) s
  simp only [simulateQ_spec_query] at h
  apply sound_step pp cut t _ pre (x, next.1.1.1.1, next.2)
  rw [← h, support_map]
  exact ⟨(x, next), ran, rfl⟩

private theorem origins (pp : PublicParam) (q : Nat) : (chronicle pp q).PreservesInv
    (Origin pp) := by
  rintro t ⟨⟨st, flag⟩, xs⟩ pre ⟨x, ⟨st', flag'⟩, xs'⟩ ran
  obtain ⟨hjoint, logEq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp ran
  obtain ⟨hwatch, _⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp hjoint
  obtain ⟨_, historyEq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp hwatch
  change st'.2 = update pp cut t x st.2 at historyEq
  change xs' = remember pp t (st, flag) x xs at logEq
  subst xs'
  refine ⟨watched_sound t st pre.sound hwatch, ?_⟩
  intro b w
  change st'.2.1.1 b = some w → _
  rw [historyEq]
  rcases t with ((coin | a) | op) | n
  · exact pre.first b w
  · by_cases fresh : MessageAt pp a ∧ st.2.1.1 a = none
    · simp only [update, remember, ite_eq_left fresh]
      intro found
      by_cases same : b = a
      · subst a
        have eq : x = w := by simpa only [recordWordAt, QueryCache.cacheQuery_self,
          Option.some.injEq] using found
        subst w
        have rows := pre.sound.rows b fresh.1
        rw [fresh.2] at rows
        have low : st.1.1.1.1.1.1 (.inl b) = none := rows.1
        have high : st.1.1.1.1.1.1 (.inr b) = none := rows.2
        exact ⟨(st, flag), List.mem_cons_self, by simp [cold, fresh.1, low, high]⟩
      · have old := pre.first b w (by simpa [recordWordAt, QueryCache.cacheQuery_of_ne, same]
        using found)
        obtain ⟨s, mem, was⟩ := old
        exact ⟨s, List.mem_cons_of_mem _ mem, was⟩
    · simpa only [update, remember, fresh, ite_false] using pre.first b w
  · exact pre.first b w
  · intro old
    obtain ⟨s, mem, was⟩ := pre.first b w (by simpa only [update, cut] using old)
    exact ⟨s, List.mem_cons_of_mem _ mem, was⟩

/-- At cold initialization all later supported runs have the first-read and readback properties. -/
theorem origin_run {α : Type} (pp : PublicParam) (q : Nat) (p : OracleComp Queries α) (r : Registry)
    {z} (ran : z ∈ support ((simulateQ (chronicle pp q) p).run
      ((((((((∅, ∅), []), r), 0), 0, 0), ((∅, ∅), fun _ => none)), false), []))) :
    Origin pp z.2 := by
  apply OracleComp.simulateQ_run_preservesInv _ _ (origins pp q) _ _ _ _ ran
  exact ⟨sound_empty pp, by simp⟩

/-- A filled ordinary low message row came from one real charged full-word call.

The same word supplies the filled high row, even when internal labels were still pending. -/
theorem Origin.filled_low {pp : PublicParam} {s : JointState × List Arrival}
    (origin : Origin pp s) (b : HashInput) (real : MessageAt pp b)
    {st : TwoLayerGraph.Honest.SharedState} (filled : st ∈ support
      (RelabelState.endFill s.1.1.1.1.1.1))
    {lo : ChainGraph.Word} (read : st.1 (.inl b) = some lo) :
    ∃ w prior, Arrival.word b w prior ∈ s.2 ∧ cold pp b prior.1.1.1.1.1 = true ∧
      (PairedHashWord.halves w).1 = lo ∧ st.1 (.inr b) = some (PairedHashWord.halves w).2 := by
  rw [RelabelState.fst_eq_of_mem_support_endFill filled] at read ⊢
  obtain ⟨low, high⟩ := origin.sound.rows b real
  cases found : s.1.1.2.1.1 b with
  | none =>
    rw [found] at low
    exact (Option.some_ne_none lo (read.symm.trans low)).elim
  | some w =>
    rw [found] at low high
    obtain ⟨prior, mem, was⟩ := origin.first b w found
    exact ⟨w, prior, mem, was, Option.some.inj (low.symm.trans read), high⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
