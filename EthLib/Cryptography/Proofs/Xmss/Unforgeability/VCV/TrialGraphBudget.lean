module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialGraphWatch
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NormalizedCharges

/-!
# One physical footprint for pre-sign and post-sign trials

The two counters can increase only on disjoint classes of fresh inputs.

The ordinary cache retains every counted input across later graph work and registration notices.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch

open HashSig OracleSpec OracleComp TwoLayerGraph CanonicalGraph.PairedQueries
open ChainGraph (Word Public)
open scoped Classical ENNReal

private theorem messages_mono (pp : PublicParam) {s t : D}
    (h : s.1.1 ≤ t.1.1) : messageInputs pp s.1.1 ⊆ messageInputs pp t.1.1 := by
  rintro b ⟨present, source⟩
  refine ⟨?_, source⟩
  rcases present with low | high
  · exact Or.inl (QueryCache.isSome_mono h low)
  · exact Or.inr (QueryCache.isSome_mono h high)

private theorem base_mono {Note R : Type} (pp : PublicParam) (notice : Note → R → R)
    (t : (Spec Note).Domain) (s : D × R) {z}
    (hz : z ∈ support (((base pp notice) t).run s)) : s.1.1.1 ≤ z.2.1.1.1 := by
  cases t with
  | inl raw =>
    simp only [base, StateT.run_mk, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ((graph pp).le_of_mem_support_simulateQ_deferredImpl _ hy).1
  | inr n =>
    simp only [base, StateT.run_mk, mem_support_pure_iff] at hz
    subst z
    rfl

private theorem base_cold_grows {Note R : Type} (pp : PublicParam) (notice : Note → R → R)
    (b : HashInput) (s : D × R) (active : cold pp b s.1 = true) {z}
    (hz : z ∈ support (((base pp notice) (.inl (.inl (.inr b)))).run s)) :
    (messageInputs pp s.1.1.1).encard + 1 ≤ (messageInputs pp z.2.1.1.1).encard := by
  have info : MessageAt pp b ∧ s.1.1.1 (.inl b) = none ∧ s.1.1.1 (.inr b) = none := by
    simpa [cold, and_assoc] using active
  obtain ⟨real, low, high⟩ := info
  have prior := messages_mono pp (base_mono pp notice _ s hz)
  have fresh : b ∉ messageInputs pp s.1.1.1 := by
    rintro ⟨hl | hh, _⟩
    · simp [low] at hl
    · simp [high] at hh
  rw [← Set.encard_insert_of_notMem fresh]
  apply Set.encard_le_encard
  apply Set.insert_subset _ prior
  refine ⟨Or.inl ?_, real⟩
  obtain ⟨l, e, m, r, eq⟩ := real
  have law := trial_fresh pp b (eq ▸ isTrial_message pp l e m r) s.1 low high
  simp only [base, StateT.run_mk, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [← support_eq_of_evalDistEq law, support_map] at hy
  obtain ⟨w, _, rfl⟩ := hy
  simp [recordWord, QueryCache.cacheQuery_of_ne]

abbrev Observed (R : Type) := ((D × R) × Nat) × Nat × Nat

/-- Measured unregistered plus registered trials cannot exceed the occupied message inputs. -/
@[expose] def Fits {R : Type} (pp : PublicParam) (s : Observed R) : Prop :=
  (s.1.2 + s.2.1 : ℕ∞) ≤ (messageInputs pp s.1.1.1.1.1).encard

/-- The same-path bound survives every response, notice, and adaptive stop. -/
theorem fits_step {Note R : Type} (pp : PublicParam) (notice : Note → R → R)
    (registered : R → HashInput → Bool) (q : Nat) (test : HashOutput → Bool) :
    (observe pp notice registered q test).PreservesInv (Fits pp) := by
  rintro t ⟨⟨⟨s, reg⟩, n⟩, k, u⟩ prior ⟨a, ⟨⟨⟨s', reg'⟩, n'⟩, k', u'⟩⟩ hz
  obtain ⟨hpost, hcount⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).1 hz
  obtain ⟨hbase, hpaid⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).1 hpost
  have npre := congrArg Prod.fst hcount
  have row := Set.encard_le_encard (messages_mono pp (base_mono pp notice t (s, reg) hbase))
  change (↑n + ↑k : ℕ∞) ≤ (messageInputs pp s.1.1).encard at prior
  change (↑n' + ↑k' : ℕ∞) ≤ (messageInputs pp s'.1.1).encard
  rcases t with ((coin | b) | op) | admin
  · simp [pre, BernoulliMoment.update] at hpaid npre
    simpa [hpaid, npre] using prior.trans row
  · by_cases fresh : cold pp b s = true
    · have grow := base_cold_grows pp notice b (s, reg) fresh hbase
      refine (le_trans ?_ (add_le_add_left prior 1)).trans grow
      cases watched : registered reg b <;> by_cases room : k < q <;>
        simp [pre, BernoulliMoment.update, fresh, watched, room] at hpaid npre <;>
        simp [hpaid, npre, Nat.cast_add, add_assoc, add_comm, add_left_comm]
    · simp [pre, BernoulliMoment.update, fresh] at hpaid npre
      simpa [hpaid, npre] using prior.trans row
  · simp [pre, BernoulliMoment.update] at hpaid npre
    simpa [hpaid, npre] using prior.trans row
  · simp [pre, BernoulliMoment.update] at hpaid npre
    simpa [hpaid, npre] using prior.trans row

/-- A stopped or completed adaptive run pays each full message input at most once. -/
theorem fits_run {Note R α : Type} (pp : PublicParam) (notice : Note → R → R)
    (registered : R → HashInput → Bool) (q : Nat) (test : HashOutput → Bool)
    (body : OracleComp (Spec Note) α) (reg : R) {z}
    (ran : z ∈ support ((simulateQ (observe pp notice registered q test) body).run
      (((((∅, ∅), []), reg), 0), 0, 0))) : Fits pp z.2 :=
  simulateQ_run_preservesInv _ _ (fits_step pp notice registered q test) body _
    (by simp [Fits]) z ran

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch
