module

public import EthLib.Cryptography.Proofs.Kzg.BlobBindingReduction
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer

set_option autoImplicit false

/-!
# Proofs: random-oracle bounds for blob binding

A fresh field element is rarely a root, including after embedding it in a polynomial ring.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open OracleComp OracleSpec ENNReal Polynomial
open scoped EthLib.Cryptography.Bls.Fr

/-- An injective map into an integral domain preserves the bound on polynomial roots. -/
theorem card_roots_embedding_le {R : Type*} [CommRing R] [IsDomain R]
    (embed : Fr ↪ R) (P : R[X]) {d : Nat} (hd : P.natDegree ≤ d)
    [DecidablePred fun r : Fr => P ≠ 0 ∧ P.eval (embed r) = 0] :
    (Finset.univ.filter fun r : Fr => P ≠ 0 ∧ P.eval (embed r) = 0).card ≤ d := by
  classical
  by_cases hP : P = 0
  · simp [hP]
  let roots := Finset.univ.filter fun r : Fr => P ≠ 0 ∧ P.eval (embed r) = 0
  have hroots : roots.map embed ⊆ P.roots.toFinset := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hr
    exact Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (Finset.mem_filter.mp hx).2.2)
  calc roots.card = (roots.map embed).card := by simp
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ ≤ d := hd

/-- Uniform field elements hit roots along an embedding with probability at most `d / r`. -/
theorem prEvent_uniform_embedding_root_le {R : Type*} [CommRing R] [IsDomain R]
    (embed : Fr ↪ R) (P : R[X]) {d : Nat} (hd : P.natDegree ≤ d) :
    Pr{let r ← $ᵗ Fr}[P ≠ 0 ∧ P.eval (embed r) = 0] ≤ d / Fr.modulus := by
  classical
  rw [SampleableType.prEvent_uniformSample, Bls.Fr.card_eq]
  gcongr
  exact_mod_cast card_roots_embedding_le embed P hd

namespace BlobBinding

open EthLib.Cryptography.Kzg.Constants

/-- Distinguish an individual challenge from the challenge of a batch. -/
def Request.isBlob : Request → Bool
  | .blob _ _ => true
  | .batch _ => false

/-- Charge only individual blob challenges, leaving private coins free. -/
def isBlobQuery : Spec.Domain → Bool
  | .inl _ => false
  | .inr request => request.isBlob

/-- Charge only batch challenges, leaving private coins free. -/
def isBatchQuery : Spec.Domain → Bool
  | .inl _ => false
  | .inr request => !request.isBlob

/-- The number of individual challenge calls, including repeated inputs. -/
def State.blobQueries (s : State) : Nat :=
  s.history.countP fun reply => reply.request.isBlob

/-- The number of batch challenge calls, including repeated inputs. -/
def State.batchQueries (s : State) : Nat :=
  s.history.countP fun reply => !reply.request.isBlob

/-- Each logged public query adds one charge to its own query count. -/
theorem State.blobQueries_record (s : State) (request : Request) (answer : Fr) (fresh : Bool) :
    (s.record request answer fresh).blobQueries =
      s.blobQueries + if request.isBlob then 1 else 0 := by
  simp [State.blobQueries, State.record]

/-- Each logged batch query adds one to the batch count. -/
theorem State.batchQueries_record (s : State) (request : Request) (answer : Fr) (fresh : Bool) :
    (s.record request answer fresh).batchQueries =
      s.batchQueries + if !request.isBlob then 1 else 0 := by
  simp [State.batchQueries, State.record]

/-- A new transcript entry contributes its own blob-root event. -/
theorem State.badBlob_record (s : State) (request : Request) (answer : Fr) (fresh : Bool) :
    (s.record request answer fresh).BadBlob ↔
      s.BadBlob ∨ (⟨request, answer, fresh⟩ : Reply).BadBlob := by
  simp [State.BadBlob, State.record]

/-- A new transcript entry contributes its own batch-root event. -/
theorem State.badBatch_record (n : Nat) (s : State) (request : Request) (answer : Fr)
    (fresh : Bool) :
    (s.record request answer fresh).BadBatch n ↔
      s.BadBatch n ∨ (⟨request, answer, fresh⟩ : Reply).BadBatch n := by
  simp [State.BadBatch, State.record]

/-- The maximum mass of a root of one commitment difference. -/
noncomputable def blobRootWeight : ℝ≥0∞ :=
  (FIELD_ELEMENTS_PER_BLOB - 1 : Nat) / Fr.modulus

/-- The maximum mass of a root of a batch polynomial with at most `n` coefficients. -/
noncomputable def batchRootWeight (n : Nat) : ℝ≥0∞ :=
  (n - 1 : Nat) / Fr.modulus

/-- The root-event charge of the public transcript, including repeated calls. -/
noncomputable def State.rootPotential (n : Nat) (s : State) : ℝ≥0∞ :=
  s.blobQueries * blobRootWeight + s.batchQueries * batchRootWeight n


/-- The charge paid by a public query of each protocol domain. -/
noncomputable def Request.rootWeight (n : Nat) (request : Request) : ℝ≥0∞ :=
  if request.isBlob then blobRootWeight else batchRootWeight n

/-- Logging a public call pays the charge of its domain. -/
theorem State.rootPotential_record (n : Nat) (s : State) (request : Request) (answer : Fr)
    (fresh : Bool) :
    (s.record request answer fresh).rootPotential n =
      s.rootPotential n + request.rootWeight n := by
  cases request <;>
    simp [State.rootPotential, State.blobQueries_record, State.batchQueries_record,
      Request.rootWeight, Request.isBlob, add_mul, add_assoc, add_comm, add_left_comm]

/-- A fresh reply hits a nonzero error polynomial only within its domain's root charge. -/
theorem prEvent_fresh_root_le (n : Nat) (request : Request) :
    Pr{let answer ← $ᵗ Fr}[
      (⟨request, answer, true⟩ : Reply).BadBlob ∨
        (⟨request, answer, true⟩ : Reply).BadBatch n] ≤ request.rootWeight n := by
  classical
  cases request with
  | blob b c =>
    simpa only [Reply.BadBlob, Reply.BadBatch, Request.rootWeight, Request.isBlob,
      ite_true, blobRootWeight, true_and, and_false, or_false, Function.Embedding.refl_apply]
      using prEvent_uniform_embedding_root_le (Function.Embedding.refl Fr) (blobError b c)
        (show (blobError b c).natDegree ≤ FIELD_ELEMENTS_PER_BLOB - 1 by
          have := natDegree_blobError_lt b c
          omega)
  | batch openings =>
    by_cases hn : openings.length ≤ n
    · have hd : (batchError openings).natDegree ≤ n - 1 :=
        (natDegree_batchError_le openings).trans (Nat.sub_le_sub_right hn 1)
      simpa only [Reply.BadBlob, Reply.BadBatch, Request.rootWeight, Request.isBlob,
        Bool.false_eq_true, ite_false, Function.Embedding.coeFn_mk, batchRootWeight,
        batchErrorAt, hn, true_and, and_false, false_or]
        using prEvent_uniform_embedding_root_le
          ⟨Polynomial.C, Polynomial.C_injective⟩ (batchError openings) hd
    · simp only [Reply.BadBlob, Reply.BadBatch, hn, false_and, and_false, false_or,
        prEvent_false, zero_le]

/-- Each public step has precisely its transcript charge, whether its answer was cached or fresh. -/
theorem rootPotential_impl (n : Nat) (query : Spec.Domain) (s : State) :
    ∀ z ∈ support ((impl query).run s),
      z.2.rootPotential n = s.rootPotential n +
        match query with
        | .inl _ => 0
        | .inr request => request.rootWeight n := by
  intro z hz
  cases query with
  | inl coins =>
    simp only [impl, StateT.run_mk, support_map] at hz
    obtain ⟨answer, _, rfl⟩ := hz
    simp
  | inr request =>
    cases hc : s.cache request.key with
    | none =>
      simp only [impl, step, StateT.run_mk, hc, support_map] at hz
      obtain ⟨answer, _, rfl⟩ := hz
      exact State.rootPotential_record n s request answer true
    | some answer =>
      simp only [impl, step, StateT.run_mk, hc, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact State.rootPotential_record n s request answer false

/-- The projected cache charges roots chosen before the current fresh answer. -/
theorem rootPotential_step (n : Nat) :
    IsPotentialStep impl (fun s => s.BadBlob ∨ s.BadBatch n) (State.rootPotential n) := by
  classical
  constructor
  · intro query s z hz
    rw [rootPotential_impl n query s z hz]
    exact le_self_add
  · intro query s hs
    have hb : ¬s.BadBlob := fun h => hs (Or.inl h)
    have hr : ¬s.BadBatch n := fun h => hs (Or.inr h)
    cases query with
    | inl coins =>
      right
      refine ⟨unifSpec.query coins, fun _ => s, 0, rfl, ?_, ?_⟩
      · simp [hs]
      · intro answer
        simp
    | inr request =>
      cases hc : s.cache request.key with
      | some answer =>
        left
        refine ⟨answer, s.record request answer false, ?_, ?_⟩
        · simp [impl, step, hc]
        · simp [State.badBlob_record, State.badBatch_record, hb, hr,
            Reply.BadBlob, Reply.BadBatch]
      | none =>
        right
        refine ⟨$ᵗ Fr,
          fun answer => {s.record request answer true with
            cache := s.cache.cacheQuery request.key answer}, request.rootWeight n, ?_, ?_, ?_⟩
        · simp [impl, step, hc]
        · change Pr{let answer ← $ᵗ Fr}[
            (s.record request answer true).BadBlob ∨
              (s.record request answer true).BadBatch n] ≤ request.rootWeight n
          simpa only [State.badBlob_record, State.badBatch_record, hb, hr, false_or]
            using prEvent_fresh_root_le n request
        · intro answer
          rw [show ({s.record request answer true with
              cache := s.cache.cacheQuery request.key answer} : State).rootPotential n =
                (s.record request answer true).rootPotential n from rfl,
            State.rootPotential_record]
          exact le_of_eq (add_comm _ _)

/-- Each call increments exactly its public-domain counter, and private coins increment neither. -/
theorem queryCounts_impl (query : Spec.Domain) (s : State) :
    ∀ z ∈ support ((impl query).run s),
      z.2.blobQueries = s.blobQueries + (if isBlobQuery query then 1 else 0) ∧
        z.2.batchQueries = s.batchQueries + (if isBatchQuery query then 1 else 0) := by
  intro z hz
  cases query with
  | inl coins =>
    simp only [impl, StateT.run_mk, support_map] at hz
    obtain ⟨answer, _, rfl⟩ := hz
    simp [isBlobQuery, isBatchQuery]
  | inr request =>
    cases hc : s.cache request.key with
    | none =>
      simp only [impl, step, StateT.run_mk, hc, support_map] at hz
      obtain ⟨answer, _, rfl⟩ := hz
      exact ⟨State.blobQueries_record s request answer true,
        State.batchQueries_record s request answer true⟩
    | some answer =>
      simp only [impl, step, StateT.run_mk, hc, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨State.blobQueries_record s request answer false,
        State.batchQueries_record s request answer false⟩

/-- A public query budget bounds the corresponding transcript counters on every path. -/
theorem queryCounts_run_le {α : Type} (client : OracleComp Spec α) {qBlob qBatch : Nat}
    (hqBlob : IsQueryBoundP client (fun q => isBlobQuery q = true) qBlob)
    (hqBatch : IsQueryBoundP client (fun q => isBatchQuery q = true) qBatch)
    {z : α × State} (hz : z ∈ support (run client)) :
    z.2.blobQueries ≤ qBlob ∧ z.2.batchQueries ≤ qBatch := by
  classical
  constructor
  · have h := hqBlob.cost_le_of_mem_support_run_simulateQ State.blobQueries
      (fun query hquery s z hz => by rw [(queryCounts_impl query s z hz).1]; simp [hquery])
      (fun query hquery s z hz => by rw [(queryCounts_impl query s z hz).1]; simp [hquery])
      State.empty z hz
    simpa [State.blobQueries, State.empty] using h
  · have h := hqBatch.cost_le_of_mem_support_run_simulateQ State.batchQueries
      (fun query hquery s z hz => by rw [(queryCounts_impl query s z hz).2]; simp [hquery])
      (fun query hquery s z hz => by rw [(queryCounts_impl query s z hz).2]; simp [hquery])
      State.empty z hz
    simpa [State.batchQueries, State.empty] using h

/-- Public query budgets bound the two adaptive fresh-root events in one shared oracle. -/
theorem prEvent_run_roots_le {α : Type} (n : Nat) (client : OracleComp Spec α) {qBlob qBatch : Nat}
    (hqBlob : IsQueryBoundP client (fun q => isBlobQuery q = true) qBlob)
    (hqBatch : IsQueryBoundP client (fun q => isBatchQuery q = true) qBatch) :
    Pr{let z ← run client}[z.2.BadBlob ∨ z.2.BadBatch n] ≤
      qBlob * blobRootWeight + qBatch * batchRootWeight n := by
  classical
  let budget : ℝ≥0∞ := qBlob * blobRootWeight + qBatch * batchRootWeight n
  have hw : (Fr.modulus : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fr.modulus_pos.ne'
  have hfinite : budget ≠ ⊤ := by
    dsimp [budget, blobRootWeight, batchRootWeight]
    finiteness
  have hp := rootPotential_step n
  have h := prEvent_and_le_of_potential impl (fun s => s.BadBlob ∨ s.BadBatch n)
    (State.rootPotential n) hp.mono hp.step client budget hfinite State.empty
      (by simp [State.BadBlob, State.BadBatch, State.empty])
  have hb : ∀ z ∈ support (run client), z.2.rootPotential n ≤ budget := by
    intro z hz
    obtain ⟨hcBlob, hcBatch⟩ := queryCounts_run_le client hqBlob hqBatch hz
    dsimp [State.rootPotential, budget]
    gcongr
  have heq := prEvent_congr_of_support (run client)
    (fun z => z.2.BadBlob ∨ z.2.BadBatch n)
    (fun z => (z.2.BadBlob ∨ z.2.BadBatch n) ∧ z.2.rootPotential n ≤ budget)
    (fun z hz => (and_iff_left (hb z hz)).symm)
  rw [heq]
  simpa [run, State.rootPotential, State.blobQueries, State.batchQueries, State.empty] using h

/-- Individual verification makes at most one blob query per submitted entry. -/
theorem challengeOpenings_blobQueries (out : List BlobOpening) :
    IsQueryBoundP (challengeOpenings out) (fun q => isBlobQuery q = true) out.length := by
  induction out with
  | nil =>
    change IsQueryBoundP (pure (some ([] : List Opening)) : OracleComp Spec _) _ _
    trivial
  | cons o out ih =>
    rw [challengeOpenings_cons]
    cases h : blobToPolynomial o.blob with
    | error e =>
      rw [challengeDecoded_error]
      trivial
    | ok values =>
      rw [challengeDecoded_ok, isQueryBoundP_query_bind_iff]
      constructor
      · exact Or.inr (Nat.succ_pos _)
      · intro z
        simp only [isBlobQuery, Request.isBlob, ite_true, List.length_cons,
          Nat.add_sub_cancel]
        exact isQueryBoundP_bind (m := 0) ih (fun _ _ => by trivial)

/-- Individual verification makes no batch challenge query. -/
theorem challengeOpenings_batchQueries (out : List BlobOpening) :
    IsQueryBoundP (challengeOpenings out) (fun q => isBatchQuery q = true) 0 := by
  induction out with
  | nil =>
    change IsQueryBoundP (pure (some ([] : List Opening)) : OracleComp Spec _) _ _
    trivial
  | cons o out ih =>
    rw [challengeOpenings_cons]
    cases h : blobToPolynomial o.blob with
    | error e =>
      rw [challengeDecoded_error]
      trivial
    | ok values =>
      rw [challengeDecoded_ok, isQueryBoundP_query_bind_iff]
      constructor
      · exact Or.inl (by simp [isBatchQuery, Request.isBlob])
      · intro z
        simp only [isBatchQuery, Request.isBlob, Bool.not_true, Bool.false_eq_true, ite_false]
        exact isQueryBoundP_bind (m := 0) ih (fun _ _ => by trivial)

/-- The verifier makes at most one blob challenge query for each output entry. -/
theorem verifierQueries_blobQueries (out : List BlobOpening) :
    IsQueryBoundP (verifierQueries out) (fun q => isBlobQuery q = true) out.length := by
  unfold verifierQueries
  refine isQueryBoundP_bind (m := 0) (challengeOpenings_blobQueries out) ?_
  intro result _
  cases result with
  | none => trivial
  | some openings =>
    rw [isQueryBoundP_query_bind_iff]
    constructor
    · exact Or.inl (by simp [isBlobQuery, Request.isBlob])
    · intro r
      trivial

/-- The verifier makes at most one batch challenge query. -/
theorem verifierQueries_batchQueries (out : List BlobOpening) :
    IsQueryBoundP (verifierQueries out) (fun q => isBatchQuery q = true) 1 := by
  unfold verifierQueries
  refine isQueryBoundP_bind (m := 1) (challengeOpenings_batchQueries out) ?_
  intro result _
  cases result with
  | none => trivial
  | some openings =>
    rw [isQueryBoundP_query_bind_iff]
    constructor
    · exact Or.inr (by decide)
    · intro r
      trivial

/-- The capped verifier adds at most `n` blob calls to the adversary's budget. -/
theorem boundedExperiment_blobQueries (n : Nat)
    {adversary : OracleComp Spec (List BlobOpening)} {qBlob : Nat}
    (hqBlob : IsQueryBoundP adversary (fun q => isBlobQuery q = true) qBlob) :
    IsQueryBoundP (boundedExperiment n adversary) (fun q => isBlobQuery q = true)
      (qBlob + n) := by
  unfold boundedExperiment
  refine isQueryBoundP_bind hqBlob ?_
  intro out _
  by_cases h : out.length ≤ n
  · simp only [h, ite_true]
    exact isQueryBoundP_bind (m := 0) ((verifierQueries_blobQueries out).mono h)
      (fun _ _ => by trivial)
  · simp only [h, ite_false, pure_bind, isQueryBoundP_pure]

/-- The capped verifier adds at most one batch call to the adversary's budget. -/
theorem boundedExperiment_batchQueries (n : Nat)
    {adversary : OracleComp Spec (List BlobOpening)} {qBatch : Nat}
    (hqBatch : IsQueryBoundP adversary (fun q => isBatchQuery q = true) qBatch) :
    IsQueryBoundP (boundedExperiment n adversary) (fun q => isBatchQuery q = true)
      (qBatch + 1) := by
  unfold boundedExperiment
  refine isQueryBoundP_bind hqBatch ?_
  intro out _
  by_cases h : out.length ≤ n
  · simp only [h, ite_true]
    exact isQueryBoundP_bind (m := 0) (verifierQueries_batchQueries out)
      (fun _ _ => by trivial)
  · simp only [h, ite_false, pure_bind, isQueryBoundP_pure]

end BlobBinding

end EthLib.Cryptography.Kzg
