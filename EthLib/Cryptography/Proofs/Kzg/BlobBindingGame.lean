module

public import EthLib.Cryptography.Proofs.Kzg.BlobBinding
public import EthLib.Cryptography.Proofs.Kzg.BlobVerifier
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer

set_option autoImplicit false

/-!
# Proofs: the algebraic blob-binding experiment

Group elements carry polynomial representations before a hash query is answered.

This is the algebraic algorithm interface of Fuchsbauer, Kiltz and Loss, §2.1, Definition 1.

<https://eprint.iacr.org/2017/620>

The hash is one typed, domain-separated random oracle with uniform values in `Fr`.

Polynomial annotations are not part of its key, so repeated protocol inputs share an answer.

Batch queries contain one list of openings, so their four arrays have the same length.

This model idealizes the input encodings and SHA-256 reduced modulo `r`.

The latter distribution is not uniform, as SOUNDNESS.md A4 explains.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.BlobBinding

open EthLib.Cryptography.Bls (Fr G1)
open EthLib.Cryptography.Kzg.Constants
open OracleComp OracleSpec Polynomial
open scoped EthLib.Cryptography.Bls.Fr

/-- A group encoding and its algebraic representation over the 4096 setup powers. -/
structure AlgebraicPoint where
  bytes : Bytes48
  polynomial : Fr[X]
  degree_lt : polynomial.natDegree < FIELD_ELEMENTS_PER_BLOB

/-- One opening, including representations of its commitment and proof. -/
structure Opening where
  commitment : AlgebraicPoint
  z : Fr
  y : Fr
  proof : AlgebraicPoint

/-- The protocol data of one opening, without polynomial annotations. -/
structure OpeningData where
  commitment : Bytes48
  z : Fr
  y : Fr
  proof : Bytes48
deriving DecidableEq

/-- Forget the algebraic representation of an opening. -/
def Opening.data (o : Opening) : OpeningData :=
  ⟨o.commitment.bytes, o.z, o.y, o.proof.bytes⟩

/-- The core opening-batch input, with all arrays built from one list. -/
def OpeningData.toBatch (openings : List OpeningData) : OpeningBatch where
  commitments := (openings.map fun o => o.commitment).toArray
  zs := (openings.map fun o => o.z).toArray
  ys := (openings.map fun o => o.y).toArray
  proofs := (openings.map fun o => o.proof).toArray

/-- The core input of an algebraically annotated batch. -/
def Opening.toBatch (openings : List Opening) : OpeningBatch :=
  OpeningData.toBatch (openings.map Opening.data)

/-- The two protocol input domains, without algebraic annotations. -/
inductive HashKey where
  | blob (blob : Blob) (commitment : Bytes48)
  | batch (openings : List OpeningData)
deriving DecidableEq

/-- An annotated hash request, chosen before its answer is sampled. -/
inductive Request where
  | blob (blob : Blob) (commitment : AlgebraicPoint)
  | batch (openings : List Opening)

/-- Remove the extraction metadata from the input of the random oracle. -/
def Request.key : Request → HashKey
  | .blob b commitment => .blob b commitment.bytes
  | .batch openings => .batch (openings.map Opening.data)

/-- The algebraic group outputs carried by a request, in their protocol order. -/
def Request.points : Request → List AlgebraicPoint
  | .blob _ commitment => [commitment]
  | .batch openings => openings.flatMap fun o => [o.commitment, o.proof]

/-- The symbolic error of one opening, as a polynomial in the setup secret. -/
noncomputable def Opening.error (o : Opening) : Fr[X] :=
  blobOpeningError o.commitment.polynomial o.proof.polynomial o.y o.z

/-- The batch polynomial in an outer variable, with opening errors as coefficients. -/
noncomputable def batchError : List Opening → (Fr[X])[X]
  | [] => 0
  | o :: openings => Polynomial.C o.error + X * batchError openings

/-- The symbolic error after substituting the batch challenge. -/
noncomputable def batchErrorAt (openings : List Opening) (r : Fr) : Fr[X] :=
  (batchError openings).eval (Polynomial.C r)

/-- The difference of two scalar polynomials, using their ring operations. -/
noncomputable def polynomialDifference (a b : Fr[X]) : Fr[X] := a - b

private theorem natDegree_polynomialDifference_lt (a b : Fr[X])
    (ha : a.natDegree < FIELD_ELEMENTS_PER_BLOB) (hb : b.natDegree < FIELD_ELEMENTS_PER_BLOB) :
    (polynomialDifference a b).natDegree < FIELD_ELEMENTS_PER_BLOB :=
  lt_of_le_of_lt (natDegree_sub_le a b) (max_lt ha hb)

/-- A decoded blob polynomial with its degree bound, using the commitment on decoding failure. -/
noncomputable def decodedBlobPolynomial (decoded : Except KzgError Polynomial)
    (commitment : AlgebraicPoint) : {p : Fr[X] // p.natDegree < FIELD_ELEMENTS_PER_BLOB} :=
  match decoded with
  | .error _ => ⟨commitment.polynomial, commitment.degree_lt⟩
  | .ok values => ⟨interpolant values, natDegree_interpolant_lt values⟩

/-- The difference of a commitment polynomial and its decoded blob, or zero on decoding failure. -/
noncomputable def blobError (blob : Blob) (commitment : AlgebraicPoint) : Fr[X] :=
  polynomialDifference commitment.polynomial
    (decodedBlobPolynomial (blobToPolynomial blob) commitment).val

/-- A commitment difference has degree below 4096. -/
theorem natDegree_blobError_lt (blob : Blob) (commitment : AlgebraicPoint) :
    (blobError blob commitment).natDegree < FIELD_ELEMENTS_PER_BLOB :=
  natDegree_polynomialDifference_lt _ _ commitment.degree_lt
    (decodedBlobPolynomial (blobToPolynomial blob) commitment).property

/-- On a decoded blob, the error is its commitment polynomial minus its interpolant. -/
theorem blobError_of_ok {blob : Blob} {values : Polynomial} (commitment : AlgebraicPoint)
    (h : blobToPolynomial blob = .ok values) :
    blobError blob commitment =
      polynomialDifference commitment.polynomial (interpolant values) := by
  rw [blobError, h]
  rfl

/-- A malformed blob does not trigger a nonzero-root event. -/
theorem blobError_of_error {blob : Blob} {error : KzgError} (commitment : AlgebraicPoint)
    (h : blobToPolynomial blob = .error error) : blobError blob commitment = 0 := by
  rw [blobError, h]
  exact sub_self commitment.polynomial

/-- One symbolic opening error has degree at most 4096 in the setup secret. -/
theorem natDegree_openingError_le (o : Opening) :
    o.error.natDegree ≤ FIELD_ELEMENTS_PER_BLOB :=
  natDegree_blobOpeningError_le o.commitment.degree_lt o.proof.degree_lt o.y o.z

/-- The symbolic batch polynomial has degree at most the number of openings minus one. -/
theorem natDegree_batchError_le (openings : List Opening) :
    (batchError openings).natDegree ≤ openings.length - 1 := by
  induction openings with
  | nil => simp [batchError]
  | cons o openings ih =>
    cases openings with
    | nil => simp [batchError]
    | cons next rest =>
      simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · simp
      · exact (natDegree_mul_le).trans (by
          have hx := natDegree_X_le (R := Fr[X])
          omega)

/-- Substituting a batch challenge leaves degree at most 4096 in the setup secret. -/
theorem natDegree_batchErrorAt_le (openings : List Opening) (r : Fr) :
    (batchErrorAt openings r).natDegree ≤ FIELD_ELEMENTS_PER_BLOB := by
  induction openings with
  | nil => simp [batchErrorAt, batchError]
  | cons o openings ih =>
    simp only [batchErrorAt, batchError, eval_add, eval_C, eval_mul, eval_X]
    refine le_trans (natDegree_add_le _ _) (max_le (natDegree_openingError_le o) ?_)
    exact (natDegree_mul_le).trans (by simpa [batchErrorAt, natDegree_C] using ih)

/-- The empty symbolic batch has zero error at every challenge. -/
@[simp] theorem batchErrorAt_nil (r : Fr) : batchErrorAt [] r = 0 := by
  simp [batchErrorAt, batchError]

/-- Horner evaluation of the symbolic batch polynomial. -/
@[simp] theorem batchErrorAt_cons (o : Opening) (openings : List Opening) (r : Fr) :
    batchErrorAt (o :: openings) r = o.error + Polynomial.C r * batchErrorAt openings r := by
  simp [batchErrorAt, batchError]

/-- The symbolic batch polynomial is zero exactly when each opening error is zero. -/
theorem batchError_eq_zero_iff (openings : List Opening) :
    batchError openings = 0 ↔ ∀ o ∈ openings, o.error = 0 := by
  induction openings with
  | nil => simp [batchError]
  | cons o openings ih =>
    constructor
    · intro h
      have ho : o.error = 0 := by
        simpa [batchError] using congrArg (fun p : (Fr[X])[X] => p.coeff 0) h
      have ht : batchError openings = 0 := by
        rw [batchError, ho, C_0, zero_add] at h
        exact (mul_eq_zero.mp h).resolve_left X_ne_zero
      simpa [ho] using ih.mp ht
    · intro h
      rw [batchError, h o (by simp), C_0, zero_add,
        ih.mpr (fun p hp => h p (by simp [hp])), mul_zero]

/-- One public query and its answer, recording whether the actual input was fresh. -/
structure Reply where
  request : Request
  answer : Fr
  fresh : Bool

/-- The shared protocol cache and complete chronological public query log. -/
structure State where
  cache : (HashKey →ₒ Fr).QueryCache
  history : List Reply

/-- The empty random oracle and empty public transcript. -/
def State.empty : State := ⟨∅, []⟩

/-- Add one public query to the transcript. -/
def State.record (s : State) (request : Request) (answer : Fr) (fresh : Bool) : State :=
  ⟨s.cache, s.history ++ [⟨request, answer, fresh⟩]⟩

/-- Answer a request from the actual-input cache, sampling only on a miss. -/
noncomputable def step (request : Request) : StateT State ProbComp Fr :=
  StateT.mk fun s =>
    match s.cache request.key with
    | some answer => pure (answer, s.record request answer false)
    | none =>
      (fun answer => (answer,
        { s.record request answer true with cache := s.cache.cacheQuery request.key answer }))
        <$> ($ᵗ Fr)

/-- Private coins and public protocol queries, with only public queries charged. -/
abbrev Spec := unifSpec + (Request →ₒ Fr)

/-- Private coins preserve the state, while public queries use the shared cache. -/
noncomputable def impl : QueryImpl Spec (StateT State ProbComp) := fun
  | .inl n => StateT.mk fun s => (fun answer => (answer, s)) <$> (unifSpec.query n : ProbComp _)
  | .inr request => step request

/-- Run an adaptive client with private coins and the shared random oracle. -/
noncomputable def run {α : Type} (client : OracleComp Spec α) : ProbComp (α × State) :=
  (simulateQ impl client).run State.empty

/-- Cached answers agree with the log, and each cached key has a fresh response. -/
def State.Coherent (s : State) : Prop :=
  (∀ reply ∈ s.history, s.cache reply.request.key = some reply.answer) ∧
    ∀ key answer, s.cache key = some answer →
      ∃ reply ∈ s.history, reply.fresh = true ∧ reply.request.key = key ∧ reply.answer = answer

/-- The empty oracle has no cached or logged answers. -/
theorem State.coherent_empty : State.empty.Coherent := by
  constructor
  · simp [State.empty]
  · intro key answer h
    simp [State.empty] at h

private theorem State.coherent_hit {s : State} (hs : s.Coherent)
    {request : Request} {answer : Fr} (h : s.cache request.key = some answer) :
    (s.record request answer false).Coherent := by
  constructor
  · intro reply hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hs.1 reply hr
    · simp only [List.mem_singleton] at hr
      subst reply
      exact h
  · intro key value hk
    obtain ⟨reply, hr, hf, heq, hv⟩ := hs.2 key value hk
    exact ⟨reply, List.mem_append_left _ hr, hf, heq, hv⟩

private theorem State.coherent_miss {s : State} (hs : s.Coherent)
    {request : Request} (h : s.cache request.key = none) (answer : Fr) :
    ({ s.record request answer true with cache := s.cache.cacheQuery request.key answer } :
      State).Coherent := by
  constructor
  · intro reply hr
    rcases List.mem_append.mp hr with hr | hr
    · have hrkey : reply.request.key ≠ request.key := by
        intro heq
        have hv := hs.1 reply hr
        rw [heq, h] at hv
        contradiction
      exact (QueryCache.cacheQuery_of_ne _ _ hrkey).trans (hs.1 reply hr)
    · simp only [List.mem_singleton] at hr
      subst reply
      exact QueryCache.cacheQuery_self _ _ _
  · intro key value hk
    by_cases heq : key = request.key
    · subst key
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hk
      subst value
      exact ⟨⟨request, answer, true⟩, List.mem_append_right _ (by simp), rfl, rfl, rfl⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hk
      obtain ⟨reply, hr, hf, heq, hv⟩ := hs.2 key value hk
      exact ⟨reply, List.mem_append_left _ hr, hf, heq, hv⟩

/-- Every public response is recorded, and prior log entries persist. -/
theorem step_recorded {request : Request} {s : State} {result : Fr × State}
    (h : result ∈ support ((step request).run s)) :
    (∃ fresh, ⟨request, result.1, fresh⟩ ∈ result.2.history) ∧
      ∀ reply ∈ s.history, reply ∈ result.2.history := by
  cases hc : s.cache request.key with
  | none =>
    simp only [step, StateT.run_mk, hc, support_map] at h
    obtain ⟨answer, _, rfl⟩ := h
    exact ⟨⟨true, List.mem_append_right _ (by simp)⟩,
      fun _ hr => List.mem_append_left _ hr⟩
  | some answer =>
    simp only [step, StateT.run_mk, hc, support_pure, Set.mem_singleton_iff] at h
    subst result
    exact ⟨⟨false, List.mem_append_right _ (by simp)⟩,
      fun _ hr => List.mem_append_left _ hr⟩

/-- The shared handler preserves agreement between cached answers and the transcript. -/
theorem impl_preserves_coherent : QueryImpl.PreservesInv impl State.Coherent := by
  intro query s hs result h
  cases query with
  | inl n =>
    simp only [impl, StateT.run_mk, support_map] at h
    obtain ⟨answer, _, rfl⟩ := h
    exact hs
  | inr request =>
    cases hc : s.cache request.key with
    | none =>
      simp only [impl, step, StateT.run_mk, hc, support_map] at h
      obtain ⟨answer, _, rfl⟩ := h
      exact State.coherent_miss hs hc answer
    | some answer =>
      simp only [impl, step, StateT.run_mk, hc, support_pure, Set.mem_singleton_iff] at h
      subst result
      exact State.coherent_hit hs hc

/-- Any adaptive run preserves the oracle's cache and transcript agreement. -/
theorem run_coherent {α : Type} {client : OracleComp Spec α} {result : α × State}
    (h : result ∈ support (run client)) : result.2.Coherent :=
  simulateQ_run_preservesInv impl State.Coherent impl_preserves_coherent client
    State.empty State.coherent_empty result h

/-- Every logged response agrees with a fresh response of the same actual protocol input. -/
theorem State.fresh_reply {s : State} (hs : s.Coherent) {reply : Reply}
    (hr : reply ∈ s.history) :
    ∃ first ∈ s.history, first.fresh = true ∧
      first.request.key = reply.request.key ∧ first.answer = reply.answer :=
  hs.2 reply.request.key reply.answer (hs.1 reply hr)

/-- An adaptive client preserves all entries already in the public query log. -/
theorem history_preserved {α : Type} (client : OracleComp Spec α) {s : State}
    {result : α × State} (h : result ∈ support ((simulateQ impl client).run s)) :
    ∀ reply ∈ s.history, reply ∈ result.2.history := by
  let invariant : State → Prop := fun final => ∀ reply ∈ s.history, reply ∈ final.history
  apply simulateQ_run_preservesInv impl invariant ?_ client s (fun _ hr => hr) result h
  intro query state hi next hn
  cases query with
  | inl n =>
    simp only [impl, StateT.run_mk, support_map] at hn
    obtain ⟨answer, _, rfl⟩ := hn
    exact hi
  | inr request =>
    exact fun reply hr => (step_recorded hn).2 reply (hi reply hr)

/-- A fresh blob challenge that is a root of a nonzero commitment difference. -/
def Reply.BadBlob (reply : Reply) : Prop :=
  reply.fresh = true ∧ match reply.request with
    | .blob b commitment =>
      blobError b commitment ≠ 0 ∧ (blobError b commitment).eval reply.answer = 0
    | .batch _ => False

/-- A fresh challenge of at most `n` openings that annihilates their nonzero batch polynomial. -/
def Reply.BadBatch (n : Nat) (reply : Reply) : Prop :=
  reply.fresh = true ∧ match reply.request with
    | .blob _ _ => False
    | .batch openings => openings.length ≤ n ∧ batchError openings ≠ 0 ∧
      batchErrorAt openings reply.answer = 0

/-- Some fresh blob response in the transcript hit its polynomial's roots. -/
def State.BadBlob (s : State) : Prop := ∃ reply ∈ s.history, reply.BadBlob

/-- Some fresh response of a batch of at most `n` openings hit its symbolic roots. -/
def State.BadBatch (n : Nat) (s : State) : Prop := ∃ reply ∈ s.history, reply.BadBatch n

/-- A blob, commitment and proof submitted by the adversary. -/
structure BlobOpening where
  blob : Blob
  commitment : AlgebraicPoint
  proof : AlgebraicPoint

/-- The group encodings and polynomial annotations submitted in the output. -/
def BlobOpening.points (out : List BlobOpening) : List AlgebraicPoint :=
  out.flatMap fun o => [o.commitment, o.proof]

/-- The opening formed from a blob's decoded values and its oracle challenge. -/
noncomputable def BlobOpening.toOpening (o : BlobOpening)
    (values : Polynomial) (z : Fr) : Opening :=
  ⟨o.commitment, z, (interpolant values).eval z, o.proof⟩

/-- Process one decoded blob before continuing with the remaining inputs. -/
noncomputable def challengeDecoded (o : BlobOpening)
    (next : OracleComp Spec (Option (List Opening))) (decoded : Except KzgError Polynomial) :
    OracleComp Spec (Option (List Opening)) :=
  match decoded with
  | .error _ => pure none
  | .ok values => do
    let z ← liftM (Spec.query (.inr (.blob o.blob o.commitment)))
    let rest ← next
    return rest.map fun rest => o.toOpening values z :: rest

/-- Query the challenge of each decoded blob, rejecting malformed blobs. -/
noncomputable def challengeOpenings :
    List BlobOpening → OracleComp Spec (Option (List Opening))
  | [] => pure (some [])
  | o :: out => challengeDecoded o (challengeOpenings out) (blobToPolynomial o.blob)

/-- Challenge generation for no blobs returns no openings. -/
@[simp] theorem challengeOpenings_nil : challengeOpenings [] = pure (some []) := rfl

/-- Challenge generation first processes the head's decoding result. -/
theorem challengeOpenings_cons (o : BlobOpening) (out : List BlobOpening) :
    challengeOpenings (o :: out) =
      challengeDecoded o (challengeOpenings out) (blobToPolynomial o.blob) := rfl

/-- A malformed head blob rejects the challenge-generation request. -/
@[simp] theorem challengeDecoded_error (o : BlobOpening)
    (next : OracleComp Spec (Option (List Opening))) (error : KzgError) :
    challengeDecoded o next (.error error) = pure none := rfl

/-- A decoded head blob queries its challenge, then retains the remaining openings. -/
theorem challengeDecoded_ok (o : BlobOpening)
    (next : OracleComp Spec (Option (List Opening))) (values : Polynomial) :
    challengeDecoded o next (.ok values) = do
      let z ← liftM (Spec.query (.inr (.blob o.blob o.commitment)))
      let rest ← next
      return rest.map fun rest => o.toOpening values z :: rest := rfl

/-- The verifier's individual challenges, followed by its one batch challenge. -/
noncomputable def verifierQueries (out : List BlobOpening) :
    OracleComp Spec (Option (List Opening × Fr)) := do
  let some openings ← challengeOpenings out | return none
  let r ← liftM (Spec.query (.inr (.batch openings)))
  return some (openings, r)

/-- Each generated opening has its submitted blob's challenge in the public transcript. -/
def QueriedBlobs (s : State) : List BlobOpening → List Opening → Prop
  | [], [] => True
  | out :: outputs, o :: openings =>
    (∃ fresh, ⟨.blob out.blob out.commitment, o.z, fresh⟩ ∈ s.history) ∧
      QueriedBlobs s outputs openings
  | _, _ => False

/-- Adding log entries preserves the provenance of the individual challenges. -/
theorem QueriedBlobs.mono {s t : State} {out : List BlobOpening} {openings : List Opening}
    (h : QueriedBlobs s out openings) (hst : ∀ reply ∈ s.history, reply ∈ t.history) :
    QueriedBlobs t out openings := by
  induction out generalizing openings with
  | nil => cases openings <;> simp_all [QueriedBlobs]
  | cons o out ih =>
    cases openings with
    | nil => cases h
    | cons opening openings =>
      obtain ⟨fresh, hf⟩ := h.1
      exact ⟨⟨fresh, hst _ hf⟩, ih h.2⟩

/-- Every successful generated opening uses the challenge recorded for its blob and commitment. -/
theorem queriedBlobs_of_mem_support_challengeOpenings (out : List BlobOpening)
    {s final : State} {openings : List Opening}
    (h : (some openings, final) ∈ support ((simulateQ impl (challengeOpenings out)).run s)) :
    QueriedBlobs final out openings := by
  induction out generalizing s final openings with
  | nil =>
    change (some openings, final) ∈ support (pure (some ([] : List Opening), s) :
      ProbComp (Option (List Opening) × State)) at h
    have heq := eq_of_mem_support_pure (some ([] : List Opening), s) h
    cases heq
    trivial
  | cons o out ih =>
    rw [challengeOpenings_cons] at h
    cases hb : blobToPolynomial o.blob with
    | error e =>
      rw [hb, challengeDecoded_error] at h
      change (some openings, final) ∈ support (pure (none, s) :
        ProbComp (Option (List Opening) × State)) at h
      have heq := eq_of_mem_support_pure (none, s) h
      cases congrArg Prod.fst heq
    | ok values =>
      rw [hb, challengeDecoded_ok] at h
      simp only [simulateQ_bind,
        StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at h
      obtain ⟨⟨z, after⟩, hz, ⟨⟨rest, final'⟩, hr, heq⟩⟩ := h
      rw [simulateQ_spec_query] at hz
      change (z, after) ∈ support ((step (.blob o.blob o.commitment)).run s) at hz
      cases rest with
      | none => cases heq
      | some rest =>
        cases heq
        obtain ⟨fresh, hf⟩ := (step_recorded hz).1
        exact ⟨⟨fresh, history_preserved (challengeOpenings out) hr _ hf⟩, ih hr⟩

/-- A successful verifier run records every individual query and its final batch query. -/
theorem queried_of_mem_support_verifierQueries (out : List BlobOpening)
    {s final : State} {openings : List Opening} {r : Fr}
    (h : (some (openings, r), final) ∈
      support ((simulateQ impl (verifierQueries out)).run s)) :
    QueriedBlobs final out openings ∧
      ∃ fresh, ⟨.batch openings, r, fresh⟩ ∈ final.history := by
  simp only [verifierQueries, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨checked, after⟩, hc, h⟩ := h
  cases checked with
  | none =>
    change (some (openings, r), final) ∈ support (pure (none, after) :
      ProbComp (Option (List Opening × Fr) × State)) at h
    have heq := eq_of_mem_support_pure (none, after) h
    cases congrArg Prod.fst heq
  | some os =>
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨⟨answer, final'⟩, hr, heq⟩ := h
    rw [simulateQ_spec_query] at hr
    change (answer, final') ∈ support ((step (.batch os)).run after) at hr
    cases heq
    exact ⟨(queriedBlobs_of_mem_support_challengeOpenings out hc).mono
      (step_recorded hr).2, (step_recorded hr).1⟩

/-- Every successful point decoding has the annotated polynomial at the hidden setup secret. -/
def AlgebraicPoint.Valid (τ : Fr) (point : AlgebraicPoint) : Prop :=
  ∀ P, validateKzgG1Point point.bytes = .ok P →
    G1.Represents P (point.polynomial.eval τ)

/-- Every point annotation supplied during the run and in its output is correct. -/
def Algebraic (τ : Fr) (out : List BlobOpening) (s : State) : Prop :=
  (∀ reply ∈ s.history, ∀ point ∈ reply.request.points, point.Valid τ) ∧
    ∀ point ∈ BlobOpening.points out, point.Valid τ

/-- Every group representation supplied in public queries or in the final output. -/
def allPoints (out : List BlobOpening) (s : State) : List AlgebraicPoint :=
  s.history.flatMap (fun reply => reply.request.points) ++ BlobOpening.points out

/-- Representations of a valid group encoding agree throughout the transcript and output. -/
def Consistent (out : List BlobOpening) (s : State) : Prop :=
  ∀ p ∈ allPoints out s, ∀ q ∈ allPoints out s, p.bytes = q.bytes →
    validateKzgG1 p.bytes = true → p.polynomial = q.polynomial

/-- Differences of representations of the same group encoding. -/
noncomputable def representationDifferences (points : List AlgebraicPoint) : List Fr[X] :=
  points.flatMap fun p => points.flatMap fun q =>
    if p.bytes = q.bytes then [p.polynomial - q.polynomial] else []

/-- Algebraicity applies to every representation in the combined transcript. -/
theorem algebraic_allPoints {τ : Fr} {out : List BlobOpening} {s : State}
    (h : Algebraic τ out s) : ∀ point ∈ allPoints out s, point.Valid τ := by
  intro point hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨reply, hr, hp⟩ := List.mem_flatMap.mp hp
    exact h.1 reply hr point hp
  · exact h.2 point hp

/-- Two representations of the same encoding contribute their difference to the search. -/
theorem representationDifference_mem {points : List AlgebraicPoint} {p q : AlgebraicPoint}
    (hp : p ∈ points) (hq : q ∈ points) (heq : p.bytes = q.bytes) :
    p.polynomial - q.polynomial ∈ representationDifferences points := by
  apply List.mem_flatMap.mpr
  refine ⟨p, hp, List.mem_flatMap.mpr ⟨q, hq, ?_⟩⟩
  simp [heq]

/-- Different valid representations of one encoding give a nonzero polynomial rooted at `τ`. -/
theorem root_of_not_consistent {τ : Fr} {out : List BlobOpening} {s : State}
    (ha : Algebraic τ out s) (hc : ¬Consistent out s) :
    ∃ p ∈ representationDifferences (allPoints out s), p ≠ 0 ∧ p.eval τ = 0 := by
  classical
  unfold Consistent at hc
  push Not at hc
  obtain ⟨p, hp, q, hq, hbytes, hvalid, hne⟩ := hc
  obtain ⟨P, hP⟩ := exists_validateKzgG1Point_of_validateKzgG1 hvalid
  have hQ : validateKzgG1Point q.bytes = .ok P := by rw [← hbytes]; exact hP
  have hscalar := (algebraic_allPoints ha p hp P hP).unique
    (algebraic_allPoints ha q hq P hQ)
  refine ⟨_, representationDifference_mem hp hq hbytes, sub_ne_zero.mpr hne, ?_⟩
  simpa only [eval_sub, sub_eq_zero] using hscalar

end EthLib.Cryptography.Kzg.BlobBinding
