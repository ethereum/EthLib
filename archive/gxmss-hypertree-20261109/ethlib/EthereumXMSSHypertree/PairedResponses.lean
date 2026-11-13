/-
Copyright (c) 2026 Matthias Meijers.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthLib.Cryptography.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.Address
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Paired chain-start responses

Each source derivation returns all 32 bytes. Its ordered halves jointly have the
law of two independent uniform digests. The source makes one derivation for each
pair of chains, retaining the complete response until both halves are read.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants
open OracleComp OracleSpec

/-- The complete response of one source seed derivation. -/
abbrev FullResponse := Vector UInt8 32

/-- The source's first and second halves, in their source order. -/
@[expose]
def splitResponse (response : FullResponse) : Digest × Digest :=
  (halfOf 0 response, halfOf 1 response)

/-- Concatenate the two digest halves into the complete source response. -/
@[expose]
def joinResponse (halves : Digest × Digest) : FullResponse :=
  Vector.ofFn fun i => if h : i.val < 16 then halves.1[i.val] else
    halves.2[i.val - 16]'(by have := i.isLt; simp only [DIGEST_LEN]; omega)

/-- Splitting a concatenation recovers both ordered halves. -/
@[simp]
theorem splitResponse_joinResponse (halves : Digest × Digest) :
    splitResponse (joinResponse halves) = halves := by
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    simp [splitResponse, joinResponse, halfOf, DIGEST_LEN]
    rfl
  · apply Vector.ext
    intro i hi
    simp [splitResponse, joinResponse, halfOf]

/-- Concatenating the source's two halves recovers every response byte. -/
@[simp]
theorem joinResponse_splitResponse (response : FullResponse) :
    joinResponse (splitResponse response) = response := by
  apply Vector.ext
  intro i hi
  by_cases h : i < 16
  · simp [joinResponse, splitResponse, h, halfOf]
  · have hindex : 16 + (i - 16) = i := by omega
    simp [joinResponse, splitResponse, h, halfOf, hindex]

/-- A full response is equivalent to its two ordered source digest halves. -/
@[expose]
def splitResponseEquiv : FullResponse ≃ Digest × Digest where
  toFun := splitResponse
  invFun := joinResponse
  left_inv := joinResponse_splitResponse
  right_inv := splitResponse_joinResponse

/-- Both halves jointly are independent uniform digests, rather than only marginally uniform. -/
theorem splitResponse_uniform :
    splitResponse <$> ($ᵗ FullResponse : ProbComp FullResponse) =ᵈ
      (do let first ← $ᵗ Digest; let second ← $ᵗ Digest; pure (first, second)) := by
  rw [← SampleableType.uniformSample_prod_eq_bind]
  exact SampleableType.map_uniformSample_evalDistEq_of_bijective splitResponseEquiv.bijective

/-- The source uses 29 complete derivations for its 58 chains. -/
theorem chain_pair_count : V / 2 = 29 ∧ V = 58 ∧ 2 * (V / 2) = V := by
  decide

/-- Distinct source pair indices make distinct complete-response requests. -/
theorem chain_start_address_injective (layer : Layer) (epoch : UInt32) :
    Function.Injective (addrPrf layer epoch) := by
  intro first second h
  exact (addrPrf_inj.mp h).2.2

/-- The exact explicit-input reconstruction performed after the 29 source derivations. -/
@[expose]
def startsFromResponses (responses : Vector FullResponse (V / 2)) : Vector Digest V :=
  Vector.ofFn fun i =>
    halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
      (responses[i.val / 2]'(by have := i.isLt; simp only [V] at *; omega))

/-- Source chain derivation retains a complete response per pair and then reads its halves. -/
theorem chainStarts_eq {m : Type → Type} [Monad m] (pp : PublicParam)
    (prf : SeedPrf m) (layer : Layer) (epoch : UInt32) :
    chainStarts pp prf layer epoch =
      (do let responses ← ofFnInOrder (V / 2) fun j =>
            prf pp (addrPrf layer epoch j) .empty
          pure (startsFromResponses responses)) := rfl

/-- Chain `2j` reads the first half of response `j`. -/
theorem startsFromResponses_even (responses : Vector FullResponse (V / 2))
    (j : Fin (V / 2)) :
    (startsFromResponses responses)[2 * j.val]'(by
      have := j.isLt
      simp only [V] at *
      omega) = halfOf 0 responses[j.val] := by
  simp [startsFromResponses, Nat.mul_mod_right]

/-- Chain `2j+1` reads the second half of the same response `j`. -/
theorem startsFromResponses_odd (responses : Vector FullResponse (V / 2))
    (j : Fin (V / 2)) :
    (startsFromResponses responses)[2 * j.val + 1]'(by
      have := j.isLt
      simp only [V] at *
      omega) = halfOf 1 responses[j.val] := by
  simp [startsFromResponses, Nat.mul_add_div]

/-- Recover the 29 complete responses by joining consecutive even and odd chain starts. -/
@[expose]
def responsesFromStarts (starts : Vector Digest V) : Vector FullResponse (V / 2) :=
  Vector.ofFn fun j => joinResponse
    (starts[2 * j.val]'(by have := j.isLt; simp only [V] at *; omega),
      starts[2 * j.val + 1]'(by have := j.isLt; simp only [V] at *; omega))

/-- The 58 source chain starts retain every byte of the 29 complete responses. -/
@[simp]
theorem responsesFromStarts_startsFromResponses
    (responses : Vector FullResponse (V / 2)) :
    responsesFromStarts (startsFromResponses responses) = responses := by
  apply Vector.ext
  intro j hj
  simp only [responsesFromStarts, Vector.getElem_ofFn]
  rw [startsFromResponses_even responses ⟨j, hj⟩,
    startsFromResponses_odd responses ⟨j, hj⟩]
  exact joinResponse_splitResponse responses[j]

/-- Joining consecutive starts and splitting their responses recovers all 58 starts. -/
@[simp]
theorem startsFromResponses_responsesFromStarts (starts : Vector Digest V) :
    startsFromResponses (responsesFromStarts starts) = starts := by
  apply Vector.ext
  intro i hi
  simp only [startsFromResponses, responsesFromStarts, Vector.getElem_ofFn]
  by_cases heven : i % 2 = 0
  · have hhalf : (⟨i % 2, Nat.mod_lt i (by decide)⟩ : Fin 2) = 0 := Fin.ext heven
    rw [hhalf]
    have hfirst (halves : Digest × Digest) : halfOf 0 (joinResponse halves) = halves.1 :=
      congrArg Prod.fst (splitResponse_joinResponse halves)
    rw [hfirst]
    change starts[2 * (i / 2)] = starts[i]
    congr 1
    omega
  · have hodd : i % 2 = 1 := by omega
    have hhalf : (⟨i % 2, Nat.mod_lt i (by decide)⟩ : Fin 2) = 1 := Fin.ext hodd
    rw [hhalf]
    have hsecond (halves : Digest × Digest) : halfOf 1 (joinResponse halves) = halves.2 :=
      congrArg Prod.snd (splitResponse_joinResponse halves)
    rw [hsecond]
    change starts[2 * (i / 2) + 1] = starts[i]
    congr 1
    omega

/-- The source's 29 complete responses are equivalent to its 58 ordered chain starts. -/
@[expose]
def startsFromResponsesEquiv : Vector FullResponse (V / 2) ≃ Vector Digest V where
  toFun := startsFromResponses
  invFun := responsesFromStarts
  left_inv := responsesFromStarts_startsFromResponses
  right_inv := startsFromResponses_responsesFromStarts

/-- Uniform complete responses induce the joint uniform law of all 58 source chain starts. -/
theorem startsFromResponses_uniform :
    startsFromResponses <$> ($ᵗ (Vector FullResponse (V / 2)) :
      ProbComp (Vector FullResponse (V / 2))) =ᵈ ($ᵗ (Vector Digest V)) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective startsFromResponsesEquiv.bijective

/-- The induced joint law is exactly 58 independent uniform digest draws in vector order. -/
theorem startsFromResponses_independent_uniform :
    startsFromResponses <$> SampleableType.vector FullResponse (V / 2) =ᵈ
      SampleableType.vector Digest V :=
  startsFromResponses_uniform

/-- Record each actual complete-response derivation address before returning its response. -/
@[expose]
def loggedSeedPrf (table : PublicParam → Address → ByteArray → FullResponse) :
    SeedPrf (StateM (List Address)) :=
  fun pp address suffix log => (table pp address suffix, log ++ [address])

private theorem orderedResponses_run (n : Nat) (addresses : Fin n → Address)
    (table : Address → FullResponse) (log : List Address) :
    (ofFnInOrder (m := StateM (List Address)) n (fun i => fun log =>
      pure (table (addresses i), log ++ [addresses i]))).run
        log = (Vector.ofFn (fun i => table (addresses i)), log ++ List.ofFn addresses) := by
  induction n generalizing log with
  | zero =>
    change (#v[], log) = (Vector.ofFn (fun i => table (addresses i)), log ++ [])
    simp
  | succ n ih =>
    change
      ((#v[table (addresses 0)] ++
          ((ofFnInOrder (m := StateM (List Address)) n (fun i => fun log =>
            pure (table (addresses i.succ), log ++ [addresses i.succ]))).run
            (log ++ [addresses 0])).1).cast _,
        ((ofFnInOrder (m := StateM (List Address)) n (fun i => fun log =>
            pure (table (addresses i.succ), log ++ [addresses i.succ]))).run
            (log ++ [addresses 0])).2) = _
    rw [ih]
    apply Prod.ext
    · apply Vector.ext
      intro i hi
      cases i with
      | zero => simp
      | succ i => simp [Fin.succ]
    · simp [List.ofFn_succ, List.append_assoc]

/-- The source's trace is exactly the 29 increasing pair addresses, with no half queries. -/
theorem chainStarts_logged (table : PublicParam → Address → ByteArray → FullResponse)
    (pp : PublicParam) (layer : Layer) (epoch : UInt32) (log : List Address) :
    (chainStarts pp (loggedSeedPrf table) layer epoch).run log =
      (startsFromResponses (Vector.ofFn fun j => table pp (addrPrf layer epoch j) .empty),
        log ++ List.ofFn (addrPrf layer epoch)) := by
  simp only [chainStarts_eq, StateT.run_bind, StateT.run_pure]
  unfold loggedSeedPrf
  have h := orderedResponses_run (V / 2) (addrPrf layer epoch)
    (fun address => table pp address .empty) log
  change (ofFnInOrder (m := StateM (List Address)) (V / 2) (fun i => fun log =>
    (table pp (addrPrf layer epoch i) .empty, log ++ [addrPrf layer epoch i]))).run log = _
    at h
  rw [h]
  rfl

/-- The source makes exactly 29 full-response requests when starting one one-time key. -/
theorem chainStarts_request_count
    (table : PublicParam → Address → ByteArray → FullResponse)
    (pp : PublicParam) (layer : Layer) (epoch : UInt32) :
    ((chainStarts pp (loggedSeedPrf table) layer epoch).run []).2.length = 29 := by
  rw [chainStarts_logged]
  simpa only [List.nil_append, List.length_ofFn] using (show V / 2 = 29 from rfl)

/-- Every one of those 29 full-response derivation addresses is distinct. -/
theorem chainStarts_requests_nodup
    (table : PublicParam → Address → ByteArray → FullResponse)
    (pp : PublicParam) (layer : Layer) (epoch : UInt32) :
    ((chainStarts pp (loggedSeedPrf table) layer epoch).run []).2.Nodup := by
  rw [chainStarts_logged]
  simp only [List.nil_append, List.nodup_ofFn]
  exact chain_start_address_injective layer epoch

end EthereumXMSSHypertree
