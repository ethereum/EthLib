module

public import EthLib.Engine.GetPayload
public import EthLib.Engine.Proofs.Json

/-!
# Proofs: `engine_getPayload`

A returned bundle has the exact ordered versioned hashes of the payload's blob transactions.

Its blob or cell proofs pass the actual KZG verifier.

From Fusaka, its proof count is exactly 128 times its blob count.

An unknown payload ID returns the Engine API's unknown-payload error.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants
open EthLib.Execution.Transactions

/-- The bundle check gives its lengths, ordered hashes and the successful KZG check. -/
theorem checkPayloadBundle_eq_ok_iff (setup : TrustedSetup) (fork : Fork)
    (hashes : List Bytes32) (bundle : BlobsBundle) :
    checkPayloadBundle setup fork hashes bundle = .ok () ↔
      (hashes.length = bundle.blobs.length ∧
        bundle.commitments.length = bundle.blobs.length ∧
        bundle.proofs.length = proofCount fork bundle.blobs.length) ∧
      bundle.commitments.map versionedHash = hashes ∧
      verifyBlobBundle setup fork bundle.blobs bundle.commitments bundle.proofs = .ok true := by
  by_cases hc : hashes.length = bundle.blobs.length ∧
      bundle.commitments.length = bundle.blobs.length ∧
      bundle.proofs.length = proofCount fork bundle.blobs.length
  · by_cases hh : bundle.commitments.map versionedHash = hashes
    · cases hp : verifyBlobBundle setup fork bundle.blobs bundle.commitments bundle.proofs with
      | error e => simp [checkPayloadBundle, hc, hh, hp, Except.mapError, bind, Except.bind]
      | ok b => cases b <;>
          simp [checkPayloadBundle, hc, hh, hp, Except.mapError, bind, Except.bind, pure,
            Except.pure, throw, throwThe, MonadExceptOf.throw]
    · simp [checkPayloadBundle, hc, hh, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · simp [checkPayloadBundle, hc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A missing build process returns unknown payload, before any fork or bundle check. -/
theorem getPayload_of_none (config : ChainConfig) (setup : TrustedSetup) (store : PayloadStore)
    (version : Nat) (id : PayloadId) (h : store id = none) :
    getPayload config setup store version id = .error (.engine .unknownPayload) := by
  simp [getPayload, h]

/-- A returned payload is the stored snapshot and, from version 3, has a checked bundle. -/
theorem getPayload_checked {config : ChainConfig} {setup : TrustedSetup} {store : PayloadStore}
    {version : Nat} {id : PayloadId} {built : StoredPayload}
    (h : getPayload config setup store version id = .ok built) :
    store id = some built ∧ acceptsGetPayloadFork version built.fork = true ∧
      (version ≥ 3 → ∃ transactions,
        decodeTransactions built.fork 0 built.payload.transactions = .ok transactions ∧
        checkPayloadBundle setup built.fork
          (ExecutionPayload.blobVersionedHashes transactions) built.bundle = .ok ()) := by
  unfold getPayload at h
  cases hstore : store id with
  | none => simp [hstore] at h
  | some found =>
    simp only [hstore] at h
    by_cases hf : config.activeFork found.payload.blockNumber.toNat found.payload.timestamp.toNat =
        some found.fork ∧ acceptsGetPayloadFork version found.fork = true
    · simp only [ite_eq_left hf] at h
      by_cases hr : (if h : .pectra ≤ found.fork then validRequests (found.requests h)
          else true) = true
      · simp only [ite_eq_left hr] at h
        by_cases hv : version ≥ 3
        · simp only [ite_eq_left hv] at h
          obtain ⟨transactions, htx, h⟩ := bind_ok_iff.mp h
          obtain ⟨result, hb, h⟩ := bind_ok_iff.mp h
          cases result
          cases h
          exact ⟨rfl, hf.2, fun _ =>
            ⟨transactions, mapError_ok_iff.mp htx, mapError_ok_iff.mp hb⟩⟩
        · simp only [ite_eq_right hv] at h
          cases h
          exact ⟨rfl, hf.2, fun hv' => False.elim (hv hv')⟩
      · simp only [ite_eq_right hr] at h
        cases h
    · simp only [ite_eq_right hf] at h
      cases h

/-- Every returned bundle from version 3 has exactly the payload's hashes and verifies. -/
theorem getPayload_bundle {config : ChainConfig} {setup : TrustedSetup} {store : PayloadStore}
    {version : Nat} {id : PayloadId} {built : StoredPayload}
    (h : getPayload config setup store version id = .ok built) (hv : version ≥ 3) :
    ∃ transactions,
      decodeTransactions built.fork 0 built.payload.transactions = .ok transactions ∧
      built.bundle.commitments.map versionedHash =
        ExecutionPayload.blobVersionedHashes transactions ∧
      built.bundle.commitments.length = built.bundle.blobs.length ∧
      built.bundle.proofs.length = proofCount built.fork built.bundle.blobs.length ∧
      verifyBlobBundle setup built.fork built.bundle.blobs built.bundle.commitments
        built.bundle.proofs = .ok true := by
  obtain ⟨transactions, htx, hb⟩ := (getPayload_checked h).2.2 hv
  obtain ⟨hc, hh, hp⟩ := (checkPayloadBundle_eq_ok_iff _ _ _ _).mp hb
  exact ⟨transactions, htx, hh, hc.2.1, hc.2.2, hp⟩

/-- Versions 5 and 6 return exactly 128 cell proofs for each blob. -/
theorem getPayload_cell_proof_count {config : ChainConfig} {setup : TrustedSetup}
    {store : PayloadStore} {version : Nat} {id : PayloadId} {built : StoredPayload}
    (h : getPayload config setup store version id = .ok built) (hv : version = 5 ∨ version = 6) :
    built.bundle.proofs.length = CELLS_PER_EXT_BLOB * built.bundle.blobs.length := by
  have hf := (getPayload_checked h).2.1
  have h3 : version ≥ 3 := by omega
  have hfork : .fusaka ≤ built.fork := by
    rcases hv with hv | hv
    · have hf' : .fusaka ≤ built.fork ∧ built.fork < .glamsterdam := by
        simpa [hv, acceptsGetPayloadFork] using hf
      exact hf'.1
    · have hf' : built.fork = .glamsterdam := by
        simpa [hv, acceptsGetPayloadFork] using hf
      rw [hf']; decide
  obtain ⟨_, _, _, _, hc, _⟩ := getPayload_bundle h h3
  simpa [proofCount, hfork] using hc

end EthLib.Engine
