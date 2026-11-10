module

public import EthLib.Engine.GetPayload
public import EthLib.Execution.Proofs.Transactions.Network

/-!
# Proofs: `engine_getPayload`

An unknown payload ID returns the Engine API's unknown-payload error.

A returned payload is the payload form of the stored block, at a fork that its version accepts.

From version 3, the bundle's commitments hash to the block's blob hashes, in order.

Its blob or cell proofs pass the KZG verifier.

Versions 3 and 4 return one proof per blob, and versions 5 and 6 return 128 per blob.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants
open EthLib.Execution.Transactions

/-- A missing build process returns unknown payload, before any fork or bundle check. -/
theorem getPayload_eq_error_of_store_eq_none (config : ChainConfig) (setup : TrustedSetup)
    (store : PayloadStore) (version : Nat) (id : PayloadId) (h : store id = none) :
    getPayload config setup store version id = .error (.engine .unknownPayload) := by
  simp [getPayload, h, throw, throwThe, MonadExceptOf.throw]

/-- A returned payload is the stored block's, at its configured fork, with a checked bundle. -/
theorem of_getPayload_eq_ok {config : ChainConfig} {setup : TrustedSetup}
    {store : PayloadStore} {version : Nat} {id : PayloadId} {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) :
    store id = some r.stored ∧
      config.activeFork r.stored.built.block.header.number
        r.stored.built.block.header.timestamp.toNat = some r.stored.fork ∧
      acceptsGetPayloadFork version r.stored.fork = true ∧
      requestsOfFork r.stored.fork r.stored.built.requests = true ∧
      r.stored.built.blockValue < 2 ^ 256 ∧
      payloadOfBlock r.stored.built.block = some r.payload ∧
      (∃ block, r.stored.blockOfPayload r.payload = .ok block) ∧
      (3 ≤ version → validateBlobs setup r.stored.fork
        (ExecutionPayload.blobVersionedHashes r.stored.built.block.transactions)
        r.stored.bundle.blobs r.stored.bundle.commitments r.stored.bundle.proofs = .ok ()) := by
  have ok_of_ne_error {α ε : Type} {x : Except ε α} (H : ∀ e, x = .error e → False) :
      ∃ a, x = .ok a := by
    cases x with
    | error e => exact (H e rfl).elim
    | ok a => exact ⟨a, rfl⟩
  unfold getPayload at h
  cases hs : store id with
  | none => simp [hs, throw, throwThe, MonadExceptOf.throw] at h
  | some stored =>
    simp only [hs, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.mapError] at h
    repeat' split at h
    all_goals cases h
    · refine ⟨rfl, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ok_of_ne_error ‹_›, fun _ => ?_⟩
      rename_i hb _
      split at hb <;> simp_all
    · exact ⟨rfl, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ok_of_ne_error ‹_›, fun hv => absurd hv ‹_›⟩

/-- From version 3, the bundle has the block's hashes in order, its counts, and verifies. -/
theorem getPayload_bundle {config : ChainConfig} {setup : TrustedSetup}
    {store : PayloadStore} {version : Nat} {id : PayloadId} {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) (hv : 3 ≤ version) :
    r.stored.bundle.commitments.map versionedHash =
        ExecutionPayload.blobVersionedHashes r.stored.built.block.transactions ∧
      r.stored.bundle.commitments.length = r.stored.bundle.blobs.length ∧
      r.stored.bundle.proofs.length =
        proofCount r.stored.fork r.stored.bundle.blobs.length ∧
      verifyBlobBundle setup r.stored.fork r.stored.bundle.blobs r.stored.bundle.commitments
        r.stored.bundle.proofs = .ok true := by
  obtain ⟨hc, hh, hp⟩ := (validateBlobs_eq_ok_iff _ _ _ _ _ _).mp
    ((of_getPayload_eq_ok h).2.2.2.2.2.2.2 hv)
  obtain ⟨h₁, h₂, h₃⟩ := (blobCountsMatch_iff _ _ _ _ _).mp hc
  exact ⟨(hashesMatch_iff_map (h₁.trans h₂.symm)).mp hh, h₂, h₃, hp⟩

/-- Versions 3 and 4 return exactly one blob proof for each blob. -/
theorem getPayload_blob_proof_count {config : ChainConfig} {setup : TrustedSetup}
    {store : PayloadStore} {version : Nat} {id : PayloadId} {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) (hv : 3 ≤ version)
    (hv' : version ≤ 4) :
    r.stored.bundle.proofs.length = r.stored.bundle.blobs.length := by
  have hf := (of_getPayload_eq_ok h).2.2.1
  have hc := (getPayload_bundle h hv).2.2.1
  obtain rfl | rfl : version = 3 ∨ version = 4 := by omega
  all_goals
    simp only [acceptsGetPayloadFork, beq_iff_eq] at hf
    simp only [proofCount, hf] at hc
    split at hc
    · rename_i hle
      exact absurd hle (by decide)
    · exact hc

/-- Versions 5 and 6 return exactly 128 cell proofs for each blob. -/
theorem getPayload_cell_proof_count {config : ChainConfig} {setup : TrustedSetup}
    {store : PayloadStore} {version : Nat} {id : PayloadId} {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) (hv : 5 ≤ version) :
    r.stored.bundle.proofs.length = CELLS_PER_EXT_BLOB * r.stored.bundle.blobs.length := by
  have hf := (of_getPayload_eq_ok h).2.2.1
  have hfork : .fusaka ≤ r.stored.fork := by
    match version, hv, hf with
    | 5, _, hf =>
      simp only [acceptsGetPayloadFork, Bool.and_eq_true, decide_eq_true_eq] at hf
      exact hf.1
    | 6, _, hf =>
      simp only [acceptsGetPayloadFork, beq_iff_eq] at hf
      rw [hf]; decide
    | n + 7, _, hf => simp [acceptsGetPayloadFork] at hf
  have hc := (getPayload_bundle h (by omega)).2.2.1
  simpa [proofCount, hfork] using hc

end EthLib.Engine
