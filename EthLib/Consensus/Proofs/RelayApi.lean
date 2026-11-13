module

public import EthLib.Consensus.RelayApi
public import EthLib.Consensus.Proofs.BuilderApi
public import EthLib.Consensus.Proofs.BuilderApi.Bid

/-!
# Proofs: what a relay keeps from a submission, and the bid it serves

A submission for the slot of a store replaces the entry of its builder, whatever the values.

No other entry changes, and a submission for another slot changes nothing.

The served bid holds the header, the value, the key and, from Deneb, the commitments of the bundle.

A blinded body that carries the header of that bid unblinds with the payload of the submission.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz BuilderApi

variable {preset : Preset} {fork : Fork}

namespace RelayApi

/-- After a submission for the slot of the store, the entry of its builder is that submission.

This holds whatever the value of the entry before, even when it was higher. -/
theorem SubmissionStore.submit_overwrites (store : SubmissionStore preset fork)
    {request : SubmitBlockRequest preset fork} (slot : request.message.slot = store.slot) :
    (store.submit request).get request.message.builderPubkey = some request := by
  simp [SubmissionStore.submit, SubmissionStore.get, slot]

/-- A submission leaves the entries of other builders unchanged. -/
theorem SubmissionStore.submit_other (store : SubmissionStore preset fork)
    (request : SubmitBlockRequest preset fork) {pubkey : BLSPubkey}
    (other : pubkey ≠ request.message.builderPubkey) :
    (store.submit request).get pubkey = store.get pubkey := by
  unfold SubmissionStore.submit
  split
  · unfold SubmissionStore.get
    dsimp only
    rw [List.find?_cons_of_neg (by simpa using fun h => other h.symm)]
    induction store.entries with
    | nil => rfl
    | cons head rest ih =>
      by_cases same : head.message.builderPubkey = request.message.builderPubkey
      · have mine : ¬head.message.builderPubkey = pubkey := fun h => other (h.symm.trans same)
        rw [List.filter_cons_of_neg (by simpa using same),
          List.find?_cons_of_neg (by simpa using mine), ih]
      · rw [List.filter_cons_of_pos (by simpa using same)]
        by_cases mine : head.message.builderPubkey = pubkey
        · rw [List.find?_cons_of_pos (by simpa using mine),
            List.find?_cons_of_pos (by simpa using mine)]
        · rw [List.find?_cons_of_neg (by simpa using mine),
            List.find?_cons_of_neg (by simpa using mine), ih]
  · rfl

/-- A submission for another slot leaves the store as it was. -/
theorem SubmissionStore.submit_other_slot (store : SubmissionStore preset fork)
    {request : SubmitBlockRequest preset fork} (slot : request.message.slot ≠ store.slot) :
    store.submit request = store := by
  simp [SubmissionStore.submit, slot]

end RelayApi

/-- The served bid always computes. -/
theorem SubmitBlockRequest.bid_total (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) :
    ∃ bid, request.bid range pubkey = .ok bid :=
  getBid_total _ _ _ _ _

/-- The served bid holds the header of the payload of the submission. -/
theorem SubmitBlockRequest.bid_header (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) :
    BuilderBid.header <$> request.bid range pubkey = request.executionPayload.header :=
  getBid_header _ _ _ _ _

/-- The served bid holds the value of the bid trace and the key it is served under. -/
theorem SubmitBlockRequest.bid_value_pubkey (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) :
    (fun bid => (bid.value, bid.pubkey)) <$> request.bid range pubkey =
      .ok (request.message.value, pubkey) := by
  obtain ⟨header, made⟩ := ExecutionPayload.header_total request.executionPayload
  simp [SubmitBlockRequest.bid, getBid, made, bind, Except.bind, pure, Except.pure, Functor.map,
    Except.map]

/-- From Deneb, the served bid holds the commitments of the blobs bundle of the submission. -/
theorem SubmitBlockRequest.bid_commitments (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) (deneb : .dencun ≤ fork) :
    (fun bid => bid.blobKzgCommitments deneb) <$> request.bid range pubkey =
      .ok (.ofSszList (request.blobsBundle ⟨deneb, range.2⟩).commitments) := by
  obtain ⟨header, made⟩ := ExecutionPayload.header_total request.executionPayload
  simp [SubmitBlockRequest.bid, getBid, made, bind, Except.bind, pure, Except.pure, Functor.map,
    Except.map]

/-- From Electra, the served bid holds the requests of the submission. -/
theorem SubmitBlockRequest.bid_requests (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) (electra : .pectra ≤ fork) :
    (fun bid => bid.executionRequests electra) <$> request.bid range pubkey =
      .ok (request.executionRequests ⟨electra, range.2⟩) := by
  obtain ⟨header, made⟩ := ExecutionPayload.header_total request.executionPayload
  simp [SubmitBlockRequest.bid, getBid, made, bind, Except.bind, pure, Except.pure, Functor.map,
    Except.map]

/-- A blinded body that carries the header of the served bid unblinds with the payload.

The unblinded body holds the payload of the submission. -/
theorem SubmitBlockRequest.bid_unblind {request : SubmitBlockRequest preset fork}
    {range : HasBuilderApi fork} {pubkey : BLSPubkey} {bid : BuilderBid preset fork}
    (served : request.bid range pubkey = .ok bid) {body : BlindedBeaconBlockBody preset fork}
    (carries : body.executionPayloadHeader range = bid.header) :
    ∃ full, body.unblind range request.executionPayload = .ok full ∧
      full.executionPayload range = request.executionPayload := by
  have computed : request.executionPayload.header = .ok bid.header := by
    rw [← SubmitBlockRequest.bid_header request range pubkey, served]
    rfl
  simp only [BlindedBeaconBlockBody.unblind, computed, carries, ↓reduceIte]
  exact ⟨_, rfl, rfl⟩

end EthLib.Consensus
