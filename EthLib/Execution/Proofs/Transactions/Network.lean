module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Transactions.Envelope
public import EthLib.Execution.Transactions.Network

/-!
# Proofs: the network form of blob transactions

The network form reads back from its bytes, at each fork from Dencun.

Bytes that decode to a network form are its encoding.

So bytes decode to a network form exactly when they encode it and the fork is Dencun or later.

The transaction it carries is the first item of its RLP list, so its hash ignores the blobs.

The check of the blobs succeeds exactly when three conditions hold.

The counts match, each commitment hashes to its versioned hash, and the proofs verify.

Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Serialization.Rlp

/-! ## Bytes -/

/-- The network form reads back from its RLP list, at every fork. -/
theorem NetworkBlobTransaction.ofItem_toItem (fork : Fork) (w : NetworkBlobTransaction) :
    NetworkBlobTransaction.ofItem fork (w.toItem fork) = .ok w := by
  unfold NetworkBlobTransaction.ofItem NetworkBlobTransaction.toItem
  by_cases h : fork ≥ .fusaka
  · simp [h, LawfulCodec.ofItem_toItem, WRAPPER_VERSION, Except.mapError, bind, Except.bind,
      pure, Except.pure]
  · simp [h, LawfulCodec.ofItem_toItem, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A list that holds a network form is the list of that form. -/
theorem NetworkBlobTransaction.toItem_of_ofItem {fork : Fork} {item : Item}
    {w : NetworkBlobTransaction} (h : NetworkBlobTransaction.ofItem fork item = .ok w) :
    w.toItem fork = item := by
  unfold NetworkBlobTransaction.ofItem at h
  unfold NetworkBlobTransaction.toItem
  split at h
  · rename_i hf
    split at h
    · rename_i tx v b c p
      obtain ⟨version, hv, h⟩ := bind_ok_iff.mp h
      have hv := LawfulCodec.toItem_of_ofItem (mapError_ok_iff.mp hv)
      split at h
      · exact nomatch h
      rename_i hver
      simp only [ne_eq, Decidable.not_not] at hver
      subst hver
      have h := mapError_ok_iff.mp h
      obtain ⟨x1, h1, h⟩ := bind_ok_iff.mp h
      obtain ⟨x2, h2, h⟩ := bind_ok_iff.mp h
      obtain ⟨x3, h3, h⟩ := bind_ok_iff.mp h
      obtain ⟨x4, h4, h⟩ := bind_ok_iff.mp h
      cases h
      simp only [hf, ↓reduceIte, hv, LawfulCodec.toItem_of_ofItem h1,
        LawfulCodec.toItem_of_ofItem h2, LawfulCodec.toItem_of_ofItem h3,
        LawfulCodec.toItem_of_ofItem h4]
    · exact nomatch h
    · exact nomatch h
  · rename_i hf
    split at h
    · have h := mapError_ok_iff.mp h
      obtain ⟨x1, h1, h⟩ := bind_ok_iff.mp h
      obtain ⟨x2, h2, h⟩ := bind_ok_iff.mp h
      obtain ⟨x3, h3, h⟩ := bind_ok_iff.mp h
      obtain ⟨x4, h4, h⟩ := bind_ok_iff.mp h
      cases h
      simp only [hf, ↓reduceIte, LawfulCodec.toItem_of_ofItem h1,
        LawfulCodec.toItem_of_ofItem h2, LawfulCodec.toItem_of_ofItem h3,
        LawfulCodec.toItem_of_ofItem h4]
    · exact nomatch h
    · exact nomatch h

/-- The network form reads back from its bytes, at each fork from Dencun. -/
theorem decodeNetwork_encodeNetwork {fork : Fork} {w : NetworkBlobTransaction} {bytes : ByteArray}
    (hFork : fork ≥ .dencun) (h : encodeNetwork fork w = .ok bytes) :
    decodeNetwork fork bytes = .ok w := by
  simp only [encodeNetwork, Functor.map, Except.map] at h
  split at h
  · exact nomatch h
  rename_i payload hPayload
  cases h
  have hList : (typedBytes 3 payload).data.toList = 3 :: payload.data.toList := by
    simp [typedBytes]
  unfold decodeNetwork
  rw [hList]
  simp only [hFork, and_self, ↓reduceIte, Array.toArray_toList]
  rw [show (⟨payload.data⟩ : ByteArray) = payload from rfl,
    Serialization.Rlp.decode_encode _ _ hPayload]
  exact NetworkBlobTransaction.ofItem_toItem fork w

/-- Bytes that decode to a network form are the encoding of that form.

So at one fork, two different byte strings never decode to the same network form. -/
theorem encodeNetwork_of_decodeNetwork {fork : Fork} {bytes : ByteArray}
    {w : NetworkBlobTransaction} (h : decodeNetwork fork bytes = .ok w) :
    encodeNetwork fork w = .ok bytes := by
  unfold decodeNetwork at h
  split at h
  · exact nomatch h
  rename_i type payload hbytes
  split at h
  · obtain ⟨item, hitem, h⟩ := bind_ok_iff.mp h
    have hitem := mapError_ok_iff.mp hitem
    have hw := NetworkBlobTransaction.toItem_of_ofItem h
    obtain ⟨hType, -⟩ := ‹type = 3 ∧ fork ≥ .dencun›
    subst hType
    simp only [encodeNetwork, hw, Serialization.Rlp.encode_decode _ _ hitem, Functor.map,
      Except.map, Except.ok.injEq]
    apply ByteArray.ext
    rw [← Array.toList_inj, hbytes]
    simp [typedBytes]
  · exact nomatch h

/-- Bytes decode to a network form exactly when they encode it and the fork is Dencun or later. -/
theorem decodeNetwork_eq_ok_iff (fork : Fork) (bytes : ByteArray) (w : NetworkBlobTransaction) :
    decodeNetwork fork bytes = .ok w ↔ fork ≥ .dencun ∧ encodeNetwork fork w = .ok bytes := by
  refine ⟨fun h => ⟨?_, encodeNetwork_of_decodeNetwork h⟩, fun ⟨hFork, h⟩ =>
    decodeNetwork_encodeNetwork hFork h⟩
  unfold decodeNetwork at h
  split at h
  · exact nomatch h
  split at h
  · rename_i hc
    exact hc.2
  · exact nomatch h

/--
The transaction of a decoded network form is the first item of its RLP list.

A block holds the transaction alone, so its bytes, and its hash, are those of that item.
-/
theorem tx_of_decodeNetwork {fork : Fork} {bytes : ByteArray} {w : NetworkBlobTransaction}
    (h : decodeNetwork fork bytes = .ok w) :
    ∃ rest, Serialization.Rlp.decode ⟨(bytes.data.toList.drop 1).toArray⟩ =
      .ok (.list (Codec.toItem w.tx :: rest)) := by
  unfold decodeNetwork at h
  split at h
  · exact nomatch h
  rename_i type payload hbytes
  split at h
  · obtain ⟨item, hitem, h⟩ := bind_ok_iff.mp h
    have hitem := mapError_ok_iff.mp hitem
    have hw := NetworkBlobTransaction.toItem_of_ofItem h
    rw [hbytes, List.drop_one, List.tail_cons, hitem, ← hw]
    unfold NetworkBlobTransaction.toItem
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact nomatch h

/-! ## The check of the blobs -/

/-- The commitments match exactly when each one hashes to the versioned hash at its position. -/
theorem hashesMatch_iff {hashes : List Bytes32} {commitments : List KZGCommitment}
    (hlen : hashes.length = commitments.length) :
    hashesMatch hashes commitments = true ↔
      ∀ (i : Nat) (hi : i < hashes.length),
        versionedHash (commitments[i]'(hlen ▸ hi)) = hashes[i] := by
  simp only [hashesMatch, List.all_eq_true, decide_eq_true_eq, Prod.forall]
  constructor
  · intro H i hi
    exact H _ _ (List.mem_iff_getElem.mpr ⟨i, by simp [← hlen, hi], List.getElem_zip⟩)
  · intro H a b hmem
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
    simp only [List.length_zip, Nat.lt_min] at hi
    simp only [List.getElem_zip, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact H i hi.1

/-- With one commitment per hash, the commitments match exactly when they hash to the list. -/
theorem hashesMatch_iff_map {hashes : List Bytes32} {commitments : List KZGCommitment}
    (hlen : hashes.length = commitments.length) :
    hashesMatch hashes commitments = true ↔ commitments.map versionedHash = hashes := by
  rw [hashesMatch_iff hlen, List.ext_getElem_iff]
  simp only [List.length_map, List.getElem_map]
  constructor
  · intro H
    exact ⟨hlen.symm, fun i h₁ h₂ => H i h₂⟩
  · intro ⟨_, H⟩ i hi
    exact H i (hlen ▸ hi) hi

/--
The check of blobs succeeds exactly when three conditions hold.

The counts match, each commitment hashes to its versioned hash, and the proofs verify.
-/
theorem validateBlobs_eq_ok_iff (setup : TrustedSetup) (fork : Fork) (hashes : List Bytes32)
    (blobs : List Blob) (commitments : List KZGCommitment) (proofs : List KZGProof) :
    validateBlobs setup fork hashes blobs commitments proofs = .ok () ↔
      blobCountsMatch fork hashes blobs commitments proofs = true ∧
        hashesMatch hashes commitments = true ∧
        verifyBlobBundle setup fork blobs commitments proofs = .ok true := by
  unfold validateBlobs
  cases blobCountsMatch fork hashes blobs commitments proofs <;>
    cases hashesMatch hashes commitments <;>
    cases verifyBlobBundle setup fork blobs commitments proofs <;>
    simp [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]

/-- The counts match exactly with one hash and one commitment per blob, and the fork's proofs. -/
theorem blobCountsMatch_iff (fork : Fork) (hashes : List Bytes32) (blobs : List Blob)
    (commitments : List KZGCommitment) (proofs : List KZGProof) :
    blobCountsMatch fork hashes blobs commitments proofs = true ↔
      hashes.length = blobs.length ∧ commitments.length = blobs.length ∧
        proofs.length = proofCount fork blobs.length := by
  simp [blobCountsMatch, and_assoc]

/--
The check of the blobs succeeds exactly when three conditions hold.

The counts match, each commitment hashes to its versioned hash, and the proofs verify.
-/
theorem validateNetwork_eq_ok_iff (setup : TrustedSetup) (fork : Fork)
    (w : NetworkBlobTransaction) :
    validateNetwork setup fork w = .ok () ↔
      countsMatch fork w = true ∧ hashesMatch w.tx.blobVersionedHashes w.commitments = true ∧
        proofsVerify setup fork w = .ok true :=
  validateBlobs_eq_ok_iff setup fork _ _ _ _

/-! ## Error codes -/

/-- A transaction error has a code of at most 16. -/
theorem TransactionError.code_le (e : TransactionError) : e.code ≤ 16 := by
  cases e <;> simp only [TransactionError.code] <;> decide

/-- Two errors with the same code come from the same constructor. -/
theorem NetworkError.code_injective (e₁ e₂ : NetworkError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- A transaction error has a code of at most 16, and the other codes start at 101.
  cases e₁ <;> cases e₂ <;> simp only [NetworkError.code] at h <;>
    first
    | rfl
    | exact absurd h (by decide)
    | (have hle := TransactionError.code_le ‹TransactionError›
       first | rw [h] at hle | rw [← h] at hle
       exact absurd hle (by decide))

end EthLib.Execution.Transactions
