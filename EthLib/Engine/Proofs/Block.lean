module

public import EthLib.Base.Proofs.MapM
public import EthLib.Engine.Block
public import EthLib.Execution.Proofs.Transactions.Envelope
public import EthLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: a payload and its block determine each other

A payload whose block hash is the hash of its header is the payload of its block.

A block of the shape that a payload gives comes back from its payload.

The shape is fixed by EIP-3675 from Paris, with roots and a requests hash that match the lists.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions

variable {fork : Fork}

/-! ## Pieces -/

/-- The requests commitment holds the bytes of the requests hash. -/
theorem packBytes_requestsCommitment (requests : List ByteArray) :
    packBytes (requestsCommitment requests) = requestsHash requests := by
  have hSize : (requestsHash requests).size = 32 := Cryptography.Hash.Sha256.hash_size _
  unfold requestsCommitment
  generalize requestsHash requests = r at hSize ⊢
  apply ByteArray.ext
  apply Array.ext
  · simp only [packBytes, Vector.toArray_ofFn, Array.size_ofFn]
    exact hSize.symm
  · intro i h₁ h₂
    simp [packBytes, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h₂]

/-- A field computed only at the forks that have it is the field of the step. -/
theorem sinceM_eq_ok {ε α : Type} {f : Fork} {g : f ≤ fork → Except ε α} {x : Since f fork α}
    (h : ∀ hf, g hf = .ok (x hf)) : sinceM g = .ok x := by
  unfold sinceM
  split
  · rename_i hf
    rw [h hf]
    exact congrArg Except.ok (Since.eq_const hf x).symm
  · exact congrArg Except.ok (Since.eq_of_not_le (by assumption) _ _)

/-- Decoded transactions encode back to their bytes, and the fork has their kinds. -/
theorem encode_of_decodeTransactions {index : Nat} {bytes : List ByteArray}
    {txs : List Transaction} (h : decodeTransactions fork index bytes = .ok txs) :
    txs.mapM encodeTransaction = .ok bytes ∧ ∀ tx ∈ txs, tx.fork ≤ fork := by
  induction bytes generalizing index txs with
  | nil =>
    simp only [decodeTransactions, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [pure, Except.pure]
  | cons b rest ih =>
    simp only [decodeTransactions, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i tx hTx
      split at h
      · cases h
      · rename_i txs' hRest
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hTx' : decodeTransaction fork b = .ok tx := by
          unfold Except.mapError at hTx
          split at hTx <;> simp_all
        obtain ⟨hEnc, hFork⟩ := encodeTransaction_of_decodeTransaction hTx'
        obtain ⟨ihEnc, ihFork⟩ := ih hRest
        refine ⟨?_, ?_⟩
        · simp [List.mapM_cons, hEnc, ihEnc, bind, Except.bind, pure, Except.pure]
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hFork
          · exact ihFork t ht

/-- Transactions of the fork's kinds decode from their bytes. -/
theorem decodeTransactions_of_encode {index : Nat} {bytes : List ByteArray}
    {txs : List Transaction} (h : txs.mapM encodeTransaction = .ok bytes)
    (hFork : ∀ tx ∈ txs, tx.fork ≤ fork) : decodeTransactions fork index bytes = .ok txs := by
  induction txs generalizing index bytes with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons tx rest ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i b hB
      split at h
      · cases h
      · rename_i bs hBs
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hDec := decodeTransaction_encodeTransaction hB (hFork tx (List.mem_cons_self ..))
        have hRest := ih (index := index + 1) hBs fun t ht => hFork t (List.mem_cons_of_mem _ ht)
        simp [decodeTransactions, hDec, hRest, Except.mapError, bind, Except.bind, pure,
          Except.pure]

/-! ## Payload to block to payload -/

private theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

private theorem pure_eq_ok {ε α : Type} {x y : α} : (pure x : Except ε α) = .ok y ↔ x = y := by
  simp [pure, Except.pure]

namespace ExecutionPayload

/-- The block of a payload has the payload's block hash, no ommers, and the fields of EIP-3675.

Its mix digest is the RANDAO mix of the payload, as EIP-4399 asks. -/
theorem toBlock_shape {hFork : fork < .glamsterdam} {p : ExecutionPayload fork}
    {beacon : Since .dencun fork Hash32} {requests : Since .pectra fork (List ByteArray)}
    {b : Block fork Transaction} (h : p.toBlock beacon requests hFork = .ok b) :
    b.header.hash = .ok p.blockHash ∧ b.ommers = [] ∧ b.header.ommersHash = EMPTY_OMMER_HASH ∧
      b.header.difficulty = 0 ∧ b.header.nonce = Vector.replicate 8 0 ∧
      b.header.prevRandao = p.prevRandao := by
  simp only [toBlock, toBlockUnchecked, toHeader, checkBlockHash, bind_ok_iff, pure_eq_ok,
    mapError_ok_iff] at h
  obtain ⟨_, ⟨txs, -, root, -, _, ⟨wr, -, rfl⟩, rfl⟩, _, ⟨computed, hHash, hCheck⟩, rfl⟩ := h
  have hComputed : computed = p.blockHash := by
    split at hCheck
    · assumption
    · cases hCheck
  subst hComputed
  exact ⟨hHash, rfl, rfl, rfl, rfl, rfl⟩

/-- A payload whose block hash is the hash of its header is the payload of its block. -/
theorem ofBlock_toBlock (hParis : .paris ≤ fork) {hFork : fork < .glamsterdam}
    {p : ExecutionPayload fork} {beacon : Since .dencun fork Hash32}
    {requests : Since .pectra fork (List ByteArray)} {b : Block fork Transaction}
    (h : p.toBlock beacon requests hFork = .ok b) : ofBlock hParis b = some p := by
  simp only [toBlock, toBlockUnchecked, toHeader, checkBlockHash, bind_ok_iff, pure_eq_ok,
    mapError_ok_iff] at h
  obtain ⟨_, ⟨txs, hTxs, root, -, _, ⟨wr, -, rfl⟩, rfl⟩, _, ⟨computed, hHash, hCheck⟩, rfl⟩ := h
  have hComputed : computed = p.blockHash := by
    split at hCheck
    · assumption
    · cases hCheck
  subst hComputed
  obtain ⟨hEnc, -⟩ := encode_of_decodeTransactions hTxs
  have hTime : (BitVec.ofNat 256 p.timestamp.toNat).toNat = p.timestamp.toNat := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans p.timestamp.toNat_lt (by decide))
  simp only [ofBlock, hEnc, hHash, Except.toOption, Option.bind_eq_bind, Option.bind_some, hTime]
  rw [ite_eq_left ⟨p.blockNumber.toNat_lt, p.gasLimit.toNat_lt, p.gasUsed.toNat_lt,
    p.timestamp.toNat_lt, p.baseFeePerGas.isLt⟩]
  cases p
  simp [pure]

/-- A block comes back from its payload when it has the shape that a payload gives.

It has no ommers, and the ommers hash, the difficulty and the nonce of EIP-3675.

Its fork has the kind of each transaction.

Its roots are those of its lists, and its requests hash is that of the request lists given. -/
theorem toBlock_ofBlock (hParis : .paris ≤ fork) (hFork : fork < .glamsterdam)
    {b : Block fork Transaction} {p : ExecutionPayload fork}
    (requests : Since .pectra fork (List ByteArray)) (h : ofBlock hParis b = some p)
    (hOmmers : b.ommers = []) (hOmmersHash : b.header.ommersHash = EMPTY_OMMER_HASH)
    (hDifficulty : b.header.difficulty = 0) (hNonce : b.header.nonce = Vector.replicate 8 0)
    (hForks : ∀ tx ∈ b.transactions, tx.fork ≤ fork)
    (hTransactionsRoot : transactionsRoot b.transactions = .ok b.header.transactionsRoot)
    (hWithdrawalsRoot :
      ∀ hf, withdrawalsRoot (b.withdrawals hf) = .ok (b.header.withdrawalsRoot hf))
    (hRequests : ∀ hf, b.header.requestsHash hf = requestsCommitment (requests hf)) :
    p.toBlock b.header.parentBeaconBlockRoot requests hFork = .ok b := by
  simp only [ofBlock, Except.toOption, Option.bind_eq_bind] at h
  cases hBytes : b.transactions.mapM encodeTransaction with
  | error => simp [hBytes] at h
  | ok bytes =>
  cases hHash : b.header.hash with
  | error => simp [hBytes, hHash] at h
  | ok blockHash =>
  simp only [hBytes, hHash, Option.bind_some] at h
  split at h
  · rename_i hBounds
    obtain ⟨hN, hG, hU, hT, hB⟩ := hBounds
    simp only [pure, Option.some.injEq] at h
    subst h
    have hDec := decodeTransactions_of_encode (index := 0) hBytes hForks
    have hRoot : indexedRoot bytes = .ok b.header.transactionsRoot := by
      simpa [transactionsRoot, hBytes, Except.mapError, bind, Except.bind] using hTransactionsRoot
    have hWr : sinceM (fork := fork) (fun hf => (withdrawalsRoot (b.withdrawals hf)).mapError
        fun _ => PayloadError.noEncoding) = .ok b.header.withdrawalsRoot :=
      sinceM_eq_ok fun hf => by simp [hWithdrawalsRoot hf, Except.mapError]
    simp only [Except.mapError] at hWr
    simp only [toBlock, toBlockUnchecked, toHeader, checkBlockHash, hDec, hRoot, bind,
      Except.bind, Except.mapError, pure, Except.pure, hWr]
    have hTime :
        BitVec.ofNat 256 b.header.timestamp.toNat.toUInt64.toNat = b.header.timestamp := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, toNat_toUInt64 hT]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    have hBase : ∀ x, (BitVec.ofNat 256 (b.header.baseFeePerGas x)).toNat =
        b.header.baseFeePerGas x := fun x => by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hB]
    have hHeader : ({ b.header with
        ommersHash := EMPTY_OMMER_HASH, difficulty := 0,
        number := b.header.number.toUInt64.toNat, gasLimit := b.header.gasLimit.toUInt64.toNat,
        gasUsed := b.header.gasUsed.toUInt64.toNat,
        timestamp := BitVec.ofNat 256 b.header.timestamp.toNat.toUInt64.toNat,
        nonce := Vector.replicate 8 0,
        baseFeePerGas := fun x => (BitVec.ofNat 256 (b.header.baseFeePerGas x)).toNat,
        requestsHash := fun hf => requestsCommitment (requests hf),
        blockAccessListHash := fun hf => absurd (Nat.lt_of_lt_of_le hFork hf) (Nat.lt_irrefl _),
        slotNumber := fun hf => absurd (Nat.lt_of_lt_of_le hFork hf) (Nat.lt_irrefl _) } :
        Header fork) = b.header := by
      obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, access, slot⟩,
        txs, ommers, ws⟩ := b
      dsimp only at *
      subst hOmmersHash hDifficulty hNonce
      simp only [toNat_toUInt64 hN, toNat_toUInt64 hG, toNat_toUInt64 hU, hTime, hBase,
        ← hRequests]
      have hGlam : ¬Fork.glamsterdam ≤ fork := fun hf =>
        Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hFork hf)
      obtain rfl := Since.eq_of_not_le hGlam access
        fun hf => absurd (Nat.lt_of_lt_of_le hFork hf) (Nat.lt_irrefl _)
      obtain rfl := Since.eq_of_not_le hGlam slot
        fun hf => absurd (Nat.lt_of_lt_of_le hFork hf) (Nat.lt_irrefl _)
      rfl
    dsimp only at hHeader
    rw [hHeader]
    simp only [hHash, ite_true]
    obtain ⟨header, txs, ommers, ws⟩ := b
    dsimp only at hOmmers
    subst hOmmers
    rfl
  · cases h

end ExecutionPayload

end EthLib.Engine
