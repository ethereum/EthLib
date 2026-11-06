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

From Glamsterdam, the block access list of the method must be the RLP form of a block access list.

The header then holds the Keccak-256 hash of its bytes, and the slot number of the method.

Bytes that are not such a form give no block, with the reason that names the list.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

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
theorem toBlock_shape {p : ExecutionPayload fork}
    {beacon : Since .dencun fork Hash32} {requests : Since .pectra fork (List ByteArray)}
    {accessList : Since .glamsterdam fork ByteArray} {slot : Since .glamsterdam fork UInt64}
    {b : Block fork Transaction} (h : p.toBlock beacon requests accessList slot = .ok b) :
    b.header.hash = .ok p.blockHash ∧ b.ommers = [] ∧ b.header.ommersHash = EMPTY_OMMER_HASH ∧
      b.header.difficulty = 0 ∧ b.header.nonce = Vector.replicate 8 0 ∧
      b.header.prevRandao = p.prevRandao := by
  simp only [toBlock, toBlockUnchecked, toHeader, checkBlockHash, bind_ok_iff, pure_eq_ok,
    mapError_ok_iff] at h
  obtain ⟨_, ⟨txs, -, root, -, _, -, _, ⟨wr, -, rfl⟩, rfl⟩, _, ⟨computed, hHash, hCheck⟩, rfl⟩ :=
    h
  have hComputed : computed = p.blockHash := by
    split at hCheck
    · assumption
    · cases hCheck
  subst hComputed
  exact ⟨hHash, rfl, rfl, rfl, rfl, rfl⟩

/-- A payload whose block hash is the hash of its header is the payload of its block. -/
theorem ofBlock_toBlock (hParis : .paris ≤ fork)
    {p : ExecutionPayload fork} {beacon : Since .dencun fork Hash32}
    {requests : Since .pectra fork (List ByteArray)}
    {accessList : Since .glamsterdam fork ByteArray} {slot : Since .glamsterdam fork UInt64}
    {b : Block fork Transaction}
    (h : p.toBlock beacon requests accessList slot = .ok b) : ofBlock hParis b = some p := by
  simp only [toBlock, toBlockUnchecked, toHeader, checkBlockHash, bind_ok_iff, pure_eq_ok,
    mapError_ok_iff] at h
  obtain ⟨_, ⟨txs, hTxs, root, -, _, -, _, ⟨wr, -, rfl⟩, rfl⟩, _, ⟨computed, hHash, hCheck⟩, rfl⟩ :=
    h
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

Its roots are those of its lists, and its requests hash is that of the request lists given.

From Glamsterdam, its access list hash is that of the bytes given, and so is its slot number. -/
theorem toBlock_ofBlock (hParis : .paris ≤ fork)
    {b : Block fork Transaction} {p : ExecutionPayload fork}
    (requests : Since .pectra fork (List ByteArray))
    (accessList : Since .glamsterdam fork ByteArray) (slot : Since .glamsterdam fork UInt64)
    (h : ofBlock hParis b = some p)
    (hOmmers : b.ommers = []) (hOmmersHash : b.header.ommersHash = EMPTY_OMMER_HASH)
    (hDifficulty : b.header.difficulty = 0) (hNonce : b.header.nonce = Vector.replicate 8 0)
    (hForks : ∀ tx ∈ b.transactions, tx.fork ≤ fork)
    (hTransactionsRoot : transactionsRoot b.transactions = .ok b.header.transactionsRoot)
    (hWithdrawalsRoot :
      ∀ hf, withdrawalsRoot (b.withdrawals hf) = .ok (b.header.withdrawalsRoot hf))
    (hRequests : ∀ hf, b.header.requestsHash hf = requestsCommitment (requests hf))
    (hAccessList :
      ∀ hf, blockAccessListHashOf (accessList hf) = .ok (b.header.blockAccessListHash hf))
    (hSlot : ∀ hf, slot hf = b.header.slotNumber hf) :
    p.toBlock b.header.parentBeaconBlockRoot requests accessList slot = .ok b := by
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
    have hAl : sinceM (fork := fork) (fun hf => blockAccessListHashOf (accessList hf)) =
        .ok b.header.blockAccessListHash := sinceM_eq_ok hAccessList
    have hSl : slot = b.header.slotNumber := funext hSlot
    subst hSl
    simp only [toBlock, toBlockUnchecked, toHeader, checkBlockHash, hDec, hRoot, bind,
      Except.bind, Except.mapError, pure, Except.pure, hWr, hAl]
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
        requestsHash := fun hf => requestsCommitment (requests hf) } :
        Header fork) = b.header := by
      obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
        txs, ommers, ws⟩ := b
      dsimp only at *
      subst hOmmersHash hDifficulty hNonce
      simp only [toNat_toUInt64 hN, toNat_toUInt64 hG, toNat_toUInt64 hU, hTime, hBase,
        ← hRequests]
    dsimp only at hHeader
    rw [hHeader]
    simp only [hHash, ite_true]
    obtain ⟨header, txs, ommers, ws⟩ := b
    dsimp only at hOmmers
    subst hOmmers
    rfl
  · cases h

/-! ## The block access list, from Glamsterdam -/

/-- A field that a step computed is the step's value at each fork that has the field. -/
theorem sinceM_apply {ε α : Type} {f : Fork} {g : f ≤ fork → Except ε α} {x : Since f fork α}
    (h : sinceM g = .ok x) (hf : f ≤ fork) : g hf = .ok (x hf) := by
  unfold sinceM at h
  rw [dite_eq_left hf] at h
  cases hg : g hf with
  | error e => simp [hg, Functor.map, Except.map] at h
  | ok a =>
    simp only [hg, Functor.map, Except.map] at h
    cases h
    rfl

/-- Bytes give the hash of a block access list exactly when they are the RLP form of one.

The hash is then the Keccak-256 hash of the bytes, as EIP-7928 writes. -/
theorem blockAccessListHashOf_eq_ok_iff (bytes : ByteArray) (hash : Hash32) :
    blockAccessListHashOf bytes = .ok hash ↔
      (∃ bal : BlockAccessList, Serialization.Rlp.Codec.decode bytes = .ok bal) ∧
        hash = keccak256 bytes := by
  unfold blockAccessListHashOf
  split
  · rename_i bal hbal
    constructor
    · intro h
      cases h
      exact ⟨⟨bal, hbal⟩, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl
  · rename_i e he
    simp only [reduceCtorEq, false_iff, not_and, he]
    rintro ⟨_, hbal⟩
    cases hbal

/-- Bytes that are not the RLP form of a block access list fail with the reason that names it. -/
theorem blockAccessListHashOf_eq_error_iff (bytes : ByteArray) (e : PayloadError) :
    blockAccessListHashOf bytes = .error e ↔
      (∀ bal : BlockAccessList, Serialization.Rlp.Codec.decode bytes ≠ .ok bal) ∧
        e = .invalidBlockAccessList := by
  unfold blockAccessListHashOf
  split
  · rename_i bal hbal
    simp only [reduceCtorEq, false_iff, not_and, hbal]
    exact fun h => absurd rfl (h bal)
  · rename_i err he
    constructor
    · intro h
      cases h
      exact ⟨fun _ hbal => (by rw [he] at hbal; cases hbal), rfl⟩
    · rintro ⟨-, rfl⟩
      rfl

/-- From Glamsterdam, the block of a payload holds the hash of the access list and the slot.

The access list is then the RLP form of a block access list. -/
theorem toBlock_glamsterdam {p : ExecutionPayload fork} {beacon : Since .dencun fork Hash32}
    {requests : Since .pectra fork (List ByteArray)}
    {accessList : Since .glamsterdam fork ByteArray} {slot : Since .glamsterdam fork UInt64}
    {b : Block fork Transaction} (h : p.toBlock beacon requests accessList slot = .ok b)
    (hf : .glamsterdam ≤ fork) :
    (∃ bal : BlockAccessList, Serialization.Rlp.Codec.decode (accessList hf) = .ok bal) ∧
      b.header.blockAccessListHash hf = keccak256 (accessList hf) ∧
      b.header.slotNumber hf = slot hf := by
  simp only [toBlock, toBlockUnchecked, toHeader, checkBlockHash, bind_ok_iff, pure_eq_ok,
    mapError_ok_iff] at h
  obtain ⟨_, ⟨txs, -, root, -, accessHash, hAccess, _, ⟨wr, -, rfl⟩, rfl⟩, -, -, rfl⟩ := h
  obtain ⟨hdecode, hhash⟩ :=
    (blockAccessListHashOf_eq_ok_iff _ _).mp (sinceM_apply hAccess hf)
  exact ⟨hdecode, hhash, rfl⟩

/-- From Glamsterdam, a payload whose access list is not the RLP form of one gives no block. -/
theorem toBlock_ne_ok_of_not_decode {p : ExecutionPayload fork}
    {beacon : Since .dencun fork Hash32} {requests : Since .pectra fork (List ByteArray)}
    {accessList : Since .glamsterdam fork ByteArray} {slot : Since .glamsterdam fork UInt64}
    (hf : .glamsterdam ≤ fork)
    (hbad : ∀ bal : BlockAccessList, Serialization.Rlp.Codec.decode (accessList hf) ≠ .ok bal)
    (b : Block fork Transaction) : p.toBlock beacon requests accessList slot ≠ .ok b := by
  intro h
  obtain ⟨⟨bal, hbal⟩, -⟩ := toBlock_glamsterdam h hf
  exact hbad bal hbal

end ExecutionPayload

end EthLib.Engine
