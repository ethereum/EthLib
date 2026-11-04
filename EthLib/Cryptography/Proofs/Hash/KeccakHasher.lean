module

public import EthLib.Cryptography.Proofs.Hash.Keccak

/-!
# Proofs: incremental Keccak-256

A hasher that absorbs a message in pieces gives the Keccak-256 digest of the whole message.

The pieces can be cut anywhere, since a block that two pieces share is absorbed once it is full.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

open Internal

/-! ## Blocks -/

/-- Cutting `m + n` blocks is cutting `m`, then `n` from the rest. -/
theorem chunks_add (k m n : Nat) (bytes : List UInt8) :
    chunks k (m + n) bytes = chunks k m bytes ++ chunks k n (bytes.drop (k * m)) := by
  induction m generalizing bytes with
  | zero => simp [chunks]
  | succ m ih =>
    rw [Nat.succ_add, chunks, chunks, ih, List.drop_drop, Nat.mul_succ, Nat.add_comm k (k * m)]
    rfl

/-- Blocks that lie inside a prefix ignore the bytes after it. -/
theorem chunks_append (k n : Nat) (bytes more : List UInt8) (inside : k * n ≤ bytes.length) :
    chunks k n (bytes ++ more) = chunks k n bytes := by
  induction n generalizing bytes with
  | zero => rfl
  | succ n ih =>
    rw [chunks, chunks, List.take_append_of_le_length (by rw [Nat.mul_succ] at inside; omega),
      List.drop_append_of_le_length (by rw [Nat.mul_succ] at inside; omega),
      ih _ (by rw [List.length_drop, Nat.mul_succ] at *; omega)]

/-- Absorbing two runs of blocks is absorbing them one after the other. -/
theorem absorbBlocks_append (f : State → State) (S : State) (a b : List (List UInt8)) :
    absorbBlocks f S (a ++ b) = absorbBlocks f (absorbBlocks f S a) b := by
  simp [absorbBlocks, List.foldl_append]

/-- The padding reads its length only mod the rate. -/
theorem padding_mod (rate len : Nat) : padding rate (len % rate) = padding rate len := by
  apply ByteArray.ext
  apply Array.ext
  · simp [padding]
  · intro i _ _
    simp [padding, paddingByte]

/-! ## The hasher -/

/-- After `q` whole blocks, the blocks of the rest follow, and so do the bytes after them. -/
theorem chunks_blocks_append (q n : Nat) (blocks rest : List UInt8)
    (whole : blocks.length = RATE * q) :
    chunks RATE (q + n) (blocks ++ rest) = chunks RATE q blocks ++ chunks RATE n rest ∧
      (blocks ++ rest).drop (RATE * (q + n)) = rest.drop (RATE * n) := by
  constructor
  · rw [chunks_add, chunks_append _ _ _ _ (by omega), ← whole, List.drop_left]
  · rw [Nat.mul_add, ← List.drop_drop, ← whole, List.drop_left]

/-- Absorbing two pieces is absorbing the two of them at once. -/
theorem absorb_absorb (h : Hasher) (a b : ByteArray) :
    (h.absorb a).absorb b = h.absorb (a ++ b) := by
  simp only [Hasher.absorb, ByteArray.data_append, Array.toList_append, ← List.append_assoc]
  -- The bytes are their whole blocks, then the bytes after them.
  generalize h.pending ++ a.data.toList = bytes
  generalize b.data.toList = more
  have hle : RATE * (bytes.length / RATE) ≤ bytes.length := Nat.mul_div_le _ _
  have hlen :
      (bytes.take (RATE * (bytes.length / RATE))).length = RATE * (bytes.length / RATE) := by
    rw [List.length_take]; omega
  have hsplit : bytes ++ more
      = bytes.take (RATE * (bytes.length / RATE))
        ++ (bytes.drop (RATE * (bytes.length / RATE)) ++ more) := by
    rw [← List.append_assoc, List.take_append_drop]
  have hcount : (bytes ++ more).length / RATE = bytes.length / RATE
      + (bytes.drop (RATE * (bytes.length / RATE)) ++ more).length / RATE := by
    rw [hsplit, List.length_append, hlen, Nat.add_comm, Nat.add_mul_div_left _ _ (by decide)]
    omega
  have hfirst : chunks RATE (bytes.length / RATE) bytes
      = chunks RATE (bytes.length / RATE) (bytes.take (RATE * (bytes.length / RATE))) := by
    have h := chunks_append RATE (bytes.length / RATE) (bytes.take (RATE * (bytes.length / RATE)))
      (bytes.drop (RATE * (bytes.length / RATE))) (by omega)
    rwa [List.take_append_drop] at h
  obtain ⟨hc, hd⟩ := chunks_blocks_append (bytes.length / RATE)
    ((bytes.drop (RATE * (bytes.length / RATE)) ++ more).length / RATE) _ _ hlen
  rw [hcount, hsplit, hc, hd, absorbBlocks_append, hfirst]

/-- The digest of a hasher that absorbed one message is its Keccak-256. -/
theorem digest_absorb_empty (msg : ByteArray) :
    (Hasher.empty.absorb msg).digest = keccak256 msg := by
  simp only [Hasher.absorb, Hasher.digest, Hasher.empty, List.nil_append, keccak256, spongeAbsorb,
    pad, ByteArray.data_append, Array.toList_append, blockCount]
  generalize hl : msg.data.toList = bytes
  have hsize : msg.size = bytes.length := by rw [← hl, Array.length_toList, ByteArray.size_data]
  rw [hsize]
  have hle : RATE * (bytes.length / RATE) ≤ bytes.length := Nat.mul_div_le _ _
  have hlen :
      (bytes.take (RATE * (bytes.length / RATE))).length = RATE * (bytes.length / RATE) := by
    rw [List.length_take]; omega
  -- The bytes after the whole blocks are `len mod 136` long, so the padding is the same.
  have hpend : (bytes.drop (RATE * (bytes.length / RATE))).length = bytes.length % RATE := by
    rw [List.length_drop]; have := Nat.div_add_mod bytes.length RATE; omega
  rw [hpend, padding_mod]
  -- The last block is those bytes and the padding: exactly one block.
  have hlast :
      (bytes.drop (RATE * (bytes.length / RATE)) ++ (padding RATE bytes.length).data.toList).length
      = RATE := by
    have := Nat.mod_lt bytes.length (show 0 < RATE by decide)
    have hpad : (padding RATE bytes.length).data.toList.length = RATE - bytes.length % RATE :=
      (Array.length_toList).trans (size_padding _ _)
    rw [List.length_append, hpend, hpad]
    omega
  have hsplit : bytes ++ (padding RATE bytes.length).data.toList
      = bytes.take (RATE * (bytes.length / RATE))
        ++ (bytes.drop (RATE * (bytes.length / RATE))
          ++ (padding RATE bytes.length).data.toList) := by
    rw [← List.append_assoc, List.take_append_drop]
  have hfirst : chunks RATE (bytes.length / RATE) bytes
      = chunks RATE (bytes.length / RATE) (bytes.take (RATE * (bytes.length / RATE))) := by
    have h := chunks_append RATE (bytes.length / RATE) (bytes.take (RATE * (bytes.length / RATE)))
      (bytes.drop (RATE * (bytes.length / RATE))) (by omega)
    rwa [List.take_append_drop] at h
  rw [hsplit, (chunks_blocks_append _ 1 _ _ hlen).1, absorbBlocks_append, hfirst]
  -- One block of 136 bytes is cut as itself.
  simp only [chunks, List.take_of_length_le (Nat.le_of_eq hlast)]

/-- The digest after `m₁`, then `m₂`, is Keccak-256 of `m₁ ++ m₂`. -/
theorem digest_absorb_absorb (m₁ m₂ : ByteArray) :
    ((Hasher.empty.absorb m₁).absorb m₂).digest = keccak256 (m₁ ++ m₂) := by
  rw [absorb_absorb, digest_absorb_empty]

end EthLib.Cryptography.Hash.Keccak
