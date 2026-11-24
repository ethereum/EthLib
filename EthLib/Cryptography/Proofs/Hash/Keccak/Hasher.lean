module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.Proofs.Hash.Keccak.Basic

/-!
# Proofs: incremental Keccak-256

A hasher that absorbs a message in pieces gives the Keccak-256 digest of the whole message.

The pieces can be cut anywhere, since a block that two pieces share is absorbed once it is full.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

open EthLib.Base (byteAtOrZero byteAtOrZero_append byteAtOrZero_extract eq_of_byteAtOrZero)
open Internal

/-! ## Blocks -/

/-- A block reads only its own `rate` bytes, when the rate is a whole number of lanes. -/
theorem absorbBlock_congr {rate : Nat} (lanes : 8 ∣ rate) (S : State) {a b : ByteArray}
    {s t : Nat} (h : ∀ j < rate, byteAtOrZero a (s + j) = byteAtOrZero b (t + j)) :
    absorbBlock rate S (laneAt a) s = absorbBlock rate S (laneAt b) t := by
  have hlane : blockLane rate (laneAt a) s = blockLane rate (laneAt b) t := by
    funext i
    unfold blockLane
    split
    · obtain ⟨m, rfl⟩ := lanes
      apply laneAt_congr
      intro k hk
      rw [Nat.add_assoc, Nat.add_assoc]
      exact h _ (by omega)
    · rfl
  simp only [absorbBlock, hlane]

/-- Absorbing `n` blocks reads only their `rate * n` bytes. -/
theorem absorbBlocks_congr (f : State → State) {rate : Nat} (lanes : 8 ∣ rate) (n : Nat)
    (S : State) {a b : ByteArray} {s t : Nat}
    (h : ∀ j < rate * n, byteAtOrZero a (s + j) = byteAtOrZero b (t + j)) :
    absorbBlocks f rate (laneAt a) n s S = absorbBlocks f rate (laneAt b) n t S := by
  induction n generalizing s t S with
  | zero => rfl
  | succ n ih =>
    rw [absorbBlocks, absorbBlocks,
      absorbBlock_congr lanes S (fun j hj => h j (by rw [Nat.mul_succ]; omega))]
    apply ih
    intro j hj
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm rate j]
    exact h _ (by rw [Nat.mul_succ]; omega)

/-- The padding reads its length only mod the rate. -/
theorem padding_mod (rate len : Nat) : padding rate (len % rate) = padding rate len := by
  unfold padding paddingByte
  rw [Nat.mod_mod]

/-! ## The hasher -/

/-- After an absorb, the pending bytes number the bytes not yet absorbed, mod the rate. -/
theorem size_pending_absorb (h : Hasher256) (data : ByteArray) :
    (h.absorb data).pending.size = (h.pending.size + data.size) % RATE_256 := by
  simp only [Hasher256.absorb, ByteArray.size_extract, ByteArray.size_append, Nat.min_self,
    RATE_256]
  omega

/-- Every hasher reached from the empty one by absorbs keeps fewer pending bytes than the rate. -/
theorem size_pending_lt (pieces : List ByteArray) :
    (pieces.foldl Hasher256.absorb Hasher256.empty).pending.size < RATE_256 := by
  suffices ∀ h : Hasher256, h.pending.size < RATE_256 →
      (pieces.foldl Hasher256.absorb h).pending.size < RATE_256 from
    this _ (by simp [Hasher256.empty, RATE_256])
  induction pieces with
  | nil => exact fun _ h => h
  | cons data pieces ih =>
    intro h _
    exact ih _ (by rw [size_pending_absorb]; exact Nat.mod_lt _ (by decide))

/-- Absorbing two pieces is absorbing the two of them at once. -/
theorem absorb_absorb (h : Hasher256) (a b : ByteArray) :
    (h.absorb a).absorb b = h.absorb (a ++ b) := by
  simp only [Hasher256.absorb, ← ByteArray.append_assoc]
  generalize h.pending ++ a = bytes
  -- The first piece leaves `q` whole blocks, then `r` bytes, which the second piece follows.
  generalize hq : bytes.size / RATE_256 = q
  have hle : RATE_256 * q ≤ bytes.size := hq ▸ Nat.mul_div_le _ _
  have hrest : ∀ k, byteAtOrZero (bytes.extract (RATE_256 * q) bytes.size ++ b) k
      = byteAtOrZero (bytes ++ b) (RATE_256 * q + k) := by
    intro k
    rw [byteAtOrZero_append, byteAtOrZero_append, ByteArray.size_extract, byteAtOrZero_extract, Nat.min_self]
    by_cases hk : RATE_256 * q + k < bytes.size
    · rw [ite_eq_left (by omega), ite_eq_left hk, ite_eq_left hk]
    · rw [ite_eq_right (by omega), ite_eq_right hk,
        show k - (bytes.size - RATE_256 * q) = RATE_256 * q + k - bytes.size by omega]
  have hsize :
      (bytes.extract (RATE_256 * q) bytes.size ++ b).size = (bytes ++ b).size - RATE_256 * q := by
    simp only [ByteArray.size_append, ByteArray.size_extract, Nat.min_self]
    omega
  -- The whole message has `q` blocks, then the blocks of the rest.
  generalize hn : (bytes.extract (RATE_256 * q) bytes.size ++ b).size / RATE_256 = n
  have hcount : (bytes ++ b).size / RATE_256 = q + n := by
    have hd := Nat.div_add_mod bytes.size RATE_256
    have e1 :
        bytes.size + b.size - RATE_256 * (bytes.size / RATE_256)
          = bytes.size % RATE_256 + b.size := by
      omega
    have e2 :
        bytes.size + b.size
          = (bytes.size % RATE_256 + b.size) + RATE_256 * (bytes.size / RATE_256) := by
      omega
    rw [← hn, hsize, ← hq, ByteArray.size_append, e1, e2, Nat.add_mul_div_left _ _ (by decide),
      Nat.add_comm]
  rw [hcount]
  congr 1
  · -- The first `q` blocks lie inside the first piece, and the next `n` follow them.
    have hfirst : absorbBlocks keccakF RATE_256 (laneAt bytes) q 0 h.state
        = absorbBlocks keccakF RATE_256 (laneAt (bytes ++ b)) q 0 h.state :=
      absorbBlocks_congr _ lanes_rate _ _ fun j hj => by
        rw [Nat.zero_add, byteAtOrZero_append, ite_eq_left (by omega)]
    rw [absorbBlocks_add, Nat.zero_add, hfirst]
    exact absorbBlocks_congr _ lanes_rate _ _ fun j _ => by rw [Nat.zero_add, hrest]
  · -- Both keep the bytes after the last whole block.
    apply eq_of_byteAtOrZero
    · simp only [ByteArray.size_extract, Nat.min_self, hsize, Nat.mul_add]
      omega
    · intro j
      rw [byteAtOrZero_extract, byteAtOrZero_extract, Nat.min_self, Nat.min_self, hsize, hrest, Nat.mul_add,
        Nat.add_assoc]
      by_cases hj : RATE_256 * q + (RATE_256 * n + j) < (bytes ++ b).size
      · rw [ite_eq_left (by omega), ite_eq_left hj]
      · rw [ite_eq_right (by omega), ite_eq_right hj]

/-- The digest of a hasher that absorbed one message is its Keccak-256. -/
theorem digest_absorb_empty (msg : ByteArray) :
    (Hasher256.empty.absorb msg).digest = keccak256 msg := by
  simp only [Hasher256.absorb, Hasher256.digest, Hasher256.empty, ByteArray.empty_append,
    keccak256_eq_squeeze256, spongeAbsorb_eq, blockCount]
  generalize hq : msg.size / RATE_256 = q
  have hle : RATE_256 * q ≤ msg.size := hq ▸ Nat.mul_div_le _ _
  -- The bytes after the whole blocks are `len mod 136` long, so the padding is the same.
  have hpend : (msg.extract (RATE_256 * q) msg.size).size = msg.size % RATE_256 := by
    rw [ByteArray.size_extract, Nat.min_self, ← hq]
    have := Nat.div_add_mod msg.size RATE_256
    omega
  -- The whole blocks lie inside the message.
  have hfirst : absorbBlocks keccakF RATE_256 (laneAt msg) q 0 State.zero
      = absorbBlocks keccakF RATE_256 (laneAt (pad RATE_256 msg)) q 0 State.zero :=
    (absorbBlocks_pad keccakF RATE_256 msg q 0 State.zero (by rw [Nat.zero_add]; exact hle)).symm
  rw [hpend, padding_mod, absorbBlocks_add, Nat.zero_add, hfirst]
  -- The last block is the bytes after them, then the padding.
  refine congrArg squeeze256 (absorbBlocks_congr _ lanes_rate _ _ fun j _ => ?_)
  rw [pad, byteAtOrZero_append, byteAtOrZero_append, ByteArray.size_extract, Nat.min_self, byteAtOrZero_extract,
    Nat.min_self, Nat.zero_add]
  by_cases hj : RATE_256 * q + j < msg.size
  · rw [ite_eq_left (by omega), ite_eq_left hj, ite_eq_left hj]
  · rw [ite_eq_right (by omega), ite_eq_right hj,
      show j - (msg.size - RATE_256 * q) = RATE_256 * q + j - msg.size by omega]

/-- The digest after `m₁`, then `m₂`, is Keccak-256 of `m₁ ++ m₂`. -/
theorem digest_absorb_absorb (m₁ m₂ : ByteArray) :
    ((Hasher256.empty.absorb m₁).absorb m₂).digest = keccak256 (m₁ ++ m₂) := by
  rw [absorb_absorb, digest_absorb_empty]

end EthLib.Cryptography.Hash.Keccak
