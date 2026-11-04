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

/-! ## Bytes -/

/-- A byte of two strings joined is a byte of the first, or of the second past its end. -/
theorem byteAt_append (a b : ByteArray) (i : Nat) :
    byteAt (a ++ b) i = if i < a.size then byteAt a i else byteAt b (i - a.size) := by
  have hs := @ByteArray.size_append a b
  unfold byteAt
  by_cases ha : i < a.size
  · rw [ite_eq_left ha, dite_eq_left ha, dite_eq_left (show i < (a ++ b).size by omega),
      ByteArray.getElem_append_left ha]
  · rw [ite_eq_right ha]
    by_cases hb : i - a.size < b.size
    · rw [dite_eq_left hb, dite_eq_left (show i < (a ++ b).size by omega),
        ByteArray.getElem_append_right (Nat.le_of_not_lt ha)]
    · rw [dite_eq_right hb, dite_eq_right (show ¬i < (a ++ b).size by omega)]

/-- A byte of a slice is the byte at the same offset from its start, or zero past its end. -/
theorem byteAt_extract (b : ByteArray) (start stop j : Nat) :
    byteAt (b.extract start stop) j
      = if start + j < min stop b.size then byteAt b (start + j) else 0 := by
  have hs := @ByteArray.size_extract b start stop
  have hm := Nat.min_le_right stop b.size
  unfold byteAt
  by_cases hj : start + j < min stop b.size
  · rw [ite_eq_left hj, dite_eq_left (show j < (b.extract start stop).size by omega),
      dite_eq_left (show start + j < b.size by omega), ByteArray.getElem_extract]
  · rw [ite_eq_right hj, dite_eq_right (show ¬j < (b.extract start stop).size by omega)]

/-- Two strings of one length are equal when they agree on every byte. -/
theorem eq_of_byteAt {a b : ByteArray} (size : a.size = b.size)
    (bytes : ∀ i, byteAt a i = byteAt b i) : a = b := by
  apply ByteArray.ext
  apply Array.ext size
  intro i ha hb
  have h := bytes i
  unfold byteAt at h
  rw [dite_eq_left (show i < a.size from ha), dite_eq_left (show i < b.size from hb)] at h
  exact h

/-! ## Blocks -/

/-- A lane reads only its own 8 bytes. -/
theorem laneAt_congr {a b : ByteArray} {s t : Nat}
    (h : ∀ k < 8, byteAt a (s + k) = byteAt b (t + k)) : laneAt a s = laneAt b t := by
  have h0 : byteAt a s = byteAt b t := by simpa using h 0 (by omega)
  unfold laneAt
  rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega)]

/-- A block reads only its own `rate` bytes, when the rate is a whole number of lanes. -/
theorem absorbBlock_congr {rate : Nat} (lanes : 8 ∣ rate) (S : State) {a b : ByteArray}
    {s t : Nat} (h : ∀ j < rate, byteAt a (s + j) = byteAt b (t + j)) :
    absorbBlock rate S a s = absorbBlock rate S b t := by
  have hlane : blockLane rate a s = blockLane rate b t := by
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

/-- Absorbing `m + n` blocks absorbs the first `m`, then the `n` after them. -/
theorem absorbBlocks_add (f : State → State) (rate : Nat) (bytes : ByteArray) (m n start : Nat)
    (S : State) :
    absorbBlocks f rate bytes (m + n) start S
      = absorbBlocks f rate bytes n (start + rate * m) (absorbBlocks f rate bytes m start S) := by
  induction m generalizing start S with
  | zero => simp [absorbBlocks]
  | succ m ih =>
    rw [Nat.succ_add, absorbBlocks, ih, absorbBlocks, Nat.mul_succ, Nat.add_comm (rate * m),
      Nat.add_assoc]

/-- Absorbing `n` blocks reads only their `rate * n` bytes. -/
theorem absorbBlocks_congr (f : State → State) {rate : Nat} (lanes : 8 ∣ rate) (n : Nat)
    (S : State) {a b : ByteArray} {s t : Nat}
    (h : ∀ j < rate * n, byteAt a (s + j) = byteAt b (t + j)) :
    absorbBlocks f rate a n s S = absorbBlocks f rate b n t S := by
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
  apply ByteArray.ext
  apply Array.ext
  · simp [padding]
  · intro i _ _
    simp [padding, paddingByte]

/-! ## The hasher -/

/-- The rate of Keccak-256 is a whole number of lanes. -/
theorem lanes_rate : 8 ∣ RATE := ⟨17, rfl⟩

/-- Absorbing two pieces is absorbing the two of them at once. -/
theorem absorb_absorb (h : Hasher) (a b : ByteArray) :
    (h.absorb a).absorb b = h.absorb (a ++ b) := by
  simp only [Hasher.absorb, ← ByteArray.append_assoc]
  generalize h.pending ++ a = bytes
  -- The first piece leaves `q` whole blocks, then `r` bytes, which the second piece follows.
  generalize hq : bytes.size / RATE = q
  have hle : RATE * q ≤ bytes.size := hq ▸ Nat.mul_div_le _ _
  have hrest : ∀ k, byteAt (bytes.extract (RATE * q) bytes.size ++ b) k
      = byteAt (bytes ++ b) (RATE * q + k) := by
    intro k
    rw [byteAt_append, byteAt_append, ByteArray.size_extract, byteAt_extract, Nat.min_self]
    by_cases hk : RATE * q + k < bytes.size
    · rw [ite_eq_left (by omega), ite_eq_left hk, ite_eq_left hk]
    · rw [ite_eq_right (by omega), ite_eq_right hk,
        show k - (bytes.size - RATE * q) = RATE * q + k - bytes.size by omega]
  have hsize : (bytes.extract (RATE * q) bytes.size ++ b).size = (bytes ++ b).size - RATE * q := by
    simp only [ByteArray.size_append, ByteArray.size_extract, Nat.min_self]
    omega
  -- The whole message has `q` blocks, then the blocks of the rest.
  generalize hn : (bytes.extract (RATE * q) bytes.size ++ b).size / RATE = n
  have hcount : (bytes ++ b).size / RATE = q + n := by
    have hd := Nat.div_add_mod bytes.size RATE
    have e1 : bytes.size + b.size - RATE * (bytes.size / RATE) = bytes.size % RATE + b.size := by
      omega
    have e2 : bytes.size + b.size = (bytes.size % RATE + b.size) + RATE * (bytes.size / RATE) := by
      omega
    rw [← hn, hsize, ← hq, ByteArray.size_append, e1, e2, Nat.add_mul_div_left _ _ (by decide),
      Nat.add_comm]
  rw [hcount]
  congr 1
  · -- The first `q` blocks lie inside the first piece, and the next `n` follow them.
    have hfirst : absorbBlocks keccakF RATE bytes q 0 h.state
        = absorbBlocks keccakF RATE (bytes ++ b) q 0 h.state :=
      absorbBlocks_congr _ lanes_rate _ _ fun j hj => by
        rw [Nat.zero_add, byteAt_append, ite_eq_left (by omega)]
    rw [absorbBlocks_add, Nat.zero_add, hfirst]
    exact absorbBlocks_congr _ lanes_rate _ _ fun j _ => by rw [Nat.zero_add, hrest]
  · -- Both keep the bytes after the last whole block.
    apply eq_of_byteAt
    · simp only [ByteArray.size_extract, Nat.min_self, hsize, Nat.mul_add]
      omega
    · intro j
      rw [byteAt_extract, byteAt_extract, Nat.min_self, Nat.min_self, hsize, hrest, Nat.mul_add,
        Nat.add_assoc]
      by_cases hj : RATE * q + (RATE * n + j) < (bytes ++ b).size
      · rw [ite_eq_left (by omega), ite_eq_left hj]
      · rw [ite_eq_right (by omega), ite_eq_right hj]

/-- The digest of a hasher that absorbed one message is its Keccak-256. -/
theorem digest_absorb_empty (msg : ByteArray) :
    (Hasher.empty.absorb msg).digest = keccak256 msg := by
  simp only [Hasher.absorb, Hasher.digest, Hasher.empty, ByteArray.empty_append, keccak256,
    spongeAbsorb, blockCount]
  generalize hq : msg.size / RATE = q
  have hle : RATE * q ≤ msg.size := hq ▸ Nat.mul_div_le _ _
  -- The bytes after the whole blocks are `len mod 136` long, so the padding is the same.
  have hpend : (msg.extract (RATE * q) msg.size).size = msg.size % RATE := by
    rw [ByteArray.size_extract, Nat.min_self, ← hq]
    have := Nat.div_add_mod msg.size RATE
    omega
  -- The whole blocks lie inside the message.
  have hfirst : absorbBlocks keccakF RATE msg q 0 State.zero
      = absorbBlocks keccakF RATE (pad RATE msg) q 0 State.zero :=
    absorbBlocks_congr _ lanes_rate _ _ fun j hj => by
      rw [Nat.zero_add, pad, byteAt_append, ite_eq_left (by omega)]
  rw [hpend, padding_mod, absorbBlocks_add, Nat.zero_add, hfirst]
  -- The last block is the bytes after them, then the padding.
  refine congrArg squeeze (absorbBlocks_congr _ lanes_rate _ _ fun j _ => ?_)
  rw [pad, byteAt_append, byteAt_append, ByteArray.size_extract, Nat.min_self, byteAt_extract,
    Nat.min_self, Nat.zero_add]
  by_cases hj : RATE * q + j < msg.size
  · rw [ite_eq_left (by omega), ite_eq_left hj, ite_eq_left hj]
  · rw [ite_eq_right (by omega), ite_eq_right hj,
      show j - (msg.size - RATE * q) = RATE * q + j - msg.size by omega]

/-- The digest after `m₁`, then `m₂`, is Keccak-256 of `m₁ ++ m₂`. -/
theorem digest_absorb_absorb (m₁ m₂ : ByteArray) :
    ((Hasher.empty.absorb m₁).absorb m₂).digest = keccak256 (m₁ ++ m₂) := by
  rw [absorb_absorb, digest_absorb_empty]

end EthLib.Cryptography.Hash.Keccak
