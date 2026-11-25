module

public import EthLib.Cryptography.Proofs.Hash.Keccak.Indifferentiability
public import EthLib.Cryptography.Proofs.Sponge.Indifferentiability
import EthLib.Base.Proofs.BitVec

/-!
# Proofs: Keccak-256 is indifferentiable from a random oracle

Keccak-256 is KECCAK[512] of FIPS 202 §5.2, with a 256-bit output.

It is the sponge of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge], §3.1.

Its rate of 1088 bits splits into the 256 bits of the digest and 832 more; its capacity has 512.

So the indifferentiability of the sponge, with that split, carries over to Keccak-256.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

open OracleComp OracleSpec ENNReal EthLib.Cryptography.LazyPermutation
  EthLib.Cryptography.Indifferentiability EthLib.Cryptography.Sponge

/-! ## Lanes as bits -/

/-- The sponge state of Keccak-256: 256 bits of digest, 832 more bits of rate, 512 of capacity. -/
abbrev SpongeState256 := SpongeState (BitVec 256) (BitVec 832) (BitVec 512)

/-- Four lanes as 256 bits: bit `64i + z` is bit `z` of lane `i`. -/
def lanesBits4 (a0 a1 a2 a3 : UInt64) : BitVec 256 :=
  a3.toBitVec ++ a2.toBitVec ++ a1.toBitVec ++ a0.toBitVec

/-- Eight lanes as 512 bits: bit `64i + z` is bit `z` of lane `i`. -/
def lanesBits8 (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) : BitVec 512 :=
  lanesBits4 a4 a5 a6 a7 ++ lanesBits4 a0 a1 a2 a3

/-- Thirteen lanes as 832 bits: bit `64i + z` is bit `z` of lane `i`. -/
def lanesBits13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : UInt64) : BitVec 832 :=
  a12.toBitVec ++ lanesBits4 a8 a9 a10 a11 ++ lanesBits8 a0 a1 a2 a3 a4 a5 a6 a7

/-- Lane `i` of a bit vector: its bits `64i` to `64i + 63`. -/
def laneOfBits {n : Nat} (v : BitVec n) (i : Nat) : UInt64 :=
  UInt64.ofBitVec (v.extractLsb' (64 * i) 64)

/-- Four lanes are determined by their 256 bits. -/
theorem lanesBits4_inj {a0 a1 a2 a3 b0 b1 b2 b3 : UInt64} :
    lanesBits4 a0 a1 a2 a3 = lanesBits4 b0 b1 b2 b3 ↔ a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  simp only [lanesBits4, Base.BitVec.append_inj_iff (w := 192) (v := 64),
    Base.BitVec.append_inj_iff (w := 128) (v := 64), Base.BitVec.append_inj_iff (w := 64) (v := 64),
    UInt64.toBitVec_inj]
  tauto

/-- Eight lanes are determined by their 512 bits. -/
theorem lanesBits8_inj {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt64} :
    lanesBits8 a0 a1 a2 a3 a4 a5 a6 a7 = lanesBits8 b0 b1 b2 b3 b4 b5 b6 b7 ↔
      a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  simp only [lanesBits8, Base.BitVec.append_inj_iff (w := 256) (v := 256), lanesBits4_inj]
  tauto

/-- Thirteen lanes are determined by their 832 bits. -/
theorem lanesBits13_inj {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : UInt64}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : UInt64} :
    lanesBits13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =
        lanesBits13 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 ↔
      a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 ∧
        a8 = b8 ∧ a9 = b9 ∧ a10 = b10 ∧ a11 = b11 ∧ a12 = b12 := by
  simp only [lanesBits13, Base.BitVec.append_inj_iff (w := 320) (v := 512),
    Base.BitVec.append_inj_iff (w := 64) (v := 256), lanesBits8_inj, lanesBits4_inj,
    UInt64.toBitVec_inj]
  tauto

/-- The four lanes of 256 bits give them back. -/
theorem lanesBits4_laneOfBits (v : BitVec 256) :
    lanesBits4 (laneOfBits v 0) (laneOfBits v 1) (laneOfBits v 2) (laneOfBits v 3) = v := by
  simp only [lanesBits4, laneOfBits, UInt64.toBitVec_ofBitVec]
  simp [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']

/-- XOR of four lanes as bits is XOR lane by lane. -/
theorem lanesBits4_xor (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    lanesBits4 a0 a1 a2 a3 ^^^ lanesBits4 b0 b1 b2 b3 =
      lanesBits4 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) := by
  simp only [lanesBits4, UInt64.toBitVec_xor]
  rw [BitVec.xor_append (w := 192) (v := 64), BitVec.xor_append (w := 128) (v := 64),
    BitVec.xor_append (w := 64) (v := 64)]

/-- XOR of eight lanes as bits is XOR lane by lane. -/
theorem lanesBits8_xor (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) :
    lanesBits8 a0 a1 a2 a3 a4 a5 a6 a7 ^^^ lanesBits8 b0 b1 b2 b3 b4 b5 b6 b7 =
      lanesBits8 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) (a4 ^^^ b4) (a5 ^^^ b5)
        (a6 ^^^ b6) (a7 ^^^ b7) := by
  simp only [lanesBits8]
  rw [BitVec.xor_append (w := 256) (v := 256), lanesBits4_xor, lanesBits4_xor]

/-- XOR of thirteen lanes as bits is XOR lane by lane. -/
theorem lanesBits13_xor (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : UInt64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : UInt64) :
    lanesBits13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 ^^^
        lanesBits13 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 =
      lanesBits13 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) (a4 ^^^ b4) (a5 ^^^ b5)
        (a6 ^^^ b6) (a7 ^^^ b7) (a8 ^^^ b8) (a9 ^^^ b9) (a10 ^^^ b10) (a11 ^^^ b11)
        (a12 ^^^ b12) := by
  simp only [lanesBits13]
  rw [BitVec.xor_append (w := 320) (v := 512), BitVec.xor_append (w := 64) (v := 256),
    lanesBits4_xor, lanesBits8_xor, UInt64.toBitVec_xor]

/-- Four zero lanes are 256 zero bits. -/
theorem lanesBits4_zero : lanesBits4 0 0 0 0 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [lanesBits4]

/-- Eight zero lanes are 512 zero bits. -/
theorem lanesBits8_zero : lanesBits8 0 0 0 0 0 0 0 0 = 0 := by
  rw [lanesBits8, lanesBits4_zero]
  exact BitVec.zero_append_zero (v := 256) (w := 256)

/-- Thirteen zero lanes are 832 zero bits. -/
theorem lanesBits13_zero : lanesBits13 0 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  rw [lanesBits13, lanesBits4_zero, lanesBits8_zero, UInt64.toBitVec_zero]
  exact (congrArg (· ++ (0 : BitVec 512)) (BitVec.zero_append_zero (v := 64) (w := 256))).trans
    (BitVec.zero_append_zero (v := 320) (w := 512))

/-! ## The state as a sponge state -/

/-- The state as a sponge state: lanes 0 to 3, lanes 4 to 16, then lanes 17 to 24.

Lane `i` holds bits `64 i` to `64 i + 63` of the three parts, read in that order. -/
def toSpongeState (S : State) : SpongeState256 :=
  -- The digest: the first 256 bits of the rate.
  ((lanesBits4 S.a0 S.a1 S.a2 S.a3,
    -- The other 832 bits of the rate of 1088 bits.
    lanesBits13 S.a4 S.a5 S.a6 S.a7 S.a8 S.a9 S.a10 S.a11 S.a12 S.a13 S.a14 S.a15 S.a16),
    -- The capacity of 512 bits.
    lanesBits8 S.a17 S.a18 S.a19 S.a20 S.a21 S.a22 S.a23 S.a24)

/-- The state of a sponge state: lane `i` is bits `64 i` to `64 i + 63` of its three parts. -/
def ofSpongeState (x : SpongeState256) : State :=
  ⟨laneOfBits x.1.1 0, laneOfBits x.1.1 1, laneOfBits x.1.1 2, laneOfBits x.1.1 3,
    laneOfBits x.1.2 0, laneOfBits x.1.2 1, laneOfBits x.1.2 2, laneOfBits x.1.2 3,
    laneOfBits x.1.2 4, laneOfBits x.1.2 5, laneOfBits x.1.2 6, laneOfBits x.1.2 7,
    laneOfBits x.1.2 8, laneOfBits x.1.2 9, laneOfBits x.1.2 10, laneOfBits x.1.2 11,
    laneOfBits x.1.2 12,
    laneOfBits x.2 0, laneOfBits x.2 1, laneOfBits x.2 2, laneOfBits x.2 3,
    laneOfBits x.2 4, laneOfBits x.2 5, laneOfBits x.2 6, laneOfBits x.2 7⟩

/-- A state is determined by its sponge state. -/
theorem toSpongeState_injective : Function.Injective toSpongeState := by
  intro S T h
  simp only [toSpongeState, Prod.mk.injEq, lanesBits4_inj, lanesBits8_inj, lanesBits13_inj] at h
  obtain ⟨⟨⟨h0, h1, h2, h3⟩, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩,
    h17, h18, h19, h20, h21, h22, h23, h24⟩ := h
  -- The two states agree lane by lane.
  cases S
  cases T
  rw [State.mk.injEq]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩

/-- The lanes of a sponge state give it back. -/
theorem toSpongeState_ofSpongeState (x : SpongeState256) : toSpongeState (ofSpongeState x) = x := by
  obtain ⟨⟨d, r⟩, c⟩ := x
  simp only [toSpongeState, ofSpongeState, lanesBits4, lanesBits8, lanesBits13, laneOfBits,
    UInt64.toBitVec_ofBitVec]
  simp [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']

/-- The sponge state of Keccak-256 has `2^1600` values, as the state has. -/
theorem card_spongeState256 : Fintype.card SpongeState256 = 2 ^ 1600 := by
  rw [Fintype.card_prod, Fintype.card_prod, ← FinEnum.card_eq_fintypeCard,
    ← FinEnum.card_eq_fintypeCard, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec,
    FinEnum.card_bitVec, FinEnum.card_bitVec, ← pow_add, ← pow_add]

/-- The Keccak state and the sponge state of Keccak-256 are in bijection, lane by lane. -/
def spongeEquiv : State ≃ SpongeState256 where
  toFun := toSpongeState
  invFun := ofSpongeState
  left_inv S := toSpongeState_injective (toSpongeState_ofSpongeState (toSpongeState S))
  right_inv := toSpongeState_ofSpongeState

/-- The zero state of Keccak is the zero sponge state. -/
theorem spongeEquiv_zero : spongeEquiv State.zero = ((0, 0), 0) := by
  simp only [spongeEquiv, Equiv.coe_fn_mk, toSpongeState, State.zero, lanesBits4_zero,
    lanesBits8_zero, lanesBits13_zero]

/-- Lanes 0 to 16 of a block at `start`, read as the rate of a sponge state. -/
def spongeBlock (read : Nat → UInt64) (start : Nat) : BitVec 256 × BitVec 832 :=
  (lanesBits4 (read start) (read (start + 8)) (read (start + 16)) (read (start + 24)),
    lanesBits13 (read (start + 32)) (read (start + 40)) (read (start + 48)) (read (start + 56))
      (read (start + 64)) (read (start + 72)) (read (start + 80)) (read (start + 88))
      (read (start + 96)) (read (start + 104)) (read (start + 112)) (read (start + 120))
      (read (start + 128)))

/-- Absorbing a block of Keccak-256 is absorbing its rate into the sponge state. -/
theorem spongeEquiv_absorbBlock (S : State) (read : Nat → UInt64) (start : Nat) :
    spongeEquiv (Internal.absorbBlock RATE_256 S read start) =
      absorb (spongeEquiv S) (spongeBlock read start) := by
  simp only [spongeEquiv, Equiv.coe_fn_mk, toSpongeState, absorb, rateXor, spongeBlock,
    lanesBits4_xor, lanesBits13_xor, Internal.absorbBlock, Internal.blockLane, RATE_256,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero, UInt64.xor_zero]

/-- A block determines the 17 lanes it reads. -/
theorem eq_of_spongeBlock_eq {read read' : Nat → UInt64} {s t : Nat}
    (h : spongeBlock read s = spongeBlock read' t) {i : Nat} (hi : i < 17) :
    read (s + 8 * i) = read' (t + 8 * i) := by
  simp only [spongeBlock, Prod.mk.injEq, lanesBits4_inj, lanesBits13_inj] at h
  obtain ⟨⟨_, _, _, _⟩, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h
  interval_cases i <;> simpa

/-! ## The padding -/

/-- The padded message `P` of FIPS 202 §4, cut into blocks of 136 bytes, each read as a rate. -/
def spongePad (msg : ByteArray) : List (BitVec 256 × BitVec 832) :=
  List.ofFn fun j : Fin (blockCount RATE_256 msg.size) =>
    spongeBlock (Internal.laneAt (pad RATE_256 msg)) (RATE_256 * j)

/-- The padding has one block for each permutation call of Keccak-256. -/
@[simp] theorem length_spongePad (msg : ByteArray) :
    (spongePad msg).length = keccak256Cost msg :=
  List.length_ofFn

/-- Distinct messages have distinct block paddings. -/
theorem spongePad_injective : Function.Injective spongePad := by
  intro m₁ m₂ h
  have hn : blockCount RATE_256 m₁.size = blockCount RATE_256 m₂.size := by
    simpa [keccak256Cost] using congrArg List.length h
  -- Each block reads the same lanes from the two padded messages.
  have hblock : ∀ j < blockCount RATE_256 m₁.size,
      spongeBlock (Internal.laneAt (pad RATE_256 m₁)) (RATE_256 * j) =
        spongeBlock (Internal.laneAt (pad RATE_256 m₂)) (RATE_256 * j) := by
    intro j hj
    have := congrArg (fun l => l[j]?) h
    simpa [spongePad, hj, ← hn] using this
  -- So the two padded messages agree byte by byte.
  have hsz : (pad RATE_256 m₁).size = (pad RATE_256 m₂).size := by
    rw [size_pad (by decide), size_pad (by decide), hn]
  refine pad_injective (rate := RATE_256) (by decide) (Base.eq_of_byteAtOrZero hsz fun k => ?_)
  -- Past the end, both bytes read as zero.
  by_cases hk : k < (pad RATE_256 m₁).size
  swap
  · rw [Base.byteAtOrZero_of_size_le (Nat.le_of_not_lt hk),
      Base.byteAtOrZero_of_size_le (hsz ▸ Nat.le_of_not_lt hk)]
  rw [size_pad (by decide)] at hk
  have hlane := eq_of_spongeBlock_eq (hblock (k / RATE_256)
    (Nat.div_lt_of_lt_mul hk)) (i := k % RATE_256 / 8)
    (by simp only [RATE_256]; omega)
  have hbyte := congrArg (fun v => (Internal.bytesOfLane v).getD (k % 8) 0) hlane
  simp only [getD_bytesOfLane_laneAt _ _ _ (Nat.mod_lt _ (by decide))] at hbyte
  have hk' : RATE_256 * (k / RATE_256) + 8 * (k % RATE_256 / 8) + k % 8 = k := by
    simp only [RATE_256]
    omega
  rwa [hk'] at hbyte

/-- The padding pad10*1 of FIPS 202 §5.1, into sponge blocks of 136 bytes. -/
def keccakPadding : Padding ByteArray (BitVec 256 × BitVec 832) where
  pad := spongePad
  pad_injective := spongePad_injective
  pad_ne_nil msg := by
    rw [ne_eq, ← List.length_eq_zero_iff, length_spongePad]
    exact Nat.ne_of_gt (one_le_keccak256Cost msg)

/-! ## The digest -/

/-- Four lanes are their 256 bits. -/
def lanesBits4Equiv : UInt64 × UInt64 × UInt64 × UInt64 ≃ BitVec 256 where
  toFun w := lanesBits4 w.1 w.2.1 w.2.2.1 w.2.2.2
  invFun v := (laneOfBits v 0, laneOfBits v 1, laneOfBits v 2, laneOfBits v 3)
  left_inv w := by
    obtain ⟨h0, h1, h2, h3⟩ := lanesBits4_inj.mp (lanesBits4_laneOfBits (lanesBits4 w.1 w.2.1
      w.2.2.1 w.2.2.2))
    exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))
  right_inv := lanesBits4_laneOfBits

/-- The digest part of the sponge state, as the 32 bytes of Keccak-256. -/
def digestEquiv : BitVec 256 ≃ Vector UInt8 DIGEST_LEN_256 :=
  lanesBits4Equiv.symm.trans (lanes4Equiv.symm.trans lanes4BytesEquiv)

/-- The digest of a state is the image of its digest part. -/
theorem squeeze256_eq_digestEquiv_out (S : State) :
    Internal.squeeze256 S = digestEquiv (spongeEquiv S).out := by
  simp only [digestEquiv, Equiv.trans_apply, spongeEquiv, Equiv.coe_fn_mk, toSpongeState,
    SpongeState.out]
  rw [show lanesBits4 S.a0 S.a1 S.a2 S.a3 = lanesBits4Equiv (S.a0, S.a1, S.a2, S.a3) from rfl,
    Equiv.symm_apply_apply]
  rfl

/-! ## The deployed sponge is the abstract sponge -/

/-- Absorbing `n` blocks of Keccak-256 is absorbing their rates into the sponge state. -/
theorem spongeEquiv_absorbBlocks (π : State → State) (read : Nat → UInt64) (n start : Nat)
    (S : State) :
    spongeEquiv (Id.run (Internal.absorbBlocks (fun T => pure (π T)) RATE_256 read n start S)) =
      Id.run (absorbAll (fun x => pure (spongeEquiv (π (spongeEquiv.symm x)))) (spongeEquiv S)
        (List.ofFn fun j : Fin n => spongeBlock read (start + RATE_256 * j))) := by
  induction n generalizing start S with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, absorbAll_cons]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, Fin.val_succ]
    rw [← spongeEquiv_absorbBlock, Equiv.symm_apply_apply]
    refine (ih (start + RATE_256) _).trans ?_
    have hl : (List.ofFn fun i : Fin n => spongeBlock read (start + RATE_256 * (i + 1))) =
        List.ofFn fun j : Fin n => spongeBlock read (start + RATE_256 + RATE_256 * j) :=
      congrArg List.ofFn (funext fun j => by rw [Nat.mul_succ, Nat.add_comm _ RATE_256,
        Nat.add_assoc])
    rw [pure_bind, hl]
    rfl

/-- **The deployed Keccak-256 over any permutation is the abstract sponge.**

Its digest part, as bytes, is the digest of Keccak-256. -/
theorem keccak256With_eq_spongeHash (π : State → State) (msg : ByteArray) :
    Id.run (keccak256With (fun S => pure (π S)) msg) =
      -- The sponge runs from the zero state, with Keccak's padding and `π` read on sponge states.
      digestEquiv (spongeHash keccakPadding ((0, 0), 0)
        (fun x => spongeEquiv (π (spongeEquiv.symm x))) msg) := by
  rw [keccak256With_eq_squeeze256, spongeAbsorb_eq]
  change Internal.squeeze256 (Id.run (Internal.absorbBlocks _ _ _ _ _ _)) = _
  rw [squeeze256_eq_digestEquiv_out, spongeEquiv_absorbBlocks, spongeEquiv_zero]
  simp only [Nat.zero_add]
  rfl

/-! ## Indifferentiability -/

/-- **Keccak-256 is indifferentiable from a random oracle**, over a uniform permutation. -/
theorem keccak256_indifferentiable :
    Indifferentiable (fun π msg => Id.run (keccak256With (fun S => pure (π S)) msg))
      keccak256Cost (spongeIndiffBound (2 ^ 1600) (2 ^ 512)) := by
  have h := ((indifferentiable_spongeHash keccakPadding ((0, 0), 0)).relabel_state
    spongeEquiv.symm).relabel_digest digestEquiv
  have hH : (fun (π : State → State) msg => Id.run (keccak256With (fun S => pure (π S)) msg)) =
      fun (π : State → State) msg => digestEquiv (spongeHash keccakPadding ((0, 0), 0)
        (fun a => spongeEquiv.symm.symm (π (spongeEquiv.symm a))) msg) :=
    funext fun π => funext fun msg => keccak256With_eq_spongeHash π msg
  have hc : (fun m => (keccakPadding.pad m).length) = keccak256Cost := funext length_spongePad
  -- The bound of the instance is at the cardinalities of the sponge state and of the capacity.
  have hcard : Nat.card SpongeState256 = 2 ^ 1600 :=
    Nat.card_eq_fintype_card.trans card_spongeState256
  have hcap : Nat.card (BitVec 512) = 2 ^ 512 := by
    rw [Nat.card_eq_fintype_card, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard, hcap, ← hH, hc] at h
  exact h

/-- **A random-oracle bound on Keccak-256 holds over a uniform permutation.**

A game of cost at most `N` wins with chance at most `δ` plus the bound above at `N`. -/
theorem keccak256_realProb_le_spongeIndiffBound
    {game : OracleComp (GameSpec State ByteArray (Vector UInt8 DIGEST_LEN_256)) Bool} {N : ℕ}
    -- The game costs at most `N`.
    (hN : WithinCost keccak256Cost game N) {δ : ℝ≥0∞}
    -- With each simulator that asks once per call, its random-oracle image wins at most `δ`.
    (hδ : ∀ (σ : Type) (s₀ : σ) (S : QueryImpl (PermSpec State)
      (StateT σ (OracleComp (RomSpec ByteArray (Vector UInt8 DIGEST_LEN_256))))),
      AsksOnce S → romProb (romGame S s₀ game) ≤ δ) :
    realProb (fun π msg => Id.run (keccak256With (fun S => pure (π S)) msg)) game ≤
      δ + spongeIndiffBound (2 ^ 1600) (2 ^ 512) N :=
  realProb_le_of_romProb_le keccak256_indifferentiable hN hδ

end EthLib.Cryptography.Hash.Keccak
