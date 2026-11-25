module

public import EthLib.Cryptography.Proofs.Hash.Keccak.Indifferentiability
public import EthLib.Cryptography.Proofs.Sponge.Indifferentiability

/-!
# Proofs: Keccak-256 is indifferentiable from a random oracle

Keccak-256 is the sponge of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge], §3.1.

Its rate of 1088 bits splits into the 256 bits of the digest and 832 more; its capacity has 512.

So the indifferentiability of the sponge, with that split, carries over to Keccak-256.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

open OracleComp OracleSpec ENNReal EthLib.Cryptography.LazyPermutation
  EthLib.Cryptography.Indifferentiability EthLib.Cryptography.Sponge

/-! ## The state as a sponge state -/

/-- The sponge state of Keccak-256: 256 bits of digest, 832 more bits of rate, 512 of capacity. -/
abbrev SpongeState256 := SpongeState (BitVec 256) (BitVec 832) (BitVec 512)

/-- Four lanes as 256 bits: bit `64i + z` is bit `z` of lane `i`. -/
def bits4 (a0 a1 a2 a3 : UInt64) : BitVec 256 :=
  a3.toBitVec ++ a2.toBitVec ++ a1.toBitVec ++ a0.toBitVec

/-- Eight lanes as 512 bits: bit `64i + z` is bit `z` of lane `i`. -/
def bits8 (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) : BitVec 512 :=
  bits4 a4 a5 a6 a7 ++ bits4 a0 a1 a2 a3

/-- Thirteen lanes as 832 bits: bit `64i + z` is bit `z` of lane `i`. -/
def bits13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : UInt64) : BitVec 832 :=
  a12.toBitVec ++ bits4 a8 a9 a10 a11 ++ bits8 a0 a1 a2 a3 a4 a5 a6 a7

/-- Two concatenations of bit vectors of the same widths agree when their parts agree. -/
private theorem append_eq_append_iff {w v : Nat} {a c : BitVec w} {b d : BitVec v} :
    a ++ b = c ++ d ↔ a = c ∧ b = d := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => by rw [h.1, h.2]⟩
  · simpa [BitVec.extractLsb'_append_eq_left] using congrArg (BitVec.extractLsb' v w) h
  · simpa [BitVec.extractLsb'_append_eq_right] using congrArg (BitVec.extractLsb' 0 v) h

/-- Four lanes are determined by their 256 bits. -/
theorem bits4_inj {a0 a1 a2 a3 b0 b1 b2 b3 : UInt64}
    (h : bits4 a0 a1 a2 a3 = bits4 b0 b1 b2 b3) : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  obtain ⟨h, h0⟩ := (append_eq_append_iff (w := 192) (v := 64)).mp h
  obtain ⟨h, h1⟩ := (append_eq_append_iff (w := 128) (v := 64)).mp h
  obtain ⟨h3, h2⟩ := (append_eq_append_iff (w := 64) (v := 64)).mp h
  exact ⟨UInt64.toBitVec_inj.mp h0, UInt64.toBitVec_inj.mp h1, UInt64.toBitVec_inj.mp h2,
    UInt64.toBitVec_inj.mp h3⟩

/-- XOR of four lanes as bits is XOR lane by lane. -/
theorem bits4_xor (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    bits4 a0 a1 a2 a3 ^^^ bits4 b0 b1 b2 b3 =
      bits4 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) := by
  simp only [bits4, UInt64.toBitVec_xor]
  rw [BitVec.xor_append (w := 192) (v := 64), BitVec.xor_append (w := 128) (v := 64),
    BitVec.xor_append (w := 64) (v := 64)]

/-- Eight lanes are determined by their 512 bits. -/
theorem bits8_inj {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt64}
    (h : bits8 a0 a1 a2 a3 a4 a5 a6 a7 = bits8 b0 b1 b2 b3 b4 b5 b6 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  obtain ⟨hhi, hlo⟩ := (append_eq_append_iff (w := 256) (v := 256)).mp h
  obtain ⟨h0, h1, h2, h3⟩ := bits4_inj hlo
  obtain ⟨h4, h5, h6, h7⟩ := bits4_inj hhi
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- XOR of eight lanes as bits is XOR lane by lane. -/
theorem bits8_xor (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) :
    bits8 a0 a1 a2 a3 a4 a5 a6 a7 ^^^ bits8 b0 b1 b2 b3 b4 b5 b6 b7 =
      bits8 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) (a4 ^^^ b4) (a5 ^^^ b5)
        (a6 ^^^ b6) (a7 ^^^ b7) := by
  simp only [bits8]
  rw [BitVec.xor_append (w := 256) (v := 256), bits4_xor, bits4_xor]

/-- Thirteen lanes are determined by their 832 bits. -/
theorem bits13_inj {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : UInt64}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : UInt64}
    (h : bits13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =
      bits13 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 ∧
      a8 = b8 ∧ a9 = b9 ∧ a10 = b10 ∧ a11 = b11 ∧ a12 = b12 := by
  obtain ⟨hhi, hlo⟩ := (append_eq_append_iff (w := 320) (v := 512)).mp h
  obtain ⟨h12, hmid⟩ := (append_eq_append_iff (w := 64) (v := 256)).mp hhi
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bits8_inj hlo
  obtain ⟨h8, h9, h10, h11⟩ := bits4_inj hmid
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, UInt64.toBitVec_inj.mp h12⟩

/-- XOR of thirteen lanes as bits is XOR lane by lane. -/
theorem bits13_xor (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : UInt64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : UInt64) :
    bits13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 ^^^
        bits13 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 =
      bits13 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) (a4 ^^^ b4) (a5 ^^^ b5)
        (a6 ^^^ b6) (a7 ^^^ b7) (a8 ^^^ b8) (a9 ^^^ b9) (a10 ^^^ b10) (a11 ^^^ b11)
        (a12 ^^^ b12) := by
  simp only [bits13]
  rw [BitVec.xor_append (w := 320) (v := 512), BitVec.xor_append (w := 64) (v := 256), bits4_xor,
    bits8_xor, UInt64.toBitVec_xor]

/-- The state as a sponge state: lanes 0 to 3, lanes 4 to 16, then lanes 17 to 24.

So bit `k` of the three parts together is bit `k` of the state string of FIPS 202 §3.1.2.

The first 1088 bits are the rate of Keccak-256, and the digest is its first 256 bits. -/
def toSpongeState (S : State) : SpongeState256 :=
  ((bits4 S.a0 S.a1 S.a2 S.a3,
    bits13 S.a4 S.a5 S.a6 S.a7 S.a8 S.a9 S.a10 S.a11 S.a12 S.a13 S.a14 S.a15 S.a16),
    bits8 S.a17 S.a18 S.a19 S.a20 S.a21 S.a22 S.a23 S.a24)

/-- A state is determined by its sponge state. -/
theorem toSpongeState_injective : Function.Injective toSpongeState := by
  intro S T h
  simp only [toSpongeState, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨_, _, _, _⟩ := bits4_inj h1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := bits13_inj h2
  obtain ⟨_, _, _, _, _, _, _, _⟩ := bits8_inj h3
  cases S
  cases T
  simp_all

/-- The sponge state of Keccak-256 has `2^1600` values, as the state has. -/
theorem card_spongeState256 : Fintype.card SpongeState256 = 2 ^ 1600 := by
  rw [Fintype.card_prod, Fintype.card_prod, ← FinEnum.card_eq_fintypeCard,
    ← FinEnum.card_eq_fintypeCard, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec,
    FinEnum.card_bitVec, FinEnum.card_bitVec, ← pow_add, ← pow_add]

/-- Every sponge state of Keccak-256 comes from exactly one state. -/
theorem toSpongeState_bijective : Function.Bijective toSpongeState := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨toSpongeState_injective, ?_⟩
  rw [card_spongeState256, ← FinEnum.card_eq_fintypeCard, card_state]

/-- Four zero lanes are 256 zero bits. -/
theorem bits4_zero : bits4 0 0 0 0 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [bits4]

/-- Eight zero lanes are 512 zero bits. -/
theorem bits8_zero : bits8 0 0 0 0 0 0 0 0 = 0 := by
  rw [bits8, bits4_zero]
  exact BitVec.zero_append_zero (v := 256) (w := 256)

/-- Thirteen zero lanes are 832 zero bits. -/
theorem bits13_zero : bits13 0 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  rw [bits13, bits4_zero, bits8_zero, UInt64.toBitVec_zero]
  exact (congrArg (· ++ (0 : BitVec 512)) (BitVec.zero_append_zero (v := 64) (w := 256))).trans
    (BitVec.zero_append_zero (v := 320) (w := 512))

/-- The Keccak state and the sponge state of Keccak-256 are in bijection, lane by lane. -/
noncomputable def spongeEquiv : State ≃ SpongeState256 :=
  Equiv.ofBijective toSpongeState toSpongeState_bijective

/-- The zero state of Keccak is the zero sponge state. -/
theorem spongeEquiv_zero : spongeEquiv State.zero = ((0, 0), 0) := by
  simp only [spongeEquiv, Equiv.ofBijective_apply, toSpongeState, State.zero, bits4_zero,
    bits8_zero, bits13_zero]

/-- Lanes 0 to 16 of a block at `start`, read as the rate of a sponge state. -/
def spongeBlock (read : Nat → UInt64) (start : Nat) : BitVec 256 × BitVec 832 :=
  (bits4 (read start) (read (start + 8)) (read (start + 16)) (read (start + 24)),
    bits13 (read (start + 32)) (read (start + 40)) (read (start + 48)) (read (start + 56))
      (read (start + 64)) (read (start + 72)) (read (start + 80)) (read (start + 88))
      (read (start + 96)) (read (start + 104)) (read (start + 112)) (read (start + 120))
      (read (start + 128)))

/-- Absorbing a block of Keccak-256 is absorbing its rate into the sponge state. -/
theorem spongeEquiv_absorbBlock (S : State) (read : Nat → UInt64) (start : Nat) :
    spongeEquiv (Internal.absorbBlock RATE_256 S read start) =
      absorb (spongeEquiv S) (spongeBlock read start) := by
  simp only [spongeEquiv, Equiv.ofBijective_apply, toSpongeState, absorb, rateXor, spongeBlock,
    bits4_xor, bits13_xor, Internal.absorbBlock, Internal.blockLane, RATE_256, Nat.reduceMul,
    Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceIte, Nat.add_zero, UInt64.xor_zero]

/-- A block determines the 17 lanes it reads. -/
theorem spongeBlock_inj {read read' : Nat → UInt64} {s t : Nat}
    (h : spongeBlock read s = spongeBlock read' t) {i : Nat} (hi : i < 17) :
    read (s + 8 * i) = read' (t + 8 * i) := by
  simp only [spongeBlock, Prod.mk.injEq] at h
  obtain ⟨h4, h13⟩ := h
  obtain ⟨_, _, _, _⟩ := bits4_inj h4
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := bits13_inj h13
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

/-- Two byte strings of one size are equal when their bytes agree inside them. -/
private theorem byteArray_ext_byteAtOrZero {a b : ByteArray} (hsz : a.size = b.size)
    (h : ∀ k, k < a.size → Base.byteAtOrZero a k = Base.byteAtOrZero b k) : a = b := by
  apply ByteArray.ext
  apply Array.ext hsz
  intro k h1 h2
  have := h k h1
  unfold Base.byteAtOrZero at this
  rwa [dite_eq_left (show k < a.size from h1), dite_eq_left (show k < b.size from h2)] at this

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
  refine pad_injective (rate := RATE_256) (by decide) (byteArray_ext_byteAtOrZero hsz ?_)
  intro k hk
  rw [size_pad (by decide)] at hk
  have hlane := spongeBlock_inj (hblock (k / RATE_256)
    (Nat.div_lt_of_lt_mul hk)) (i := k % RATE_256 / 8)
    (by simp only [RATE_256]; omega)
  have hbyte := congrArg (fun v => (Internal.bytesOfLane v).getD (k % 8) 0) hlane
  simp only [getD_bytesOfLane_laneAt _ _ _ (Nat.mod_lt _ (by decide))] at hbyte
  have hk' : RATE_256 * (k / RATE_256) + 8 * (k % RATE_256 / 8) + k % 8 = k := by
    simp only [RATE_256]
    omega
  rwa [hk'] at hbyte

/-- Keccak's padding pad10*1, as a padding of byte strings into sponge blocks. -/
def keccakPadding : Padding ByteArray (BitVec 256 × BitVec 832) where
  pad := spongePad
  pad_injective := spongePad_injective
  pad_ne_nil msg := by
    rw [ne_eq, ← List.length_eq_zero_iff, length_spongePad]
    exact Nat.ne_of_gt (one_le_keccak256Cost msg)

/-! ## The digest -/

/-- Four lanes as 256 bits are in bijection with the four lanes. -/
theorem bits4_bijective :
    Function.Bijective fun w : UInt64 × UInt64 × UInt64 × UInt64 =>
      bits4 w.1 w.2.1 w.2.2.1 w.2.2.2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun v w h => ?_, ?_⟩
  · obtain ⟨h0, h1, h2, h3⟩ := bits4_inj h
    exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))
  · rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ← FinEnum.card_eq_fintypeCard,
      ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt64, FinEnum.card_bitVec, ← pow_add,
      ← pow_add, ← pow_add]

/-- The bytes of four lanes are in bijection with the four lanes. -/
theorem bytes4_bijective : Function.Bijective
    fun w : UInt64 × UInt64 × UInt64 × UInt64 =>
      (⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩ : Lanes4).bytes := by
  refine ⟨fun v w h => ?_, fun d => ?_⟩
  · have := Lanes4.bytes_injective h
    simp only [Lanes4.mk.injEq] at this
    obtain ⟨h0, h1, h2, h3⟩ := this
    exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))
  · -- The lanes read from the bytes give back the bytes.
    have h : 0 + 32 ≤ (Base.packBytes d).size := by simp
    refine ⟨((Lanes4.read (Base.packBytes d) 0).w0, (Lanes4.read (Base.packBytes d) 0).w1,
      (Lanes4.read (Base.packBytes d) 0).w2, (Lanes4.read (Base.packBytes d) 0).w3), ?_⟩
    exact (Lanes4.bytes_read _ 0 h).trans (Base.readBytes_packBytes d h)

/-- The digest part of the sponge state, as the 32 bytes of Keccak-256. -/
noncomputable def digestEquiv : BitVec 256 ≃ Vector UInt8 DIGEST_LEN_256 :=
  (Equiv.ofBijective _ bits4_bijective).symm.trans (Equiv.ofBijective _ bytes4_bijective)

/-- The digest of a state is the image of its digest part. -/
theorem squeeze256_eq (S : State) :
    Internal.squeeze256 S = digestEquiv (spongeEquiv S).out := by
  simp only [digestEquiv, Equiv.trans_apply, spongeEquiv, Equiv.ofBijective_apply, toSpongeState,
    SpongeState.out]
  rw [show bits4 S.a0 S.a1 S.a2 S.a3 = Equiv.ofBijective _ bits4_bijective (S.a0, S.a1, S.a2, S.a3)
    from rfl, Equiv.symm_apply_apply]
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

The sponge runs from the zero state, with Keccak's padding and `π` read on sponge states.

Its digest part, as bytes, is the digest of Keccak-256. -/
theorem keccak256With_eq_spongeHash (π : State → State) (msg : ByteArray) :
    Id.run (keccak256With (fun S => pure (π S)) msg) =
      digestEquiv (spongeHash keccakPadding ((0, 0), 0)
        (fun x => spongeEquiv (π (spongeEquiv.symm x))) msg) := by
  rw [keccak256With_eq_squeeze256, spongeAbsorb_eq]
  change Internal.squeeze256 (Id.run (Internal.absorbBlocks _ _ _ _ _ _)) = _
  rw [squeeze256_eq, spongeEquiv_absorbBlocks, spongeEquiv_zero]
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
  rw [hH, ← hc]
  convert h using 2
  · convert card_spongeState256.symm
  · exact (FinEnum.card_bitVec 512).symm.trans FinEnum.card_eq_fintypeCard

/-- **A random-oracle bound on Keccak-256 holds over a uniform permutation**, up to the bound above.

Take a game that costs at most `N`.

Let `δ` bound its image in the random-oracle model, for every simulator that asks once per call.

Then over a uniform permutation, the game wins with chance at most `δ` plus the bound at `N`. -/
theorem keccak256_realProb_le_spongeIndiffBound
    {game : OracleComp (GameSpec State ByteArray (Vector UInt8 DIGEST_LEN_256)) Bool} {N : ℕ}
    (hN : WithinCost keccak256Cost game N) {δ : ℝ≥0∞}
    (hδ : ∀ (σ : Type) (s₀ : σ) (S : QueryImpl (PermSpec State)
      (StateT σ (OracleComp (RomSpec ByteArray (Vector UInt8 DIGEST_LEN_256))))),
      AsksOnce S → romProb (romGame S s₀ game) ≤ δ) :
    realProb (fun π msg => Id.run (keccak256With (fun S => pure (π S)) msg)) game ≤
      δ + spongeIndiffBound (2 ^ 1600) (2 ^ 512) N :=
  realProb_le_of_romProb_le keccak256_indifferentiable hN hδ

end EthLib.Cryptography.Hash.Keccak
