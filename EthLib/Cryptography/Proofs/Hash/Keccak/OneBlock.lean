module

public import EthLib.Cryptography.Proofs.Hash.Keccak.BitsSponge
public import EthLib.Cryptography.Proofs.OneCallPermutation

/-!
# Proofs: one-block Keccak-256 over a random permutation

A message of at most 135 bytes pads to one block of 136 bytes.

Keccak-256 of it is then one call to the permutation on that block, with a zero capacity.

The output is the first 256 bits of the result.

Here the permutation is uniform, and the adversary evaluates it and its inverse.

An adversary with `q` such calls finds a collision with chance at most a ratio.

Its numerator is `Q (Q - 1) / 2 * 2^1344 + Q * 2^1088`, with `Q = q + 2`.

Its denominator is `2^1600 - Q`.

That is about `Q (Q - 1) / 2^257 + Q / 2^512`.

It finds a preimage of a given digest with chance at most `Q (2^1344 + 2^1088) / (2^1600 - Q)`.

There `Q = q + 1`, and the bound is about `Q / 2^256 + Q / 2^512`.

Appendix A.1, Table 4, of [FIPS 202][fips] covers SHA3-256, which has the same capacity.

The table claims 128 bits against collisions for it.

It claims 256 bits against preimages.

The bounds above meet these two claims for one-block messages.

[fips]: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

open OracleComp OracleSpec ENNReal EthLib.Cryptography.LazyPermutation

/-! ## One call to the permutation -/

/-- The state `P_0 || 0^c` that the sponge permutes first, FIPS 202 §4, Algorithm 8, step 6.

`P_0` is the first block of the padded message, at the Keccak-256 rate of 136 bytes. -/
def oneBlockState (msg : ByteArray) : State :=
  Internal.absorbBlock RATE_256 State.zero (Internal.laneAt (pad RATE_256 msg)) 0

/-- Below 136 bytes, the absorbing phase is one call to the permutation, whatever it is. -/
theorem spongeAbsorb_of_size_lt (f : State → State) {msg : ByteArray} (h : msg.size < RATE_256) :
    Internal.spongeAbsorb f RATE_256 msg.size (Internal.laneAt msg) = f (oneBlockState msg) := by
  have hn : blockCount RATE_256 msg.size = 1 := by simp [blockCount, Nat.div_eq_of_lt h]
  simp only [spongeAbsorb_eq, hn, Internal.absorbBlocks, oneBlockState]

/-- Below 136 bytes, Keccak-256 is the first 256 bits of one call to Keccak-f[1600]. -/
theorem keccak256_of_size_lt {msg : ByteArray} (h : msg.size < RATE_256) :
    keccak256 msg = Internal.squeeze256 (keccakF (oneBlockState msg)) := by
  rw [keccak256_eq_squeeze256, spongeAbsorb_of_size_lt keccakF h]

/-! ## The state space -/

/-- A state is its 25 lanes. -/
def laneEquiv : State ≃ (Fin 5 → Fin 5 → UInt64) where
  toFun := State.lane
  invFun := State.ofLanes
  left_inv := ofLanes_lane
  right_inv f := funext fun x => funext fun y => lane_ofLanes f x y

instance : FinEnum State := FinEnum.ofEquiv _ laneEquiv

/-- There are `2^1600` states. -/
theorem card_state : FinEnum.card State = 2 ^ 1600 := by
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_congr laneEquiv, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_fin, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt64,
    ← pow_mul, ← pow_mul]

/-- At most `2^(64 k)` states have given lanes outside `k` free positions. -/
theorem card_filter_lanes_le (P : Fin 5 → Fin 5 → Prop) [∀ x y, Decidable (P x y)]
    (w : Fin 5 → Fin 5 → UInt64) :
    (Finset.univ.filter fun S : State => ∀ x y, ¬P x y → S.lane x y = w x y).card ≤
      (2 ^ 64) ^ Fintype.card {p : Fin 5 × Fin 5 // P p.1 p.2} := by
  have hinj : Set.InjOn
      (fun (S : State) (p : {p : Fin 5 × Fin 5 // P p.1 p.2}) => S.lane p.1.1 p.1.2)
      (Finset.univ.filter fun S : State => ∀ x y, ¬P x y → S.lane x y = w x y) := by
    intro S hS S' hS' h
    refine State.ext_lane fun x y => ?_
    by_cases hp : P x y
    · exact congrFun h ⟨(x, y), hp⟩
    · rw [(Finset.mem_filter.1 hS).2 x y hp, (Finset.mem_filter.1 hS').2 x y hp]
  refine (Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj).trans ?_
  rw [Finset.card_univ, Fintype.card_fun, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt64]

/-! ## The encoding of a message -/

/-- Lane `(x, y)` of the first state reads 8 bytes of the padded message, or is in the capacity. -/
theorem lane_oneBlockState (msg : ByteArray) (x y : Fin 5) :
    (oneBlockState msg).lane x y =
      if x.val + 5 * y.val < 17 then Internal.laneAt (pad RATE_256 msg) (8 * (x.val + 5 * y.val))
      else 0 := by
  have hz : State.zero.lane x y = 0 := by fin_cases x <;> fin_cases y <;> rfl
  rw [oneBlockState, Internal.absorbBlock_lane, hz, UInt64.zero_xor,
    Internal.blockLane]
  by_cases h : x.val + 5 * y.val < 17
  · have hr : 8 * (x.val + 5 * y.val) + 8 ≤ RATE_256 := by unfold RATE_256; omega
    simp only [hr, h, ↓reduceIte, Nat.zero_add]
  · have hr : ¬8 * (x.val + 5 * y.val) + 8 ≤ RATE_256 := by unfold RATE_256; omega
    simp only [hr, h, ↓reduceIte]

/-- The states whose capacity lanes, 17 to 24, are zero. -/
noncomputable def zeroCapacity : Finset State :=
  Finset.univ.filter fun S => ∀ x y : Fin 5, ¬(x.val + 5 * y.val < 17) → S.lane x y = 0

/-- The first state of every message has a zero capacity. -/
theorem oneBlockState_mem_zeroCapacity (msg : ByteArray) : oneBlockState msg ∈ zeroCapacity := by
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x y h => ?_⟩
  simp only [lane_oneBlockState, h, ↓reduceIte]

/-- At most `2^1088` states have a zero capacity. -/
theorem card_zeroCapacity_le : zeroCapacity.card ≤ 2 ^ 1088 := by
  refine (card_filter_lanes_le (fun x y => x.val + 5 * y.val < 17) fun _ _ => 0).trans ?_
  have : Fintype.card {p : Fin 5 × Fin 5 // p.1.val + 5 * p.2.val < 17} = 17 := by decide
  rw [this, ← pow_mul]

/-- Two messages below 136 bytes with one first state are equal. -/
theorem oneBlockState_injective {m₁ m₂ : ByteArray} (h₁ : m₁.size < RATE_256)
    (h₂ : m₂.size < RATE_256) (h : oneBlockState m₁ = oneBlockState m₂) : m₁ = m₂ := by
  have hr : 0 < RATE_256 := by decide
  have hsize (m : ByteArray) (hm : m.size < RATE_256) : (pad RATE_256 m).size = 136 := by
    rw [size_pad hr, blockCount, Nat.div_eq_of_lt hm]
    rfl
  -- Each byte of the block is read back from its lane.
  have hbyte : ∀ j < 136, EthLib.Base.byteAt (pad RATE_256 m₁) j =
      EthLib.Base.byteAt (pad RATE_256 m₂) j := by
    intro j hj
    have hx : j / 8 % 5 < 5 := Nat.mod_lt _ (by decide)
    have hy : j / 8 / 5 < 5 := by omega
    have hlane := congrArg (fun S => S.lane ⟨j / 8 % 5, hx⟩ ⟨j / 8 / 5, hy⟩) h
    simp only [lane_oneBlockState] at hlane
    have hk : j / 8 % 5 + 5 * (j / 8 / 5) = j / 8 := by omega
    simp only [hk, show j / 8 < 17 by omega, ↓reduceIte] at hlane
    apply UInt8.toNat_inj.1
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hb : b < 8
    · have := congrArg (fun v : UInt64 => v.toBitVec.getLsbD (8 * (j % 8) + b)) hlane
      simp only [Internal.laneAt_testBit _ _ _ (show 8 * (j % 8) + b < 64 by omega)] at this
      have e1 : 8 * (j / 8) + (8 * (j % 8) + b) / 8 = j := by omega
      have e2 : (8 * (j % 8) + b) % 8 = b := by omega
      rwa [e1, e2] at this
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (UInt8.toNat_lt _) (Nat.pow_le_pow_right
        (by decide) (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le (UInt8.toNat_lt _)
        (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hat (m : ByteArray) (i : Nat) (hi : i < m.data.size) :
      EthLib.Base.byteAt m i = m.data[i] :=
    dite_eq_left_of_eq_true (eq_true hi)
  refine pad_injective hr (ByteArray.ext (Array.ext ((hsize m₁ h₁).trans (hsize m₂ h₂).symm)
    fun j hj₁ hj₂ => ?_))
  have hj : j < 136 := (hsize m₁ h₁) ▸ hj₁
  have := hbyte j hj
  rwa [hat _ _ hj₁, hat _ _ hj₂] at this

/-! ## The output -/

/-- Two states with one digest agree on lanes `(0, 0)` to `(3, 0)`. -/
theorem lane_eq_of_squeeze256_eq {S T : State}
    (h : Internal.squeeze256 S = Internal.squeeze256 T) (x : Fin 5) (hx : x.val < 4) :
    S.lane x 0 = T.lane x 0 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : 8 * x.val + k / 8 < 32 := by omega
  have hbyte : Models.KeccakBits.outputByte (Models.KeccakBits.ofLanes S) (8 * x.val + k / 8) =
      Models.KeccakBits.outputByte (Models.KeccakBits.ofLanes T) (8 * x.val + k / 8) := by
    have hS := Models.KeccakBits.outputByte_eq_squeeze S ⟨_, hi⟩
    have hT := Models.KeccakBits.outputByte_eq_squeeze T ⟨_, hi⟩
    rw [h] at hS
    exact hS.trans hT.symm
  rw [Models.KeccakBits.outputByte_ofLanes _ (show 8 * x.val + k / 8 < 200 by omega),
    Models.KeccakBits.outputByte_ofLanes _ (show 8 * x.val + k / 8 < 200 by omega)] at hbyte
  have hx' : (⟨(8 * x.val + k / 8) / 8 % 5, by omega⟩ : Fin 5) = x := Fin.ext (by simp; omega)
  have hy' : (⟨(8 * x.val + k / 8) / 40, by omega⟩ : Fin 5) = 0 := Fin.ext (by simp; omega)
  simp only [hx', hy'] at hbyte
  have := congrArg (fun b : UInt8 => b.toBitVec.getLsbD (k % 8)) hbyte
  simp only [Models.KeccakBits.bytesOfLane_bit _ _ _ (show (8 * x.val + k / 8) % 8 < 8 by omega)
    (show k % 8 < 8 by omega)] at this
  have e : 8 * ((8 * x.val + k / 8) % 8) + k % 8 = k := by omega
  rwa [e] at this

/-- At most `2^1344` states share a digest. -/
theorem card_squeeze256_fiber_le (T : State) :
    (Finset.univ.filter fun S => Internal.squeeze256 S = Internal.squeeze256 T).card ≤
      2 ^ 1344 := by
  refine (Finset.card_le_card fun S hS => ?_).trans
    ((card_filter_lanes_le (fun x y => ¬(y = 0 ∧ x.val < 4)) T.lane).trans ?_)
  · have hS := (Finset.mem_filter.1 hS).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x y h => ?_⟩
    obtain ⟨rfl, hx⟩ := not_not.1 h
    exact lane_eq_of_squeeze256_eq hS x hx
  · have : Fintype.card {p : Fin 5 × Fin 5 // ¬(p.2 = 0 ∧ p.1.val < 4)} = 21 := by decide
    rw [this, ← pow_mul]

/-! ## The bounds -/

/-- A message of at most 135 bytes, which Keccak-256 absorbs in one block. -/
abbrev ShortMessage := {m : ByteArray // m.size < RATE_256}

/-- With the permutation `π` in place of Keccak-f[1600], the game's hash is the spec's sponge. -/
theorem oneCallHash_eq (π : State → State) (m : ShortMessage) :
    oneCallHash (fun m : ShortMessage => oneBlockState m.1) Internal.squeeze256 π m =
      Internal.squeeze256 (Internal.spongeAbsorb π RATE_256 m.1.size (Internal.laneAt m.1)) := by
  rw [oneCallHash, spongeAbsorb_of_size_lt π m.2]

/-- **Collisions of one-block Keccak-256 over a random permutation.**

The adversary makes at most `q` calls to the permutation and its inverse, and `Q = q + 2`.

It finds two messages below 136 bytes with one digest with chance at most this ratio.

The numerator is `Q (Q - 1) / 2 * 2^1344 + Q * 2^1088`, and the denominator `2^1600 - Q`.

For `Q ≥ 2^1600` the denominator is zero and the bound is trivial. -/
theorem keccak256_collisionAdvantage_le (adversary : PermComp State (ShortMessage × ShortMessage))
    {q : ℕ} (hq : IsQueryBoundP adversary (·.isRight = true) q) :
    collisionAdvantage (fun m : ShortMessage => oneBlockState m.1) Internal.squeeze256
        adversary ≤
      (((q + 2).choose 2 * 2 ^ 1344 + (q + 2) * 2 ^ 1088 : ℕ) : ℝ≥0∞) /
        ((2 ^ 1600 - (q + 2) : ℕ) : ℝ≥0∞) := by
  rw [← card_state]
  exact collisionAdvantage_le (F := 2 ^ 1344) (K := 2 ^ 1088) zeroCapacity Internal.squeeze256 _
    (fun m₁ m₂ h => Subtype.ext (oneBlockState_injective m₁.2 m₂.2 h))
    (fun m => oneBlockState_mem_zeroCapacity m.1) card_zeroCapacity_le
    card_squeeze256_fiber_le adversary hq

/-- **Preimages of one-block Keccak-256 over a random permutation.**

The adversary gets a digest, and makes at most `q` calls to the permutation and its inverse.

It returns a message below 136 bytes with that digest with chance at most this ratio.

The ratio is `Q (2^1344 + 2^1088) / (2^1600 - Q)`, with `Q = q + 1`.

For `Q ≥ 2^1600` the denominator is zero and the bound is trivial. -/
theorem keccak256_preimageAdvantage_le
    (adversary : Vector UInt8 DIGEST_LEN_256 → PermComp State ShortMessage)
    (d : Vector UInt8 DIGEST_LEN_256) {q : ℕ}
    (hq : IsQueryBoundP (adversary d) (·.isRight = true) q) :
    preimageAdvantage (fun m : ShortMessage => oneBlockState m.1) Internal.squeeze256
        adversary d ≤
      (((q + 1) * (2 ^ 1344 + 2 ^ 1088) : ℕ) : ℝ≥0∞) / ((2 ^ 1600 - (q + 1) : ℕ) : ℝ≥0∞) := by
  have h := preimageAdvantage_le (F := 2 ^ 1344) (K := 2 ^ 1088) zeroCapacity Internal.squeeze256
    (fun m : ShortMessage => oneBlockState m.1)
    (fun m => oneBlockState_mem_zeroCapacity m.1) card_zeroCapacity_le
    card_squeeze256_fiber_le adversary d hq
  rw [card_state] at h
  exact h

end EthLib.Cryptography.Hash.Keccak
