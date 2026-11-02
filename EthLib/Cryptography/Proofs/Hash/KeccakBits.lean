module

public import EthLib.Cryptography.Hash.KeccakBits
public import EthLib.Cryptography.Proofs.Hash.Keccak

/-!
# Keccak bit model prerequisites

These facts cover bit coordinates, step mappings and padding lengths.
The permutation and sponge correspondence are proved in separate modules.
-/

@[expose] public section
namespace EthLib.Cryptography.Hash.KeccakBits

/-- A lane state viewed at the bit coordinates of FIPS 202 section 3.1.2. -/
def ofLanes (a : Keccak.State) : State := fun x y z =>
  (a[x.val + 5 * y.val]'(by simp only [Keccak.LANES]; omega)).toBitVec.getLsbD z.val

/-- Flattening a coordinate and reading it recovers that coordinate. -/
theorem stateBit_index (a : State) (x y : Fin 5) (z : Fin 64) :
    stateBit a (index x y z) = a x y z := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  unfold stateBit index xy zcoord
  congr 1 <;> apply Fin.ext <;> simp only <;> omega

/-- A bounded lane rotation moves each bit to its source coordinate. -/
theorem rotl_bit (v : UInt64) (n i : Nat) (hn : n < 64) (hi : i < 64) :
    (Keccak.rotl v (UInt64.ofNat n)).toBitVec.getLsbD i =
      v.toBitVec.getLsbD ((i + 64 - n) % 64) := by
  simp only [Keccak.rotl, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat,
    UInt64.toBitVec_ofNat', BitVec.getLsbD_or, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_sub]
  simp only [show (64 : BitVec 64).toNat = 64 by decide, show 2 ^ 64 = 18446744073709551616 by decide, Nat.reduceMod]
  by_cases hn0 : n = 0
  · subst n
    simp [hi, Nat.mod_eq_of_lt hi]
  · have hlarge : n < 18446744073709551616 := by omega
    simp only [Nat.mod_eq_of_lt hlarge, Nat.mod_eq_of_lt hn]
    have hsub : (18446744073709551616 - n + 64) % 18446744073709551616 = 64 - n := by omega
    rw [hsub]
    have hsmall : 64 - n < 64 := by omega
    simp only [Nat.mod_eq_of_lt hsmall, hi, decide_true, Bool.true_and]
    by_cases h : i < n
    · have hidx : (i + 64 - n) % 64 = 64 - n + i := by omega
      simp [h, hidx]
    · have hidx : (i + 64 - n) % 64 = i - n := by omega
      have out : 64 ≤ 64 - n + i := by omega
      simp [h, hidx, BitVec.getLsbD_of_ge _ _ out]


/-- Pi agrees with the lane implementation at every state bit. -/
theorem pi_ofLanes (a : Keccak.State) :
    ofLanes (Keccak.pi a) = pi (ofLanes a) := by
  funext x y z
  simp only [ofLanes, Keccak.pi, Vector.getElem_ofFn, Keccak.lane, pi, xy]
  congr 2
  have hx := x.isLt
  have hy := y.isLt
  congr 1
  omega

/-- The bit model's rho walk agrees with every lane rotation offset. -/
theorem rhoOffset_eq : ∀ x y : Fin 5,
    rhoOffset x y = (Keccak.RHO[x.val + 5 * y.val]'(by simp only [Keccak.LANES]; omega)).toNat := by
  decide +kernel

/-- Every offset assigned by the rho walk is below the lane width. -/
theorem rhoOffset_lt : ∀ x y : Fin 5, rhoOffset x y < 64 := by
  decide +kernel

/-- Rho agrees with the lane implementation at every state bit. -/
theorem rho_ofLanes (a : Keccak.State) :
    ofLanes (Keccak.rho a) = rho (ofLanes a) := by
  funext x y z
  have hOffset := rhoOffset_eq x y
  have hBound := rhoOffset_lt x y
  simp only [ofLanes, Keccak.rho, Vector.getElem_ofFn, rho, zcoord]
  have idx : x.val + 5 * y.val < Keccak.LANES := by
    simp only [Keccak.LANES]
    have := x.isLt
    have := y.isLt
    omega
  change (Keccak.rotl (a[x.val + 5 * y.val]'idx) (Keccak.RHO[x.val + 5 * y.val]'idx)).toBitVec.getLsbD z.val =
    (a[x.val + 5 * y.val]'idx).toBitVec.getLsbD ((z.val + 64 - rhoOffset x y) % 64)
  rw [← UInt64.ofNat_toNat (x := Keccak.RHO[x.val + 5 * y.val]'idx)]
  rw [rotl_bit _ _ _ (by rw [← hOffset]; exact hBound) z.isLt]
  simp only [← hOffset]

private def laneColumn (a : Keccak.State) (x : Fin 5) : UInt64 :=
  Keccak.lane a x.val 0 ^^^ Keccak.lane a x.val 1 ^^^ Keccak.lane a x.val 2 ^^^ Keccak.lane a x.val 3 ^^^ Keccak.lane a x.val 4
private theorem column_bit (a : Keccak.State) (x : Fin 5) (z : Fin 64) :
    (laneColumn a x).toBitVec.getLsbD z.val = column (ofLanes a) x z := by
  simp [laneColumn, Keccak.lane, column, ofLanes, Nat.mod_eq_of_lt x.isLt,
    UInt64.toBitVec_xor]
  rfl
private theorem theta_lane (a : Keccak.State) (x y : Fin 5) :
    (Keccak.theta a)[x.val + 5*y.val]'(by simp [Keccak.LANES]; omega) =
      (a[x.val + 5*y.val]'(by simp [Keccak.LANES]; omega)) ^^^
        (laneColumn a (xy (x.val + 4)) ^^^ Keccak.rotl (laneColumn a (xy (x.val + 1))) 1) := by
  have hmod : (x.val + 5*y.val)%5 = x.val := by have := x.isLt; omega
  simp only [Keccak.theta, Vector.getElem_ofFn, hmod, laneColumn, xy, Keccak.lane, Nat.mod_mod]
  rfl
/-- Theta agrees with the lane implementation at every state bit. -/
theorem theta_ofLanes (a : Keccak.State) : ofLanes (Keccak.theta a) = theta (ofLanes a) := by
  funext x y z
  simp only [ofLanes]
  rw [theta_lane]
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  have rot := rotl_bit (laneColumn a (xy (x.val + 1))) 1 z.val (by decide) z.isLt
  change (Keccak.rotl (laneColumn a (xy (x.val + 1))) 1).toBitVec.getLsbD z.val = _ at rot
  rw [rot]
  simp only [column_bit]
  change _ = Bool.xor _ (Bool.xor _ _)
  simp only [ofLanes, zcoord]
  have shift : (z.val + 64 - 1) % 64 = (z.val + 63) % 64 := by omega
  rw [shift]
  have col := column_bit a (xy (x.val + 1)) ⟨(z.val + 63) % 64, Nat.mod_lt _ (by decide)⟩
  rw [← col]

/-- Chi agrees with the lane implementation at every state bit. -/
theorem chi_ofLanes (a : Keccak.State) :
    ofLanes (Keccak.chi a) = chi (ofLanes a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hmod : (x.val + 5 * y.val) % 5 = x.val := by omega
  have hdiv : (x.val + 5 * y.val) / 5 = y.val := by omega
  simp only [ofLanes, Keccak.chi, Vector.getElem_ofFn, Keccak.lane, chi, xy,
    UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not,
    hmod, hdiv, Nat.mod_eq_of_lt hy, hz, decide_true, Bool.true_and]
  rfl

private theorem finiteRC : ∀ (t : Fin 255), rc t.val = Keccak.Internal.rc t.val := by
  decide +kernel
/-- The independent register bit agrees with the lane constant generator for every index. -/
theorem rc_eq (t : Nat) : rc t = Keccak.Internal.rc t := by
  have h := finiteRC ⟨t % 255, Nat.mod_lt _ (by decide)⟩
  simpa only [rc, Keccak.Internal.rc, Nat.mod_mod] using h
/-- Every FIPS round-constant bit agrees with the lane table. -/
theorem roundConstantBit_eq : ∀ (ir : Fin 24) (z : Fin 64),
    roundConstantBit ir.val z = (Keccak.RC[ir]).toBitVec.getLsbD z.val := by
  decide +kernel
/-- Iota agrees with the lane implementation at every state bit. -/
theorem iota_ofLanes (a : Keccak.State) (ir : Fin 24) :
    ofLanes (Keccak.iota ir a) = iota ir.val (ofLanes a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : x.val = 0 ∧ y.val = 0
  · have idx : x.val + 5 * y.val = 0 := by omega
    simp [ofLanes, Keccak.iota, iota, h, roundConstantBit_eq, UInt64.toBitVec_xor]
    rfl
  · have idx : x.val + 5 * y.val ≠ 0 := by omega
    simp only [ofLanes, Keccak.iota, iota, h, ite_false]
    rw [Vector.getElem_set_ne _ _ (Ne.symm idx)]

/-- The linear index of every bounded coordinate is in the 1600-bit state. -/
theorem index_lt (x y : Fin 5) (z : Fin 64) : index x y z < 1600 := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  simp only [index]
  omega

/-- Every source byte supplies exactly eight bits. -/
theorem byteBits_length (byte : UInt8) : (byteBits byte).length = 8 := by
  simp [byteBits]

/-- Message bit length is eight times the byte length. -/
theorem messageBits_length (msg : ByteArray) : (messageBits msg).length = 8 * msg.size := by
  unfold messageBits
  have h : ∀ bytes : List UInt8, (bytes.flatMap byteBits).length = 8 * bytes.length := by
    intro bytes
    induction bytes with
    | nil => simp
    | cons b bs ih => simp [byteBits_length, ih]; omega
  simpa only [Array.length_toList, ByteArray.size] using h msg.data.toList

/-- pad10*1 has its source-defined length for every bit length. -/
theorem padding_length (length : Nat) :
    (padding length).length = ((1088 - ((length + 2) % 1088)) % 1088) + 2 := by
  simp only [padding, List.length_cons, List.length_append, List.length_replicate, List.length_nil]

/-- pad10*1 ends on a rate boundary for every input length. -/
theorem padded_length_multiple (length : Nat) :
    (length + (padding length).length) % 1088 = 0 := by
  rw [padding_length]
  have h : (length + 2) % 1088 < 1088 := Nat.mod_lt _ (by decide)
  omega

/-- Every padded input consists of a whole number of rate-sized blocks. -/
theorem padded_blocks (msg : ByteArray) : 1088 ∣ (padded msg).length := by
  apply Nat.dvd_of_mod_eq_zero
  simpa [padded] using padded_length_multiple (messageBits msg).length

/-- The independent bit padding and byte implementation have the same total length. -/
theorem padded_length_eq_lane (msg : ByteArray) :
    (padded msg).length = 8 * (Keccak.pad msg).size := by
  simp only [padded, List.length_append, messageBits_length, padding_length,
    Keccak.size_pad, Keccak.RATE, Keccak.blockCount]
  omega


/-- Padding retains every message bit in its original position. -/
theorem padded_prefix (msg : ByteArray) :
    (padded msg).take (messageBits msg).length = messageBits msg := by
  simp only [padded, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

/-- Both representations split an input into the same number of rate blocks. -/
theorem padded_blockCount_eq (msg : ByteArray) :
    (padded msg).length / 1088 = Keccak.blockCount msg.size := by
  rw [padded_length_eq_lane, Keccak.size_pad]
  simp only [Keccak.RATE]
  omega

/-- Coordinate conversion reads the bit of the corresponding lane. -/
theorem ofLanes_index (a : Keccak.State) (x y : Fin 5) (z : Fin 64) :
    stateBit (ofLanes a) (index x y z) =
      (a[x.val + 5 * y.val]'(by simp only [Keccak.LANES]; omega)).toBitVec.getLsbD z.val := by
  rw [stateBit_index]
  rfl

/-- The source padding starts with one. -/
theorem padding_first (length : Nat) : (padding length).head? = some true := by
  rfl

/-- The source padding ends with one. -/
theorem padding_last (length : Nat) : (padding length).getLast? = some true := by
  change ((true :: List.replicate _ false) ++ [true]).getLast? = some true
  exact List.getLast?_concat

/-- Each extracted block bit is the corresponding padded source bit. -/
theorem paddedBlock_bit (msg : ByteArray) (i : Fin ((padded msg).length / 1088))
    (j : Fin 1088) :
    (paddedBlock msg i)[j] = (padded msg)[1088 * i.val + j.val]'(by
      have hm := padded_size_multiple msg
      have hi := i.isLt
      have hj := j.isLt
      omega) := by
  simp [paddedBlock]

/-- Absorption leaves capacity bits unchanged, for any complete block. -/
theorem absorb_capacity (a : State) (block : Block) (x y : Fin 5) (z : Fin 64)
    (capacity : 1088 ≤ index x y z) : absorb a block x y z = a x y z := by
  simp [absorb, Nat.not_lt.mpr capacity]

/-- Absorption XORs each rate bit with its corresponding block bit. -/
theorem absorb_rate (a : State) (block : Block) (x y : Fin 5) (z : Fin 64)
    (rate : index x y z < 1088) :
    absorb a block x y z = Bool.xor (a x y z) (block[index x y z]'rate) := by
  simp [absorb, rate]

/-- The first round-constant bit is one, as in FIPS 202 Algorithm 5. -/
theorem rc_zero : rc 0 = true := by rfl

/-- Local transition correspondences compose over every finite list of block pairs.

The premise relates each supplied byte block and bit block for one transition.
It does not assume equality of complete hashes.
-/
theorem absorb_fold_of_step (blocks : List (List UInt8 × Block)) (initial : Keccak.State)
    (step : ∀ a pair, pair ∈ blocks →
      ofLanes (Keccak.keccakF (Keccak.Internal.absorbBlock a pair.1)) =
        permutation (absorb (ofLanes a) pair.2)) :
    ofLanes (blocks.foldl (fun a pair => Keccak.keccakF (Keccak.Internal.absorbBlock a pair.1)) initial) =
      (blocks.foldl (fun a pair => permutation (absorb a pair.2)) (ofLanes initial)) := by
  induction blocks generalizing initial with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.foldl_cons]
    have remaining : ∀ a pair, pair ∈ rest →
        ofLanes (Keccak.keccakF (Keccak.Internal.absorbBlock a pair.1)) =
          permutation (absorb (ofLanes a) pair.2) := by
      intro a pair member
      exact step a pair (List.mem_cons_of_mem _ member)
    rw [ih _ remaining, step _ _ (List.mem_cons_self ..)]

end EthLib.Cryptography.Hash.KeccakBits
