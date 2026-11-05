module

public import EthLib.Cryptography.Proofs.Models.KeccakBits
public import EthLib.Cryptography.Proofs.Hash.KeccakPermutation

/-!
# Proofs: Keccak-f[1600] on lanes and on bits

`Hash.Keccak` computes Keccak-f[1600] on 25 lanes of 64 bits.

The model `Models.KeccakBits` computes it on 1600 single bits, as FIPS 202 §3.2 writes it.

FIPS 202 §3.1.2 places bit `z` of lane `(x, y)` at position `64 * (x + 5 * y) + z` of the state.

This file reads each lane state at those positions.

Each step mapping commutes with that reading.

So the two permutations agree on every state.
-/

@[expose] public section

namespace EthLib.Cryptography.Models.KeccakBits

open EthLib.Cryptography.Hash

/-! ## Bit coordinates -/

/-- A lane state viewed at the bit coordinates of FIPS 202 §3.1.2. -/
def ofLanes (a : Keccak.State) : State := fun x y z => (a.lane x y).toBitVec.getLsbD z.val

/-- The bit view of a state built lane by lane reads the bits of those lanes. -/
theorem ofLanes_ofLanes (f : Fin 5 → Fin 5 → UInt64) :
    ofLanes (Keccak.State.ofLanes f) = fun x y z => (f x y).toBitVec.getLsbD z.val := by
  funext x y z
  simp only [ofLanes, Keccak.lane_ofLanes]

/-- Flattening a coordinate and reading it recovers that coordinate. -/
theorem stateBit_index (a : State) (x y : Fin 5) (z : Fin 64) :
    stateBit a (index x y z) = a x y z := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  unfold stateBit index xy zcoord
  congr 1 <;> apply Fin.ext <;> simp only <;> omega

/-- The `Fin 5` sums of the lane formulas are the wrapped sums of the bit model. -/
private theorem coordinates :
    (∀ x y : Fin 5, x + 3 * y = xy (x.val + 3 * y.val)) ∧
    (∀ x : Fin 5, x - 1 = xy (x.val + 4)) ∧ (∀ x : Fin 5, x + 1 = xy (x.val + 1)) ∧
    (∀ x : Fin 5, x + 2 = xy (x.val + 2)) := by
  decide

/-! ## The step mappings -/

/-- Pi agrees with the lane implementation at every state bit. -/
theorem pi_ofLanes (a : Keccak.State) : ofLanes (Keccak.pi a) = pi (ofLanes a) := by
  rw [Keccak.pi_eq, ofLanes_ofLanes]
  funext x y z
  simp only [pi, ofLanes, coordinates.1]

/-- The rho walk of the model gives the offset of the lane table at every lane. -/
theorem rhoOffset_eq : ∀ x y : Fin 5,
    rhoOffset x y = (Keccak.RHO[x.val + 5 * y.val]'(by simp only [Keccak.LANES]; omega)).toNat := by
  decide +kernel

/-- Every offset of the rho walk is below the lane width. -/
theorem rhoOffset_lt : ∀ x y : Fin 5, rhoOffset x y < 64 := by
  decide +kernel

/-- Rho agrees with the lane implementation at every state bit. -/
theorem rho_ofLanes (a : Keccak.State) : ofLanes (Keccak.rho a) = rho (ofLanes a) := by
  rw [Keccak.rho_eq, ofLanes_ofLanes]
  funext x y z
  have offset := rhoOffset_eq x y
  have bound := rhoOffset_lt x y
  simp only [rho, ofLanes, zcoord]
  rw [Keccak.getLsbD_rotl _ _ (by omega) _ z.isLt, ← offset, Nat.mod_eq_of_lt bound]

/-- A bit of a lane column parity is the column parity of the model. -/
private theorem column_bit (a : Keccak.State) (x : Fin 5) (z : Fin 64) :
    (a.column x).toBitVec.getLsbD z.val = column (ofLanes a) x z := by
  simp [Keccak.State.column, column, ofLanes, UInt64.toBitVec_xor]

/-- Theta agrees with the lane implementation at every state bit. -/
theorem theta_ofLanes (a : Keccak.State) : ofLanes (Keccak.theta a) = theta (ofLanes a) := by
  rw [Keccak.theta_eq, ofLanes_ofLanes]
  funext x y z
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  rw [Keccak.getLsbD_rotl _ _ (by decide) _ z.isLt, column_bit, coordinates.2.1]
  -- The rotation by one reads bit `z - 1`, which is bit `z + 63` mod 64.
  have shift : (z.val + 64 - (1 : UInt64).toNat % 64) % 64 = (z.val + 63) % 64 := by
    simp only [UInt64.reduceToNat]
    omega
  rw [shift, coordinates.2.2.1]
  have col := column_bit a (xy (x.val + 1)) ⟨(z.val + 63) % 64, Nat.mod_lt _ (by decide)⟩
  rw [col]
  rfl

/-- Chi agrees with the lane implementation at every state bit. -/
theorem chi_ofLanes (a : Keccak.State) : ofLanes (Keccak.chi a) = chi (ofLanes a) := by
  rw [Keccak.chi_eq, ofLanes_ofLanes]
  funext x y z
  simp only [chi, ofLanes, coordinates.2.2.1, coordinates.2.2.2,
    UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, z.isLt, decide_true,
    Bool.true_and]

/-- Every round-constant bit of the model is the bit of the lane table. -/
theorem roundConstantBit_eq : ∀ (ir : Fin Keccak.ROUNDS) (z : Fin 64),
    roundConstantBit ir.val z = (Keccak.RC[ir]).toBitVec.getLsbD z.val := by
  decide +kernel

/-- Iota agrees with the lane implementation at every state bit. -/
theorem iota_ofLanes (a : Keccak.State) (ir : Fin Keccak.ROUNDS) :
    ofLanes (Keccak.iota ir a) = iota ir.val (ofLanes a) := by
  rw [Keccak.iota_eq, ofLanes_ofLanes]
  funext x y z
  -- Lane `(0, 0)` is the one whose coordinates are both zero.
  have zero : (x = 0 ∧ y = 0) ↔ (x.val = 0 ∧ y.val = 0) := by
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨hx, hy⟩
      exact ⟨Fin.ext hx, Fin.ext hy⟩
  by_cases h : x.val = 0 ∧ y.val = 0
  · obtain ⟨hx, hy⟩ := zero.mpr h
    subst hx hy
    simp [iota, ofLanes, roundConstantBit_eq]
  · have h' : ¬ (x = 0 ∧ y = 0) := fun e => h (zero.mp e)
    simp only [h', ite_false, iota, h, ofLanes]

/-! ## The permutation -/

/-- One round of the model agrees with one lane round. -/
theorem round_ofLanes (a : Keccak.State) (ir : Fin Keccak.ROUNDS) :
    ofLanes (Keccak.round ir a) = round ir.val (ofLanes a) := by
  simp only [Keccak.round, round, iota_ofLanes, chi_ofLanes, pi_ofLanes, rho_ofLanes,
    theta_ofLanes]

/-- The lane rounds from `i` to 23 agree with the model rounds from `i` to 23. -/
theorem roundsFrom_ofLanes (n i : Nat) (h : i + n = 24) (a : Keccak.State) :
    ofLanes (Keccak.keccakF.roundsFrom i a) =
      (List.range' i n).foldl (fun s ir => round ir s) (ofLanes a) := by
  induction n generalizing i a with
  | zero =>
    -- At round 24 no round is left.
    rw [Keccak.keccakF.roundsFrom, dite_eq_right (by simp only [Keccak.ROUNDS]; omega)]
    rfl
  | succ n ih =>
    -- Run round `i`, then the rounds after it.
    have hi : i < Keccak.ROUNDS := by simp only [Keccak.ROUNDS]; omega
    rw [Keccak.keccakF.roundsFrom, dite_eq_left hi, ih (i + 1) (by omega), round_ofLanes,
      List.range'_succ, List.foldl_cons]

/-- Keccak-f[1600] on lanes agrees with the 24 rounds of the model on every state. -/
theorem permutation_ofLanes (a : Keccak.State) :
    ofLanes (Keccak.keccakF a) = permutation (ofLanes a) := by
  rw [Keccak.keccakF, roundsFrom_ofLanes 24 0 rfl, permutation, List.range_eq_range']

/-! ## Packing bits into lanes -/

/-- Pack the bits of each lane coordinate into its 64-bit lane, bit `z` in bit `z`. -/
def toLanes (a : State) : Keccak.State :=
  Keccak.State.ofLanes fun x y => UInt64.ofBitVec ((BitVec.ofBoolListLE
    (List.ofFn fun z : Fin 64 => a x y z)).cast (by simp))

/-- Each bit of a packed lane is the bit at the same coordinate. -/
theorem toLanes_bit (a : State) (x y : Fin 5) (z : Fin 64) :
    ((toLanes a).lane x y).toBitVec.getLsbD z.val = a x y z := by
  simp only [toLanes, Keccak.lane_ofLanes, UInt64.toBitVec_ofBitVec, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some, List.getElem_ofFn]

/-- Packing a bit state and reading it back gives the same bit state. -/
theorem ofLanes_toLanes (a : State) : ofLanes (toLanes a) = a := by
  funext x y z
  exact toLanes_bit a x y z

/-- Reading a lane state and packing it back gives the same lane state. -/
theorem toLanes_ofLanes (a : Keccak.State) : toLanes (ofLanes a) = a := by
  apply Keccak.State.ext_lane
  intro x y
  apply Keccak.lane_ext
  intro z hz
  exact toLanes_bit (ofLanes a) x y ⟨z, hz⟩

/-- The model permutation, packed into lanes, is Keccak-f[1600] on the packed state. -/
theorem toLanes_permutation (a : State) :
    toLanes (permutation a) = Keccak.keccakF (toLanes a) := by
  have h := congrArg toLanes (permutation_ofLanes (toLanes a))
  simpa only [ofLanes_toLanes, toLanes_ofLanes] using h.symm

end EthLib.Cryptography.Models.KeccakBits
