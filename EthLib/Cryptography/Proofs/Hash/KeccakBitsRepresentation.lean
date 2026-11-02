module

public import EthLib.Cryptography.Proofs.Hash.KeccakBitsRefinement

/-!
# Keccak state representation

FIPS 202 section 3.1.2 places bit `z` of lane `(x, y)` at
`64 * (x + 5 * y) + z` in the state string.
The conversion packs bits in that order.
-/

@[expose] public section
namespace EthLib.Cryptography.Hash.KeccakBits

/-- Pack every coordinate of a bit state into its little-endian 64-bit lane. -/
def toLanes (a : State) : Keccak.State :=
  Vector.ofFn fun i => UInt64.ofBitVec ((BitVec.ofBoolListLE
    (List.ofFn fun z : Fin 64 => a (xy (i.val % 5)) (xy (i.val / 5)) z)).cast (by simp))
/-- Each bit of a packed lane is the corresponding bit-state coordinate. -/
theorem toLanes_bit (a : State) (i : Fin 25) (z : Fin 64) :
    ((toLanes a)[i]).toBitVec.getLsbD z.val = a (xy (i.val % 5)) (xy (i.val / 5)) z := by
  change ((toLanes a)[i.val]'(by simp [Keccak.LANES])).toBitVec.getLsbD z.val = _
  simp only [toLanes, Vector.getElem_ofFn, UInt64.toBitVec_ofBitVec, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some, List.getElem_ofFn]
/-- Packing and unpacking preserves every bit state. -/
theorem ofLanes_toLanes (a : State) : ofLanes (toLanes a) = a := by
  funext x y z
  have idx : x.val + 5 * y.val < 25 := by have := x.isLt; have := y.isLt; omega
  have h := toLanes_bit a ⟨x.val + 5*y.val, idx⟩ z
  change ((toLanes a)[x.val + 5*y.val]'(by simpa [Keccak.LANES] using idx)).toBitVec.getLsbD z.val = a x y z
  have h1 : (x.val + 5*y.val)%5 = x.val := by have := x.isLt; omega
  have h2 : (x.val + 5*y.val)/5 = y.val := by have := x.isLt; omega
  simpa [xy, h1, h2, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] using h
/-- Unpacking and packing preserves every lane state. -/
theorem toLanes_ofLanes (a : Keccak.State) : toLanes (ofLanes a) = a := by
  apply Vector.ext
  intro i hi
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  have h := toLanes_bit (ofLanes a) ⟨i, by simpa [Keccak.LANES] using hi⟩ ⟨z, hz⟩
  have hidx : i % 5 + 5 * (i / 5) = i := by omega
  simpa [ofLanes, xy, Nat.mod_mod, hidx, Nat.mod_eq_of_lt (show i / 5 < 5 by simp only [Keccak.LANES] at hi; omega)] using h

/-- The theta mapping agrees for every bit state. -/
theorem toLanes_theta (a : State) : toLanes (theta a) = Keccak.theta (toLanes a) := by
  have h := congrArg toLanes (theta_ofLanes (toLanes a))
  simpa only [ofLanes_toLanes, toLanes_ofLanes] using h.symm
/-- The rho mapping agrees for every bit state. -/
theorem toLanes_rho (a : State) : toLanes (rho a) = Keccak.rho (toLanes a) := by
  have h := congrArg toLanes (rho_ofLanes (toLanes a))
  simpa only [ofLanes_toLanes, toLanes_ofLanes] using h.symm
/-- Pi agrees for every bit state. -/
theorem toLanes_pi (a : State) : toLanes (pi a) = Keccak.pi (toLanes a) := by
  have h := congrArg toLanes (pi_ofLanes (toLanes a))
  simpa only [ofLanes_toLanes, toLanes_ofLanes] using h.symm

/-- Chi agrees for every bit state. -/
theorem toLanes_chi (a : State) : toLanes (chi a) = Keccak.chi (toLanes a) := by
  have h := congrArg toLanes (chi_ofLanes (toLanes a))
  simpa only [ofLanes_toLanes, toLanes_ofLanes] using h.symm

/-- Iota agrees for every bit state and FIPS round index. -/
theorem toLanes_iota (a : State) (ir : Fin 24) : toLanes (iota ir.val a) = Keccak.iota ir (toLanes a) := by
  have h := congrArg toLanes (iota_ofLanes (toLanes a) ir)
  simpa only [ofLanes_toLanes, toLanes_ofLanes] using h.symm
/-- A round agrees for every bit state and FIPS round index. -/
theorem toLanes_round (a : State) (ir : Fin 24) : toLanes (round ir.val a) = Keccak.round ir (toLanes a) := by
  have h := congrArg toLanes (round_ofLanes (toLanes a) ir)
  simpa only [ofLanes_toLanes, toLanes_ofLanes] using h.symm
/-- The full permutation agrees for every bit state. -/
theorem toLanes_permutation (a : State) : toLanes (permutation a) = Keccak.keccakF (toLanes a) := by
  have h := congrArg toLanes (permutation_ofLanes (toLanes a))
  simpa only [ofLanes_toLanes, toLanes_ofLanes] using h.symm
/-- Column parity is the parity of the five packed lane bits. -/
theorem column_toLanes (a : State) (x : Fin 5) (z : Fin 64) :
    let bit := fun y : Fin 5 => ((toLanes a)[x.val + 5*y.val]'(by simp [Keccak.LANES]; have := x.isLt; have := y.isLt; omega)).toBitVec.getLsbD z.val
    column a x z = Bool.xor (Bool.xor (Bool.xor (Bool.xor (bit 0) (bit 1)) (bit 2)) (bit 3)) (bit 4) := by
  have h : column a x z = column (ofLanes (toLanes a)) x z := by rw [ofLanes_toLanes]
  rw [h]
  rfl

end EthLib.Cryptography.Hash.KeccakBits
