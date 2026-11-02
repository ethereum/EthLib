module

public import EthLib.Cryptography.Proofs.Hash.KeccakBitsSponge

/-!
# Keccak output extraction

FIPS 202 section 4, Algorithm 8, truncates the state to the requested output length.
Appendix B.1 gives the byte and bit ordering.
-/

@[expose] public section
namespace EthLib.Cryptography.Hash.KeccakBits

private theorem squeezeBit (a : Keccak.State) (i : Fin 32) (j : Nat) (hj : j < 8) :
    ((Keccak.Internal.squeeze a)[i]).toBitVec.getLsbD j =
      (a[i.val / 8]'(by simp [Keccak.LANES]; have := i.isLt; omega)).toBitVec.getLsbD (8 * (i.val % 8) + j) := by
  have hi := i.isLt
  simp only [Keccak.Internal.squeeze, Keccak.DIGEST_LEN]
  change ((Vector.ofFn (fun k : Fin 32 => (a[k.val / 8]'(by simp [Keccak.LANES]; omega) >>> UInt64.ofNat (8 * (k.val % 8))).toUInt8))[i.val]'hi).toBitVec.getLsbD j = _
  rw [Vector.getElem_ofFn]
  simp only [UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat', BitVec.ushiftRight_eq',
    BitVec.getLsbD_ushiftRight, BitVec.toNat_umod, BitVec.toNat_ofNat]
  have shiftBound : 8 * (i.val % 8) < 64 := by omega
  have large : 8 * (i.val % 8) < 2 ^ 64 := by omega
  simp only [show (64 : BitVec 64).toNat = 64 by decide,
    Nat.mod_eq_of_lt large, Nat.mod_eq_of_lt shiftBound]
/-- Each packed output byte agrees with the lane sponge squeeze. -/
theorem outputByte_eq_squeeze (a : Keccak.State) (i : Fin 32) :
    outputByte (ofLanes a) i.val = (Keccak.Internal.squeeze a)[i] := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  calc
    (outputByte (ofLanes a) i.val).toBitVec.getLsbD j = stateBit (ofLanes a) (8 * i.val + j) :=
      outputByte_bit (ofLanes a) i.val ⟨j, hj⟩
    _ = (a[i.val / 8]'(by simp [Keccak.LANES]; have := i.isLt; omega)).toBitVec.getLsbD (8 * (i.val % 8) + j) :=
      state_output_bit a i.val j i.isLt hj
    _ = ((Keccak.Internal.squeeze a)[i]).toBitVec.getLsbD j := (squeezeBit a i j hj).symm

end EthLib.Cryptography.Hash.KeccakBits
