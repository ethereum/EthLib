module

public import EthLib.Cryptography.Proofs.HashSig.Bytes
public import EthLib.Cryptography.Proofs.Hash.Keccak.Lanes

/-!
# Proofs: the oracle on strings of lanes

The lanes are FIPS 202's representation of the state (§3.1.2, Appendix B.1).

A query on a string of lanes queries the byte oracle at the bytes of the lanes.

Its answer splits into four lanes, whose halves are the answer's low and high 128 bits.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open OracleSpec OracleComp ENNReal
open EthLib.Cryptography.Hash.Keccak

/-! ## Bit vectors as lanes -/

/-- The low 128 bits of a bit vector as two lanes. -/
def ofDigestLanes {w : Nat} (x : BitVec w) : Lanes2 :=
  ⟨UInt64.ofBitVec (x.extractLsb' 0 64), UInt64.ofBitVec (x.extractLsb' 64 64)⟩

/-- The low 256 bits of a bit vector, an oracle answer, as four lanes. -/
def ofOutputLanes {w : Nat} (x : BitVec w) : Lanes4 :=
  ⟨UInt64.ofBitVec (x.extractLsb' 0 64), UInt64.ofBitVec (x.extractLsb' 64 64),
    UInt64.ofBitVec (x.extractLsb' 128 64), UInt64.ofBitVec (x.extractLsb' 192 64)⟩

/-- Byte `q` of the lane at bit `off` of a bit vector is the vector's byte `off / 8 + q`. -/
private theorem byte_lane {w : Nat} (x : BitVec w) (off q : Nat) (hq : q < 8) :
    (Internal.bytesOfLane (UInt64.ofBitVec (x.extractLsb' off 64))).getD q 0 =
      UInt8.ofBitVec (x.extractLsb' (off + 8 * q) 8) := by
  rw [getD_bytesOfLane _ _ hq, ← extractLsb'_byte_low x off 64 q (by omega)]
  apply UInt8.toNat_inj.mp
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, BitVec.extractLsb'_toNat]
  rw [Nat.mod_eq_of_lt (by omega : 8 * q < 64)]

/-- The bytes of the low 256 bits as four lanes are the vector's 32 low bytes. -/
theorem bytes_ofOutputLanes {w : Nat} (x : BitVec w) : (ofOutputLanes x).bytes = ofOutput x := by
  apply Vector.ext
  intro j hj
  rw [getElem_ofBV, getElem_lanes4_bytes _ _ hj]
  simp only [ofOutputLanes]
  split_ifs <;> rw [byte_lane _ _ _ (by omega)] <;> congr 2 <;> omega

/-- The bytes of the low 128 bits as two lanes are the vector's 16 low bytes. -/
theorem bytes_ofDigestLanes {w : Nat} (x : BitVec w) : (ofDigestLanes x).bytes = ofBV 16 x := by
  apply Vector.ext
  intro j hj
  rw [getElem_ofBV, getElem_lanes2_bytes _ _ hj]
  simp only [ofDigestLanes]
  split_ifs <;> rw [byte_lane _ _ _ (by omega)] <;> congr 2 <;> omega

/-- The first two lanes of an answer are its low 128 bits as two lanes. -/
theorem first_lanes_ofOutputLanes (x : HashOutput) :
    (⟨(ofOutputLanes x).w0, (ofOutputLanes x).w1⟩ : Lanes2) = ofDigestLanes (truncateHash x) := by
  simp only [ofOutputLanes, ofDigestLanes, truncateHash, digestBits,
    extractLsb'_extractLsb'_add _ _ _ _ _ (show 0 + 64 ≤ 128 by omega),
    extractLsb'_extractLsb'_add _ _ _ _ _ (show 64 + 64 ≤ 128 by omega)]

/-- The last two lanes of an answer are its high 128 bits as two lanes. -/
theorem last_lanes_ofOutputLanes (x : HashOutput) :
    (⟨(ofOutputLanes x).w2, (ofOutputLanes x).w3⟩ : Lanes2) = ofDigestLanes (highDigest x) := by
  simp only [ofOutputLanes, ofDigestLanes, highDigest, splitHashOutput, digestBits,
    extractLsb'_extractLsb'_add _ _ _ _ _ (show 0 + 64 ≤ 128 by omega),
    extractLsb'_extractLsb'_add _ _ _ _ _ (show 64 + 64 ≤ 128 by omega)]
  -- The cast to two halves changes the type of the answer, not its bits.
  simp
  exact ⟨rfl, rfl⟩

/-- Two 128-bit vectors with the same two lanes are equal. -/
theorem ofDigestLanes_injective : Function.Injective (ofDigestLanes (w := digestBits)) := by
  intro x y h
  simp only [ofDigestLanes, Lanes2.mk.injEq, UInt64.ofBitVec.injEq] at h
  obtain ⟨h0, h1⟩ := h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hi64 : i < 64
  · have := congrArg (fun v => v.getLsbD i) h0
    simpa [hi64] using this
  · have := congrArg (fun v => v.getLsbD (i - 64)) h1
    simpa [show i - 64 < 64 by simp [digestBits] at hi; omega, show 64 + (i - 64) = i by omega]
      using this

/-- The low 128 bits as two lanes are in bijection with the values of two lanes. -/
theorem ofDigestLanes_bijective : Function.Bijective (ofDigestLanes (w := digestBits)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨ofDigestLanes_injective, ?_⟩
  rw [card_lanes2, Fintype.card_bitVec]
  rfl

/-! ## The oracle on lanes -/

/-- `H` as a query to the oracle, on strings of lanes.

The bytes of the lanes go in, and the answer comes out as four lanes. -/
def queryLanes {m : Type → Type} [Monad m] [HasQuery HashSpec m] (input : Array UInt64) :
    m Lanes4 :=
  ofOutputLanes <$> oracleHash (m := m) (lanesBytes input)

/-- The low 128 bits of a uniform answer, as two lanes, are uniform. -/
theorem prEvent_ofDigestLanes_truncateHash (P : Lanes2 → Prop) :
    Pr{let u ← $ᵗ HashOutput}[P (ofDigestLanes (truncateHash u))]
      = (Nat.card {d : Lanes2 // P d} : ℝ≥0∞) / 2 ^ 128 := by
  classical
  rw [← prEvent_map ($ᵗ HashOutput) truncateHash (fun b => P (ofDigestLanes b)),
    EvalDistEq.prEvent_eq evalDist_truncate_uniformHashOutput,
    SampleableType.prEvent_uniformSample, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  -- The 128-bit values and the values of two lanes are in bijection through the lanes.
  have hc : Nat.card {b : BitVec digestBits // P (ofDigestLanes b)} =
      Nat.card {d : Lanes2 // P d} :=
    Nat.card_congr
      ((Equiv.ofBijective _ ofDigestLanes_bijective).subtypeEquiv fun _ => Iff.rfl)
  rw [hc]
  congr 1
  norm_num [digestBits]

end EthLib.Cryptography.HashSig
