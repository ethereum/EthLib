module

public import EthLib.Base.Proofs.LittleEndian
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Words as little-endian bytes

The leanXMSS specification, "Hashing and parameters", uses little-endian integers.

The equivalence uses the shared byte conversions and keeps all bits of the word.

At length 32 it keeps the full hash output, before either 16-byte half is taken.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV

/-- The shared little-endian conversions are inverse at every byte length, including zero. -/
def wordBytesEquiv (n : Nat) : BitVec (8 * n) ≃ Vector UInt8 n where
  toFun word := EthLib.Base.uintToBytes n word.toNat
  invFun bytes := BitVec.ofNat (8 * n) (EthLib.Base.bytesToUint bytes)
  left_inv word := by
    apply BitVec.eq_of_toNat_eq
    -- The byte modulus equals the word modulus, so encoding discards no bits.
    simp only [BitVec.toNat_ofNat, EthLib.Base.bytesToUint_uintToBytes]
    have hpow : (256 : Nat) ^ n = 2 ^ (8 * n) := by rw [pow_mul]; norm_num
    rw [hpow, Nat.mod_eq_of_lt word.isLt, Nat.mod_eq_of_lt word.isLt]
  right_inv bytes := by
    -- The decoded integer is below the word modulus, so constructing the word does not wrap.
    have hlt : EthLib.Base.bytesToUint bytes < 2 ^ (8 * n) := by
      simpa only [pow_mul, Nat.reducePow] using EthLib.Base.bytesToUint_lt bytes
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      EthLib.Base.uintToBytes_bytesToUint]

/-- The existing equivalence transport samples uniformly from all byte vectors. -/
theorem uniform_wordBytes (n : Nat)
    [MeasurableSpace (Vector UInt8 n)] [MeasurableSingletonClass (Vector UInt8 n)] :
    𝒟[(SampleableType.ofEquiv (wordBytesEquiv n)).selectElem] =
      ProbabilityTheory.uniformOn Set.univ :=
  SampleableType.evalDist_ofEquiv (wordBytesEquiv n)

end EthLib.Cryptography.Xmss.Unforgeability.VCV
