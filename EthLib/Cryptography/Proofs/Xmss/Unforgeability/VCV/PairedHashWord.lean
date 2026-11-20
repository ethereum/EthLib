module

public import EthLib.Cryptography.Proofs.HashSig.Bytes
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue

/-!
# Read one leanXMSS hash word through its two halves

The leanXMSS draft at leanVM commit `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`,
"Hashing and parameters" and "WOTS+C", uses the first and last 16 bytes as separate chain starts.

The low row holds the bits for the first 16 bytes and the high row those for the last 16 bytes.
Joining the rows restores the word seen by a caller of the shared hash oracle.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.PairedHashWord

open HashSig OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

/-- The low half comes first in the byte order used by the chains. -/
abbrev halves : HashOutput ≃ BitVec digestBits × BitVec digestBits :=
  hashOutputEquivDigestPair.trans (Equiv.prodComm _ _)

/-- The first row encodes exactly the bytes used by an even chain. -/
theorem first_half_bytes (word : HashOutput) :
    halfOf 0 (ofOutput word) = ofBV 16 (halves word).1 := by
  change halfOf 0 (ofOutput word) = ofBV 16 (truncateHash word)
  apply Vector.ext
  intro i hi
  rw [getElem_halfOf]
  simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add]
  exact getElem_ofOutput_of_lt word i hi

/-- The second row encodes exactly the bytes used by an odd chain. -/
theorem second_half_bytes (word : HashOutput) :
    halfOf 1 (ofOutput word) = ofBV 16 (halves word).2 := by
  change halfOf 1 (ofOutput word) = ofBV 16 (word.extractLsb' 128 128)
  apply Vector.ext (n := 16)
  intro i hi
  calc
    _ = (ofBV 32 word)[16 * (1 : Fin 2).val + i]'(by change 16 * 1 + i < 32; omega) := by
      exact getElem_halfOf 1 (ofOutput word) i hi
    _ = UInt8.ofBitVec (word.extractLsb' (8 * (16 * (1 : Fin 2).val + i)) 8) :=
      getElem_ofBV 32 word _ _
    _ = UInt8.ofBitVec (word.extractLsb' (128 + 8 * i) 8) := by
      apply congrArg (fun j => UInt8.ofBitVec (word.extractLsb' j 8))
      change 8 * (16 * 1 + i) = 128 + 8 * i
      omega
    _ = UInt8.ofBitVec ((word.extractLsb' 128 128).extractLsb' (8 * i) 8) :=
      congrArg UInt8.ofBitVec (extractLsb'_byte_low word 128 128 i (by omega)).symm
    _ = _ := (getElem_ofBV 16 _ i hi).symm

/-- The two rows for a hash input have distinct tags. -/
abbrev HalfSpec := (HashInput ⊕ HashInput) →ₒ BitVec digestBits

/-- Split every populated word in a cache, leaving empty rows empty. -/
abbrev splitCache (cache : HashSpec.QueryCache) : HalfSpec.QueryCache :=
  RandomOraclePairedValue.splitCache halves cache

/-- A complete pair of rows reconstructs one original word. -/
abbrev joinCache (cache : HalfSpec.QueryCache) : HashSpec.QueryCache :=
  RandomOraclePairedValue.joinCache halves cache

/-- A hash query returns the same distribution of reply and complete caches in either representation. -/
theorem hash_query_joint (input : HashInput) (initial : HashSpec.QueryCache) :
    (fun z : HashOutput × HashSpec.QueryCache => (z.1, z.2, splitCache z.2)) <$>
      (HashSpec.randomOracle input).run initial =ᵈ
    (fun z : HashOutput × HalfSpec.QueryCache => (z.1, joinCache z.2, z.2)) <$>
      (simulateQ HalfSpec.randomOracle (do
        let low ← liftM (HalfSpec.query (.inl input))
        let high ← liftM (HalfSpec.query (.inr input))
        pure (halves.symm (low, high)))).run (splitCache initial) :=
  RandomOraclePairedValue.run_pair_macro_evalDistEq_full_joint halves input initial

/-- Private uniform queries pass through and each public hash returns a complete word. -/
abbrev readHalves : QueryImpl OracleWorld (OracleComp (unifSpec + HalfSpec)) :=
  RandomOraclePairedValue.readHalves halves

/-- Every adaptive caller sees the same joint law of its result and both forms of the final cache. -/
theorem run_joint {α : Type} (caller : OracleComp OracleWorld α) (initial : HashSpec.QueryCache) :
    (fun z : α × HashSpec.QueryCache => (z.1, z.2, splitCache z.2)) <$>
      (simulateQ HashSpec.romImpl caller).run initial =ᵈ
    (fun z : α × HalfSpec.QueryCache => (z.1, joinCache z.2, z.2)) <$>
      (simulateQ HalfSpec.romImpl (simulateQ readHalves caller)).run (splitCache initial) :=
  RandomOraclePairedValue.evalDist_world_run_joint halves caller initial

end EthLib.Cryptography.Xmss.Unforgeability.VCV.PairedHashWord
