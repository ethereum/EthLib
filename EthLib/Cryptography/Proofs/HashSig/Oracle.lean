module

public import EthLib.Cryptography.Proofs.EvalDistEq
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import EthLib.Cryptography.Proofs.HashSig
public import ToCslib.Data.Fin.MOfFn

/-!
# Proofs: the random oracle of the hash-based signatures

The security games of leanXMSS and leanSPHINCS share one random oracle.

It takes any byte string and answers 256 uniform bits.

The games also sample uniform values privately, and those samples are not hash calls.

The low 128 bits of a uniform answer are a uniform 128-bit value.

The games compute a function in order, as the lemmas of the oracle framework do.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace EthLib.Cryptography.HashSig

/-! ## The oracle -/

/-- The bits of a 16-byte digest. -/
def digestBits : Nat := 128

/-- The bits of a 32-byte oracle answer. -/
def hashOutputBits : Nat := 256

/-- An oracle input: any byte string. -/
abbrev HashInput := List UInt8

/-- An oracle answer, as a little-endian bit vector. -/
abbrev HashOutput := BitVec hashOutputBits

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- Private uniform sampling and the shared hash oracle.

Only hash calls count toward the query budget. -/
abbrev OracleWorld := unifSpec + HashSpec

/-- One query to the random oracle `H`. -/
def oracleHash {m : Type → Type} [Monad m] [HasQuery HashSpec m] (input : HashInput) :
    m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-! ## Truncation -/

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : BitVec digestBits :=
  output.extractLsb' 0 digestBits

theorem hashOutputBits_eq : hashOutputBits = digestBits + digestBits := by
  decide

/-- A 256-bit oracle output viewed as two digest halves.

Truncation keeps the low half. -/
def splitHashOutput (output : HashOutput) : BitVec (digestBits + digestBits) :=
  output.cast hashOutputBits_eq

/-- The answer whose high half is `high` and whose low half is `low`. -/
def joinDigest (high low : BitVec digestBits) : HashOutput :=
  (high ++ low).cast hashOutputBits_eq.symm

/-- The high half of an answer. -/
def highDigest (output : HashOutput) : BitVec digestBits :=
  (splitHashOutput output).extractLsb' digestBits digestBits

/-- A 256-bit random-oracle answer is equivalently two independent parts.

These are a high half and the 128-bit digest. -/
def hashOutputEquivDigestPair : HashOutput ≃ BitVec digestBits × BitVec digestBits where
  toFun output := (highDigest output, truncateHash output)
  invFun halves := joinDigest halves.1 halves.2
  left_inv output := by
    calc
      joinDigest (highDigest output) (truncateHash output) =
          (splitHashOutput output).cast hashOutputBits_eq.symm := by
        exact congrArg (BitVec.cast hashOutputBits_eq.symm)
          (BitVec.extractLsb'_append_extractLsb' (x := splitHashOutput output))
      _ = output := by simp [splitHashOutput]
  right_inv halves := by
    apply Prod.ext
    · change BitVec.extractLsb' digestBits digestBits (halves.1 ++ halves.2) = halves.1
      exact BitVec.extractLsb'_append_eq_left
    · change BitVec.extractLsb' 0 digestBits (halves.1 ++ halves.2) = halves.2
      exact BitVec.extractLsb'_append_eq_right

/-- Two independent uniform halves, the high one first. -/
noncomputable def independentDigestHalves : ProbComp (BitVec digestBits × BitVec digestBits) := do
  let high ← $ᵗ BitVec digestBits
  let low ← $ᵗ BitVec digestBits
  return (high, low)

/-- Splitting a uniform 256-bit answer gives two independent uniform 128-bit halves. -/
theorem evalDist_split_uniformHashOutput_eq_independent :
    (hashOutputEquivDigestPair <$> ($ᵗ HashOutput)) =ᵈ independentDigestHalves := by
  calc
    (hashOutputEquivDigestPair <$> ($ᵗ HashOutput)) =ᵈ
        ($ᵗ (BitVec digestBits × BitVec digestBits)) :=
      SampleableType.map_uniformSample_evalDistEq_of_bijective
        hashOutputEquivDigestPair.bijective
    _ =ᵈ independentDigestHalves := by
      unfold independentDigestHalves
      rw [SampleableType.uniformSample_prod_eq_bind]

/-- Truncating a uniform 256-bit answer gives a uniform 128-bit digest. -/
theorem evalDist_truncate_uniformHashOutput :
    (truncateHash <$> ($ᵗ HashOutput)) =ᵈ ($ᵗ BitVec digestBits) := by
  calc
    (truncateHash <$> ($ᵗ HashOutput)) =ᵈ
        (Prod.snd <$> (hashOutputEquivDigestPair <$> ($ᵗ HashOutput))) := by
      simp [Functor.map_map, hashOutputEquivDigestPair]
    _ =ᵈ (Prod.snd <$> independentDigestHalves) :=
      evalDist_split_uniformHashOutput_eq_independent.map _
    _ =ᵈ ($ᵗ BitVec digestBits) := by
      unfold independentDigestHalves
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply, bind_pure]
      exact OracleComp.EvalDistEq.bind_const _ _

/-! ## Computing a function in order -/

/-- The games' function computed in order is the one the oracle framework's lemmas use. -/
theorem sequenceFin_eq_mOfFn {m : Type → Type} [Monad m] {α : Type} :
    ∀ (n : Nat) (c : Fin n → m α), sequenceFin c = Fin.mOfFn n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [sequenceFin, Fin.mOfFn, sequenceFin_eq_mOfFn n]
    rfl

end EthLib.Cryptography.HashSig
