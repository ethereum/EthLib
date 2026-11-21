module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphSource

/-!
# Private calls in the graph of one public parameter

The leanXMSS draft gives chain starts and message randomizers different address types.

See sections "WOTS+C" and "The scheme".

Only the chain-start derivations enter the graph's labelled table.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient

open Constants HashSig OracleComp OracleSpec RandomOraclePairedValue SecretEncoding.Residual
open scoped Classical

/-- On a chain PRF word the two forwarded labels are the adjacent starts.

The residual caches retain their complete previous contents.
-/
theorem residual_pair (pp : PublicParam) (layer : Layer) (epoch : UInt32) (j : Fin (V / 2))
    (extra : ResidualCache pp) :
    residualProgram pp (liftM (Source.query (.inr (pp, addrPrf layer epoch j,
      ByteArray.empty)))) extra =
      (do
        let lo ← (liftM (ChainWorld.query (.inr (layer, epoch,
          ChainGraph.indexAt j 0))) : OracleComp ChainWorld _)
        let hi ← (liftM (ChainWorld.query (.inr (layer, epoch,
          ChainGraph.indexAt j 1))) : OracleComp ChainWorld _)
        return (PairedHashWord.halves.symm (lo, hi), extra)) := by
  obtain ⟨lo, hi⟩ := privateKeyEquiv_pair pp layer epoch j
  simp only [residualProgram, keyedProgram, simulateQ_spec_query, Derivations.expand,
    Derivations.pair, simulateQ_bind, simulateQ_pure, Derivations.privateWord,
      SecretEncoding.reindexQueries,
    StateT.run_bind, StateT.run_pure]
  rw [lo, hi]
  simp [handler]

/-- Every tagged randomizer word belongs to the residual table at both layers. -/
theorem randomizer_residual (pp : PublicParam) (layer : Layer) (epoch : UInt32) (msg : ByteArray) :
    let key : PrfInput := (pp, addrRnd layer epoch, msg)
    (Sum.inl key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp) ∧
      (Sum.inr key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp) := by
  intro key
  have sep (k : StartKey) : startLabel pp k ≠ key := by
    intro eq
    have addr := congrArg (fun i : PrfInput => i.2.1) eq
    change addrPrf k.1 k.2.1 (ChainGraph.pairIndex k.2.2) = addrRnd layer epoch at addr
    unfold addrPrf addrRnd at addr
    exact (by decide : AddressType.prf.code ≠ AddressType.rnd.code) (encodeAddress_inj.mp addr).1
  constructor <;> rintro ⟨k, h⟩ <;> apply sep k
  · calc
      startLabel pp k = (taggedStart pp k).elim id id := by unfold taggedStart; split <;> rfl
      _ = key := congrArg (Sum.elim id id) h
  · calc
      startLabel pp k = (taggedStart pp k).elim id id := by unfold taggedStart; split <;> rfl
      _ = key := congrArg (Sum.elim id id) h

/-- Query two residual PRF halves with the original local table.

The only effects forwarded to the graph world are uniform draws on cache misses.
-/
theorem residual_other (pp : PublicParam) (key : PrfInput)
    (low : (Sum.inl key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (high : (Sum.inr key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (extra : ResidualCache pp) :
    let a : OtherPrivate pp := ⟨Sum.inl key, low⟩
    let b : OtherPrivate pp := ⟨Sum.inr key, high⟩
    let table := (OtherPrivate pp →ₒ BitVec digestBits).randomOracle
    residualProgram pp (liftM (Source.query (.inr key))) extra = (do
      let first ← (liftM ((table a).run extra.2) : OracleComp ChainWorld _)
      let second ← (liftM ((table b).run first.2) : OracleComp ChainWorld _)
      return (PairedHashWord.halves.symm (first.1, second.1), (extra.1, second.2))) := by
  intro a b table
  have lo : (privateKeyEquiv pp).symm (.inl key) = Sum.inr a :=
    (privateKeyEquiv pp).symm_apply_eq.mpr (privateKeyEquiv_other pp a).symm
  have hi : (privateKeyEquiv pp).symm (.inr key) = Sum.inr b :=
    (privateKeyEquiv pp).symm_apply_eq.mpr (privateKeyEquiv_other pp b).symm
  simp only [residualProgram, keyedProgram, simulateQ_spec_query, Derivations.expand,
    Derivations.pair, simulateQ_bind, simulateQ_pure, Derivations.privateWord,
    SecretEncoding.reindexQueries, StateT.run_bind, StateT.run_pure]
  rw [lo, hi]
  simp [handler, table, bind_map_left]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
