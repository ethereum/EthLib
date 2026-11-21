module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedResidual

/-!
# Replaying the private low row of a randomizer

The scheme selects the first 16 bytes of its private PRF word.

It reads the high row even when the low bytes are known.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig OracleComp OracleSpec
open ChainGraph (Word)
open scoped OracleSpec.PrimitiveQuery Classical

/-- Keep the complete result of the high-row lookup, including its new cache on a miss. -/
@[expose] noncomputable def finishLocalWord (pp : PublicParam) (hi : OtherPrivate pp) (low : Word)
    (s : ResidualCache pp) : OracleComp MixedWorld (HashOutput × ResidualCache pp) := do
  let high ← (liftM (((OtherPrivate pp →ₒ Word).randomOracle hi).run s.2) : OracleComp MixedWorld _)
  return (PairedHashWord.halves.symm (low, high.1), (s.1, high.2))

/-- The first draw is skipped whenever the low row is occupied. -/
theorem mixedLocalWord_low_hit (pp : PublicParam) (key : PrfInput)
    (lo : (Sum.inl key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (hi : (Sum.inr key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (s : ResidualCache pp) (v : Word) (hit : s.2 ⟨.inl key, lo⟩ = some v) :
    (mixedLocalWord pp key lo hi).run s = finishLocalWord pp ⟨.inr key, hi⟩ v s := by
  simp [mixedLocalWord, hit, finishLocalWord]

/-- A missing low row samples one independent 128-bit value before the high lookup. -/
theorem mixedLocalWord_low_miss (pp : PublicParam) (key : PrfInput)
    (lo : (Sum.inl key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (hi : (Sum.inr key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (s : ResidualCache pp) (cold : s.2 ⟨.inl key, lo⟩ = none) :
    (mixedLocalWord pp key lo hi).run s = (do
      let low ← (liftM ($ᵗ Word) : OracleComp MixedWorld Word)
      finishLocalWord pp ⟨.inr key, hi⟩ low (s.1, s.2.cacheQuery ⟨.inl key, lo⟩ low)) := by
  simp [mixedLocalWord, cold, finishLocalWord, bind_map_left]

/-- Project the scheme's randomizer while still performing the complete high-row operation. -/
theorem finishLocalWord_base (pp : PublicParam) (hi : OtherPrivate pp) (low : Word)
    (s : ResidualCache pp) :
    (fun z => (halfOf 0 (ofOutput z.1), z.2)) <$> finishLocalWord pp hi low s =
      (fun z => (ofBV 16 low, (s.1, z.2))) <$>
        (liftM (((OtherPrivate pp →ₒ Word).randomOracle hi).run s.2) : OracleComp MixedWorld
          _) := by
  simp [finishLocalWord, PairedHashWord.first_half_bytes, bind_pure_comp]
  rfl

/-- The exact byte-string callback used by the bottom or top signing finder. -/
@[expose] noncomputable def mixedBase (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) :
    MixedLocal pp Digest := StateT.mk fun s =>
  (fun z => (halfOf 0 (ofOutput z.1), z.2)) <$>
    (mixedLocalWord pp (pp, addrRnd l e, msg)
      (randomizer_residual pp l e msg).1 (randomizer_residual pp l e msg).2).run s

/-- After any earlier call at this same address, reuse its low word and still query the high row. -/
theorem mixedBase_hit (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (s : ResidualCache pp) (v : Word) :
    let key : PrfInput := (pp, addrRnd l e, msg)
    let outside := randomizer_residual pp l e msg
    s.2 ⟨.inl key, outside.1⟩ = some v →
      (mixedBase pp l e msg).run s = (fun z => (ofBV 16 v, (s.1, z.2))) <$>
        (liftM (((OtherPrivate pp →ₒ Word).randomOracle ⟨.inr key, outside.2⟩).run s.2) :
          OracleComp MixedWorld _) := by
  intro key outside hit
  simp only [mixedBase, StateT.run_mk]
  rw [mixedLocalWord_low_hit pp key outside.1 outside.2 s v hit]
  exact finishLocalWord_base pp _ v s

/-- A fresh randomizer originates in its own low row even if the corresponding high row was warm. -/
theorem mixedBase_miss (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (s : ResidualCache pp) :
    let key : PrfInput := (pp, addrRnd l e, msg)
    let outside := randomizer_residual pp l e msg
    s.2 ⟨.inl key, outside.1⟩ = none →
      (mixedBase pp l e msg).run s = (do
        let v ← (liftM ($ᵗ Word) : OracleComp MixedWorld Word)
        let table := s.2.cacheQuery ⟨.inl key, outside.1⟩ v
        (fun z => (ofBV 16 v, (s.1, z.2))) <$>
          (liftM (((OtherPrivate pp →ₒ Word).randomOracle ⟨.inr key, outside.2⟩).run table) :
            OracleComp MixedWorld _)) := by
  intro key outside cold
  simp only [mixedBase, StateT.run_mk]
  rw [mixedLocalWord_low_miss pp key outside.1 outside.2 s cold, map_bind]
  apply bind_congr
  intro v
  exact finishLocalWord_base pp _ v _

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
