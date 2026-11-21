module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SingleBuildSource

/-!
# The two seed sources for the current single-build signer

Master derivation queries become paid ticks when the scheme word is fixed.

The second source issues one private request per PRF input.

The original client continues to see an optional signature after every request.

Source: leanXMSS draft, sections "Hashing and parameters" and "Security".
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient

open OracleComp OracleSpec
open XmssSecurity (HashSpec HashOutput MasterSeed)

/-- The master-seed source, queried at key generation and again on each signing request. -/
@[expose] def masterSource (A : Adversary) : OracleComp SeedSpec Outcome :=
  sourceOf (HashSpec.withDerivationsLift Unit HashOutput)
    (ofOutput <$> SeedSpec.query (.inr ()))
    (seedPrf (hashOf (HashSpec.withDerivationsLift Unit HashOutput))) A

/-- Realizing a master-seed request runs the original single-build game with that master seed. -/
theorem realize_master (s0 : MasterSeed) (A : Adversary) :
    simulateQ (seedEncoding.deriveImpl s0) (masterSource A) =
      sourceOf (QueryImpl.id' World) (schemeSeed (hashOf (QueryImpl.id' World)) (ofSeed s0))
        (seedPrf (hashOf (QueryImpl.id' World))) A := by
  have input : (ByteArray.mk Constants.SEED_TAG.toArray ++ packBytes (ofSeed s0)).data.toList =
      XmssSecurity.seedHashInput s0 := by
    simp only [HashSig.toList_data_append, HashSig.toList_data_packBytes, toList_ofSeed]
    rfl
  have key : simulateQ (seedEncoding.deriveImpl s0)
      (ofOutput <$> (SeedSpec.query (.inr ()) : OracleComp SeedSpec HashOutput)) =
      schemeSeed (hashOf (QueryImpl.id' World)) (ofSeed s0) := by
    rw [simulateQ_map, simulateQ_spec_query]
    unfold schemeSeed hashOf
    rw [input]
    rfl
  have prf : (fun (s : Seed) p a b => simulateQ (seedEncoding.deriveImpl s0)
      (seedPrf (hashOf (HashSpec.withDerivationsLift Unit HashOutput)) s p a b)) =
      seedPrf (hashOf (QueryImpl.id' World)) := by
    funext s p a b
    simp only [seedPrf, simulateQ_hashOf, SecretEncoding.deriveImpl_comp_withDerivationsLift]
  unfold masterSource
  erw [source_map, SecretEncoding.deriveImpl_comp_withDerivationsLift, key, prf]
  rfl

/-- Master source realization is exact before applying any interpreter or cost observer. -/
theorem observe_eq_master (A : Adversary) :
    observe A = (liftM XmssSecurity.sampleMasterSeed : OracleComp World _) >>= fun s0 =>
      simulateQ (seedEncoding.deriveImpl s0) (masterSource A) := by
  simp only [realize_master, observe_eq_source]

/-- A local paid call carries no data once the full scheme word has been sampled. -/
abbrev Tick := Unit →ₒ Unit
abbrev Backend := HashSpec + Tick
abbrev Ambient := unifSpec + Backend
abbrev Source := Backend.withDerivations PrfInput HashOutput

/-- Ordinary coin and byte queries retain their physical keys. -/
@[expose] def ordinary : QueryImpl World (OracleComp Ambient)
  | .inl n => liftM (Ambient.query (.inl n))
  | .inr raw => liftM (Ambient.query (.inr (.inl raw)))

/-- Move only the master-seed derivation to the auxiliary paid tick. -/
@[expose] def payMaster (word : HashOutput) : QueryImpl SeedSpec (OracleComp Ambient)
  | .inl t => ordinary t
  | .inr _ => (fun _ : Unit => word) <$>
      (liftM (Ambient.query (.inr (.inr ()))) : OracleComp Ambient Unit)

/-- The scheme source keeps the original hash, coin, tick and private full-word calls. -/
@[expose] def paidSource (A : Adversary) : OracleComp Source Outcome :=
  sourceOf (Backend.withDerivationsLift PrfInput HashOutput ∘ₛ ordinary)
    (liftM (Source.query (.inl (.inr (.inr ())))) : OracleComp Source Unit)
    (fun _ p a suffix => ofOutput <$> Source.query (.inr (p, a, suffix))) A

/-- Every private scheme input realizes to the actual byte string on the original hash port. -/
@[expose] def paidEncoding : SecretEncoding Backend HashOutput PrfInput HashOutput where
  enc w k := .inl (prfEncoding.enc (fun _ => w) k)
  range_eq _ _ := rfl
  injective w _ _ h := prfEncoding.injective (fun _ => w) (Sum.inl.inj h)

private theorem seed_map {ι τ σ : Type} {spec : OracleSpec ι}
    (pass : QueryImpl World (OracleComp spec))
    (seed : OracleComp spec σ) (f : σ → τ) (derive : τ → SeedPrf (OracleComp spec))
    (A : Adversary) :
    sourceOf pass (f <$> seed) derive A = sourceOf pass seed (fun s => derive (f s)) A := by
  have signer : signerOf pass (f <$> seed) derive = signerOf pass seed (fun s => derive (f s)) := by
    funext t
    cases t with
    | inl q => rfl
    | inr r => simp only [signerOf, failSignerOf, WriterT.run_mk, bind_map_left]
  simp only [sourceOf, bind_map_left, signer]

/-- The same complete observation on both sides uses the same physical tick for each master read. -/
theorem paid_square (word : HashOutput) (A : Adversary) :
    simulateQ (payMaster word) (masterSource A) =
      simulateQ (paidEncoding.deriveImpl word) (paidSource A) := by
  let send := HashSpec.withDerivationsLift Unit HashOutput
  let sendPaid := Backend.withDerivationsLift PrfInput HashOutput ∘ₛ ordinary
  have h₁ := source_map (payMaster word) send
    (ofOutput <$> (SeedSpec.query (.inr ()) : OracleComp SeedSpec HashOutput) : OracleComp
      SeedSpec Seed)
    (seedPrf (hashOf send)) A
  have h₂ := source_map (paidEncoding.deriveImpl word) sendPaid
    (liftM (Source.query (.inl (.inr (.inr ())))) : OracleComp Source Unit)
    (fun _ p a suffix => ofOutput <$> (Source.query (.inr (p, a,
      suffix)) : OracleComp Source HashOutput)) A
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  dsimp only [send, sendPaid]
  have leftPass : payMaster word ∘ₛ HashSpec.withDerivationsLift Unit HashOutput = ordinary := by
    funext t
    cases t <;> rfl
  have rightPass : paidEncoding.deriveImpl word ∘ₛ
      (Backend.withDerivationsLift PrfInput HashOutput ∘ₛ ordinary) =
      ordinary := by
    funext t
    cases t <;> rfl
  have tick : simulateQ (paidEncoding.deriveImpl word)
      (liftM (Source.query (.inl (.inr (.inr ())))) : OracleComp Source Unit) =
      (liftM (Ambient.query (.inr (.inr ()))) : OracleComp Ambient Unit) := by
    rw [simulateQ_spec_query]
    rfl
  have master : simulateQ (payMaster word)
      (ofOutput <$> (SeedSpec.query (.inr ()) : OracleComp SeedSpec HashOutput) : OracleComp
        SeedSpec Seed) =
      (fun _ : Unit => (ofOutput word : Seed)) <$>
        (liftM (Ambient.query (.inr (.inr ()))) : OracleComp Ambient Unit) := by
    have h : simulateQ (payMaster word)
        (ofOutput <$> (SeedSpec.query (.inr ()) : OracleComp SeedSpec HashOutput)) =
        (fun _ : Unit => ofOutput word) <$>
          (liftM (Ambient.query (.inr (.inr ()))) : OracleComp Ambient Unit) := by
      simp [payMaster, Functor.map_map]
    exact h
  rw [leftPass, rightPass]
  erw [master, tick, seed_map]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
