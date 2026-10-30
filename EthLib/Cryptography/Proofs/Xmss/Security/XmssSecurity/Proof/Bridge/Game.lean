import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Signer
import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Deterministic.TranscriptReduction
import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Adversary

/-!
# EthLib's game as the model's

After key generation, EthLib's game with a signer that keeps `S` and `P` is the model's game.

The model's game uses the table signer, and the prepared cache answers EthLib's derivations.

The adversary is translated as in `Unforgeability/Adversary.lean`.

The transcripts correspond entry by entry.

The forgery wins in one exactly when its translation wins in the other.
-/

open OracleComp OracleSpec
open EthLib.Cryptography
open EthLib.Cryptography.Xmss.Unforgeability (queryH ofParam ofSeed ofDigest ofLeafIndex ofMessage
  ofSignature ofPublicKey toLeafIndex toMessage toSignature toModelAdversary toModelForgery
  toModelRequest adversaryImpl ofEntry)

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

/-! ## Logged simulations with translated logs -/

theorem Erases.simulateQ_writer_map {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    {α L L' : Type} (known : QueryCache target)
    (left : QueryImpl source (WriterT (List L) (OracleComp target)))
    (right : QueryImpl source (WriterT (List L') (OracleComp target))) (g : L' → L)
    (h : ∀ input, Erases known (left input).run
      ((fun p => (p.1, p.2.map g)) <$> (right input).run))
    (computation : OracleComp source α) :
    Erases known (simulateQ left computation).run
      ((fun p => (p.1, p.2.map g)) <$> (simulateQ right computation).run) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', map_pure]
      exact .pure _
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind', map_bind]
      show Erases known ((left input).run >>= fun x =>
          Prod.map id (x.2 ++ ·) <$> (simulateQ left (next x.1)).run)
        ((right input).run >>= fun a => (fun p => (p.1, p.2.map g)) <$>
          (Prod.map id (a.2 ++ ·) <$> (simulateQ right (next a.1)).run))
      have hright : ((right input).run >>= fun a => (fun p => (p.1, p.2.map g)) <$>
            (Prod.map id (a.2 ++ ·) <$> (simulateQ right (next a.1)).run)) =
          ((fun p => (p.1, p.2.map g)) <$> (right input).run) >>= fun a =>
            Prod.map id (a.2 ++ ·) <$> ((fun p => (p.1, p.2.map g)) <$>
              (simulateQ right (next a.1)).run) := by
        rw [bind_map_left]
        apply bind_congr
        intro a
        simp only [Functor.map_map]
        congr 1
        funext q
        simp [List.map_append]
      rw [hright]
      exact (h input).bind _ _ fun a => (ih a.1).map _

theorem Erases.of_eq {ι : Type} {spec : OracleSpec ι} {α : Type} {known : QueryCache spec}
    {left right : OracleComp spec α} (h : left = right) : Erases known left right :=
  h ▸ .refl known left

theorem liftM_hash_map {α β : Type} (f : α → β) (c : OracleComp HashSpec α) :
    (liftM (f <$> c) : OracleComp OracleWorld β) = f <$> (liftM c : OracleComp OracleWorld α) := by
  rw [map_eq_bind_pure_comp, liftM_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_def, liftM_pure]

/-! ## EthLib's game after key generation -/

/-- EthLib's signer from the scheme's seed `S` and the parameter `P`, each request logged. -/
def derivedSigningOracle (s : Xmss.Seed) (pp : Xmss.PublicParam) :
    QueryImpl Xmss.Unforgeability.SigningSpec
      (WriterT (QueryLog Xmss.Unforgeability.SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Except.toOption <$> Xmss.signDerived queryH s pp request.leafIndex request.message :
      OracleComp HashSpec _)

/-- EthLib's game after key generation, its signer keeping `S` and `P`. -/
noncomputable def realRest (adversary : Xmss.Unforgeability.Adversary) (pk : Xmss.PublicKey)
    (seed : MasterSeed) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Xmss.Unforgeability.Forgery × QueryLog Xmss.Unforgeability.SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog Xmss.Unforgeability.SigningSpec) (OracleComp OracleWorld)) +
        derivedSigningOracle (ofSeed seed) pk.publicParam) (adversary.main pk)).run
  let verified ← liftM (Xmss.verifyWith queryH pk forgery.message forgery.signature :
    OracleComp HashSpec Bool)
  return decide (Xmss.Unforgeability.Valid log ∧ ¬Xmss.Unforgeability.Contains log forgery) &&
    verified

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

theorem erases_oracles (h : Prepared seed d result cache)
    (input : (OracleWorld + Xmss.Unforgeability.SigningSpec).Domain) :
    Erases (worldKnown cache)
      ((QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog Xmss.Unforgeability.SigningSpec) (OracleComp OracleWorld)) +
          derivedSigningOracle (ofSeed seed) (ofParam d.parameter)) input).run
      ((fun p => (p.1, p.2.map ofEntry)) <$>
        (((forwardOracles + signingOracle (tableScheme d.rnd) (modelSecretKey d result)) ∘ₛ
          adversaryImpl) input).run) := by
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl, QueryImpl.apply_compose, adversaryImpl,
        simulateQ_spec_query, forwardOracles, QueryImpl.ofLift_apply]
      show Erases _ ((fun a => (a, ([] : QueryLog Xmss.Unforgeability.SigningSpec))) <$>
          (liftM (OracleWorld.query input) : OracleComp OracleWorld _))
        ((fun p => (p.1, p.2.map ofEntry)) <$> ((fun a => (a, ([] : QueryLog SigningSpec))) <$>
          (liftM (OracleWorld.query input) : OracleComp OracleWorld _)))
      rw [Functor.map_map]
      exact .refl _ _
  | inr request =>
      simp only [QueryImpl.add_apply_inr, QueryImpl.apply_compose, adversaryImpl, simulateQ_map,
        simulateQ_spec_query, WriterT.run_map', derivedSigningOracle, signingOracle,
        QueryImpl.run_withLogging_apply, tableScheme]
      -- The request is the translation of its model request.
      have hidx : ofLeafIndex (toModelRequest request).leafIndex = request.leafIndex := by
        simp [toModelRequest]
      have hmsg : ofMessage (toModelRequest request).message = request.message := by
        simp [toModelRequest]
      have key := (h.erases_sign (toModelRequest request).leafIndex
        (toModelRequest request).message).lift_hash.bind
        (fun u => (pure (u, [(⟨request, u⟩ :
          (_ : Xmss.Unforgeability.SignRequest) × Option Xmss.Signature)]) :
          OracleComp OracleWorld _))
        (fun u => (pure (u, [(⟨request, u⟩ :
          (_ : Xmss.Unforgeability.SignRequest) × Option Xmss.Signature)]) :
          OracleComp OracleWorld _)) fun u => .pure _
      rw [hidx, hmsg] at key
      refine (congrArg₂ (Erases (worldKnown cache)) ?_ ?_).mpr key
      -- `erw`: the oracle's `<$>` is the free monad's functor, the lemmas' the monad's.
      · erw [liftM_hash_map, bind_map_left]
      · erw [liftM_hash_map, bind_map_left, map_bind]
        refine Eq.trans (map_bind _ _ _) (bind_congr fun a => ?_)
        erw [map_pure]
        simp [ofEntry, toModelRequest]

/-- EthLib's game after key generation erases to the model's. -/
theorem erases_rest (h : Prepared seed d result cache) (adversary : Xmss.Unforgeability.Adversary) :
    Erases (worldKnown cache)
      (realRest adversary (ofPublicKey (modelPublicKey d result)) seed)
      (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary) (modelPublicKey d result)
        (modelSecretKey d result)) := by
  unfold realRest Seeded.gameRest toModelAdversary
  simp only [simulateQ_map, WriterT.run_map', ← QueryImpl.simulateQ_compose]
  have hsim := Erases.simulateQ_writer_map (worldKnown cache) _ _ ofEntry h.erases_oracles
    (adversary.main (ofPublicKey (modelPublicKey d result)))
  refine Erases.trans (hsim.bind _ _ fun _ => Erases.refl _ _) (Erases.of_eq ?_)
  -- `erw`, as above: the `<$>` is the free monad's functor.
  erw [bind_map_left]
  refine Eq.trans ?_ (bind_map_left _ _ _).symm
  refine bind_congr fun p => ?_
  -- The verifier is the model's, on the translated forgery.
  have hverify :
      (Xmss.verifyWith queryH (ofPublicKey (modelPublicKey d result)) p.1.message p.1.signature :
        OracleComp HashSpec Bool)
      = Concrete.verify (modelPublicKey d result) (toLeafIndex p.1.signature.leafIndex)
        (toMessage p.1.message) (toSignature p.1.signature) := by
    rw [← Xmss.Unforgeability.verifyWith_queryH, Xmss.Unforgeability.ofMessage_toMessage,
      Xmss.Unforgeability.ofSignature_toSignature]
  -- So is the winning condition.
  have hwin : decide (Xmss.Unforgeability.Valid (p.2.map ofEntry) ∧
        ¬Xmss.Unforgeability.Contains (p.2.map ofEntry) p.1)
      = decide (SigningTranscript.Valid p.2 ∧
          ¬SigningTranscript.Contains p.2 (toModelForgery p.1)) :=
    decide_eq_decide.mpr (and_congr (Xmss.Unforgeability.valid_map _)
      (not_congr (Xmss.Unforgeability.contains_map _ _)))
  simp only [tableScheme, Concrete.scheme]
  rw [hverify]
  exact bind_congr fun verified => congrArg (fun b => pure (b && verified)) hwin

end Prepared

end XmssSecurity.Bridge
