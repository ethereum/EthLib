module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Sign
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Inverse
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Statement
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Statement
public import EthLib.Cryptography.Proofs.HashSig.Interchange
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Proofs: an adversary against EthLib wins at most as often as one against the model

The model's adversary runs EthLib's adversary on the translated public key.

It sends each signing request on, translated, and translates each answer back.

It returns the forgery translated to the model.

Both games then draw the same seed and give the adversary the same answers in distribution.

Key generation and verification are the same calls.

The signers make different calls.

Key generation leaves a cache, and every answer function that agrees with it gives the key.

Under such an answer function the signers agree, since EthLib rebuilds the same key.

So the forgery, the log and the verdict have the same joint distribution in both games.

A forgery that wins against EthLib also wins against the model.

EthLib's cap of `2^30` requests is below the model's cap of 1,182,000,000.

A signature that no request returned stays so after translation.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec OracleWorld RomEquiv RomEquivFrom)

/-! ## A run is fixed by its final cache -/

/-- A lifted hash computation run from any cache returns its value under the final cache.

This is its value under every answer function that agrees with the final cache. -/
theorem evalWithAnswerFn_eq_of_mem_support_run {α : Type} (oa : OracleComp HashSpec α)
    {cache : HashSpec.QueryCache} {z : α × HashSpec.QueryCache}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (OracleComp.liftComp oa OracleWorld)).run cache))
    {f : QueryImpl HashSpec Id} (hf : z.2.AgreesWithFn f) : evalWithAnswerFn f oa = z.1 := by
  rw [QueryImpl.simulateQ_add_liftComp_right] at hz
  exact QueryCache.evalWithAnswerFn_eq_of_agreesWithFn hf oa
    (QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
      uniformSampleImpl oa hz)

/-! ## The translated adversary -/

/-- EthLib's message as the model's: its little-endian number, on 256 bits. -/
def toMessage (m : Message) : SphincsSecurity.Message :=
  BitVec.ofNat _ (Base.bytesToUint m)

/-- A message read as a number and written back is itself. -/
theorem ofMessage_toMessage (m : Message) : ofMessage (toMessage m) = m :=
  HashSig.ofBV_ofNat_bytesToUint m (by decide)

/-- EthLib's forgery as the model's. -/
def toForgery (forgery : Forgery) : SphincsSecurity.Forgery :=
  ⟨toMessage forgery.message, toSignature forgery.signature⟩

/-- The model's adversary that runs EthLib's adversary.

It translates the public key, each signing request and its answer, and the forgery. -/
noncomputable def translate (adversary : Adversary) : SphincsSecurity.Security.Adversary where
  main pk := toForgery <$> simulateQ (HashSig.translateImpl toMessage (Option.map ofSignature))
    (adversary.main (ofPublicKey pk))

/-- The log entry of a model request, as EthLib's entry. -/
def ofEntry (entry : (_ : SphincsSecurity.Message) × Option SphincsSecurity.Signature) :
    (_ : Message) × Option Signature :=
  ⟨ofMessage entry.1, Option.map ofSignature entry.2⟩

/-- The model's game against the translated adversary, up to the verdict.

It returns EthLib's forgery, the model's log of requests and the result of verification. -/
noncomputable def modelRun (adversary : Adversary) :
    OracleComp OracleWorld (Forgery × QueryLog SphincsSecurity.SigningSpec × Bool) := do
  let seed ← liftM SphincsSecurity.sampleMasterSeed
  let (pk, sk) ← liftM (SphincsSecurity.Seeded.keygen seed)
  let ((forgery, log) : Forgery × QueryLog SphincsSecurity.SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SphincsSecurity.SigningSpec) (OracleComp OracleWorld)) +
        SphincsSecurity.Security.signingOracle sk)
      (simulateQ (HashSig.translateImpl toMessage (Option.map ofSignature))
        (adversary.main (ofPublicKey pk)))).run
  let verified ← liftM (SphincsSecurity.Concrete.verify pk (toMessage forgery.message)
    (toSignature forgery.signature) : OracleComp HashSpec Bool)
  return (forgery, log, verified)

/-- The model's verdict on a run. -/
def modelWins (run : Forgery × QueryLog SphincsSecurity.SigningSpec × Bool) : Bool :=
  decide (SphincsSecurity.SigningTranscript.Valid run.2.1 ∧
    ¬SphincsSecurity.SigningTranscript.Contains run.2.1 (toForgery run.1)) && run.2.2

/-- EthLib's verdict on a run, with the log translated back. -/
def wins (run : Forgery × QueryLog SphincsSecurity.SigningSpec × Bool) : Bool :=
  decide (Valid (run.2.1.map ofEntry) ∧ ¬Contains (run.2.1.map ofEntry) run.1) && run.2.2

/-- A run that EthLib counts as a win is a win for the model. -/
theorem modelWins_of_wins (run : Forgery × QueryLog SphincsSecurity.SigningSpec × Bool)
    (h : wins run = true) : modelWins run = true := by
  simp only [wins, modelWins, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hvalid, hfresh⟩, hv⟩ := h
  refine ⟨⟨?_, fun ⟨entry, hmem, hm, hs⟩ ↦
    hfresh ⟨ofEntry entry, List.mem_map_of_mem hmem, ?_, ?_⟩⟩, hv⟩
  · simp only [Valid, List.length_map] at hvalid
    exact hvalid.trans signatureLimit_le
  · simp only [ofEntry, hm, toForgery, ofMessage_toMessage]
  · simp only [ofEntry, hs, toForgery, Option.map_some, ofSignature_toSignature]

/-- The model's game against the translated adversary is its verdict on the run. -/
theorem gameCore_translate (adversary : Adversary) :
    SphincsSecurity.Security.gameCore (translate adversary) =
      modelWins <$> modelRun adversary := by
  simp only [SphincsSecurity.Security.gameCore, modelRun, translate, simulateQ_map,
    WriterT.run_map, map_bind, bind_map_left, map_pure]
  rfl

/-- EthLib's game with the model's signer, whose answers are translated back. -/
noncomputable def signedGame (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM SphincsSecurity.sampleMasterSeed
  let (pk, sk) ← liftM (SphincsSecurity.Seeded.keygen seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        QueryImpl.withLogging (fun message ↦ Option.map ofSignature <$>
          liftM (SphincsSecurity.Seeded.sign sk (toMessage message) :
            OracleComp HashSpec (Option SphincsSecurity.Signature)) :
              QueryImpl SigningSpec (OracleComp OracleWorld)))
      (adversary.main (ofPublicKey pk))).run
  let verified ← liftM (SphincsSecurity.Concrete.verify pk (toMessage forgery.message)
    (toSignature forgery.signature) : OracleComp HashSpec Bool)
  return decide (Valid log ∧ ¬Contains log forgery) && verified

/-- With the model's signer, EthLib's game is EthLib's verdict on the model's run. -/
theorem signedGame_eq (adversary : Adversary) :
    signedGame adversary = wins <$> modelRun adversary := by
  unfold signedGame modelRun
  simp only [map_bind, map_pure]
  refine bind_congr fun seed ↦ bind_congr fun ⟨pk, sk⟩ ↦ ?_
  rw [← HashSig.map_run_simulateQ_withLogging_translateImpl
    (fun request ↦ liftM (SphincsSecurity.Seeded.sign sk request :
      OracleComp HashSpec (Option SphincsSecurity.Signature))) toMessage (Option.map ofSignature)
    ofMessage ofMessage_toMessage]
  simp only [bind_map_left]
  rfl

/-- EthLib's game and the game with the model's signer are interchangeable.

Key generation leaves a cache, and every answer function that agrees with it gives the key.

From then on, both signers agree under every such answer function. -/
theorem gameCore_romEquiv (adversary : Adversary) :
    RomEquiv (gameCore adversary) (signedGame adversary) := by
  have hverify : ∀ (pk : SphincsSecurity.PublicKey) (forgery : Forgery),
      verifyWith H (ofPublicKey pk) forgery.message forgery.signature =
        (SphincsSecurity.Concrete.verify pk (toMessage forgery.message)
          (toSignature forgery.signature) : OracleComp HashSpec Bool) := fun pk forgery ↦ by
    have h := verifyWith_queryH (m := OracleComp HashSpec) pk (toMessage forgery.message)
      (toSignature forgery.signature)
    rwa [ofMessage_toMessage, ofSignature_toSignature] at h
  unfold gameCore signedGame sampleSeed signingOracle
  simp only [← liftComp_eq_liftM, liftComp_map, bind_map_left, keyGenWith_queryH, hverify]
  apply RomEquiv.bind_right
  intro seed
  rw [← RomEquivFrom.empty_iff]
  refine RomEquivFrom.bind_right_of_mem_support _ fun _ _ z hz ↦ ?_
  -- The answers that agree with the cache after key generation give its key.
  have hkey : ∀ f : QueryImpl HashSpec Id, z.2.AgreesWithFn f →
      evalWithAnswerFn f (SphincsSecurity.Seeded.keygen seed : OracleComp HashSpec _) = z.1 :=
    fun _ hf ↦ evalWithAnswerFn_eq_of_mem_support_run _ hz hf
  apply RomEquivFrom.bind_left
  apply RomEquivFrom.run_simulateQ_withLogging
  intro message
  rw [← liftComp_map, ← liftComp_map]
  apply RomEquivFrom.liftComp
  intro f hf
  conv_lhs => rw [← ofMessage_toMessage message]
  rw [signWith_answers f seed (toMessage message), evalWithAnswerFn_map, hkey f hf]

/-- An adversary against EthLib wins at most as often as its translation against the model. -/
theorem forgeAdvantage_le (adversary : Adversary) :
    forgeAdvantage adversary ≤ SphincsSecurity.Security.forgeAdvantage (translate adversary) := by
  have hE : forgeAdvantage adversary =
      Pr{let result ←
        (simulateQ HashSpec.romImpl (gameCore adversary)).run' ∅}[result = true] :=
    HashSig.prEvent_run_withAddCost _ _
  have hM : SphincsSecurity.Security.forgeAdvantage (translate adversary) =
      Pr{let result ← (simulateQ HashSpec.romImpl
        (SphincsSecurity.Security.gameCore (translate adversary))).run' ∅}[result = true] :=
    HashSig.prEvent_run_withAddCost _ _
  have hd := RomEquiv.evalDist_run' (gameCore_romEquiv adversary) ∅
  rw [hE, hM, (_root_.EvalDistEq.of_evalDist_eq hd).prEvent_eq, signedGame_eq,
    gameCore_translate]
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  exact prEvent_mono _ _ _ fun x ↦ modelWins_of_wins x.1

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
