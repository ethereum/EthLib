module

public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Proofs.HashSig.Bytes
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# The leanXMSS strong-forgery experiment

Source: the leanXMSS specification draft, section "Security".

The experiment runs EthLib's key generation, signing and verification over the oracle.

The signer computes the full bottom tree root before the top layer.

VCVio supplies the counted experiment, whose signing replies may be errors.

The winning condition also requires distinct signing-request leaf indices.

One random oracle answers every hash call of every party.

Its answers are 256-bit words, read as 32 little-endian bytes.

Every hash call is charged, including repeated inputs.

Private uniform sampling is free.

This module states the experiment and its winning condition.

It proves no security bound.

The merged unforgeability theorem bounds a game whose signing replies drop the error.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV

open OracleComp OracleSpec
open scoped ENNReal

open HashSig (HashOutput HashSpec ofOutput)

/-- The parties have private sampling and access to the same hash oracle. -/
abbrev World := HashSig.OracleWorld

/-- Ask the shared oracle on exactly the bytes passed to EthLib's hashing definitions. -/
def H (input : ByteArray) : OracleComp World (Vector UInt8 32) :=
  ofOutput <$> (liftM (HashSpec.query input.data.toList) : OracleComp World HashOutput)

/-- The adversary chooses both a leaf index and a message in each signing request. -/
structure Request where
  /-- This leaf index may occur in at most one signing request in a winning experiment. -/
  leafIndex : LeafIndex
  /-- The 32-byte message hash the signature authenticates. -/
  message : Message
  deriving DecidableEq

/-- Every actual signing failure remains visible to the adversary. -/
abbrev Reply := Except XmssError Signature

/-- Extract only successful signatures for the freshness predicate. -/
def readback : Reply → Option Signature
  | .ok signature => some signature
  | .error _ => none

/-- EthLib's algorithms, with a signing reply that may be an error.

A signing error is a normal reply, so the adversary may continue after it.

All attempted leaf indices remain reserved by the final winning predicate.
-/
noncomputable def view :
    SignatureAlg.SigningView (OracleComp World) Request PublicKey SecretKey Signature Reply where
  keygen := do
    let seed ← (liftM ($ᵗ BitVec 256) : OracleComp World (BitVec 256))
    let (sk, pk) ← EthLib.Cryptography.Xmss.keyGenWith H (ofOutput seed)
    return (pk, sk)
  sign _ sk request := EthLib.Cryptography.Xmss.signWith H sk request.leafIndex request.message
  verify pk request signature :=
    if signature.leafIndex = request.leafIndex then
      EthLib.Cryptography.Xmss.verifyWith H pk request.message signature
    else pure false
  readback := readback

/-- Key generation uses the actual seed sampler and oracle-parametric key generator. -/
theorem view_keygen_eq : view.keygen = (do
    let seed ← (liftM ($ᵗ BitVec 256) : OracleComp World (BitVec 256))
    let (sk, pk) ← EthLib.Cryptography.Xmss.keyGenWith H (ofOutput seed)
    return (pk, sk)) := rfl

/-- The view exposes the complete actual signing result without converting errors. -/
theorem view_sign_eq (pk : PublicKey) (sk : SecretKey) (request : Request) :
    view.sign pk sk request =
      EthLib.Cryptography.Xmss.signWith H sk request.leafIndex request.message := rfl

/-- The view uses the actual verifier when the candidate carries its requested index. -/
theorem view_verify_eq (pk : PublicKey) (request : Request) (signature : Signature)
    (h : signature.leafIndex = request.leafIndex) :
    view.verify pk request signature =
      EthLib.Cryptography.Xmss.verifyWith H pk request.message signature := by
  simp [view, h]

/-- Successful readback identifies the exact successful raw reply. -/
theorem readback_eq_some_iff (reply : Reply) (signature : Signature) :
    readback reply = some signature ↔ reply = .ok signature := by
  cases reply <;> simp [readback]

/-- An adaptive free client sees private randomness, hashing and all actual signing replies. -/
abbrev Adversary := PublicKey →
  OracleComp (World + (Request →ₒ Reply)) (Request × Signature)

/-- The shared outcome keeps the candidate, every raw reply and final verification verdict. -/
abbrev Transcript := SignatureAlg.SigningView.Outcome Request Signature Reply

/-- The indexed strong-forgery predicate reserves every raw signing request.

Only successful replies contribute signatures to strong freshness.
-/
noncomputable def wins (transcript : Transcript) : Bool := by
  classical
  exact decide ((transcript.rawLog.map fun entry => entry.1.leafIndex).Nodup ∧
    SignatureAlg.SigningView.Wins readback transcript)

/-- Every attempted index is distinct and verification accepts.

No successful reply returned the candidate pair.
-/
theorem wins_eq_true_iff (transcript : Transcript) :
    wins transcript = true ↔
      (transcript.rawLog.map fun entry => entry.1.leafIndex).Nodup ∧
        transcript.forgery ∉ SignatureAlg.SigningView.returnedPairs readback transcript.rawLog ∧
          transcript.verified = true := by
  classical
  simp [wins, SignatureAlg.SigningView.Wins, SignatureAlg.SigningView.Fresh,
    and_assoc, and_comm]

/-- Generate the key, run the complete raw-reply adversary, and verify its actual signature. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp World Bool :=
  wins <$> view.experiment adversary

/-- Every phase charges one for a hash call and zero for uniform draws or signing requests.

The shared observer charges before the hash handler, including on cache hits.
-/
def hashCost : SignatureAlg.SigningView.Event World Request → ℕ
  | .ambient _ (.inr _) => 1
  | _ => 0

/-- Every actual hash input is charged in each of the four experiment phases. -/
theorem hashCost_hash (phase : SignatureAlg.SigningView.Phase) (input : List UInt8) :
    hashCost (.ambient phase (.inr input)) = 1 := rfl

/-- Private uniform draws are free in every phase. -/
theorem hashCost_uniform (phase : SignatureAlg.SigningView.Phase) (n : ℕ) :
    hashCost (.ambient phase (.inl n)) = 0 := rfl

/-- Reserving a signing request is separate from charging its actual internal hash calls. -/
theorem hashCost_attempt (request : Request) : hashCost (.signingAttempt request) = 0 := rfl

/-- Retain the full actual outcome, all-party hash count and one shared final cache jointly. -/
noncomputable def transcriptExperiment (adversary : Adversary) :
    ProbComp ((Transcript × ℕ) × QueryCache HashSpec) :=
  (fun result => ((SignatureAlg.SigningView.erase result.1, result.1.cost), result.2)) <$>
    (simulateQ HashSpec.romImpl
      (SignatureAlg.SigningView.countedExperiment hashCost view adversary)).run ∅

/-- Observe the winning bit and retain the exact count from the same complete execution. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × ℕ) :=
  (fun result => (wins result.1.1, result.1.2)) <$> transcriptExperiment adversary

/-- The probability of a strong forgery with a valid signing transcript. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← experiment adversary}[result.1 = true]

/-- Every execution charges at most `q` hash calls over all parties and all stages. -/
def HasHashQueryBound (adversary : Adversary) (q : ℕ) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- Every adversary within `q ≥ 1` hash calls of all parties forges with chance `≤ q / 2^bits`. -/
def HasClassicalSecurityBits (bits : ℕ) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞)

/-- The `q / 2^127` bound, stated for this experiment.

No proof of it is given here. -/
abbrev SecurityStatement : Prop := HasClassicalSecurityBits 127

end EthLib.Cryptography.Xmss.Unforgeability.VCV
