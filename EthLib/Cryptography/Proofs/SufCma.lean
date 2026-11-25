module

public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.OracleComp.Runtime

/-!
# Proofs: strong unforgeability of a stateful signature scheme

The game follows the leanXMSS specification draft, section "Security"; leanXMSS is one instance.

The game has one key, and the caller chooses each request, such as a message and a leaf index.

The signer keeps its key across requests and may fail, which the adversary sees.

The adversary wins with a pair that verifies and that the signer never returned.

A run whose requests break the scheme's rule of use, such as a leaf index used twice, loses.

The oracles are coins and a hash oracle, such as a random oracle.

A model answers them.

One bound charges the adversary's own hash calls, and the other every hash call of the game.
-/

@[expose] public section

namespace EthLib.Cryptography.SufCma

open OracleComp OracleSpec ENNReal

variable {ι : Type} {hs : OracleSpec ι}
  {Request Message PublicKey SecretKey Signature : Type}

/-! ## The scheme and the adversary -/

/-- The signing oracle answers a request with a signature, or nothing when signing fails. -/
abbrev SigningSpec (Request Signature : Type) := Request →ₒ Option Signature

/-- A claimed forgery: a message and a signature.

The game fixes the freshness check on this pair, so no scheme can redefine it. -/
structure Forgery (Message Signature : Type) where
  message : Message
  signature : Signature
  deriving DecidableEq

/-- A stateful signature scheme whose algorithms make coin and hash queries.

Its rule of use is the caller's duty on its requests, read on the log of a run.

The rule reads the requests only, accepts every single request, and every prefix it accepts.

These conditions keep the game winnable.

A bound on an instance holds for runs that keep its rule, so it reads with that rule. -/
structure Scheme (hs : OracleSpec ι) (Request Message PublicKey SecretKey Signature : Type) where
  /-- Key generation. -/
  keyGen : OracleComp (unifSpec + hs) (PublicKey × SecretKey)
  /-- A signature or nothing for a request, and the next key. -/
  sign : SecretKey → Request → OracleComp (unifSpec + hs) (Option Signature × SecretKey)
  /-- Verification of a signature on a message. -/
  verify : PublicKey → Message → Signature → OracleComp (unifSpec + hs) Bool
  /-- The message a request asks to sign. -/
  message : Request → Message
  /-- The rule of use, on the requests of a run with their answers, in order. -/
  Admissible : QueryLog (SigningSpec Request Signature) → Prop
  /-- The rule is decidable. -/
  decidableAdmissible : DecidablePred Admissible
  /-- One request alone keeps the rule. -/
  admissible_singleton : ∀ entry, Admissible [entry]
  /-- A prefix of a log that keeps the rule keeps it. -/
  admissible_of_append_left : ∀ log log', Admissible (log ++ log') → Admissible log
  /-- The rule reads the requests, not the signer's answers. -/
  admissible_congr : ∀ log log', log.map (·.1) = log'.map (·.1) →
    (Admissible log ↔ Admissible log')

attribute [instance] Scheme.decidableAdmissible

/-- An adaptive adversary.

From the public key, it samples coins, queries the hash, requests signatures, and returns a forgery.

It sees whether each request failed. -/
structure Adversary (hs : OracleSpec ι) (Request Message PublicKey Signature : Type) where
  main : PublicKey →
    OracleComp ((unifSpec + hs) + SigningSpec Request Signature) (Forgery Message Signature)

/-- A query of the adversary that is a hash call, neither a coin nor a request. -/
abbrev IsAdversaryHash (hs : OracleSpec ι) (Request Signature : Type) :=
  SignatureAlg.IsHashQuery (hs := hs) (M := Request) (S := Option Signature)

/-- A query of the adversary that is a signing request. -/
abbrev IsAdversaryRequest (hs : OracleSpec ι) (Request Signature : Type) :=
  SignatureAlg.IsSignQuery (hs := hs) (M := Request) (S := Option Signature)

variable (scheme : Scheme hs Request Message PublicKey SecretKey Signature)

/-- Some request for the forgery's message was answered with the forgery's signature.

Any other signature of a signed message is a strong forgery.

A request is not a message, so this reads the message of each request. -/
def Returned (log : QueryLog (SigningSpec Request Signature))
    (forgery : Forgery Message Signature) : Prop :=
  ∃ entry ∈ log, scheme.message entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance [DecidableEq Message] [DecidableEq Signature]
    (log : QueryLog (SigningSpec Request Signature)) (forgery : Forgery Message Signature) :
    Decidable (Returned scheme log forgery) :=
  inferInstanceAs (Decidable (∃ entry ∈ log, _ ∧ _))

/-! ## The game -/

/-- The signer on each request, with the key the request before it returned.

The oracle keeps the new key, and logs the request with its answer. -/
def signingOracle : QueryImpl (SigningSpec Request Signature)
    (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
      (OracleComp (unifSpec + hs)))) :=
  fun request => StateT.mk fun sk => WriterT.mk
    ((fun result => (result, [⟨request, result.1⟩])) <$> scheme.sign sk request)

variable [DecidableEq Message] [DecidableEq Signature]

/-- The check of a forgery, once the adversary returned it with the log of its requests.

It wins when the forgery verifies, the log keeps the rule, and the signer never returned it. -/
def checkForgery (pk : PublicKey)
    (y : Forgery Message Signature × QueryLog (SigningSpec Request Signature)) :
    OracleComp (unifSpec + hs) Bool :=
  scheme.verify pk y.1.message y.1.signature >>= fun verified =>
    pure (decide (scheme.Admissible y.2 ∧ ¬Returned scheme y.2 y.1) && verified)

/-- The game once the keys exist: the adversary with its oracles, then the check of its forgery.

Coins and hash queries pass through, and a request goes to the signer. -/
def gameAfterKeys (adversary : Adversary hs Request Message PublicKey Signature)
    (pk : PublicKey) (sk : SecretKey) : OracleComp (unifSpec + hs) Bool :=
  ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
      (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
        (OracleComp (unifSpec + hs)))) + signingOracle scheme) (adversary.main pk)).run sk).run >>=
    fun x => checkForgery scheme pk (x.1.1, x.2)

/-- The game: key generation, the adversary with its oracles, then the check of its forgery.

It has one key. -/
def game (adversary : Adversary hs Request Message PublicKey Signature) :
    OracleComp (unifSpec + hs) Bool :=
  scheme.keyGen >>= fun keys => gameAfterKeys scheme adversary keys.1 keys.2

/-! ## The models -/

/-- A model of the oracles: a state, drawn once, and the answers to coins and hash queries.

It is a runtime of the oracle framework; the game reads only its draw and its answers. -/
abbrev Model (hs : OracleSpec ι) := OracleRuntime unifSpec (unifSpec + hs)

/-- The random oracle model: coins pass through, and the hash is lazy from the empty cache. -/
noncomputable def randomOracleModel (hs : OracleSpec ι) [DecidableEq ι]
    [∀ t, SampleableType (hs.Range t)] : Model hs where
  State := hs.QueryCache
  setup := pure ∅
  handler := hs.romImpl

/-- The game against a model: its state is drawn, then the game runs on its answers. -/
noncomputable def runIn (model : Model hs) {α : Type} (oa : OracleComp (unifSpec + hs) α) :
    ProbComp α :=
  model.setup >>= fun state => (simulateQ model.handler oa).run' state

/-- The probability that the adversary forges against a model. -/
noncomputable def advantage (model : Model hs)
    (adversary : Adversary hs Request Message PublicKey Signature) : ℝ≥0∞ :=
  Pr{let b ← runIn model (game scheme adversary)}[b = true]

/-! ## The adversary's own calls -/

/-- **`bits` bits of strong unforgeability against a model, up to `maxSignings` requests.**

Take an adversary that itself makes at most `q` hash calls and `maxSignings` requests.

Both bounds hold on every path and for every public key.

It forges with probability at most `(q + slack) * 2^-bits`. -/
def StronglyUnforgeable (model : Model hs) (maxSignings slack bits : ℕ) : Prop :=
  -- Key generation, the signer and the final verification are not charged to `q`.
  ∀ q (adversary : Adversary hs Request Message PublicKey Signature),
    (∀ pk, IsQueryBoundP (adversary.main pk) (IsAdversaryHash hs Request Signature) q) →
    (∀ pk, IsQueryBoundP (adversary.main pk) (IsAdversaryRequest hs Request Signature)
      maxSignings) →
      advantage scheme model adversary ≤ ((q : ℝ≥0∞) + slack) * (2 : ℝ≥0∞)⁻¹ ^ bits

/-! ## Every call of the game -/

/-- A query of the game that is a hash call, not a coin. -/
def IsHashCall (hs : OracleSpec ι) (t : (unifSpec + hs).Domain) : Prop :=
  t.isRight = true

instance : DecidablePred (IsHashCall hs) := fun t =>
  inferInstanceAs (Decidable (t.isRight = true))

/-- A hash query costs one, and a coin nothing. -/
def hashCost : (unifSpec + hs).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- A query costs one exactly when it is a hash call. -/
theorem hashCost_eq_ite (t : (unifSpec + hs).Domain) :
    hashCost t = if IsHashCall hs t then 1 else 0 := by
  cases t <;> rfl

/-- A computation against a model, with the count of its hash calls.

A repeated input counts again. -/
noncomputable def countedRunIn (model : Model hs) {α : Type} (oa : OracleComp (unifSpec + hs) α) :
    ProbComp (α × ℕ) :=
  model.setup >>= fun state =>
    (simulateQ (model.handler.withAddCost hashCost) oa).run.run' state

/-- Every run of the game makes at most `q` hash calls.

It counts key generation, signing, the adversary's queries and the final verification. -/
def IsGameQueryBound (model : Model hs)
    (adversary : Adversary hs Request Message PublicKey Signature) (q : ℕ) : Prop :=
  ∀ result ∈ support (countedRunIn model (game scheme adversary)), result.2 ≤ q

/-- **`bits` bits of strong unforgeability when every hash call of the game is charged.**

An adversary whose game makes at most `q` hash calls forges with probability `<= q * 2^-bits`.

The number of requests is not bounded.

The bound is claimed for `q >= 1` only.

A game whose key generation hashes has no run with `q = 0`. -/
def StronglyUnforgeableAllCalls (model : Model hs) (bits : ℕ) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : Adversary hs Request Message PublicKey Signature,
    IsGameQueryBound scheme model adversary q →
      advantage scheme model adversary ≤ (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ bits

/-! ## Lemmas -/

/-- A bound `x * 2^-bits` is the bound `x / 2^bits`. -/
theorem mul_inv_two_pow (x : ℝ≥0∞) (bits : ℕ) :
    x * (2 : ℝ≥0∞)⁻¹ ^ bits = x / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
  rw [div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

/-- Against the random oracle, the game runs from the empty cache. -/
theorem runIn_randomOracleModel [DecidableEq ι] [∀ t, SampleableType (hs.Range t)] {α : Type}
    (oa : OracleComp (unifSpec + hs) α) :
    runIn (randomOracleModel hs) oa = (simulateQ hs.romImpl oa).run' ∅ :=
  pure_bind _ _

/-- The count of hash calls does not change a computation's result. -/
theorem fst_map_countedRunIn (model : Model hs) {α : Type} (oa : OracleComp (unifSpec + hs) α) :
    Prod.fst <$> countedRunIn model oa = runIn model oa := by
  -- The count is a multiplicative writer of natural numbers.
  change Prod.fst <$> (model.setup >>= fun state =>
      ((simulateQ (model.handler.withAddCost hashCost) oa).run.run' state :
        ProbComp (α × Multiplicative ℕ))) = _
  rw [map_bind]
  refine bind_congr fun state => ?_
  rw [← QueryImpl.fst_map_run_simulateQ_withAddCost model.handler hashCost, StateT.run'_eq,
    StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

/-- An event of a computation's result has the same probability with the count as without. -/
theorem prEvent_countedRunIn (model : Model hs) {α : Type} (oa : OracleComp (unifSpec + hs) α)
    (P : α → Prop) :
    Pr{let result ← countedRunIn model oa}[P result.1] = Pr{let x ← runIn model oa}[P x] := by
  rw [← fst_map_countedRunIn, prEvent_map]

end EthLib.Cryptography.SufCma
