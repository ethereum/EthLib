module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.ConcreteStatement
public import EthLib.Cryptography.Proofs.Xmss.MapMonad
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed

/-!
# The leanXMSS signing oracle over a source of seed derivations

A request returns its signature or its signing error.

The game records whether the caller received a signature before running verification.

Source: the leanXMSS specification draft, sections "The scheme" and "Security".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec
open EthLib.Cryptography.Xmss
open XmssSecurity (OracleWorld HashSpec HashOutput)

/-- The signing oracle answers a request with the signer's result, its error included. -/
abbrev ReasonSigningSpec := SignRequest →ₒ Except XmssError Signature

/-- An adversary that sees why a signing request failed. -/
structure ReasonAdversary where
  main : PublicKey → OracleComp (OracleWorld + ReasonSigningSpec) Forgery

/-- `Sig(S_0, idx, m)` of the stateless signer on each request.

The log records whether it succeeded, as the winning rule needs. -/
def statelessReasonSigningOracle (sk : Seed) :
    QueryImpl ReasonSigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun request => WriterT.mk ((fun result => (result, [⟨request, result.toOption⟩])) <$>
    liftM (statelessSignWith H sk request.leafIndex request.message))

/-- What the game returns: the forgery, the log of the signing requests, and the verification. -/
abbrev FailOutput := Forgery × QueryLog SigningSpec × Bool

/-- Some signing request of the game failed. -/
def SomeFailure (z : FailOutput) : Prop :=
  ∃ entry ∈ z.2.1, entry.2 = none

/-! ## The game over a source of derivations -/

section Source

variable {ι : Type} {spec : OracleSpec ι}

/-- The hash of a game whose hash and coin queries a handler answers. -/
def hashOf (pass : QueryImpl OracleWorld (OracleComp spec)) (x : ByteArray) :
    OracleComp spec (Vector UInt8 32) :=
  ofOutput <$> pass (.inr x.data.toList)

/-- The game's oracles: hash and coin queries go to `pass`, and a request signs.

A request first obtains the value its secrets derive from, as the signer does. -/
def failSignerOf {σ : Type} (pass : QueryImpl OracleWorld (OracleComp spec))
    (seedSrc : OracleComp spec σ) (prfOf : σ → SeedPrf (OracleComp spec)) :
    QueryImpl (OracleWorld + ReasonSigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp spec))
  | .inl t => (liftM (pass t) : WriterT (QueryLog SigningSpec) (OracleComp spec) _)
  | .inr request => WriterT.mk (do
      let s ← seedSrc
      let pp ← publicParamOf (prfOf s)
      let result ← signDerived (hashOf pass) (prfOf s) pp request.leafIndex request.message
      return (result, [⟨request, result.toOption⟩]))

/-- The game of a signing failure after the seed: keys, the adversary, then the verification.

The secrets derive from `prfOf s`, where `s` comes from `seedSrc`. -/
def failGameOf {σ : Type} (pass : QueryImpl OracleWorld (OracleComp spec))
    (seedSrc : OracleComp spec σ) (prfOf : σ → SeedPrf (OracleComp spec))
    (adversary : ReasonAdversary) : OracleComp spec FailOutput := do
  let s ← seedSrc
  let pk ← publicKeyOf (hashOf pass) (prfOf s)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (failSignerOf pass seedSrc prfOf) (adversary.main pk)).run
  let verified ← verifyWith (hashOf pass) pk forgery.message forgery.signature
  return (forgery, log, verified)

section Map

variable {ι' : Type} {spec' : OracleSpec ι'} (so : QueryImpl spec (OracleComp spec'))

/-- Simulating a hash call gives the hash of the simulated handler. -/
theorem simulateQ_hashOf (pass : QueryImpl OracleWorld (OracleComp spec)) (x : ByteArray) :
    simulateQ so (hashOf pass x) = hashOf (so ∘ₛ pass) x := by
  simp [hashOf, QueryImpl.apply_compose]

/-- Simulating a request gives the request over the simulated handler and source. -/
theorem simulateQ_run_failSignerOf_apply {σ : Type}
    (pass : QueryImpl OracleWorld (OracleComp spec)) (seedSrc : OracleComp spec σ)
    (prfOf : σ → SeedPrf (OracleComp spec)) (t : (OracleWorld + ReasonSigningSpec).Domain) :
    simulateQ so (failSignerOf pass seedSrc prfOf t).run =
      (failSignerOf (so ∘ₛ pass) (simulateQ so seedSrc)
        (fun s pp a suffix => simulateQ so (prfOf s pp a suffix)) t).run := by
  rcases t with t | request
  · simp [failSignerOf, QueryImpl.apply_compose]
  · simp only [failSignerOf, WriterT.run_mk, simulateQ_bind, simulateQ_pure]
    refine bind_congr fun s => ?_
    rw [publicParamOf_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
      (fun x f => simulateQ_bind so x f)]
    refine bind_congr fun pp => ?_
    rw [signDerived_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
      (fun x f => simulateQ_bind so x f)]
    simp only [simulateQ_hashOf]

/-- Simulating the run of the game's oracles gives their run over the simulated sources. -/
theorem simulateQ_run_failSignerOf {σ : Type}
    (pass : QueryImpl OracleWorld (OracleComp spec)) (seedSrc : OracleComp spec σ)
    (prfOf : σ → SeedPrf (OracleComp spec)) {α : Type}
    (oa : OracleComp (OracleWorld + ReasonSigningSpec) α) :
    simulateQ so (simulateQ (failSignerOf pass seedSrc prfOf) oa).run =
      (simulateQ (failSignerOf (so ∘ₛ pass) (simulateQ so seedSrc)
        (fun s pp a suffix => simulateQ so (prfOf s pp a suffix))) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', simulateQ_map,
      simulateQ_run_failSignerOf_apply, ih]

end Map

/-- Simulating the queries of the game gives the game over the simulated handler and source. -/
theorem simulateQ_failGameOf {ι' : Type} {spec' : OracleSpec ι'} {σ : Type}
    (so : QueryImpl spec (OracleComp spec')) (pass : QueryImpl OracleWorld (OracleComp spec))
    (seedSrc : OracleComp spec σ) (prfOf : σ → SeedPrf (OracleComp spec))
    (adversary : ReasonAdversary) :
    simulateQ so (failGameOf pass seedSrc prfOf adversary) =
      failGameOf (so ∘ₛ pass) (simulateQ so seedSrc)
        (fun s pp a suffix => simulateQ so (prfOf s pp a suffix)) adversary := by
  simp only [failGameOf, simulateQ_bind, simulateQ_pure, simulateQ_run_failSignerOf]
  refine bind_congr fun s => ?_
  rw [publicKeyOf_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
    (fun x f => simulateQ_bind so x f)]
  simp only [simulateQ_hashOf]
  refine bind_congr fun pk => bind_congr fun z => ?_
  rw [verifyWith_map_monad (simulateQ so) (fun b => simulateQ_pure so b)
    (fun x f => simulateQ_bind so x f)]
  simp only [simulateQ_hashOf]

end Source

/-! ## The real game -/

/-- The game's `H`, lifted to hash and coin queries, is the hash of the identity handler. -/
theorem liftM_H (x : ByteArray) :
    (liftM (H x) : OracleComp OracleWorld (Vector UInt8 32)) =
      hashOf (QueryImpl.id' OracleWorld) x := by
  simp [H, queryH, hashOf, HashSig.oracleHash]
  rfl

/-- The derivations of the game, lifted, are those over the hash of the identity handler. -/
theorem liftM_seedPrf (s : Seed) :
    (fun pp a suffix =>
        (liftM (seedPrf H s pp a suffix) : OracleComp OracleWorld (Vector UInt8 32))) =
      seedPrf (hashOf (QueryImpl.id' OracleWorld)) s := by
  funext pp a suffix
  exact liftM_H _

/-- The real game's oracles, for the secret key of a seed, are the game's over that seed. -/
theorem reasonOracles_eq_failSignerOf (seed : Seed) :
    QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        statelessReasonSigningOracle seed =
      failSignerOf (QueryImpl.id' OracleWorld)
        (schemeSeed (hashOf (QueryImpl.id' OracleWorld)) seed)
        (seedPrf (hashOf (QueryImpl.id' OracleWorld))) := by
  funext t
  rcases t with t | request
  · rfl
  · rw [QueryImpl.add_apply_inr]
    simp only [statelessReasonSigningOracle, failSignerOf]
    refine congrArg WriterT.mk ?_
    have hseed : (liftM (schemeSeed H seed) : OracleComp OracleWorld Seed) =
        schemeSeed (hashOf (QueryImpl.id' OracleWorld)) seed :=
      liftM_H _
    simp only [statelessSignWith, liftM_bind, map_bind, hseed]
    refine bind_congr fun s => ?_
    rw [publicParamOf_map_monad (fun {β} (c : OracleComp HashSpec β) =>
      (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f),
      liftM_seedPrf]
    refine bind_congr fun pp => ?_
    rw [signDerived_map_monad (fun {β} (c : OracleComp HashSpec β) =>
      (liftM c : OracleComp OracleWorld β)) (fun b => liftM_pure b) (fun x f => liftM_bind x f),
      liftM_seedPrf, funext liftM_H]
    simp

/-- The oracles of a game whose scheme seed is a derivation query. -/
abbrev SeedSpec := HashSpec.withDerivations Unit HashOutput

end EthLib.Cryptography.Xmss.Unforgeability
