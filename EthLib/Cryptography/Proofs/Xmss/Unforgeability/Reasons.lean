module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Game
public import EthLib.Cryptography.Proofs.LoggedUntilBad

/-!
# Proofs: a signer that tells why signing failed

In the game of the unforgeability theorem, a failed signing request gets no signature.

Here the signer replies with its whole result instead, its error included.

The only error signing returns is a one-time key that found no codeword.

The request fixes that key on each layer, so the error tells which layer failed.

The keys, the oracles and the winning rule are those of the theorem.

The adversary forges with probability at most the theorem's bound, plus that of a failure.

A failure is a signing request whose signer returns an error.

The proof runs the adversary behind a reduction to the theorem's game.

The reduction answers every failure with the bottom layer's error, whichever layer failed.

Both games agree until the first failure, so they differ by at most its probability.

The budget is that of the reduction's run in the theorem's game.

After a failure, the reduction may give a reply that the adversary never gets here.

So the adversary's calls in this game do not bound the reduction's calls there.

Every adversary of the theorem's game, read in this game, keeps its budget behind the reduction.

The probability of a failure is not bounded here.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open XmssSecurity (OracleWorld HashSpec romImpl countHashQueries countHashQueries_forget
  simulateQ_countHashQueries)

/-! ## The game -/

/-- The signing oracle answers a request with the signer's result, its error included. -/
abbrev ReasonSigningSpec := SignRequest →ₒ Except XmssError Signature

/-- An adversary that sees why a signing request failed. -/
structure ReasonAdversary where
  main : PublicKey → OracleComp (OracleWorld + ReasonSigningSpec) Forgery

/-- `Sig(sk, idx, m)` on each request.

The log records whether it succeeded, as the winning rule needs. -/
def reasonSigningOracle (sk : SecretKey) :
    QueryImpl ReasonSigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun request => WriterT.mk ((fun result => (result, [⟨request, result.toOption⟩])) <$>
    liftM (signWith H sk request.leafIndex request.message))

/-- The game up to its result: keys, the adversary with its log, then the verification. -/
noncomputable def reasonRun (adversary : ReasonAdversary) :
    OracleComp OracleWorld (Forgery × QueryLog SigningSpec × Bool) := do
  let seed ← liftM sampleSeed
  let (sk, pk) ← liftM (keyGenWith H seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + reasonSigningOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return (forgery, log, verified)

/-- The game against the counted random oracle of the theorem, from an empty cache. -/
noncomputable def reasonExperiment (adversary : ReasonAdversary) :
    ProbComp ((Forgery × QueryLog SigningSpec × Bool) × Nat) :=
  (simulateQ countedOracle (reasonRun adversary)).run.run' ∅

/-- The probability that the adversary forges, under the winning rule of the theorem. -/
noncomputable def reasonForgeAdvantage (adversary : ReasonAdversary) : ℝ≥0∞ :=
  Pr{let result ← reasonExperiment adversary}[
    (Valid result.1.2.1 ∧ ¬Contains result.1.2.1 result.1.1) ∧ result.1.2.2 = true]

/-- The probability that some signing request of the game fails. -/
noncomputable def signingFailure (adversary : ReasonAdversary) : ℝ≥0∞ :=
  Pr{let result ← reasonExperiment adversary}[∃ entry ∈ result.1.2.1, entry.2 = none]

/-! ## The reduction -/

/-- The error the reduction replies with: no codeword for the request's bottom key. -/
def hiddenReason (request : SignRequest) : XmssError :=
  .noAdmissibleEncoding .bottom request.leafIndex.toNat

/-- A signature as itself, and no signature as the error of the bottom layer. -/
def withHiddenReason (request : SignRequest) : Option Signature → Except XmssError Signature
  | some signature => .ok signature
  | none => .error (hiddenReason request)

/-- Hash and coin queries, as the left oracles of a sum. -/
def toLeft {ι₂ : Type} (spec₂ : OracleSpec ι₂) :
    QueryImpl OracleWorld (OracleComp (OracleWorld + spec₂)) :=
  fun t => liftM ((OracleWorld + spec₂).query (.inl t))

/-- The reduction's oracles: other queries pass through, and a failure reads as the bottom's. -/
def hideReasonsImpl :
    QueryImpl (OracleWorld + ReasonSigningSpec) (OracleComp (OracleWorld + SigningSpec)) :=
  toLeft SigningSpec + fun (request : SignRequest) => withHiddenReason request <$>
    (liftM ((OracleWorld + SigningSpec).query (.inr request)) :
      OracleComp (OracleWorld + SigningSpec) (Option Signature))

/-- The adversary of the theorem's game that runs `adversary`, and hides why signing failed. -/
def hideReasons (adversary : ReasonAdversary) : Adversary where
  main pk := simulateQ hideReasonsImpl (adversary.main pk)

/-- An adversary of the theorem's game, in this game: it reads a reply as a signature or none. -/
def ignoreReasons (adversary : Adversary) : ReasonAdversary where
  main pk := simulateQ (toLeft ReasonSigningSpec + fun (request : SignRequest) =>
    Except.toOption <$> (liftM ((OracleWorld + ReasonSigningSpec).query (.inr request)) :
      OracleComp (OracleWorld + ReasonSigningSpec) (Except XmssError Signature)))
    (adversary.main pk)

/-- Hiding a reason, then reading the reply as a signature or none, gives the reply back. -/
theorem toOption_withHiddenReason (request : SignRequest) (reply : Option Signature) :
    (withHiddenReason request reply).toOption = reply := by
  cases reply <;> rfl

/-- The reduction undoes the embedding: every adversary of the theorem's game is covered. -/
theorem hideReasons_ignoreReasons (adversary : Adversary) :
    hideReasons (ignoreReasons adversary) = adversary := by
  obtain ⟨main⟩ := adversary
  simp only [hideReasons, ignoreReasons, Adversary.mk.injEq]
  funext pk
  rw [← QueryImpl.simulateQ_compose]
  have h : hideReasonsImpl ∘ₛ (toLeft ReasonSigningSpec + fun (request : SignRequest) =>
      Except.toOption <$> (liftM ((OracleWorld + ReasonSigningSpec).query (.inr request)) :
        OracleComp (OracleWorld + ReasonSigningSpec) (Except XmssError Signature)))
      = QueryImpl.ofLift (OracleWorld + SigningSpec) (OracleComp (OracleWorld + SigningSpec)) := by
    funext t
    rcases t with t | request
    · change simulateQ hideReasonsImpl
        (liftM ((OracleWorld + ReasonSigningSpec).query (.inl t))) = _
      rw [simulateQ_spec_query]
      rfl
    · change simulateQ hideReasonsImpl (Except.toOption <$>
        (liftM ((OracleWorld + ReasonSigningSpec).query (.inr request)) :
          OracleComp (OracleWorld + ReasonSigningSpec) (Except XmssError Signature))) = _
      rw [simulateQ_map, simulateQ_spec_query]
      change Except.toOption <$> (withHiddenReason request <$>
        (liftM ((OracleWorld + SigningSpec).query (.inr request)) :
          OracleComp (OracleWorld + SigningSpec) (Option Signature))) = _
      rw [Functor.map_map]
      simp only [toOption_withHiddenReason, id_map']
      rfl
  rw [h, simulateQ_ofLift_eq_self]

/-! ## Both games as one adversary with two signing oracles -/

/-- An event of the counted experiment is the event of the plain random oracle's run. -/
theorem prEvent_countedOracle {α : Type} (game : OracleComp OracleWorld α) (P : α → Prop) :
    Pr{let result ← (simulateQ countedOracle game).run.run' ∅}[P result.1]
      = Pr{let x ← (simulateQ romImpl game).run' ∅}[P x] := by
  have h := congrArg (fun c : OracleComp OracleWorld α => (simulateQ romImpl c).run' ∅)
    (countHashQueries_forget game)
  simp only [simulateQ_map, StateT.run'_map'] at h
  rw [← h, prEvent_map, simulateQ_countHashQueries]
  rfl

/-- Hash and coin queries log nothing. -/
theorem run_simulateQ_ofLift_writer {L β : Type} (c : OracleComp OracleWorld β) :
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (List L) (OracleComp OracleWorld))) c).run
      = (·, []) <$> c := by
  induction c using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp [ih]
    rfl

/-- A computation of hash and coin queries, lifted to the adversary's oracles, logs nothing. -/
theorem run_simulateQ_toLeft {ι₂ L β : Type} {spec₂ : OracleSpec ι₂}
    (so : QueryImpl spec₂ (WriterT (List L) (OracleComp OracleWorld)))
    (c : OracleComp OracleWorld β) :
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (List L) (OracleComp OracleWorld)) + so)
        (simulateQ (toLeft spec₂) c)).run = (·, []) <$> c := by
  rw [← QueryImpl.simulateQ_compose]
  have h : (QueryImpl.ofLift OracleWorld (WriterT (List L) (OracleComp OracleWorld)) + so) ∘ₛ
      toLeft spec₂ = QueryImpl.ofLift OracleWorld (WriterT (List L) (OracleComp OracleWorld)) := by
    funext t
    simp [QueryImpl.apply_compose, toLeft]
  rw [h, run_simulateQ_ofLift_writer]

/-- A computation of hash and coin queries, run after the adversary, logs nothing. -/
theorem run_simulateQ_bind_toLeft {ι₂ L α β : Type} {spec₂ : OracleSpec ι₂}
    (so : QueryImpl spec₂ (WriterT (List L) (OracleComp OracleWorld)))
    (oa : OracleComp (OracleWorld + spec₂) α) (c : α → OracleComp OracleWorld β) :
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (List L) (OracleComp OracleWorld)) + so)
        (oa >>= fun a => (a, ·) <$> simulateQ (toLeft spec₂) (c a))).run
      = (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (List L) (OracleComp OracleWorld)) + so)
          oa).run >>= fun p => (fun b => ((p.1, b), p.2)) <$> c p.1 := by
  simp only [simulateQ_bind, simulateQ_map, WriterT.run_bind', WriterT.run_map',
    run_simulateQ_toLeft]
  simp

/-- The reduction passes a lifted computation of hash and coin queries through. -/
theorem simulateQ_hideReasonsImpl_toLeft {β : Type} (c : OracleComp OracleWorld β) :
    simulateQ hideReasonsImpl (simulateQ (toLeft ReasonSigningSpec) c)
      = simulateQ (toLeft SigningSpec) c := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- Hash and coin queries pass through, and a signing request runs the signer. -/
def signerImpl (sk : SecretKey) :
    QueryImpl (OracleWorld + ReasonSigningSpec) (OracleComp OracleWorld) :=
  QueryImpl.ofLift OracleWorld (OracleComp OracleWorld) +
    fun (request : SignRequest) => (liftM (signWith H sk request.leafIndex request.message) :
      OracleComp OracleWorld (Except XmssError Signature))

/-- A signing request logs whether it succeeded; other queries log nothing. -/
def signerEntry : (t : (OracleWorld + ReasonSigningSpec).Domain) →
    (OracleWorld + ReasonSigningSpec).Range t → QueryLog SigningSpec
  | .inl _, _ => []
  | .inr request, result => [⟨request, result.toOption⟩]

/-- The reduction's reply: a failure reads as the bottom layer's. -/
def hiddenReply : (t : (OracleWorld + ReasonSigningSpec).Domain) →
    (OracleWorld + ReasonSigningSpec).Range t → (OracleWorld + ReasonSigningSpec).Range t
  | .inl _, answer => answer
  | .inr request, result => withHiddenReason request result.toOption

/-- The variant game's oracles: the signer's reply as it is. -/
theorem reasonOracles_eq (sk : SecretKey) :
    QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        reasonSigningOracle sk
      = logReply (signerImpl sk) signerEntry fun _ answer => answer := by
  funext t
  rcases t with t | request
  · rfl
  · rfl

/-- The theorem's oracles, behind the reduction: a failure reads as the bottom layer's. -/
theorem hiddenOracles_eq (sk : SecretKey) :
    (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        signingOracle sk) ∘ₛ hideReasonsImpl
      = logReply (signerImpl sk) signerEntry hiddenReply := by
  funext t
  rcases t with t | request
  · rfl
  · change simulateQ _ (withHiddenReason request <$>
      (liftM ((OracleWorld + SigningSpec).query (.inr request)) :
        OracleComp (OracleWorld + SigningSpec) (Option Signature))) = _
    rw [simulateQ_map, simulateQ_spec_query]
    apply WriterT.ext
    simp only [QueryImpl.add_apply_inr, signingOracle, WriterT.run_map',
      QueryImpl.run_withLogging_apply]
    simp [logReply, signerImpl, signerEntry, hiddenReply]
    rfl

/-- The adversary, followed by the verification of its forgery. -/
noncomputable def verifiedMain (adversary : ReasonAdversary) (pk : PublicKey) :
    OracleComp (OracleWorld + ReasonSigningSpec) (Forgery × Bool) :=
  adversary.main pk >>= fun forgery => (forgery, ·) <$>
    simulateQ (toLeft ReasonSigningSpec)
      (liftM (verifyWith H pk forgery.message forgery.signature) : OracleComp OracleWorld Bool)

/-- The keys of both games: a seed, then key generation. -/
noncomputable def keys : OracleComp OracleWorld (SecretKey × PublicKey) :=
  liftM sampleSeed >>= fun seed => liftM (keyGenWith H seed)

theorem reasonRun_eq (adversary : ReasonAdversary) :
    reasonRun adversary = keys >>= fun keys =>
      (fun p => (p.1.1, p.2, p.1.2)) <$>
        (simulateQ (logReply (signerImpl keys.1) signerEntry fun _ answer => answer)
          (verifiedMain adversary keys.2)).run := by
  unfold reasonRun keys verifiedMain
  simp only [bind_assoc, ← reasonOracles_eq, run_simulateQ_bind_toLeft]
  simp [map_bind]

theorem gameCore_hideReasons_eq (adversary : ReasonAdversary) :
    gameCore (hideReasons adversary) = keys >>= fun keys =>
      (fun p => decide (Valid p.2 ∧ ¬Contains p.2 p.1.1) && p.1.2) <$>
        (simulateQ (logReply (signerImpl keys.1) signerEntry hiddenReply)
          (verifiedMain adversary keys.2)).run := by
  unfold gameCore keys verifiedMain hideReasons
  simp only [bind_assoc, ← hiddenOracles_eq, QueryImpl.simulateQ_compose, simulateQ_bind,
    simulateQ_map, simulateQ_hideReasonsImpl_toLeft]
  simp [map_bind, run_simulateQ_toLeft]

/-! ## The bound -/

/-- A signing request that failed logs no signature. -/
theorem hiddenReply_eq (t : (OracleWorld + ReasonSigningSpec).Domain)
    (answer : (OracleWorld + ReasonSigningSpec).Range t)
    (h : ∀ entry ∈ signerEntry t answer, ¬entry.2 = none) : hiddenReply t answer = answer := by
  rcases t with t | request
  · rfl
  · rcases answer with err | signature
    · simp [signerEntry, Except.toOption] at h
    · rfl

/-- The reduction's reply logs what the signer's reply logs. -/
theorem signerEntry_hiddenReply (t : (OracleWorld + ReasonSigningSpec).Domain)
    (answer : (OracleWorld + ReasonSigningSpec).Range t) :
    signerEntry t (hiddenReply t answer) = signerEntry t answer := by
  rcases t with t | request
  · rfl
  · rcases answer with err | signature <;> rfl

/-- **The signer's reasons cost at most the probability of a failure.**

The adversary forges at most as often as its reduction, plus the probability of a failure.

The reduction plays the theorem's game. -/
theorem reasonForgeAdvantage_le (adversary : ReasonAdversary) :
    reasonForgeAdvantage adversary
      ≤ forgeAdvantage (hideReasons adversary) + signingFailure adversary := by
  have hwin : reasonForgeAdvantage adversary
      = Pr{let x ← (simulateQ romImpl (reasonRun adversary)).run' ∅}[
          (Valid x.2.1 ∧ ¬Contains x.2.1 x.1) ∧ x.2.2 = true] :=
    prEvent_countedOracle _ fun x : Forgery × QueryLog SigningSpec × Bool =>
      (Valid x.2.1 ∧ ¬Contains x.2.1 x.1) ∧ x.2.2 = true
  have hfail : signingFailure adversary
      = Pr{let x ← (simulateQ romImpl (reasonRun adversary)).run' ∅}[
          ∃ entry ∈ x.2.1, entry.2 = none] :=
    prEvent_countedOracle _ fun x : Forgery × QueryLog SigningSpec × Bool =>
      ∃ entry ∈ x.2.1, entry.2 = none
  have hgame : forgeAdvantage (hideReasons adversary)
      = Pr{let x ← (simulateQ romImpl (gameCore (hideReasons adversary))).run' ∅}[x = true] :=
    prEvent_countedOracle _ fun x : Bool => x = true
  rw [hwin, hfail, hgame, reasonRun_eq, gameCore_hideReasons_eq]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine prEvent_bind_le_add _ _ _ _ _ _ fun p => ?_
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]
  rw [add_comm]
  refine prEvent_le_prEvent_add_of_prEvent_and_not_le _ _ _ _ _ ?_
  have h := prEvent_logReply_and_not_bad_le romImpl (signerImpl p.1.1) signerEntry hiddenReply
    (fun entry => entry.2 = none) signerEntry_hiddenReply hiddenReply_eq
    (verifiedMain adversary p.1.2) p.2
    fun z => (Valid z.1.2 ∧ ¬Contains z.1.2 z.1.1.1) ∧ z.1.1.2 = true
  refine (le_of_eq ?_).trans (h.trans_eq ?_)
  · refine prEvent_congr _ _ _ fun z => ?_
    simp only [and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact ⟨fun h w hw hn => h ⟨w, hw, hn⟩, fun h ⟨w, hw, hn⟩ => h w hw hn⟩
  · refine prEvent_congr _ _ _ fun z => ?_
    simp

/-- **leanXMSS with a signer that reveals its reasons.**

Take an adversary whose reduction to the theorem's game makes at most `q >= 1` hash calls.

It forges with probability at most `q / 2^127`, plus the probability that a request fails. -/
theorem reasonForgeAdvantage_le_add (q : Nat) (hq : 1 ≤ q) (adversary : ReasonAdversary)
    (hbound : HasHashQueryBound (hideReasons adversary) q) :
    reasonForgeAdvantage adversary
      ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞) + signingFailure adversary :=
  (reasonForgeAdvantage_le adversary).trans
    (add_le_add_left (unforgeable q hq _ hbound) _)

/-- Each adversary of the theorem's game keeps its budget when read in this game.

So the budget of the bound above holds for it. -/
theorem hasHashQueryBound_hideReasons_ignoreReasons (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q) :
    HasHashQueryBound (hideReasons (ignoreReasons adversary)) q := by
  rwa [hideReasons_ignoreReasons]

end EthLib.Cryptography.Xmss.Unforgeability
