module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Game
public import EthLib.Cryptography.Proofs.LoggedUntilBad

/-!
# Proofs: a signer that tells why signing failed

In the theorem's game, a failed signing request gets no signature.

Here the signer replies with its whole result instead, its error included.

Its signer keeps its key across requests, as the theorem's game does.

The only error signing returns is a one-time key that found no codeword.

The request fixes that key on each layer, so the error tells which layer failed.

The keys, the oracles and the winning rule are those of the theorem's game.

The adversary forges with probability at most the theorem's bound, plus that of a failure.

A failure is a signing request whose signer returns an error.

The proof runs the adversary behind a reduction to the theorem's game.

The reduction answers every failure with the bottom layer's error, whichever layer failed.

Both games agree until the first failure, so they differ by at most its probability.

The proof joins the signer and the random oracle into one oracle.

Its state is the cache and the key.

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
open XmssSecurity (OracleWorld HashSpec romImpl)

/-! ## The game -/

/-- The signing oracle answers a request with the signer's result, its error included. -/
abbrev ReasonSigningSpec := SignRequest →ₒ Except XmssError Signature

/-- An adversary that sees why a signing request failed. -/
structure ReasonAdversary where
  main : PublicKey → OracleComp (OracleWorld + ReasonSigningSpec) Forgery

/-- `Sig(sk, idx, m)` on each request, its error included, with the key the last request returned.

The log records whether it succeeded, as the winning rule needs. -/
def reasonSigningOracle : QueryImpl ReasonSigningSpec
    (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) :=
  fun request => StateT.mk fun sk => WriterT.mk
    ((fun result => ((result.1, result.2), [⟨request, result.1.toOption⟩])) <$>
      liftM (signWith H sk request.leafIndex request.message))

/-- The game up to its result: keys, the adversary with its log, then the verification. -/
noncomputable def reasonRun (adversary : ReasonAdversary) :
    OracleComp OracleWorld (Forgery × QueryLog SigningSpec × Bool) := do
  let seed ← liftM sampleSeed
  let (pk, sk) ← liftM (keyGenWith H seed)
  let (((forgery, _), log) : (Forgery × SecretKey) × QueryLog SigningSpec) ←
    ((simulateQ (QueryImpl.ofLift OracleWorld
      (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) +
        reasonSigningOracle) (adversary.main pk)).run sk).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return (forgery, log, verified)

/-- The game against the counted random oracle of the theorem, from an empty cache. -/
noncomputable def reasonExperiment (adversary : ReasonAdversary) :
    ProbComp ((Forgery × QueryLog SigningSpec × Bool) × Nat) :=
  SufCma.countedRunIn (SufCma.randomOracleModel HashSpec) (reasonRun adversary)

/-- The probability that the adversary forges, under the winning rule of the theorem. -/
noncomputable def reasonForgeAdvantage (adversary : ReasonAdversary) : ℝ≥0∞ :=
  Pr{let result ← reasonExperiment adversary}[
    (Valid result.1.2.1 ∧ ¬SufCma.Returned scheme result.1.2.1 result.1.1) ∧ result.1.2.2 = true]

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
  simp only [hideReasons, ignoreReasons, SufCma.Adversary.mk.injEq]
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

/-! ## Both games as one adversary over one stateful oracle

The signer and the random oracle become one oracle, whose state is the cache and the key.

The adversary's queries pass through to it, and each reply is logged. -/

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

/-- Each query passes through to the joined oracle. -/
def passImpl : QueryImpl (OracleWorld + ReasonSigningSpec)
    (OracleComp (OracleWorld + ReasonSigningSpec)) :=
  fun t => liftM ((OracleWorld + ReasonSigningSpec).query t)

/-- The random oracle and the signer as one oracle: its state is the cache and the kept key. -/
noncomputable def keyedRo : QueryImpl (OracleWorld + ReasonSigningSpec)
    (StateT (QueryCache HashSpec × SecretKey) ProbComp)
  | .inl t => StateT.mk fun st => (fun p => (p.1, (p.2, st.2))) <$> (romImpl t).run st.1
  | .inr request => StateT.mk fun st => (fun p => (p.1.1, (p.2, p.1.2))) <$>
      (simulateQ romImpl (liftM (signWith H st.2 request.leafIndex request.message) :
        OracleComp OracleWorld _)).run st.1

/-- The game's oracles, with a reply that may change the signer's result.

A hash or coin query passes through, and a request signs with the kept key and logs its result. -/
def keyedImpl (reply : (t : (OracleWorld + ReasonSigningSpec).Domain) →
    (OracleWorld + ReasonSigningSpec).Range t → (OracleWorld + ReasonSigningSpec).Range t) :
    QueryImpl (OracleWorld + ReasonSigningSpec)
      (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
  | .inl t => StateT.mk fun sk => WriterT.mk ((fun u => ((reply (.inl t) u, sk), [])) <$>
      (liftM (OracleWorld.query t) : OracleComp OracleWorld _))
  | .inr request => StateT.mk fun sk => WriterT.mk
      ((fun result => ((reply (.inr request) result.1, result.2),
        signerEntry (.inr request) result.1)) <$>
        liftM (signWith H sk request.leafIndex request.message))

/-- The game's oracles reply with the signer's result as it is. -/
theorem keyedImpl_id :
    QueryImpl.ofLift OracleWorld
        (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) +
      reasonSigningOracle = keyedImpl fun _ answer => answer := by
  funext t
  rcases t with t | request
  · simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    rfl
  · rfl

/-- The theorem's game behind the reduction: a failure reads as the bottom layer's. -/
theorem keyedImpl_hiddenReply :
    (QueryImpl.ofLift OracleWorld
        (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) +
      SufCma.signingOracle scheme) ∘ₛ hideReasonsImpl = keyedImpl hiddenReply := by
  funext t
  rcases t with t | request
  · change simulateQ _ (liftM ((OracleWorld + SigningSpec).query (.inl t))) = _
    rw [simulateQ_spec_query]
    simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    rfl
  · change simulateQ _ (withHiddenReason request <$>
      (liftM ((OracleWorld + SigningSpec).query (.inr request)) :
        OracleComp (OracleWorld + SigningSpec) (Option Signature))) = _
    rw [simulateQ_map, simulateQ_spec_query]
    refine StateT.ext fun sk => ?_
    apply WriterT.ext
    simp only [StateT.run_map, WriterT.run_map', QueryImpl.add_apply_inr, SufCma.signingOracle,
      scheme, keyedImpl, StateT.run_mk, WriterT.run_mk, Functor.map_map]
    rfl

/-- A computation of hash and coin queries, lifted to the adversary's oracles, logs nothing.

It leaves the key as it is. -/
theorem run_keyedImpl_toLeft (reply : (t : (OracleWorld + ReasonSigningSpec).Domain) →
    (OracleWorld + ReasonSigningSpec).Range t → (OracleWorld + ReasonSigningSpec).Range t)
    (hreply : ∀ t u, reply (.inl t) u = u) {β : Type} (c : OracleComp OracleWorld β)
    (sk : SecretKey) :
    ((simulateQ (keyedImpl reply) (simulateQ (toLeft ReasonSigningSpec) c)).run sk).run =
      (fun b => ((b, sk), ([] : QueryLog SigningSpec))) <$> c := by
  induction c using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind']
    change (((keyedImpl reply (.inl t)).run sk).run >>= _) = _
    simp only [keyedImpl, StateT.run_mk, WriterT.run_mk, hreply]
    erw [bind_map_left, map_bind]
    refine bind_congr fun u => ?_
    rw [ih, Functor.map_map]
    rfl

/-- **A run over the game's oracles, then the random oracle, is a run over the joined oracle.**

The two runs give the same value, log, cache and key, in another order. -/
theorem run_romImpl_keyedImpl (reply : (t : (OracleWorld + ReasonSigningSpec).Domain) →
    (OracleWorld + ReasonSigningSpec).Range t → (OracleWorld + ReasonSigningSpec).Range t)
    {α : Type} (oa : OracleComp (OracleWorld + ReasonSigningSpec) α) (sk : SecretKey)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((simulateQ (keyedImpl reply) oa).run sk).run).run cache =
      (fun z => (((z.1.1, z.2.2), z.1.2), z.2.1)) <$>
        (simulateQ keyedRo (simulateQ (logReply passImpl signerEntry reply) oa).run).run
          (cache, sk) := by
  induction oa using OracleComp.inductionOn generalizing sk cache with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
      simulateQ_map, StateT.run_map, map_bind]
    -- The first query: the same run of the random oracle, or of the signer, on both sides.
    rcases t with t | request
    · have hL : (simulateQ romImpl ((keyedImpl reply (.inl t)).run sk).run).run cache =
          (keyedRo (.inl t)).run (cache, sk) >>= fun p =>
            pure (((reply (.inl t) p.1, p.2.2), signerEntry (.inl t) p.1), p.2.1) := by
        simp only [keyedImpl, keyedRo, StateT.run_mk, WriterT.run_mk, simulateQ_map,
          StateT.run_map, signerEntry, simulateQ_spec_query]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
        rfl
      have hR : (simulateQ keyedRo (logReply passImpl signerEntry reply (.inl t)).run).run
          (cache, sk) = (keyedRo (.inl t)).run (cache, sk) >>= fun p =>
            pure ((reply (.inl t) p.1, signerEntry (.inl t) p.1), p.2) := by
        simp only [logReply, passImpl, WriterT.run_mk, map_eq_bind_pure_comp]
        rfl
      rw [hL, hR, bind_assoc, bind_assoc]
      refine bind_congr fun p => ?_
      rw [pure_bind, pure_bind, ih, Functor.map_map, Functor.map_map]
      rfl
    · have hL : (simulateQ romImpl ((keyedImpl reply (.inr request)).run sk).run).run cache =
          (keyedRo (.inr request)).run (cache, sk) >>= fun p =>
            pure (((reply (.inr request) p.1, p.2.2), signerEntry (.inr request) p.1), p.2.1) := by
        simp only [keyedImpl, keyedRo, StateT.run_mk, WriterT.run_mk, simulateQ_map,
          StateT.run_map]
        simp only [map_eq_bind_pure_comp, bind_assoc]
        rfl
      have hR : (simulateQ keyedRo (logReply passImpl signerEntry reply (.inr request)).run).run
          (cache, sk) = (keyedRo (.inr request)).run (cache, sk) >>= fun p =>
            pure ((reply (.inr request) p.1, signerEntry (.inr request) p.1), p.2) := by
        simp only [logReply, passImpl, WriterT.run_mk, map_eq_bind_pure_comp]
        rfl
      rw [hL, hR, bind_assoc, bind_assoc]
      refine bind_congr fun p => ?_
      rw [pure_bind, pure_bind, ih, Functor.map_map, Functor.map_map]
      rfl

/-- The adversary, followed by the verification of its forgery. -/
noncomputable def verifiedMain (adversary : ReasonAdversary) (pk : PublicKey) :
    OracleComp (OracleWorld + ReasonSigningSpec) (Forgery × Bool) :=
  adversary.main pk >>= fun forgery => (forgery, ·) <$>
    simulateQ (toLeft ReasonSigningSpec)
      (liftM (verifyWith H pk forgery.message forgery.signature) : OracleComp OracleWorld Bool)

/-- The keys of both games: a seed, then key generation. -/
noncomputable def keys : OracleComp OracleWorld (PublicKey × SecretKey) :=
  liftM sampleSeed >>= fun seed => liftM (keyGenWith H seed)

/-- A run of the adversary over the game's oracles, then its verification, run after it. -/
theorem run_keyedImpl_verifiedMain (reply : (t : (OracleWorld + ReasonSigningSpec).Domain) →
    (OracleWorld + ReasonSigningSpec).Range t → (OracleWorld + ReasonSigningSpec).Range t)
    (hreply : ∀ t u, reply (.inl t) u = u) (adversary : ReasonAdversary) (pk : PublicKey)
    (sk : SecretKey) :
    ((simulateQ (keyedImpl reply) (verifiedMain adversary pk)).run sk).run =
      ((simulateQ (keyedImpl reply) (adversary.main pk)).run sk).run >>= fun p =>
        (fun b => (((p.1.1, b), p.1.2), p.2)) <$>
          (liftM (verifyWith H pk p.1.1.message p.1.1.signature) :
            OracleComp OracleWorld Bool) := by
  unfold verifiedMain
  simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, WriterT.run_bind',
    WriterT.run_map']
  refine bind_congr fun p => ?_
  rw [run_keyedImpl_toLeft reply hreply]
  simp [Functor.map_map, Prod.map]

/-- The variant game, once the keys exist, as a run over the joined oracle. -/
theorem reasonRun_eq (adversary : ReasonAdversary) :
    (simulateQ romImpl (reasonRun adversary)).run' ∅ =
      (simulateQ romImpl keys).run ∅ >>= fun p =>
        (fun z => (z.1.1.1, z.1.2, z.1.1.2)) <$>
          (simulateQ keyedRo (simulateQ (logReply passImpl signerEntry fun _ answer => answer)
            (verifiedMain adversary p.1.1)).run).run (p.2, p.1.2) := by
  have hrun : reasonRun adversary = keys >>= fun k =>
      (fun x => (x.1.1.1, x.2, x.1.1.2)) <$>
        ((simulateQ (keyedImpl fun _ answer => answer) (verifiedMain adversary k.1)).run
          k.2).run := by
    unfold reasonRun keys
    simp only [bind_assoc]
    refine bind_congr fun seed => bind_congr fun k => ?_
    rcases k with ⟨pk, sk⟩
    rw [run_keyedImpl_verifiedMain _ (fun _ _ => rfl), ← keyedImpl_id]
    simp only [map_bind, Functor.map_map]
    refine bind_congr fun p => ?_
    rcases p with ⟨⟨forgery, sk'⟩, log⟩
    simp only [map_eq_bind_pure_comp]
    rfl
  rw [hrun, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine bind_congr fun p => ?_
  rw [simulateQ_map, StateT.run_map, run_romImpl_keyedImpl, Functor.map_map, Functor.map_map]

/-- The theorem's game behind the reduction, once the keys exist, over the joined oracle. -/
theorem game_hideReasons_eq (adversary : ReasonAdversary) :
    (simulateQ romImpl (SufCma.game scheme (hideReasons adversary))).run' ∅ =
      (simulateQ romImpl keys).run ∅ >>= fun p =>
        (fun z => decide (Valid z.1.2 ∧ ¬SufCma.Returned scheme z.1.2 z.1.1.1) && z.1.1.2) <$>
          (simulateQ keyedRo (simulateQ (logReply passImpl signerEntry hiddenReply)
            (verifiedMain adversary p.1.1)).run).run (p.2, p.1.2) := by
  have hrun : SufCma.game scheme (hideReasons adversary) = keys >>= fun k =>
      (fun x => decide (Valid x.2 ∧ ¬SufCma.Returned scheme x.2 x.1.1.1) && x.1.1.2) <$>
        ((simulateQ (keyedImpl hiddenReply) (verifiedMain adversary k.1)).run k.2).run := by
    rw [game_eq]
    unfold SufCma.gameAfterKeys SufCma.checkForgery keys hideReasons
    simp only [bind_assoc]
    refine bind_congr fun seed => bind_congr fun k => ?_
    rcases k with ⟨pk, sk⟩
    rw [run_keyedImpl_verifiedMain _ (fun _ _ => rfl), ← QueryImpl.simulateQ_compose,
      keyedImpl_hiddenReply]
    simp only [map_bind, Functor.map_map]
    refine bind_congr fun p => ?_
    rcases p with ⟨⟨forgery, sk'⟩, log⟩
    simp only [map_eq_bind_pure_comp]
    rfl
  rw [hrun, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine bind_congr fun p => ?_
  rw [simulateQ_map, StateT.run_map, run_romImpl_keyedImpl, Functor.map_map, Functor.map_map]

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
      ≤ SufCma.advantage scheme (SufCma.randomOracleModel HashSpec) (hideReasons adversary) +
        signingFailure adversary := by
  have hwin : reasonForgeAdvantage adversary
      = Pr{let x ← (simulateQ romImpl (reasonRun adversary)).run' ∅}[
          (Valid x.2.1 ∧ ¬SufCma.Returned scheme x.2.1 x.1) ∧ x.2.2 = true] :=
    SufCma.prEvent_countedRunIn _ _ fun x : Forgery × QueryLog SigningSpec × Bool =>
      (Valid x.2.1 ∧ ¬SufCma.Returned scheme x.2.1 x.1) ∧ x.2.2 = true
  have hfail : signingFailure adversary
      = Pr{let x ← (simulateQ romImpl (reasonRun adversary)).run' ∅}[
          ∃ entry ∈ x.2.1, entry.2 = none] :=
    SufCma.prEvent_countedRunIn _ _ fun x : Forgery × QueryLog SigningSpec × Bool =>
      ∃ entry ∈ x.2.1, entry.2 = none
  have hgame : SufCma.advantage scheme (SufCma.randomOracleModel HashSpec) (hideReasons adversary)
      = Pr{let x ← (simulateQ romImpl (SufCma.game scheme (hideReasons adversary))).run' ∅}[
          x = true] :=
    rfl
  rw [hwin, hfail, hgame, reasonRun_eq, game_hideReasons_eq]
  simp only [map_bind]
  refine prEvent_bind_le_add ((simulateQ romImpl keys).run ∅) _ _ _ _ _ fun p => ?_
  rw [add_comm]
  refine prEvent_le_prEvent_add_of_prEvent_and_not_le _ _ _ _ _ ?_
  have h := prEvent_logReply_and_not_bad_le keyedRo passImpl signerEntry hiddenReply
    (fun entry => entry.2 = none) signerEntry_hiddenReply hiddenReply_eq
    (verifiedMain adversary p.1.1) (p.2, p.1.2)
    fun z => (Valid z.1.2 ∧ ¬SufCma.Returned scheme z.1.2 z.1.1.1) ∧ z.1.1.2 = true
  simp only [prEvent_map] at h ⊢
  refine (le_of_eq ?_).trans (h.trans_eq ?_)
  · refine prEvent_congr _ _ _ fun z => ?_
    simp only [and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact ⟨fun h w hw hn => h ⟨w, hw, hn⟩, fun h ⟨w, hw, hn⟩ => h w hw hn⟩
  · refine prEvent_congr _ _ _ fun z => ?_
    simp

/-- **leanXMSS with a signer that reveals its reasons.**

Take an adversary whose reduction to the theorem's game has a budget of `q >= 1` hash calls.

It forges with probability at most `q / 2^127`, plus the probability that a request fails. -/
theorem reasonForgeAdvantage_le_add (q : Nat) (hq : 1 ≤ q) (adversary : ReasonAdversary)
    (hbound : SufCma.IsGameQueryBound scheme (SufCma.randomOracleModel HashSpec)
      (hideReasons adversary) q) :
    reasonForgeAdvantage adversary
      ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞) + signingFailure adversary :=
  (reasonForgeAdvantage_le adversary).trans
    (add_le_add_left ((unforgeable q hq _ hbound).trans_eq (SufCma.mul_inv_two_pow _ _)) _)

/-- Each adversary of the theorem's game keeps its budget when read in this game.

So the budget of the bound above holds for it. -/
theorem hasHashQueryBound_hideReasons_ignoreReasons (adversary : Adversary) (q : Nat)
    (hbound : SufCma.IsGameQueryBound scheme (SufCma.randomOracleModel HashSpec) adversary q) :
    SufCma.IsGameQueryBound scheme (SufCma.randomOracleModel HashSpec)
      (hideReasons (ignoreReasons adversary)) q := by
  rwa [hideReasons_ignoreReasons]

end EthLib.Cryptography.Xmss.Unforgeability
