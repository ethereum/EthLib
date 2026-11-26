module

public import EthLib.Cryptography.Proofs.SufCma
public import EthLib.Cryptography.Proofs.ChargeBound
public import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# Proofs: the strong-unforgeability game under a change of oracles

A scheme's queries can be answered by computations over other oracles.

An adversary's coin and hash queries can be answered by a simulator with a state.

The game commutes with the first, and with the second when it turns one scheme into the other.

Every query of the game, the scheme's and the adversary's, can be answered by other oracles.
-/

@[expose] public section

namespace EthLib.Cryptography.SufCma

open OracleComp OracleSpec PFunctor.FreeM

variable {ι ι' : Type} {hs : OracleSpec ι} {hs' : OracleSpec ι'}
  {Request Message PublicKey SecretKey Signature : Type} {σ : Type}

/-! ## Schemes and adversaries over other oracles -/

/-- The scheme with each coin and hash query answered by `φ`, under the same rule of use. -/
def Scheme.mapOracles (φ : QueryImpl (unifSpec + hs) (OracleComp (unifSpec + hs')))
    (scheme : Scheme hs Request Message PublicKey SecretKey Signature) :
    Scheme hs' Request Message PublicKey SecretKey Signature where
  keyGen := simulateQ φ scheme.keyGen
  sign sk request := simulateQ φ (scheme.sign sk request)
  verify pk message signature := simulateQ φ (scheme.verify pk message signature)
  message := scheme.message
  Admissible := scheme.Admissible
  decidableAdmissible := scheme.decidableAdmissible
  admissible_singleton := scheme.admissible_singleton
  admissible_of_append_left := scheme.admissible_of_append_left
  admissible_congr := scheme.admissible_congr

/-- The adversary's oracles: coin and hash queries answered by `ψ`, requests sent unchanged. -/
def Adversary.routeImpl
    (ψ : QueryImpl (unifSpec + hs') (StateT σ (OracleComp (unifSpec + hs)))) :
    QueryImpl ((unifSpec + hs') + SigningSpec Request Signature)
      (StateT σ (OracleComp ((unifSpec + hs) + SigningSpec Request Signature)))
  | .inl t => StateT.mk fun s => ((ψ t).run s).liftComp _
  | .inr request => liftM (((unifSpec + hs) + SigningSpec Request Signature).query (.inr request))

/-- The adversary run through `ψ`: each coin or hash query is answered by `ψ`, from the state `s₀`.

Its requests go to the signer unchanged, and the final state of `ψ` is dropped. -/
def Adversary.route (ψ : QueryImpl (unifSpec + hs') (StateT σ (OracleComp (unifSpec + hs))))
    (s₀ : σ) (adversary : Adversary hs' Request Message PublicKey Signature) :
    Adversary hs Request Message PublicKey Signature where
  main pk := (simulateQ (Adversary.routeImpl ψ) (adversary.main pk)).run' s₀

/-! ## The game -/

/-- Coin and hash queries alone, run with the signer, keep the key and log no request. -/
theorem run_simulateQ_adversaryOracles_liftM
    (scheme : Scheme hs Request Message PublicKey SecretKey Signature) {β : Type}
    (oa : OracleComp (unifSpec + hs) β) (sk : SecretKey) :
    ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
      (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
        (OracleComp (unifSpec + hs)))) + signingOracle scheme)
      (oa.liftComp ((unifSpec + hs) + SigningSpec Request Signature))).run sk).run =
      (fun x => ((x, sk), ∅)) <$> oa := by
  rw [simulateQ_add_liftComp_sum_left]
  induction oa using OracleComp.inductionOn generalizing sk with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.ofLift_apply, StateT.run_bind,
      StateT.run_monadLift, WriterT.run_bind', ih, Functor.map_map]
    rfl

/-- The adversary's phase commutes with a simulator that turns one signer into the other. -/
theorem run_simulateQ_adversaryPhase
    (ψ : QueryImpl (unifSpec + hs') (StateT σ (OracleComp (unifSpec + hs))))
    (scheme' : Scheme hs' Request Message PublicKey SecretKey Signature)
    (scheme : Scheme hs Request Message PublicKey SecretKey Signature)
    (hsign : ∀ sk request s,
      (simulateQ ψ (scheme'.sign sk request)).run s = (·, s) <$> scheme.sign sk request)
    {α : Type} (oa : OracleComp ((unifSpec + hs') + SigningSpec Request Signature) α)
    (sk : SecretKey) (s : σ) :
    (simulateQ ψ ((simulateQ (QueryImpl.ofLift (unifSpec + hs')
      (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
        (OracleComp (unifSpec + hs')))) + signingOracle scheme') oa).run sk).run).run s =
      (fun r => (((r.1.1.1, r.1.2), r.2), r.1.1.2)) <$>
        ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
          (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
            (OracleComp (unifSpec + hs)))) + signingOracle scheme)
          ((simulateQ (Adversary.routeImpl ψ) oa).run s)).run sk).run := by
  induction oa using OracleComp.inductionOn generalizing sk s with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with t | request
    · simp only [add_apply_inl, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        LawfulFunctor.id_map, StateT.run_bind, StateT.run_monadLift, LawfulMonad.bind_pure_comp,
        bind_map_left, WriterT.run_bind, simulateQ_map, StateT.run_map, ih, Functor.map_map,
        Adversary.routeImpl, StateT.run_mk, run_simulateQ_adversaryOracles_liftM, List.empty_eq,
        List.nil_append, Prod.mk.eta, id_map', _root_.map_bind]
      -- The coin or hash query is lifted through the log by the composite of two lifts.
      erw [WriterT.run_monadLift']
      simp only [List.empty_eq, monadLift_self, simulateQ_map, StateT.run_map, bind_map_left,
        List.nil_append]
      have hq : simulateQ ψ (MonadLift.monadLift (OracleSpec.query t) :
          OracleComp (unifSpec + hs') ((unifSpec + hs').Range t)) = ψ t :=
        (simulateQ_query ψ (OracleSpec.query t)).trans (by simp)
      rw [hq]
    · simp only [add_apply_inr, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, QueryImpl.add_apply_inr, signingOracle, LawfulFunctor.id_map,
        StateT.run_bind, StateT.run_mk, WriterT.run_bind, WriterT.run_mk, bind_map_left,
        List.cons_append, List.nil_append, simulateQ_map, hsign, StateT.run_map, ih,
        Functor.map_map, Adversary.routeImpl, StateT.run_monadLift, LawfulMonad.bind_pure_comp,
        _root_.map_bind]

variable [DecidableEq Message] [DecidableEq Signature]

/-- **A simulator that turns one scheme into another moves into the adversary.**

The simulator answers the queries of the scheme over `hs'` as the scheme over `hs` asks them.

From every state, it runs the scheme's algorithms as the other scheme's and returns the same state.

So only the adversary's queries change its state.

The two schemes have the same messages and the same rule of use. -/
theorem run'_simulateQ_game
    (ψ : QueryImpl (unifSpec + hs') (StateT σ (OracleComp (unifSpec + hs)))) (s₀ : σ)
    (scheme' : Scheme hs' Request Message PublicKey SecretKey Signature)
    (scheme : Scheme hs Request Message PublicKey SecretKey Signature)
    (hkey : ∀ s, (simulateQ ψ scheme'.keyGen).run s = (·, s) <$> scheme.keyGen)
    (hsign : ∀ sk request s,
      (simulateQ ψ (scheme'.sign sk request)).run s = (·, s) <$> scheme.sign sk request)
    (hverify : ∀ pk message signature s,
      (simulateQ ψ (scheme'.verify pk message signature)).run s =
        (·, s) <$> scheme.verify pk message signature)
    (hmessage : scheme'.message = scheme.message)
    (hadmissible : scheme'.Admissible = scheme.Admissible)
    (adversary : Adversary hs' Request Message PublicKey Signature) :
    (simulateQ ψ (game scheme' adversary)).run' s₀ = game scheme (adversary.route ψ s₀) := by
  unfold game gameAfterKeys checkForgery Adversary.route
  simp [StateT.run'_eq, hkey, hadmissible, run_simulateQ_adversaryPhase ψ scheme' scheme hsign,
    hverify, hmessage, Returned]
  refine bind_congr fun keys => bind_congr fun a => ?_
  congr 1
  funext b
  congr 1
  exact decide_eq_decide.mpr (by rw [hadmissible, hmessage])

/-! ## Oracles answered without a state -/

/-- The adversary with its coin and hash queries answered by `φ`, and its requests unchanged. -/
def Adversary.mapOracles (φ : QueryImpl (unifSpec + hs) (OracleComp (unifSpec + hs')))
    (adversary : Adversary hs Request Message PublicKey Signature) :
    Adversary hs' Request Message PublicKey Signature where
  main pk :=
    simulateQ (φ.addLift (QueryImpl.id' (SigningSpec Request Signature))) (adversary.main pk)

omit [DecidableEq Message] [DecidableEq Signature] in
/-- Answering by `φ` with a state of type `Unit` is the plain simulation, state unchanged. -/
private theorem run_simulateQ_liftTarget_unit
    (φ : QueryImpl (unifSpec + hs) (OracleComp (unifSpec + hs'))) {α : Type}
    (oa : OracleComp (unifSpec + hs) α) (s : Unit) :
    (simulateQ (φ.liftTarget (StateT Unit (OracleComp (unifSpec + hs')))) oa).run s =
      (·, s) <$> simulateQ φ oa := by
  rw [simulateQ_liftTarget]
  simp only [StateT.run_monadLift, monadLift_self, LawfulMonad.bind_pure_comp]

omit [DecidableEq Message] [DecidableEq Signature] in
/-- Routing an adversary through `φ` with a state of type `Unit` answers its queries by `φ`. -/
theorem Adversary.route_liftTarget_eq_mapOracles
    (φ : QueryImpl (unifSpec + hs) (OracleComp (unifSpec + hs')))
    (adversary : Adversary hs Request Message PublicKey Signature) :
    adversary.route (φ.liftTarget (StateT Unit (OracleComp (unifSpec + hs')))) () =
      adversary.mapOracles φ := by
  have key : ∀ {α : Type} (oa : OracleComp ((unifSpec + hs) + SigningSpec Request Signature) α),
      (simulateQ (Adversary.routeImpl (φ.liftTarget (StateT Unit (OracleComp (unifSpec + hs')))))
        oa).run () =
        (·, ()) <$> simulateQ (φ.addLift (QueryImpl.id' (SigningSpec Request Signature))) oa := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t k ih =>
      rcases t with t | request
      · simp only [add_apply_inl, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, Adversary.routeImpl, PFunctor.Handler.liftTarget_apply,
          ofPFunctor_toPFunctor, StateT.run_monadLift, monadLift_self, LawfulMonad.bind_pure_comp,
          liftComp_map, LawfulFunctor.id_map, StateT.run_bind, StateT.run_mk, ih,
          QueryImpl.addLift_def, bind_map_left, QueryImpl.add_apply_inl, _root_.map_bind]
        rw [liftComp_eq_liftM_add_add]
      · simp only [add_apply_inr, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, Adversary.routeImpl, LawfulFunctor.id_map, StateT.run_bind,
          StateT.run_monadLift, LawfulMonad.bind_pure_comp, ih, QueryImpl.addLift_def,
          bind_map_left, QueryImpl.add_apply_inr, PFunctor.Handler.liftTarget_apply,
          ofPFunctor_toPFunctor, QueryImpl.id'_apply, _root_.map_bind]
        rfl
  obtain ⟨main⟩ := adversary
  simp only [Adversary.route, Adversary.mapOracles, StateT.run'_eq, key, Functor.map_map, id_map']

/-- **Naturality of the game.**

Answering every query of the game by `φ` gives the same game with `φ` pushed inside.

The scheme's and the adversary's own coin and hash queries are then each answered by `φ`. -/
theorem simulateQ_game (φ : QueryImpl (unifSpec + hs) (OracleComp (unifSpec + hs')))
    (scheme : Scheme hs Request Message PublicKey SecretKey Signature)
    (adversary : Adversary hs Request Message PublicKey Signature) :
    simulateQ φ (game scheme adversary) = game (scheme.mapOracles φ) (adversary.mapOracles φ) := by
  have h := run'_simulateQ_game (φ.liftTarget (StateT Unit (OracleComp (unifSpec + hs')))) ()
    scheme (scheme.mapOracles φ)
    (fun s => run_simulateQ_liftTarget_unit φ _ s)
    (fun sk request s => run_simulateQ_liftTarget_unit φ _ s)
    (fun pk message signature s => run_simulateQ_liftTarget_unit φ _ s) rfl rfl adversary
  rw [← Adversary.route_liftTarget_eq_mapOracles, ← h, StateT.run'_eq,
    run_simulateQ_liftTarget_unit]
  simp only [Functor.map_map, id_map']

omit [DecidableEq Message] [DecidableEq Signature] in
/-- Answering a scheme's queries by `φ`, then by `φ'`, is answering them by the composite. -/
theorem Scheme.mapOracles_mapOracles {ι'' : Type} {hs'' : OracleSpec ι''}
    (φ : QueryImpl (unifSpec + hs) (OracleComp (unifSpec + hs')))
    (φ' : QueryImpl (unifSpec + hs') (OracleComp (unifSpec + hs'')))
    (scheme : Scheme hs Request Message PublicKey SecretKey Signature) :
    (scheme.mapOracles φ).mapOracles φ' = scheme.mapOracles (φ' ∘ₛ φ) := by
  simp only [Scheme.mapOracles, QueryImpl.simulateQ_compose]

omit [DecidableEq Message] [DecidableEq Signature] in
/-- Answering a scheme's queries by the same queries leaves it unchanged. -/
theorem Scheme.mapOracles_id' (scheme : Scheme hs Request Message PublicKey SecretKey Signature) :
    scheme.mapOracles (QueryImpl.id' (unifSpec + hs)) = scheme := by
  simp only [Scheme.mapOracles, simulateQ_id']

omit [DecidableEq Message] [DecidableEq Signature] in
/-- Answering an adversary's queries by `φ`, then by `φ'`, is answering them by the composite. -/
theorem Adversary.mapOracles_mapOracles {ι'' : Type} {hs'' : OracleSpec ι''}
    (φ : QueryImpl (unifSpec + hs) (OracleComp (unifSpec + hs')))
    (φ' : QueryImpl (unifSpec + hs') (OracleComp (unifSpec + hs'')))
    (adversary : Adversary hs Request Message PublicKey Signature) :
    (adversary.mapOracles φ).mapOracles φ' = adversary.mapOracles (φ' ∘ₛ φ) := by
  have key : (φ'.addLift (QueryImpl.id' (SigningSpec Request Signature)) :
      QueryImpl _ (OracleComp ((unifSpec + hs'') + SigningSpec Request Signature))) ∘ₛ
      (φ.addLift (QueryImpl.id' (SigningSpec Request Signature)) :
        QueryImpl _ (OracleComp ((unifSpec + hs') + SigningSpec Request Signature))) =
      (φ' ∘ₛ φ).addLift (QueryImpl.id' (SigningSpec Request Signature)) := by
    ext (t | request) <;>
      simp only [QueryImpl.apply_compose, QueryImpl.addLift_def, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
    · rw [simulateQ_add_liftM_add_add, simulateQ_liftTarget]
    · exact (simulateQ_query _
        (((unifSpec + hs') + SigningSpec Request Signature).query (.inr request))).trans (by simp)
  obtain ⟨main⟩ := adversary
  unfold Adversary.mapOracles
  simp only [Adversary.mk.injEq]
  funext pk
  rw [← QueryImpl.simulateQ_compose, key]

omit [DecidableEq Message] [DecidableEq Signature] in
/-- Answering an adversary's queries by the same queries leaves it unchanged. -/
theorem Adversary.mapOracles_id' (adversary : Adversary hs Request Message PublicKey Signature) :
    adversary.mapOracles (QueryImpl.id' (unifSpec + hs)) = adversary := by
  have key : ((QueryImpl.id' (unifSpec + hs)).addLift
      (QueryImpl.id' (SigningSpec Request Signature)) :
      QueryImpl _ (OracleComp ((unifSpec + hs) + SigningSpec Request Signature))) =
      QueryImpl.id' ((unifSpec + hs) + SigningSpec Request Signature) := by
    ext ((n | i) | request) <;> rfl
  obtain ⟨main⟩ := adversary
  unfold Adversary.mapOracles
  simp only [Adversary.mk.injEq]
  funext pk
  rw [key, simulateQ_id']

/-! ## The calls of a routed adversary -/

/-- A query of an adversary that is a coin or hash query marked by `p`, not a request. -/
def IsMarkedQuery (p : (unifSpec + hs').Domain → Prop) :
    ((unifSpec + hs') + SigningSpec Request Signature).Domain → Prop
  | .inl t => p t
  | .inr _ => False

instance (p : (unifSpec + hs').Domain → Prop) [DecidablePred p] :
    DecidablePred (IsMarkedQuery (Request := Request) (Signature := Signature) p)
  | .inl t => inferInstanceAs (Decidable (p t))
  | .inr _ => inferInstanceAs (Decidable False)

omit [DecidableEq Message] [DecidableEq Signature] in
/-- Coins and hash queries lifted to the adversary's oracles keep a bound on marked queries.

The marks before and after the lift agree on every coin or hash query. -/
private theorem isQueryBoundP_liftComp {p : (unifSpec + hs).Domain → Prop} [DecidablePred p]
    {q : ((unifSpec + hs) + SigningSpec Request Signature).Domain → Prop} [DecidablePred q]
    (hpq : ∀ t, p t ↔ q (.inl t)) {α : Type} {oa : OracleComp (unifSpec + hs) α} {n : ℕ}
    (h : IsQueryBoundP oa p n) :
    IsQueryBoundP (oa.liftComp ((unifSpec + hs) + SigningSpec Request Signature)) q n := by
  have := IsQueryBoundP.liftComp_subSpec
    (superSpec := (unifSpec + hs) + SigningSpec Request Signature) (q := q) hpq h
  convert this using 1
  exact liftComp_inst_irrel (fun t => by rcases t with i | i <;> rfl) oa

omit [DecidableEq Message] [DecidableEq Signature] in
/-- **A routed adversary's hash calls.**

Let each answer of `ψ` to a query that `p` marks ask at most one hash query, and the others none.

An adversary with at most `q` marked queries is routed into one with at most `q` hash calls. -/
theorem isQueryBoundP_route (ψ : QueryImpl (unifSpec + hs') (StateT σ (OracleComp (unifSpec + hs))))
    (s₀ : σ) (p : (unifSpec + hs').Domain → Prop) [DecidablePred p]
    (hψ : ∀ t s, IsQueryBoundP ((ψ t).run s) (IsHashCall hs) (if p t then 1 else 0))
    (adversary : Adversary hs' Request Message PublicKey Signature) {q : ℕ}
    (hq : ∀ pk, IsQueryBoundP (adversary.main pk)
      (IsMarkedQuery (Request := Request) (Signature := Signature) p) q)
    (pk : PublicKey) :
    IsQueryBoundP ((adversary.route ψ s₀).main pk) (IsAdversaryHash hs Request Signature) q := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((hq pk).simulateQ_run_StateT_of_step ?_ s₀)
  rintro (t | request) s
  · exact isQueryBoundP_liftComp (fun t => by
      rcases t with n | x <;> simp [IsHashCall, SignatureAlg.IsHashQuery]) (hψ t s)
  · exact (isQueryBoundP_query_bind_iff (spec := (unifSpec + hs) + SigningSpec Request Signature)
      (p := IsAdversaryHash hs Request Signature) (Sum.inr request) _ _).2
        ⟨Or.inl id, fun _ => trivial⟩

omit [DecidableEq Message] [DecidableEq Signature] in
/-- A routed adversary makes at most as many requests as the adversary. -/
theorem isQueryBoundP_route_request
    (ψ : QueryImpl (unifSpec + hs') (StateT σ (OracleComp (unifSpec + hs)))) (s₀ : σ)
    (adversary : Adversary hs' Request Message PublicKey Signature) {n : ℕ}
    (hn : ∀ pk, IsQueryBoundP (adversary.main pk) (IsAdversaryRequest hs' Request Signature) n)
    (pk : PublicKey) :
    IsQueryBoundP ((adversary.route ψ s₀).main pk) (IsAdversaryRequest hs Request Signature) n := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((hn pk).simulateQ_run_StateT_of_step ?_ s₀)
  rintro (t | request) s
  · exact isQueryBoundP_liftComp (p := fun _ => False) (fun t => by
      rcases t with n | x <;> simp [SignatureAlg.IsSignQuery])
      (isQueryBoundP_false _ _)
  · exact (isQueryBoundP_query_bind_iff (spec := (unifSpec + hs) + SigningSpec Request Signature)
      (p := IsAdversaryRequest hs Request Signature) (Sum.inr request) _ _).2
        ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

/-! ## The charge of the game

A bound on the charge holds on every run: the costs `c` of the run's queries sum to at most it.
-/

/-- An adversary's coin or hash query costs what the scheme pays for it, and a request nothing. -/
def adversaryCharge (c : (unifSpec + hs).Domain → ℕ) :
    ((unifSpec + hs) + SigningSpec Request Signature).Domain → ℕ
  | .inl t => c t
  | .inr _ => 0

omit [DecidableEq Message] [DecidableEq Signature] in
/-- Under the hash cost, an adversary's query costs one exactly when it is a hash query. -/
theorem adversaryCharge_hashCost (t : ((unifSpec + hs) + SigningSpec Request Signature).Domain) :
    adversaryCharge hashCost t = if IsAdversaryHash hs Request Signature t then 1 else 0 := by
  rcases t with (n | x) | request <;> rfl

omit [DecidableEq Message] [DecidableEq Signature] in
/-- An adversary makes at most `q` hash calls of its own exactly when its queries cost at most `q`.

A hash call costs one, and a coin or a request nothing. -/
theorem isQueryBoundP_adversaryHash_iff
    {α : Type} (oa : OracleComp ((unifSpec + hs) + SigningSpec Request Signature) α) (q : ℕ) :
    IsQueryBoundP oa (IsAdversaryHash hs Request Signature) q ↔
      IsQueryBound oa q
        (fun t b =>
          adversaryCharge (Request := Request) (Signature := Signature) (hashCost (hs := hs)) t ≤ b)
        (fun t b =>
          b - adversaryCharge (Request := Request) (Signature := Signature)
            (hashCost (hs := hs)) t) := by
  rw [isQueryBoundP_iff_isChargeBound, isChargeBound_iff_isRollBound_nat]
  simp only [adversaryCharge_hashCost]
  rfl

/-- An adversary's request costs one, and a coin or a hash call nothing. -/
def requestCharge : ((unifSpec + hs) + SigningSpec Request Signature).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

omit [DecidableEq Message] [DecidableEq Signature] in
/-- An adversary makes at most `n` requests exactly when its queries cost at most `n`.

A request costs one, and a coin or a hash call nothing. -/
theorem isQueryBoundP_adversaryRequest_iff
    {α : Type} (oa : OracleComp ((unifSpec + hs) + SigningSpec Request Signature) α) (n : ℕ) :
    IsQueryBoundP oa (IsAdversaryRequest hs Request Signature) n ↔
      IsQueryBound oa n
        (fun t b => requestCharge (hs := hs) (Request := Request) (Signature := Signature) t ≤ b)
        (fun t b =>
          b - requestCharge (hs := hs) (Request := Request) (Signature := Signature) t) := by
  rw [isQueryBoundP_iff_isChargeBound,
    show (fun t => if IsAdversaryRequest hs Request Signature t then 1 else 0) = requestCharge
      from funext fun t => by
        rcases t with _ | _ <;> simp [SignatureAlg.IsSignQuery, requestCharge],
    isChargeBound_iff_isRollBound_nat]
  rfl

omit [DecidableEq Message] [DecidableEq Signature] in
/-- The adversary's phase is charged its own queries, and the signer's bound `S` per request. -/
theorem isChargeBound_adversaryPhase (c : (unifSpec + hs).Domain → ℕ) {S q n : ℕ}
    (scheme : Scheme hs Request Message PublicKey SecretKey Signature)
    (hS : ∀ sk request, IsChargeBound (scheme.sign sk request) c S) {α : Type}
    (oa : OracleComp ((unifSpec + hs) + SigningSpec Request Signature) α)
    (hq : IsChargeBound oa (adversaryCharge (Request := Request) (Signature := Signature) c) q)
    (hn : IsQueryBoundP oa (IsAdversaryRequest hs Request Signature) n) (sk : SecretKey) :
    IsChargeBound ((simulateQ (QueryImpl.ofLift (unifSpec + hs)
      (StateT SecretKey (WriterT (QueryLog (SigningSpec Request Signature))
        (OracleComp (unifSpec + hs)))) + signingOracle scheme) oa).run sk).run c (q + n * S) := by
  have h := hq.add_mul ((isQueryBoundP_iff_isChargeBound _ _ _).1 hn) S
  rw [zero_mul, add_zero] at h
  refine isChargeBound_run_simulateQ _ (fun t sk => ?_) h sk
  rcases t with t | request
  · simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply, StateT.run_monadLift,
      adversaryCharge, SignatureAlg.IsSignQuery, ↓reduceIte, zero_mul, add_zero]
    exact (isChargeBound_lift_iff (P := (unifSpec + hs).toPFunctor) t).2 (by rw [zero_add])
  · simp only [QueryImpl.add_apply_inr, signingOracle, StateT.run_mk, WriterT.run_mk,
      isChargeBound_map_iff', adversaryCharge, SignatureAlg.IsSignQuery, ↓reduceIte, one_mul,
      zero_add]
    exact hS sk request

/-- **The charge of the game is at most `K + (q + n * S) + V` on every run.**

Key generation costs `K`, the adversary's own queries `q`, and verification `V`.

Each of the at most `n` requests costs the signer's bound `S`. -/
theorem isChargeBound_game (c : (unifSpec + hs).Domain → ℕ) {K S V q n : ℕ}
    (scheme : Scheme hs Request Message PublicKey SecretKey Signature)
    (adversary : Adversary hs Request Message PublicKey Signature)
    (hK : IsChargeBound scheme.keyGen c K)
    (hS : ∀ sk request, IsChargeBound (scheme.sign sk request) c S)
    (hV : ∀ pk message signature, IsChargeBound (scheme.verify pk message signature) c V)
    (hq : ∀ pk, IsChargeBound (adversary.main pk)
      (adversaryCharge (Request := Request) (Signature := Signature) c) q)
    (hn : ∀ pk, IsQueryBoundP (adversary.main pk) (IsAdversaryRequest hs Request Signature) n) :
    IsChargeBound (game scheme adversary) c (K + (q + n * S) + V) := by
  rw [add_assoc]
  refine hK.bind fun keys => ?_
  refine (isChargeBound_adversaryPhase c scheme hS _ (hq keys.1) (hn keys.1) keys.2).bind
    fun x => ?_
  rw [← add_zero V]
  exact (hV _ _ _).bind fun _ => isChargeBound_pure _

end EthLib.Cryptography.SufCma
