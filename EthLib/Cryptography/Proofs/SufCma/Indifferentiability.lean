module

public import EthLib.Cryptography.Proofs.SufCma.Simulate
public import EthLib.Cryptography.Proofs.SufCma.Permutation
public import EthLib.Cryptography.Proofs.Indifferentiability
import VCVio.OracleComp.MapLens

/-!
# Proofs: strong unforgeability carries over from a random oracle to a random permutation

Let a hash `H` built on a permutation be indifferentiable from a random oracle.

A scheme's hash calls then run as `H` over the permutation, whose inverse the adversary also calls.

The scheme's forging advantage there is its random-oracle bound plus the indifferentiability bound.

That bound is taken at the cost of the whole game, the scheme's hash calls and the adversary's own.

The composition is Theorem 3.1 of [Ristenpart, Shacham, Shrimpton, Eurocrypt 2011][rss], §3.

It holds because the game is single-stage.

[rss]: https://hovav.net/ucsd/dist/revindiff.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.SufCma

open OracleComp OracleSpec ENNReal PFunctor.FreeM LazyPermutation Indifferentiability

variable {A Msg Dg : Type} [FinEnum A] [DecidableEq Msg] [SampleableType Dg]
  {Request Message PublicKey SecretKey Signature : Type}
  [DecidableEq Message] [DecidableEq Signature]

/-! ## The hybrid world

The hybrid oracles are coins, the hash and the permutation, side by side.

The scheme asks the hash there, and the adversary the permutation.

Read in the order of a game of indifferentiability, the hybrid game is a game of that kind.
-/

/-- The hybrid oracles: coins, then the hash beside the permutation. -/
private abbrev HybridSpec (A Msg Dg : Type) := unifSpec + ((Msg →ₒ Dg) + PermSpec A)

/-- The scheme's coin and hash queries, asked among the hybrid oracles. -/
private def schemeLens (A Msg Dg : Type) :
    PFunctor.Lens (unifSpec + (Msg →ₒ Dg)).toPFunctor (HybridSpec A Msg Dg).toPFunctor where
  toFunA
    | .inl n => .inl n
    | .inr m => .inr (.inl m)
  toFunB
    | .inl _ => id
    | .inr _ => id

/-- The adversary's coin and permutation queries, asked among the hybrid oracles. -/
private def permLens (A Msg Dg : Type) :
    PFunctor.Lens (unifSpec + PermSpec A).toPFunctor (HybridSpec A Msg Dg).toPFunctor where
  toFunA
    | .inl n => .inl n
    | .inr t => .inr (.inr t)
  toFunB
    | .inl _ => id
    | .inr _ => id

/-- The adversary's queries with its requests, asked among the hybrid oracles and the signer. -/
private def adversaryLens (A Msg Dg Request Signature : Type) :
    PFunctor.Lens ((unifSpec + PermSpec A) + SigningSpec Request Signature).toPFunctor
      (HybridSpec A Msg Dg + SigningSpec Request Signature).toPFunctor where
  toFunA
    | .inl (.inl n) => .inl (.inl n)
    | .inl (.inr t) => .inl (.inr (.inr t))
    | .inr request => .inr request
  toFunB
    | .inl (.inl _) => id
    | .inl (.inr _) => id
    | .inr _ => id

/-- The hybrid oracles, read in the order of a game of indifferentiability. -/
private def gameLens (A Msg Dg : Type) :
    PFunctor.Lens (HybridSpec A Msg Dg).toPFunctor (GameSpec A Msg Dg).toPFunctor where
  toFunA
    | .inl n => .inl (.inl n)
    | .inr (.inl m) => .inr m
    | .inr (.inr t) => .inl (.inr t)
  toFunB
    | .inl _ => id
    | .inr (.inl _) => id
    | .inr (.inr _) => id

/-- The hybrid oracles answered over the permutation: the hash by `impl`, the rest as asked. -/
private def hybridImpl
    (impl : QueryImpl (unifSpec + (Msg →ₒ Dg)) (OracleComp (unifSpec + PermSpec A))) :
    QueryImpl (HybridSpec A Msg Dg) (OracleComp (unifSpec + PermSpec A))
  | .inl n => impl (.inl n)
  | .inr (.inl m) => impl (.inr m)
  | .inr (.inr t) => liftM ((unifSpec + PermSpec A).query (.inr t))

/-- **A random-oracle bound holds in the random-permutation model, up to indifferentiability.**

The hash `H` over `π` is indifferentiable from a random oracle, with bound `ε` on the cost.

The scheme's hash calls run as `impl`, which returns `H π m` over any fixed permutation `π`.

Key generation, each request and verification cost at most `K`, `S` and `V`.

An adversary makes at most `q` permutation calls of its own and `maxSignings` requests.

Its forging chance is at most its random-oracle bound plus `ε (K + (q + maxSignings * S) + V)`. -/
theorem advantage_randomPermutationModel_le {H : (A → A) → Msg → Dg} {hashCost : Msg → ℕ}
    {ε : ℕ → ℝ≥0∞} (hind : Indifferentiable H hashCost ε)
    (impl : QueryImpl (unifSpec + (Msg →ₒ Dg)) (OracleComp (unifSpec + PermSpec A)))
    (hcoin : ∀ n, impl (.inl n) = liftM ((unifSpec + PermSpec A).query (.inl n)))
    (hhash : ∀ (π : Equiv.Perm A) m, simulateQ (permImpl π) (impl (.inr m)) = pure (H π m))
    (scheme : Scheme (Msg →ₒ Dg) Request Message PublicKey SecretKey Signature)
    {maxSignings slack bits K S V : ℕ}
    (hrom : StronglyUnforgeable scheme (randomOracleModel (Msg →ₒ Dg)) maxSignings slack bits)
    (hK : IsChargeBound scheme.keyGen (hashCharge (hs := Msg →ₒ Dg) hashCost) K)
    (hS : ∀ sk request,
      IsChargeBound (scheme.sign sk request) (hashCharge (hs := Msg →ₒ Dg) hashCost) S)
    (hV : ∀ pk message signature,
      IsChargeBound (scheme.verify pk message signature) (hashCharge (hs := Msg →ₒ Dg) hashCost) V)
    (adversary : Adversary (PermSpec A) Request Message PublicKey Signature) {q : ℕ}
    (hq : ∀ pk,
      IsQueryBoundP (adversary.main pk) (IsAdversaryHash (PermSpec A) Request Signature) q)
    (hn : ∀ pk, IsQueryBoundP (adversary.main pk)
      (IsAdversaryRequest (PermSpec A) Request Signature) maxSignings) :
    advantage (scheme.mapOracles impl) (randomPermutationModel A) adversary ≤
      ((q : ℝ≥0∞) + slack) * (2 : ℝ≥0∞)⁻¹ ^ bits + ε (K + (q + maxSignings * S) + V) := by
  -- The scheme and the adversary among the hybrid oracles, and their game.
  let schemeH := scheme.mapOracles (QueryImpl.comapLens (QueryImpl.id' _) (schemeLens A Msg Dg))
  let adversaryH := adversary.mapOracles (QueryImpl.comapLens (QueryImpl.id' _) (permLens A Msg Dg))
  let gameH := game schemeH adversaryH
  -- The adversary among the hybrid oracles is the adversary with its queries renamed.
  have hmainH : ∀ pk, adversaryH.main pk =
      (adversary.main pk).mapLens (adversaryLens A Msg Dg Request Signature) := by
    intro pk
    simp only [adversaryH, Adversary.mapOracles]
    rw [mapLens_eq_simulateQ]
    congr 1
    funext t
    rcases t with ((n | t) | request) <;>
      simp [QueryImpl.addLift, adversaryLens, permLens, QueryImpl.comapLens] <;> rfl
  -- The adversary among the hybrid oracles makes the requests of the adversary.
  have hnH : ∀ pk, IsQueryBoundP (adversaryH.main pk)
      (IsAdversaryRequest ((Msg →ₒ Dg) + PermSpec A) Request Signature) maxSignings := by
    have hpA : (fun t => IsAdversaryRequest ((Msg →ₒ Dg) + PermSpec A) Request Signature
        ((adversaryLens A Msg Dg Request Signature).toFunA t)) =
          IsAdversaryRequest (PermSpec A) Request Signature := by
      funext t
      rcases t with ((n | t) | request) <;> rfl
    intro pk
    rw [hmainH]
    exact IsQueryBoundP.mapLens _ (by simp only [hpA]; exact hn pk)
  -- The real world: the hybrid game read as a game of indifferentiability.
  have hreal : advantage (scheme.mapOracles impl) (randomPermutationModel A) adversary =
      realProb H (gameH.mapLens (gameLens A Msg Dg)) := by
    -- The game over the permutation is the hybrid game with its hash calls run by `impl`.
    have hgame : game (scheme.mapOracles impl) adversary = simulateQ (hybridImpl impl) gameH := by
      have hH : hybridImpl impl ∘ₛ QueryImpl.comapLens (QueryImpl.id' _) (schemeLens A Msg Dg) =
          impl := by
        funext t
        rcases t with n | m <;> simp [hybridImpl, schemeLens, QueryImpl.comapLens]
      have hP : hybridImpl impl ∘ₛ QueryImpl.comapLens (QueryImpl.id' _) (permLens A Msg Dg) =
          QueryImpl.id' _ := by
        funext t
        rcases t with n | t <;> simp [hybridImpl, permLens, QueryImpl.comapLens, hcoin]
      simp only [gameH, schemeH, adversaryH]
      rw [simulateQ_game, Scheme.mapOracles_mapOracles, Adversary.mapOracles_mapOracles, hH, hP,
        Adversary.mapOracles_id']
    -- Over a fixed permutation, both worlds answer each hybrid query alike.
    have himpl : ∀ π : Equiv.Perm A, permImpl π ∘ₛ hybridImpl impl =
        QueryImpl.comapLens (realImpl H π) (gameLens A Msg Dg) := by
      intro π
      funext t
      rcases t with n | m | t
      · simp [hybridImpl, gameLens, QueryImpl.comapLens, hcoin, realImpl]
        rfl
      · simp only [QueryImpl.apply_compose, hybridImpl]
        rw [hhash]
        simp [gameLens, QueryImpl.comapLens, realImpl]
        rfl
      · simp [hybridImpl, gameLens, QueryImpl.comapLens, realImpl]
        rfl
    rw [advantage, prEvent_runIn_randomPermutationModel, hgame]
    unfold realProb
    simp only [OracleComp.simulateQ_mapLens, ← himpl, QueryImpl.simulateQ_compose]
  -- The cost of the hybrid game.
  have hcost : WithinCost hashCost (gameH.mapLens (gameLens A Msg Dg))
      (K + (q + maxSignings * S) + V) := by
    -- A hybrid query costs what it costs read as a query of a game of indifferentiability.
    let c : (HybridSpec A Msg Dg).Domain → ℕ :=
      fun t => queryCost hashCost ((gameLens A Msg Dg).toFunA t)
    have hcH : c ∘ (schemeLens A Msg Dg).toFunA = hashCharge (hs := Msg →ₒ Dg) hashCost := by
      funext t
      rcases t with n | m <;> rfl
    have hscheme : ∀ {α : Type} (oa : OracleComp (unifSpec + (Msg →ₒ Dg)) α) (B : ℕ),
        IsChargeBound oa (hashCharge (hs := Msg →ₒ Dg) hashCost) B →
          IsChargeBound (simulateQ (QueryImpl.comapLens (QueryImpl.id' _) (schemeLens A Msg Dg))
            oa) c B := by
      intro α oa B h
      rw [← mapLens_eq_simulateQ]
      exact IsChargeBound.mapLens _ (hcH ▸ h)
    have hcA : adversaryCharge (Request := Request) (Signature := Signature) c ∘
        (adversaryLens A Msg Dg Request Signature).toFunA =
          fun t => if IsAdversaryHash (PermSpec A) Request Signature t then 1 else 0 := by
      funext t
      rcases t with ((n | t) | request) <;> rfl
    have hc : IsChargeBound gameH c (K + (q + maxSignings * S) + V) := by
      refine isChargeBound_game c schemeH adversaryH (hscheme _ _ hK)
        (fun sk request => hscheme _ _ (hS sk request))
        (fun pk message signature => hscheme _ _ (hV pk message signature)) (fun pk => ?_)
        (fun pk => ?_)
      · rw [hmainH]
        exact IsChargeBound.mapLens _
          (hcA ▸ (isQueryBoundP_iff_isChargeBound _ _ _).1 (hq pk))
      · exact hnH pk
    exact (isChargeBound_iff_isRollBound_nat _ _ _).1 (IsChargeBound.mapLens _ hc)
  -- The ideal world: every simulator turns the hybrid game into the game of an adversary.
  have hideal : ∀ (σ : Type) (s₀ : σ)
      (Sim : QueryImpl (PermSpec A) (StateT σ (OracleComp (RomSpec Msg Dg)))),
      AsksOnce Sim → romProb (romGame Sim s₀ (gameH.mapLens (gameLens A Msg Dg))) ≤
        ((q : ℝ≥0∞) + slack) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
    intro σ s₀ Sim hSim
    -- The simulator on the hybrid game, through the order of a game of indifferentiability.
    let ψ := QueryImpl.comapLens (idealImpl Sim) (gameLens A Msg Dg)
    -- The scheme's queries reach the random oracle unchanged, and keep the simulator's state.
    have hlift : ∀ {α : Type} (oa : OracleComp (unifSpec + (Msg →ₒ Dg)) α) (s : σ),
        (simulateQ ψ (simulateQ (QueryImpl.comapLens (QueryImpl.id' _) (schemeLens A Msg Dg))
          oa)).run s = (·, s) <$> oa := by
      intro α oa s
      have hstep : ∀ t s, ((ψ ∘ₛ QueryImpl.comapLens (QueryImpl.id' _) (schemeLens A Msg Dg))
          t).run s = (·, s) <$>
            (liftM ((unifSpec + (Msg →ₒ Dg)).query t) : OracleComp (RomSpec Msg Dg) _) := by
        rintro (n | m) s <;> simp [ψ, idealImpl, gameLens, schemeLens, QueryImpl.comapLens]
      rw [← QueryImpl.simulateQ_compose]
      generalize ψ ∘ₛ QueryImpl.comapLens (QueryImpl.id' _) (schemeLens A Msg Dg) = φ at hstep
      induction oa using OracleComp.inductionOn generalizing s with
      | pure x => simp
      | query_bind t k ih =>
        rw [simulateQ_query_bind, StateT.run_bind]
        simp [hstep, ih]
    have hgame : romGame Sim s₀ (gameH.mapLens (gameLens A Msg Dg)) =
        game scheme (adversaryH.route ψ s₀) := by
      rw [romGame, OracleComp.simulateQ_mapLens]
      exact run'_simulateQ_game ψ s₀ schemeH scheme (hlift _) (fun sk request => hlift _)
        (fun pk message signature => hlift _) rfl rfl adversaryH
    -- Each hash or permutation call of the adversary asks the random oracle at most once.
    have hψ : ∀ t s, IsQueryBoundP ((ψ t).run s) (IsHashCall (Msg →ₒ Dg))
        (if (fun t : (HybridSpec A Msg Dg).Domain => t.isRight = true) t then 1 else 0) := by
      rintro (n | m | t) s
      · simp [ψ, idealImpl, gameLens, IsHashCall]
      · simp [ψ, idealImpl, gameLens]
      · simp [ψ, idealImpl, gameLens]
        exact hSim t s
    have hqH : ∀ pk, IsQueryBoundP (adversaryH.main pk)
        (IsMarkedQuery (Request := Request) (Signature := Signature)
          (fun t : (HybridSpec A Msg Dg).Domain => t.isRight = true)) q := by
      have hp : (fun t => IsMarkedQuery (Request := Request) (Signature := Signature)
          (fun t : (HybridSpec A Msg Dg).Domain => t.isRight = true)
          ((adversaryLens A Msg Dg Request Signature).toFunA t)) =
            IsAdversaryHash (PermSpec A) Request Signature := by
        funext t
        rcases t with ((n | t) | request) <;>
          simp [IsMarkedQuery, adversaryLens, SignatureAlg.IsHashQuery]
      intro pk
      rw [hmainH]
      exact IsQueryBoundP.mapLens _ (by simp only [hp]; exact hq pk)
    rw [hgame, romProb, ← runIn_randomOracleModel]
    exact hrom q _ (isQueryBoundP_route ψ s₀ _ hψ adversaryH hqH)
      (isQueryBoundP_route_request ψ s₀ adversaryH hnH)
  rw [hreal]
  exact realProb_le_of_romProb_le hind hcost hideal

end EthLib.Cryptography.SufCma
