module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Game
public import EthLib.Cryptography.Proofs.Xmss.Sign

/-!
# Proofs: the signer that keeps its key wins as often as the stateless one

The game's signer keeps its key: `S`, `P`, the top tree, and the bottom trees it signed in last.

The stateless signer of the note rebuilds them from the seed on each request.

Every hash call the kept parts stand for was made before, and the oracle's cache holds its answer.

So the stateless signer's extra calls return what the key holds, and it signs the same bytes.

The two games give the adversary the same answers, with the same oracle cache after each step.

Hence both games win with the same probability.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.Xmss.Internal (signRootWith cacheTreeWith fetchTreeWith)
open XmssSecurity (HashSpec OracleWorld romImpl)
open XmssSecurity.Seeded (Erases worldKnown erases_pure_of_resolves)
open DeterministicSigning (Resolves resolves_of_run cache_le_of_run)

/-! ## A resolved build resolves its nodes and paths -/

section Merkle

variable {D R α : Type} {cache : QueryCache (D →ₒ R)}
  (hash : Merkle.Position → α → α → OracleComp (D →ₒ R) α) (leaves : Nat → OracleComp (D →ₒ R) α)

/-- A resolved build resolves the build of every node below it. -/
theorem resolves_build_below : ∀ (L J : Nat) (T : Merkle.Built α),
    Resolves cache (Merkle.build hash leaves ⟨L, J⟩) T →
    ∀ k i, k ≤ L → i / 2 ^ (L - k) = J →
      ∃ T', Resolves cache (Merkle.build hash leaves ⟨k, i⟩) T'
  | 0, J, T, h, k, i, hk, hi => by
    obtain rfl : k = 0 := by omega
    simp only [Nat.sub_self, pow_zero, Nat.div_one] at hi
    subst hi
    exact ⟨T, h⟩
  | L + 1, J, T, h, k, i, hk, hi => by
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · simp only [Nat.sub_self, pow_zero, Nat.div_one] at hi
      subst hi
      exact ⟨T, h⟩
    · rw [Merkle.build_succ] at h
      obtain ⟨l, hl, h⟩ := h.of_bind
      obtain ⟨r, hr, -⟩ := h.of_bind
      -- The node sits below the left child or the right child, by one bit of its index.
      have hdiv : i / 2 ^ (L - k) / 2 = J := by
        rw [Merkle.div_pow_div_two, show L - k + 1 = L + 1 - k by omega, hi]
      rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ (L - k)) with h0 | h1
      · exact resolves_build_below L (2 * J) l hl k i (by omega) (by omega)
      · exact resolves_build_below L (2 * J + 1) r hr k i (by omega) (by omega)

/-- A resolved build resolves the node at its position, to its top value. -/
theorem resolves_node_of_build {p : Merkle.Position} {T : Merkle.Built α}
    (h : Resolves cache (Merkle.build hash leaves p) T) :
    Resolves cache (Merkle.node hash leaves p) T.value := by
  rw [← Merkle.value_build]
  exact h.map _

/-- The siblings resolve when each sibling node does. -/
theorem resolves_siblings : ∀ (n : Nat) (p : Merkle.Position),
    (∀ t < n, ∃ v, Resolves cache (Merkle.node hash leaves (p.ancestor t).sibling) v) →
    ∃ v, Resolves cache (Merkle.siblings hash leaves p n) v
  | 0, _, _ => ⟨_, .pure _⟩
  | n + 1, p, h => by
    obtain ⟨s, hs⟩ := h 0 (by omega)
    obtain ⟨rest, hrest⟩ := resolves_siblings n p.parent fun t ht => by
      simpa only [Merkle.Position.ancestor_parent] using h (t + 1) (by omega)
    rw [Merkle.Position.ancestor_zero] at hs
    exact ⟨_, hs.bind (hrest.bind (.pure _))⟩

/-- A resolved build of a tree of height `h` resolves the path of each of its leaves. -/
theorem resolves_path_of_build {h : Nat} {T : Merkle.Built α}
    (hT : Resolves cache (Merkle.build hash leaves ⟨h, 0⟩) T) {j : Nat} (hj : j < 2 ^ h) :
    ∃ v, Resolves cache (Merkle.path hash leaves h j) v := by
  refine resolves_siblings hash leaves h ⟨0, j⟩ fun t ht => ?_
  -- The sibling on level `t` is a node of the tree, below its root.
  have hlt : j / 2 ^ t < 2 ^ (h - t) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, show h - t + t = h by omega]
    exact hj
  have hsib : (j / 2 ^ t) ^^^ 1 < 2 ^ (h - t) :=
    Nat.xor_lt_two_pow hlt (Nat.one_lt_two_pow (by omega))
  obtain ⟨T', hT'⟩ := resolves_build_below hash leaves h 0 T hT t ((j / 2 ^ t) ^^^ 1) (by omega)
    (Nat.div_eq_of_lt hsib)
  refine ⟨T'.value, ?_⟩
  rw [Merkle.Position.ancestor_mk_zero, Merkle.Position.sibling_mk]
  exact resolves_node_of_build hash leaves hT'

end Merkle

/-! ## The top tree's paths -/

/- A concrete height would let Lean unfold a whole tree, so the height stays opaque. -/
attribute [local irreducible] LAYER_HEIGHT

/-- `H` in the game, on the hash oracle alone. -/
local notation "Hh" => (queryH : ByteArray → OracleComp HashSpec (Vector UInt8 32))

/-- A resolved top tree resolves the path of each top key, to the path the tree holds. -/
theorem resolves_path_top {cache : QueryCache HashSpec} {pp : PublicParam} {s : Seed}
    {T : Merkle.Built Digest}
    (hT : Resolves cache (build Hh pp (seedPrf Hh s) .top LAYER_HEIGHT 0) T) {b : Nat}
    (hb : b < 2 ^ LAYER_HEIGHT) :
    Resolves cache (path Hh pp (seedPrf Hh s) .top b) (T.path LAYER_HEIGHT b) := by
  obtain ⟨v, hv⟩ := resolves_path_of_build _ _ hT hb
  change Resolves cache (path Hh pp (seedPrf Hh s) .top b) v at hv
  convert hv using 1
  -- Answer every query from the cache: the build and the path then evaluate to their values.
  let f : QueryImpl HashSpec Id := fun x => (cache x).getD default
  have hf : ∀ x a, cache x = some a → f x = a := fun x a hx => by simp [f, hx]
  rw [← hT.eval f hf, ← hv.eval f hf]
  have hbuild := build_map_monad (m := OracleComp HashSpec) (m' := Id)
    (fun {β} (c : OracleComp HashSpec β) => (evalWithAnswerFn f c : Id β)) (fun _ => rfl)
    (fun x g => evalWithAnswerFn_bind f x g) Hh (seedPrf Hh s) pp .top LAYER_HEIGHT 0
  have hpath := path_map_monad (m := OracleComp HashSpec) (m' := Id)
    (fun {β} (c : OracleComp HashSpec β) => (evalWithAnswerFn f c : Id β)) (fun _ => rfl)
    (fun x g => evalWithAnswerFn_bind f x g) Hh (seedPrf Hh s) pp .top b
  rw [hbuild, hpath]
  have := path_build_run (H := fun x => (evalWithAnswerFn f (Hh x) : Id _)) (pp := pp)
    (prf := fun pp a suffix => (evalWithAnswerFn f (seedPrf Hh s pp a suffix) : Id _))
    (layer := .top) b
  rwa [Nat.div_eq_of_lt hb] at this

/-! ## What the cache knows of a key -/

/-- The cache answers every call that a key's parts stand for, with the key's values.

Those are the derivations of `S` and `P` from the seed, the top tree, and each kept tree.

Each kept tree comes with its top signature, all computed as the stateless signer computes them. -/
structure KeyInv (seed : Seed) (sk : SecretKey) (cache : QueryCache HashSpec) : Prop where
  /-- The scheme seed `S` of the seed. -/
  seed_resolves : Resolves cache (schemeSeed Hh seed) sk.schemeSeed
  /-- The parameter `P`, derived from `S`. -/
  param_resolves : Resolves cache (publicParamOf (seedPrf Hh sk.schemeSeed)) sk.publicParam
  /-- The top tree, built from `S`. -/
  top_resolves :
    Resolves cache (build Hh sk.publicParam (seedPrf Hh sk.schemeSeed) .top LAYER_HEIGHT 0) sk.top
  /-- Each kept tree, and the top signature of its root. -/
  kept_resolves : ∀ t ∈ sk.cache,
    Resolves cache (build Hh sk.publicParam (seedPrf Hh sk.schemeSeed) .bottom LAYER_HEIGHT
      t.index) t.tree ∧
    Resolves cache (signLayer Hh sk.publicParam (seedPrf Hh sk.schemeSeed) .top t.index
      (packBytes t.tree.value)) t.top

section KeyInv

variable {seed : Seed} {sk : SecretKey} {cache : QueryCache HashSpec}

/-- A cache that grows keeps knowing a key. -/
theorem KeyInv.mono (h : KeyInv seed sk cache) {cache' : QueryCache HashSpec}
    (hle : cache ≤ cache') : KeyInv seed sk cache' :=
  ⟨h.seed_resolves.mono hle, h.param_resolves.mono hle, h.top_resolves.mono hle,
    fun t ht => ⟨(h.kept_resolves t ht).1.mono hle, (h.kept_resolves t ht).2.mono hle⟩⟩

/-- A cache that resolved key generation knows the key it returned. -/
theorem keyInv_keyGenWith {pk : PublicKey}
    (h : Resolves cache (keyGenWith Hh seed) (pk, sk)) : KeyInv seed sk cache := by
  unfold keyGenWith at h
  obtain ⟨s, hs, h⟩ := h.of_bind
  obtain ⟨pp, hpp, h⟩ := h.of_bind
  obtain ⟨top, htop, h⟩ := h.of_bind
  obtain ⟨-, rfl⟩ := Prod.mk.inj h.pure_inv.symm
  exact ⟨hs, hpp, htop, fun t ht => absurd ht List.not_mem_nil⟩

/-- The top key's signature of a root, path read from the top tree, erases the stateless one.

The stateless one computes the path from the seed, and the cache answers those calls. -/
theorem erases_signLayer_signRootWith (h : KeyInv seed sk cache) {b : Nat}
    (hb : b < 2 ^ LAYER_HEIGHT) (root : Digest) :
    Erases cache (signLayer Hh sk.publicParam (seedPrf Hh sk.schemeSeed) .top b (packBytes root))
      (signRootWith Hh sk b root) := by
  unfold signLayer signRootWith
  simp only [Internal.otsSignTrials_hashTrials]
  refine Erases.bind (Erases.refl _ _) _ _ fun o => ?_
  rcases o with _ | ⟨rho, y⟩
  · exact .pure _
  · exact Erases.bind_known (erases_pure_of_resolves (resolves_path_top h.top_resolves hb)) _ _
      (.pure _)

/-- A resolved top signature of a root, path read from the top tree, resolves the stateless one. -/
theorem resolves_signLayer_of_signRootWith (h : KeyInv seed sk cache) {b : Nat}
    (hb : b < 2 ^ LAYER_HEIGHT) {root : Digest} {r : Except XmssError LayerSignature}
    (hr : Resolves cache (signRootWith Hh sk b root) r) :
    Resolves cache (signLayer Hh sk.publicParam (seedPrf Hh sk.schemeSeed) .top b
      (packBytes root)) r := by
  unfold signRootWith at hr
  simp only [Internal.otsSignTrials_hashTrials] at hr
  unfold signLayer
  obtain ⟨o, ho, hr⟩ := hr.of_bind
  refine ho.bind ?_
  rcases o with _ | ⟨rho, y⟩
  · exact hr
  · rw [← hr.pure_inv]
    exact (resolves_path_top h.top_resolves hb).bind (.pure _)

/-- A resolved fetch of a bottom tree returns a key that the cache knows. -/
theorem keyInv_fetchTreeWith (h : KeyInv seed sk cache) {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT)
    {t : CachedTree} {sk' : SecretKey}
    (hr : Resolves cache (fetchTreeWith Hh sk b) (t, sk')) : KeyInv seed sk' cache := by
  unfold fetchTreeWith at hr
  split at hr
  · -- A kept tree moves to the front; the others stay.
    next t0 ht =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr.pure_inv
    refine ⟨h.seed_resolves, h.param_resolves, h.top_resolves, fun u hu => ?_⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h.kept_resolves _ (List.mem_of_find?_eq_some ht)
    · exact h.kept_resolves u (List.mem_filter.1 hu).1
  · -- A new tree goes in front, and the trees past the limit are dropped.
    obtain ⟨t0, ht0, hr⟩ := hr.of_bind
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr.pure_inv
    unfold cacheTreeWith at ht0
    obtain ⟨tree, htree, ht0⟩ := ht0.of_bind
    obtain ⟨top, htop, ht0⟩ := ht0.of_bind
    rw [← ht0.pure_inv]
    refine ⟨h.seed_resolves, h.param_resolves, h.top_resolves, fun u hu => ?_⟩
    rcases List.mem_cons.1 (List.mem_of_mem_take hu) with rfl | hu
    · exact ⟨htree, resolves_signLayer_of_signRootWith h hb htop⟩
    · exact h.kept_resolves u hu

/-- A resolved signature returns a key that the cache knows. -/
theorem keyInv_signWith (h : KeyInv seed sk cache) {idx : LeafIndex} {msg : Message}
    {r : Except XmssError Signature} {sk' : SecretKey}
    (hr : Resolves cache (signWith Hh sk idx msg) (r, sk')) : KeyInv seed sk' cache := by
  unfold signWith Internal.signWithTrials at hr
  simp only [Internal.otsSignTrials_hashTrials] at hr
  obtain ⟨o, -, hr⟩ := hr.of_bind
  rcases o with _ | ⟨rho, y⟩
  · obtain ⟨-, rfl⟩ := Prod.mk.inj hr.pure_inv.symm
    exact h
  · obtain ⟨⟨t, sk1⟩, hfetch, hr⟩ := hr.of_bind
    have hsk : sk1 = sk' := by
      dsimp only at hr
      rcases htt : t.top with top | err <;> rw [htt] at hr <;> exact (Prod.mk.inj hr.pure_inv).2
    subst hsk
    exact keyInv_fetchTreeWith h (bottomTree_lt idx) hfetch

/-- **The stateless signature erases to the signature of a key that the cache knows.**

The stateless signer derives `S` and `P` again, and rebuilds the top path and any kept tree.

The cache answers all those calls, with the values the key holds. -/
theorem erases_statelessSignWith_signWith (h : KeyInv seed sk cache) (idx : LeafIndex)
    (msg : Message) :
    Erases cache (statelessSignWith Hh seed idx msg) (Prod.fst <$> signWith Hh sk idx msg) := by
  unfold statelessSignWith
  refine Erases.bind_known (erases_pure_of_resolves h.seed_resolves) _ _ ?_
  refine Erases.bind_known (erases_pure_of_resolves h.param_resolves) _ _ ?_
  unfold signDerived signWith Internal.signWithTrials
  simp only [Internal.otsSignTrials_hashTrials]
  rw [map_bind]
  refine Erases.bind (Erases.refl _ _) _ _ fun o => ?_
  rcases o with _ | ⟨rho, y⟩
  · exact .pure _
  · dsimp only
    rw [map_bind]
    unfold fetchTreeWith
    split
    · -- A kept tree: its build and its top signature are answered by the cache.
      next t ht =>
      have hidx : t.index = bottomTree idx := by simpa using List.find?_some ht
      obtain ⟨htree, htop⟩ := h.kept_resolves t (List.mem_of_find?_eq_some ht)
      rw [hidx] at htree htop
      rw [pure_bind]
      refine Erases.bind_known (erases_pure_of_resolves htree) _ _ ?_
      refine Erases.bind_known (erases_pure_of_resolves htop) _ _ ?_
      cases t.top <;> exact .pure _
    · -- A new tree: the same build, and the top path is answered by the cache.
      unfold cacheTreeWith
      simp only [bind_assoc, pure_bind]
      refine Erases.bind (Erases.refl _ _) _ _ fun tree => ?_
      refine Erases.bind (erases_signLayer_signRootWith h (bottomTree_lt idx) _) _ _ fun r => ?_
      cases r <;> exact .pure _

end KeyInv

/-! ## Two simulations, one of them keeping a state -/

section Coupling

variable {ι : Type} {spec : OracleSpec ι} {σ L : Type}

/-- A run with a state, its state forgotten: its value, its log and the cache after it. -/
def dropState {β : Type} (x : ((β × σ) × List L) × QueryCache HashSpec) :
    (β × List L) × QueryCache HashSpec :=
  ((x.1.1.1, x.1.2), x.2)

/-- **Two simulations agree when each query does, under an invariant of the state and cache.**

One simulation keeps a state, the other none, and both log their queries.

When each query gives the same answer, log and cache, and keeps the invariant, so does the run. -/
theorem evalDistEq_simulateQ_state (Inv : σ → QueryCache HashSpec → Prop)
    (implL : QueryImpl spec (StateT σ (WriterT (List L) (OracleComp OracleWorld))))
    (implR : QueryImpl spec (WriterT (List L) (OracleComp OracleWorld)))
    (hstep : ∀ q s c, Inv s c →
      dropState <$> (simulateQ romImpl ((implL q).run s).run).run c =ᵈ
        (simulateQ romImpl (implR q).run).run c)
    (hinv : ∀ q s c, Inv s c →
      ∀ x ∈ support ((simulateQ romImpl ((implL q).run s).run).run c), Inv x.1.1.2 x.2)
    {α : Type} (oa : OracleComp spec α) :
    ∀ (s : σ) (c : QueryCache HashSpec), Inv s c →
      dropState <$> (simulateQ romImpl ((simulateQ implL oa).run s).run).run c =ᵈ
        (simulateQ romImpl (simulateQ implR oa).run).run c := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s c _
    simp [dropState]
  | query_bind q k ih =>
    intro s c hsc
    simp only [StateT.run_bind, WriterT.run_bind', simulateQ_bind,
      simulateQ_map, StateT.run_map, map_bind, simulateQ_spec_query]
    -- After the query, the rest of each run agrees, on every outcome of the stateful query.
    refine (OracleComp.EvalDistEq.bind_congr_of_support _ (g := fun a =>
      (fun p => (Prod.map id (fun x => a.1.2 ++ x) p.1, p.2)) <$>
        (simulateQ romImpl (simulateQ implR (k a.1.1.1)).run).run a.2) fun a ha => ?_).trans ?_
    · rw [Functor.map_map]
      -- Forgetting the state commutes with prefixing the log.
      have h := (ih a.1.1.1 _ _ (hinv q s c hsc a ha)).map
        (fun p : (α × List L) × QueryCache HashSpec => (Prod.map id (fun x => a.1.2 ++ x) p.1, p.2))
      rw [Functor.map_map] at h
      exact h
    · -- The query itself agrees once its state is forgotten.
      have h := (hstep q s c hsc).bind_left fun p =>
        (fun p' => (Prod.map id (fun x => p.1.2 ++ x) p'.1, p'.2)) <$>
          (simulateQ romImpl (simulateQ implR (k p.1.1)).run).run p.2
      rw [bind_map_left] at h
      exact h

end Coupling

/-! ## One signing request -/

section Request

variable {seed : Seed} {sk : SecretKey} {cache : QueryCache HashSpec}

/-- A signature with a key that the cache knows answers as the stateless signature.

The answer and the cache after it agree, once the updated key is forgotten. -/
theorem evalDistEq_signWith (h : KeyInv seed sk cache) (idx : LeafIndex) (msg : Message) :
    (fun x => (x.1.1, x.2)) <$>
        (simulateQ romImpl (liftM (signWith Hh sk idx msg) : OracleComp OracleWorld _)).run cache =ᵈ
      (simulateQ romImpl
        (liftM (statelessSignWith Hh seed idx msg) : OracleComp OracleWorld _)).run cache := by
  have he := ((erases_statelessSignWith_signWith h idx msg).lift_hash).evalDist_run cache le_rfl
  rw [XmssSecurity.Bridge.liftM_hash_map, simulateQ_map, StateT.run_map] at he
  exact he.symm

/-- A signature with a key that the cache knows returns a key that the cache after it knows. -/
theorem keyInv_of_mem_support_signWith (h : KeyInv seed sk cache) {idx : LeafIndex}
    {msg : Message} {x : (Except XmssError Signature × SecretKey) × QueryCache HashSpec}
    (hx : x ∈ support
      ((simulateQ romImpl (liftM (signWith Hh sk idx msg) : OracleComp OracleWorld _)).run cache)) :
    KeyInv seed x.1.2 x.2 := by
  rw [XmssSecurity.Bridge.lift_hash_romImpl] at hx
  have hres := resolves_of_run _ _ _ hx
  exact keyInv_signWith (h.mono (cache_le_of_run _ _ _ hx)) hres

/-- Key generation returns a key that the cache after it knows. -/
theorem keyInv_of_mem_support_keyGenWith {x : (PublicKey × SecretKey) × QueryCache HashSpec}
    (hx : x ∈ support
      ((simulateQ romImpl (liftM (keyGenWith Hh seed) : OracleComp OracleWorld _)).run cache)) :
    KeyInv seed x.1.2 x.2 := by
  rw [XmssSecurity.Bridge.lift_hash_romImpl] at hx
  exact keyInv_keyGenWith (resolves_of_run _ _ _ hx)

end Request

/-! ## The oracles of the game -/

/-- The game's oracles: coins and hashes pass through, and a request signs with the kept key. -/
abbrev keyedOracles : QueryImpl (OracleWorld + SigningSpec)
    (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) :=
  QueryImpl.ofLift OracleWorld
    (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) + signingOracle

/-- The oracles of the game with the stateless signer. -/
abbrev statelessOracles (seed : Seed) : QueryImpl (OracleWorld + SigningSpec)
    (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
    statelessSigningOracle seed

/-- A coin or hash query of the game passes through, and leaves the key as it is. -/
theorem run_keyedOracles_inl (t : OracleWorld.Domain) (sk : SecretKey) :
    ((keyedOracles (.inl t)).run sk).run =
      (fun u => ((u, sk), [])) <$> (liftM (OracleWorld.query t) : OracleComp OracleWorld _) := by
  simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
  rfl

/-- A coin or hash query of the stateless game passes through. -/
theorem run_statelessOracles_inl (seed : Seed) (t : OracleWorld.Domain) :
    (statelessOracles seed (.inl t)).run =
      (fun u => (u, [])) <$> (liftM (OracleWorld.query t) : OracleComp OracleWorld _) := by
  simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
  rfl

/-- A request of the game signs with the kept key, and logs the signature or its absence. -/
theorem run_keyedOracles_inr (request : SignRequest) (sk : SecretKey) :
    ((keyedOracles (.inr request)).run sk).run =
      (fun r => ((r.1.toOption, r.2), [⟨request, r.1.toOption⟩])) <$>
        (liftM (signWith H sk request.leafIndex request.message) : OracleComp OracleWorld _) :=
  rfl

/-- A request of the stateless game signs from the seed, and logs the same entry. -/
theorem run_statelessOracles_inr (seed : Seed) (request : SignRequest) :
    (statelessOracles seed (.inr request)).run =
      (fun r => (r.toOption, [⟨request, r.toOption⟩])) <$>
        (liftM (statelessSignWith H seed request.leafIndex request.message) :
          OracleComp OracleWorld _) := by
  simp only [QueryImpl.add_apply_inr, statelessSigningOracle, QueryImpl.run_withLogging_apply]
  rw [XmssSecurity.Bridge.liftM_hash_map, bind_map_left, map_eq_bind_pure_comp]
  rfl

section Oracles

variable {seed : Seed} {sk : SecretKey} {cache : QueryCache HashSpec}

/-- Each query answers alike in the two games, once the key is forgotten. -/
theorem keyedOracles_step (h : KeyInv seed sk cache) (q : (OracleWorld + SigningSpec).Domain) :
    dropState <$> (simulateQ romImpl ((keyedOracles q).run sk).run).run cache =ᵈ
      (simulateQ romImpl (statelessOracles seed q).run).run cache := by
  rcases q with t | request
  · rw [run_keyedOracles_inl, run_statelessOracles_inl, simulateQ_map, simulateQ_map,
      StateT.run_map, StateT.run_map, Functor.map_map]
    exact EvalDistEq.rfl
  · rw [run_keyedOracles_inr, run_statelessOracles_inr, simulateQ_map, simulateQ_map,
      StateT.run_map, StateT.run_map, Functor.map_map]
    have he := (evalDistEq_signWith h request.leafIndex request.message).map
      (Prod.map (fun r : Except XmssError Signature =>
        (r.toOption, ([⟨request, r.toOption⟩] : QueryLog SigningSpec))) id)
    rw [Functor.map_map] at he
    exact he

/-- Each query of the game returns a key that the cache after it knows. -/
theorem keyedOracles_inv (h : KeyInv seed sk cache) (q : (OracleWorld + SigningSpec).Domain) :
    ∀ x ∈ support ((simulateQ romImpl ((keyedOracles q).run sk).run).run cache),
      KeyInv seed x.1.1.2 x.2 := by
  intro x hx
  rcases q with t | request
  · rw [run_keyedOracles_inl, simulateQ_map, StateT.run_map, support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [simulateQ_spec_query] at hy
    exact h.mono (XmssSecurity.romImpl_query_cache_le _ _ _ hy)
  · rw [run_keyedOracles_inr, simulateQ_map, StateT.run_map, support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact keyInv_of_mem_support_signWith h hy

end Oracles

/-! ## The two games -/

/-- The stateless key generation is key generation, with the seed as the secret key. -/
theorem statelessKeyGenWith_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (H : ByteArray → m (Vector UInt8 32)) (seed : Seed) :
    statelessKeyGenWith H seed = (fun p => (seed, p.1)) <$> keyGenWith H seed := by
  unfold statelessKeyGenWith keyGenWith publicKeyOf node build
  simp only [← Merkle.value_build, map_bind, map_pure, bind_assoc, bind_map_left, pure_bind]

/-- A run of the adversary, then a continuation, agrees in the two simulations.

It holds from a cache that knows the key, when each query agrees and keeps the cache knowing it. -/
theorem evalDistEq_run_bind {ι : Type} {spec : OracleSpec ι} {L α β : Type} (seed : Seed)
    (implL : QueryImpl spec (StateT SecretKey (WriterT (List L) (OracleComp OracleWorld))))
    (implR : QueryImpl spec (WriterT (List L) (OracleComp OracleWorld)))
    (hstep : ∀ q sk c, KeyInv seed sk c →
      dropState <$> (simulateQ romImpl ((implL q).run sk).run).run c =ᵈ
        (simulateQ romImpl (implR q).run).run c)
    (hinv : ∀ q sk c, KeyInv seed sk c →
      ∀ x ∈ support ((simulateQ romImpl ((implL q).run sk).run).run c), KeyInv seed x.1.1.2 x.2)
    (oa : OracleComp spec α) (sk : SecretKey) (cache : QueryCache HashSpec)
    (h : KeyInv seed sk cache)
    (contL : (α × SecretKey) × List L → OracleComp OracleWorld β)
    (cont : α × List L → OracleComp OracleWorld β) (hcont : ∀ x, contL x = cont (x.1.1, x.2)) :
    (simulateQ romImpl (((simulateQ implL oa).run sk).run >>= contL)).run' cache =ᵈ
      (simulateQ romImpl ((simulateQ implR oa).run >>= cont)).run' cache := by
  rw [show contL = fun x => cont (x.1.1, x.2) from funext hcont]
  have hrun := evalDistEq_simulateQ_state (fun sk c => KeyInv seed sk c) implL implR hstep hinv
    oa sk cache h
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine EvalDistEq.trans ?_ (hrun.bind_left _)
  rw [bind_map_left]
  exact EvalDistEq.rfl

/-- After key generation, the game wins as the game with the stateless signer.

The cache after key generation knows the key, and the two runs agree from there. -/
theorem evalDistEq_rest (adversary : Adversary) (seed : Seed) (pk : PublicKey) (sk : SecretKey)
    (cache : QueryCache HashSpec) (h : KeyInv seed sk cache) {β : Type}
    (contL : (Forgery × SecretKey) × QueryLog SigningSpec → OracleComp OracleWorld β)
    (cont : Forgery × QueryLog SigningSpec → OracleComp OracleWorld β)
    (hcont : ∀ x, contL x = cont (x.1.1, x.2)) :
    (simulateQ romImpl (((simulateQ keyedOracles (adversary.main pk)).run sk).run >>=
        contL)).run' cache =ᵈ
      (simulateQ romImpl ((simulateQ (statelessOracles seed) (adversary.main pk)).run >>=
        cont)).run' cache :=
  evalDistEq_run_bind seed keyedOracles (statelessOracles seed)
    (fun q _ _ hs => keyedOracles_step hs q) (fun q _ _ hs => keyedOracles_inv hs q)
    (adversary.main pk) sk cache h contL cont hcont

/-- A run of a bind is the run of its first part, then of the rest from the cache after it. -/
theorem run'_romImpl_bind {α β : Type} (oa : OracleComp OracleWorld α)
    (f : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (oa >>= f)).run' cache =
      (simulateQ romImpl oa).run cache >>= fun z => (simulateQ romImpl (f z.1)).run' z.2 := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- The game's check of a forgery, once the adversary returned it with the log. -/
noncomputable def checkForgery (pk : PublicKey) (y : Forgery × QueryLog SigningSpec) :
    OracleComp OracleWorld Bool := do
  let verified ← liftM (verifyWith H pk y.1.message y.1.signature)
  return decide (Valid y.2 ∧ ¬Contains y.2 y.1) && verified

/-- The game, its seed drawn, with the keys of key generation. -/
noncomputable def keyedRun (adversary : Adversary) (seed : Seed) : OracleComp OracleWorld Bool :=
  (liftM (keyGenWith Hh seed) : OracleComp OracleWorld _) >>= fun p =>
    ((simulateQ keyedOracles (adversary.main p.1)).run p.2).run >>= fun x =>
      checkForgery p.1 (x.1.1, x.2)

/-- The game with the stateless signer, its seed drawn, with the keys of key generation. -/
noncomputable def statelessRun (adversary : Adversary) (seed : Seed) :
    OracleComp OracleWorld Bool :=
  (liftM (keyGenWith Hh seed) : OracleComp OracleWorld _) >>= fun p =>
    (simulateQ (statelessOracles seed) (adversary.main p.1)).run >>= checkForgery p.1

/-- The game draws a seed, then runs from that seed. -/
theorem gameCore_eq_bind (adversary : Adversary) :
    gameCore adversary = liftM sampleSeed >>= keyedRun adversary :=
  rfl

/-- The stateless game draws a seed, then runs from that seed. -/
theorem statelessGameCore_eq_bind (adversary : Adversary) :
    statelessGameCore adversary = liftM sampleSeed >>= statelessRun adversary := by
  unfold statelessGameCore statelessRun
  refine bind_congr fun seed => ?_
  rw [statelessKeyGenWith_eq, XmssSecurity.Bridge.liftM_hash_map, bind_map_left]
  rfl

/-- **The game wins as the game with the stateless signer, in distribution.** -/
theorem evalDistEq_gameCore (adversary : Adversary) :
    (simulateQ romImpl (gameCore adversary)).run' ∅ =ᵈ
      (simulateQ romImpl (statelessGameCore adversary)).run' ∅ := by
  rw [gameCore_eq_bind, statelessGameCore_eq_bind, XmssSecurity.Seeded.run'_lift_sample_bind,
    XmssSecurity.Seeded.run'_lift_sample_bind]
  refine EvalDistEq.bind_right _ fun seed => ?_
  unfold keyedRun statelessRun
  rw [run'_romImpl_bind, run'_romImpl_bind]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun b hb => ?_
  exact evalDistEq_rest adversary seed b.1.1 b.1.2 b.2 (keyInv_of_mem_support_keyGenWith hb) _ _
    fun _ => rfl

/-- **The adversary forges against the game's signer as often as against the stateless one.**

The two games give the same signatures, so the adversary wins each with the same probability. -/
theorem forgeAdvantage_eq_statelessForgeAdvantage (adversary : Adversary) :
    forgeAdvantage adversary = statelessForgeAdvantage adversary := by
  have hnew : forgeAdvantage adversary =
      Pr{let x ← (simulateQ romImpl (gameCore adversary)).run' ∅}[x = true] := by
    unfold forgeAdvantage experiment
    exact prEvent_countedOracle _ fun x : Bool => x = true
  have hold : statelessForgeAdvantage adversary =
      Pr{let x ← (simulateQ romImpl (statelessGameCore adversary)).run' ∅}[x = true] := by
    unfold statelessForgeAdvantage statelessExperiment
    exact prEvent_countedOracle _ fun x : Bool => x = true
  rw [hnew, hold]
  exact (evalDistEq_gameCore adversary).prEvent_eq _

/-- **leanXMSS as EthLib computes it is strongly unforgeable in the random oracle model.**

The signer keeps its key across requests, as a real signer does.

Take an adversary whose game with the stateless signer makes at most `q >= 1` hash calls.

It forges with probability at most `q / 2^127`.

`q` counts the calls of key generation and of every signing request too.

A signing request of the stateless signer can make more than `2^33` calls.

So `2^32` requests give `q > 2^65`, and over the key's lifetime the bound is above `2^-62`. -/
theorem unforgeable : HasClassicalSecurityBits 127 := fun q hq adversary hbound =>
  (forgeAdvantage_eq_statelessForgeAdvantage adversary).trans_le
    (statelessForgeAdvantage_le q hq adversary hbound)

end EthLib.Cryptography.Xmss.Unforgeability
