module

public import EthLib.Cryptography.Proofs.Merkle.RandomOracle
public import EthLib.Cryptography.Proofs.RandomOracleFromCache

/-!
# Proofs: a tight second-preimage bound for one Merkle tree

In the random oracle model, a forger sees the root and every honest path of a tree of height `h`.

It opens a leaf with a wrong value or path with probability at most `(Q + h) / N`.

Here `Q` counts its oracle calls, not its private randomness, and `N` is the number of digests.

Each oracle input carries its position, so a query can hit only the honest node there.

This is analogous to the tweaks of SPHINCS+ (Bernstein et al., CCS 2019, section 2).

<https://eprint.iacr.org/2019/1086>

The bound is tight: retrying random leaves with the honest path wins with probability about `Q / N`.

Limits: one tree, as the oracle input has no tree address; `T` trees give about `T * Q / N`.

The leaves are fixed values independent of the oracle, so leaf hashing is outside the model.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle.RandomOracle

open OracleComp OracleSpec ENNReal

variable {R : Type}

/-- Every input in the cache hashes the children that the cache replays at its position. -/
def HonestKeys (leaves : Nat → R) (c : (NodeInput R →ₒ R).QueryCache) : Prop :=
  ∀ (x : NodeInput R) (v : R), c x = some v →
    simulateQ c.toPartialImpl (node queryNode (fun j => pure (leaves j)) x.1.left) = some x.2.1 ∧
    simulateQ c.toPartialImpl (node queryNode (fun j => pure (leaves j)) x.1.right) = some x.2.2

/-- Building an honest node keeps every cached input honest. -/
theorem honestKeys_run_node [DecidableEq R] [SampleableType R] (leaves : Nat → R) :
    ∀ (level j : Nat) {c : (NodeInput R →ₒ R).QueryCache} {z : R × (NodeInput R →ₒ R).QueryCache},
      HonestKeys leaves c →
      z ∈ support ((simulateQ (NodeInput R →ₒ R).randomOracle
        (node.go queryNode (fun j => pure (leaves j)) level j)).run c) →
      HonestKeys leaves z.2 := by
  intro level
  induction level with
  | zero =>
    intro j c z hc hz
    simp only [node.go, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    exact hz ▸ hc
  | succ level ih =>
    intro j c z hc hz
    simp only [node.go, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨a, c₁⟩, h₁, ⟨b, c₂⟩, h₂, hz⟩ := hz
    have k₂ := ih (2 * j + 1) (ih (2 * j) hc h₁) h₂
    have r₁ := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
      uniformSampleImpl _ h₁
    have r₂ := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
      uniformSampleImpl _ h₂
    have l₂ := QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching uniformSampleImpl _ h₂
    have l₃ := QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching uniformSampleImpl _ hz
    -- A new input is the last call, which hashes the two children.
    simp only [queryNode, simulateQ_spec_query] at hz
    intro x v hx
    rcases (QueryImpl.withCaching_run_isSome_apply_iff _ hz x).1 (by simp [hx]) with hx₂ | rfl
    · obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp hx₂
      obtain ⟨hl, hr⟩ := k₂ x v₂ hv₂
      exact ⟨QueryCache.simulateQ_toPartialImpl_mono l₃ _ hl,
        QueryCache.simulateQ_toPartialImpl_mono l₃ _ hr⟩
    · exact ⟨QueryCache.simulateQ_toPartialImpl_mono (l₂.trans l₃) _ r₁,
        QueryCache.simulateQ_toPartialImpl_mono l₃ _ r₂⟩

/-- The second preimage found on a climb that the cache replays is in the cache. -/
theorem cached_of_findSecondPreimage [DecidableEq R] (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (hg : c.AgreesWithFn (QueryImpl.ofFn g))
    (leaves : Nat → Id R) :
    ∀ (t : List R) (p : Position) (b r : R) (w : SecondPreimage R),
      simulateQ c.toPartialImpl (climb queryNode p b t) = some r →
      findSecondPreimage (nodeHash g) leaves p b t = some w →
      c (w.position, w.y.1, w.y.2) = some (g (w.position, w.y.1, w.y.2)) := by
  intro t
  induction t with
  | nil => intro p b r w _ hw; simp [findSecondPreimage] at hw
  | cons v t ih =>
    intro p b r w hr hw
    simp only [climb, queryNode, simulateQ_bind, simulateQ_spec_query,
      QueryCache.toPartialImpl_apply] at hr
    obtain ⟨x, hx, hr⟩ := Option.bind_eq_some_iff.mp hr
    have hgx : g (p.parent, (ordered p b v).1, (ordered p b v).2) = x := hg hx
    rw [findSecondPreimage_cons] at hw
    dsimp only at hw
    split at hw
    · cases hw
      simpa [hgx] using hx
    · exact ih _ _ _ w hr (by simpa [nodeHash, hgx] using hw)

/-! ## The game and the bound -/

/-- The forger gets the root and the honest paths, then outputs a leaf index, a leaf and a path.

It wins when the index is below `2^h`, the opening differs, and the climb reaches the root. -/
def secondPreimageGame [DecidableEq R] (leaves : Nat → R) (h : Nat)
    (adversary : R → List (Vector R h) →
      OracleComp (unifSpec + (NodeInput R →ₒ R)) (Nat × R × Vector R h)) :
    OracleComp (unifSpec + (NodeInput R →ₒ R)) Bool := do
  let honestRoot ← liftComp (root queryNode (fun j => pure (leaves j)) h) _
  let honestPaths ← liftComp
    ((List.range (2 ^ h)).mapM (path queryNode (fun j => pure (leaves j)) h)) _
  let (j, b, t) ← adversary honestRoot honestPaths
  if j < 2 ^ h then
    let reached ← liftComp (climb queryNode ⟨0, j⟩ b t.toList) _
    let honestPath ← liftComp (path queryNode (fun j => pure (leaves j)) h j) _
    return decide (reached = honestRoot ∧ (b, t) ≠ (leaves j, honestPath))
  else return false

/-- Some input missing from `c₀` is answered in `c` by the node that `c₀` replays there. -/
def HitsHonest (leaves : Nat → R) (c₀ c : (NodeInput R →ₒ R).QueryCache) : Prop :=
  ∃ (x : NodeInput R) (a : R), c₀ x = none ∧
    simulateQ c₀.toPartialImpl (node queryNode (fun j => pure (leaves j)) x.1) = some a ∧
    c x = some a

/-- A fresh answer hits the honest node at its own position with probability at most `1 / N`. -/
theorem prEvent_hitsHonest_cacheQuery_le [DecidableEq R] [SampleableType R] (leaves : Nat → R)
    (c₀ c : (NodeInput R →ₒ R).QueryCache) (hc : ¬ HitsHonest leaves c₀ c) (t : NodeInput R) :
    Pr{let u ← $ᵗ R}[HitsHonest leaves c₀ (c.cacheQuery t u)] ≤ 1 / (Nat.card R : ℝ≥0∞) := by
  -- A new hit is the new input, answered by its honest node.
  have hsub : ∀ u : R, HitsHonest leaves c₀ (c.cacheQuery t u) →
      some u = simulateQ c₀.toPartialImpl (node queryNode (fun j => pure (leaves j)) t.1) := by
    rintro u ⟨x, a, hx₀, hxa, hx⟩
    by_cases hxt : x = t
    · subst x
      rw [hxa]
      simpa using hx
    · rw [QueryCache.cacheQuery_of_ne _ _ hxt] at hx
      exact (hc ⟨x, a, hx₀, hxa, hx⟩).elim
  refine (prEvent_mono _ _ _ hsub).trans ?_
  cases simulateQ c₀.toPartialImpl (node queryNode (fun j => pure (leaves j)) t.1) with
  | none => simp
  | some a => simp [SampleableType.prEvent_uniformSample_eq_singleton_natCard, one_div]

/-- A forger opens a leaf with a wrong value or path with probability at most `(Q + h) / N`.

For example, `Q = 2^64` and `h = 32` with 32-byte digests give about `2^(-192)`. -/
theorem prEvent_secondPreimageGame_le [DecidableEq R] [SampleableType R] (leaves : Nat → R)
    (h : Nat)
    (adversary : R → List (Vector R h) →
      OracleComp (unifSpec + (NodeInput R →ₒ R)) (Nat × R × Vector R h))
    {Q : Nat} (hQ : ∀ r P, IsQueryBoundP (adversary r P) (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).romImpl
      (secondPreimageGame leaves h adversary)).run ∅}[z.1 = true] ≤
        ((Q + h : Nat) : ℝ≥0∞) / Nat.card R := by
  classical
  -- Fix the honest tree's root `r` and cache `c₀`.
  rw [secondPreimageGame, simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ⟨r, c₀⟩ h₀ => ?_
  have h₀' : (r, c₀) ∈ support ((simulateQ (NodeInput R →ₒ R).randomOracle
      (node.go queryNode (fun j => pure (leaves j)) h 0)).run ∅) := by
    simp only [OracleSpec.romImpl, QueryImpl.simulateQ_add_liftComp_right] at h₀
    exact h₀
  have hroot := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    uniformSampleImpl _ h₀'
  have hkeys : HonestKeys leaves c₀ :=
    honestKeys_run_node leaves h 0 (fun x v hx => by simp at hx) h₀'
  have hfin : QueryCache.enncard c₀ ≠ ⊤ := by
    have hb : IsQueryBoundP (liftComp (root queryNode (fun j => pure (leaves j)) h)
        (unifSpec + (NodeInput R →ₒ R))) (fun t => t.isRight = true) (2 ^ h - 1) :=
      IsQueryBoundP.liftComp_subSpec (fun _ => iff_of_true trivial rfl)
        (node_queryBound leaves ⟨h, 0⟩).isQueryBoundP
    refine ne_top_of_le_ne_top ?_ (enncard_le_of_mem_support_run_romImpl hb h₀)
    simp
  dsimp only at hroot
  -- The root is the ancestor of each leaf `j < 2^h`.
  have hancestor : ∀ j < 2 ^ h, simulateQ c₀.toPartialImpl
      (node queryNode (fun j => pure (leaves j)) ((⟨0, j⟩ : Position).ancestor h)) = some r := by
    intro j hj
    rw [show (⟨0, j⟩ : Position).ancestor h = ⟨h, 0⟩ by
      simpa using Position.ancestor_eq_of_index_lt (p := ⟨0, j⟩) hj]
    exact hroot
  -- The honest paths are cached, so handing them out keeps `c₀`.
  obtain ⟨paths, hpaths₀⟩ := Option.isSome_iff_exists.mp
    (partial_mapM_isSome c₀ _ (List.range (2 ^ h)) fun j hj =>
      partial_siblings_isSome c₀ leaves h ⟨0, j⟩ (by rw [hancestor j (List.mem_range.mp hj)]; rfl))
  dsimp only
  rw [simulateQ_bind, StateT.run_bind]
  have hpaths : (simulateQ (NodeInput R →ₒ R).romImpl (liftComp ((List.range (2 ^ h)).mapM
      (path queryNode (fun j => pure (leaves j)) h)) (unifSpec + (NodeInput R →ₒ R)))).run c₀ =
        pure (paths, c₀) := by
    rw [OracleSpec.romImpl, QueryImpl.simulateQ_add_liftComp_right]
    exact run_randomOracle_of_partial _ hpaths₀
  rw [hpaths, pure_bind]
  -- After the tree, each of the at most `Q + h` fresh answers costs `1 / N`.
  dsimp only
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    ((prEvent_run_and_enncard_le_of_fresh_bound_from (HitsHonest leaves c₀) _
      (ENNReal.div_ne_top (by simp) (by exact_mod_cast (Nat.card_pos.ne' : Nat.card R ≠ 0)))
      (fun t c hc _ => prEvent_hitsHonest_cacheQuery_le leaves c₀ c hc t) _ (Q + h) c₀
      (fun ⟨_, _, hx₀, _, hx⟩ => by simp [hx₀] at hx) hfin).trans
      (le_of_eq (mul_one_div _ _)))
  -- A win ends with the bad event, after at most `Q + h` new entries.
  intro z hz hwin
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨⟨j, b, t⟩, c₁⟩, h₁, hz⟩ := hz
  dsimp only at hz
  by_cases hj : j < 2 ^ h
  swap
  · rw [ite_eq_right hj] at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    simp [hz] at hwin
  rw [ite_eq_left hj, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨reached, c₂⟩, h₂, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨honestPath, c₃⟩, h₃, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp only [decide_eq_true_eq] at hwin
  obtain ⟨hreach, hne⟩ := hwin
  dsimp only at h₃ ⊢
  have l₁ : c₀ ≤ c₁ :=
    le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl _ h₁
  have e₁ := enncard_le_of_mem_support_run_romImpl (hQ r paths) h₁
  have hcb : IsQueryBoundP (liftComp (climb queryNode ⟨0, j⟩ b t.toList)
      (unifSpec + (NodeInput R →ₒ R))) (fun t => t.isRight = true) h := by
    have := IsQueryBoundP.liftComp_subSpec (superSpec := unifSpec + (NodeInput R →ₒ R))
      (q := fun t => t.isRight = true) (fun _ => iff_of_true trivial rfl)
      (climb_queryBound t.toList ⟨0, j⟩ b).isQueryBoundP
    simpa using this
  have e₂ := enncard_le_of_mem_support_run_romImpl hcb h₂
  simp only [OracleSpec.romImpl, QueryImpl.simulateQ_add_liftComp_right] at h₂ h₃
  have l₂ : c₁ ≤ c₂ :=
    QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching uniformSampleImpl _ h₂
  have rclimb := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    uniformSampleImpl _ h₂
  have hroot' := hancestor j hj
  -- The honest path is cached, so `c₃ = c₂`.
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp
    (partial_siblings_isSome c₀ leaves h ⟨0, j⟩ (by rw [hroot']; rfl))
  have h₃' := run_randomOracle_of_partial _
    (QueryCache.simulateQ_toPartialImpl_mono (l₁.trans l₂) _ hP)
  change (honestPath, c₃) ∈ support ((simulateQ (NodeInput R →ₒ R).randomOracle
    (siblings queryNode (fun j => pure (leaves j)) ⟨0, j⟩ h)).run c₂) at h₃
  rw [h₃', support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h₃
  obtain ⟨rfl, rfl⟩ := h₃
  dsimp only at e₁ e₂ rclimb
  refine ⟨?_, ?_⟩
  swap
  · calc QueryCache.enncard c₃ ≤ QueryCache.enncard c₁ + h := e₂
      _ ≤ QueryCache.enncard c₀ + Q + h := by gcongr
      _ = _ := by push_cast; rw [add_assoc]
  -- Read the run through a complete table that agrees with `c₃`.
  obtain ⟨g, hg⟩ := c₃.exists_agreesWithFn
  have hg₃ : c₃.AgreesWithFn (QueryImpl.ofFn (fun x => g x)) := hg
  have hg₀ : c₀.AgreesWithFn (QueryImpl.ofFn (fun x => g x)) :=
    fun _ _ hx => hg ((l₁.trans l₂) hx)
  have hreached : reached = (climb (nodeHash fun x => g x) ⟨0, j⟩ b t.toList).run := by
    rw [← evalWithAnswerFn_climb]
    exact (c₃.evalWithAnswerFn_eq_of_agreesWithFn hg₃ _ rclimb).symm
  have hr : r = (node (nodeHash fun x => g x) (fun j => pure (leaves j))
      ((⟨0, j⟩ : Position).ancestor h)).run := by
    rw [← evalWithAnswerFn_node]
    exact (c₀.evalWithAnswerFn_eq_of_agreesWithFn hg₀ _ hroot').symm
  have hpath : honestPath = (siblings (nodeHash fun x => g x) (fun j => pure (leaves j))
      ⟨0, j⟩ h).run := by
    rw [← evalWithAnswerFn_siblings]
    exact (c₀.evalWithAnswerFn_eq_of_agreesWithFn hg₀ _ hP).symm
  -- The climb is honest, or the search finds a second preimage.
  rcases climb_binding_node (nodeHash fun x => g x) (fun j => pure (leaves j)) h ⟨0, j⟩ b
      t.toList (by simp) (by rw [← hreached, ← hr, hreach]) with ⟨hb, ht⟩ | hs
  · -- The honest opening does not win.
    exact (hne (by rw [hpath, ← Vector.toList_inj.mp ht, hb]; rfl)).elim
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨⟨-, hy, hval⟩, ⟨k, hk⟩, hlev⟩ :=
    findSecondPreimage_valid _ (fun j => pure (leaves j)) t.toList ⟨0, j⟩ b w hw
  -- The forged pair was queried by the climb.
  have hc₃ := cached_of_findSecondPreimage (fun x => g x) c₃ hg₃ _ t.toList ⟨0, j⟩ b reached w
    rclimb hw
  -- Its position is below the root, so `c₀` replays the honest node there.
  have hpos : w.position.ancestor (h - (k + 1)) = (⟨0, j⟩ : Position).ancestor h := by
    have hk' : k + 1 ≤ h := by simpa [hk] using hlev
    rw [hk, Position.ancestor_parent, Position.ancestor_ancestor]
    congr 1
    omega
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
    (partial_node_isSome_of_ancestor c₀ leaves _ w.position (by rw [hpos, hroot']; rfl))
  have ha' : a = g (w.position, w.y.1, w.y.2) := by
    rw [← c₀.evalWithAnswerFn_eq_of_agreesWithFn hg₀ _ ha, evalWithAnswerFn_node]
    exact hval.symm
  refine ⟨(w.position, w.y.1, w.y.2), a, ?_, ha, by rw [ha']; exact hc₃⟩
  -- The forged pair is not in `c₀`, whose inputs hash honest children.
  rcases hx : c₀ (w.position, w.y.1, w.y.2) with _ | v
  · rfl
  obtain ⟨hl, hr'⟩ := hkeys _ v hx
  refine (hy ?_).elim
  have e₁ := c₀.evalWithAnswerFn_eq_of_agreesWithFn hg₀ _ hl
  have e₂ := c₀.evalWithAnswerFn_eq_of_agreesWithFn hg₀ _ hr'
  rw [evalWithAnswerFn_node] at e₁ e₂
  exact Prod.ext e₁.symm e₂.symm

end EthLib.Cryptography.Merkle.RandomOracle
