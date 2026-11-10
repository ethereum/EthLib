module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.JointGame
public import EthLib.Cryptography.Proofs.TaggedLazyPermutation

/-!
# Proofs: where the pair of a forgery entered the cache of `Π`

The joint game runs the adversary, the signer and the final check against one cache of `Π`.

Here each pair of that cache carries its origin.

The adversary's forward queries tag theirs `forward`, and its inverse queries `inverse`.

The final check asks `Π` as the adversary does, so a new pair of the check is tagged `forward`.

The signer's queries tag theirs `signing`.

Erase the tags, and the game is the joint lazy game.

A forgery that wins has its pair in the final cache.

That pair is `(φ(R), β)`, with `R` the point of the forgery and `ψ(β)` its `t`.

If the final check is the first to ask for `φ(R)`, the pair is tagged `forward`.

Otherwise it keeps the tag it had before the check.

No theorem yet ties that earlier tag to the call that set it.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The proof of their Theorem 1, §4.1, splits on whether that pair is in the list `Π_S`.

That is line 27 of their Figure 6.

The proof of their Theorem 2, §4.2, splits on a forward or an inverse query, line 12 of Figure 7.

Their Definition 4 assumes that the forger asked every query its verification needs.

Their §4.2 reads this as a forward query at `φ(R)`, or an inverse query that returned `φ(R)`.

Here the check asks for `φ(R)` instead, and that query would count as one more forward query.

The tag `signing` is coarser than `Π_S`.

The real signer asks `Π` once per nonzero nonce it tries.

A failed nonce leaves a pair with no signature.

The simulated signer of their Game G3, Figure 5, sets only the pairs of its signatures.

So the step to that signer needs an argument for those other pairs.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec LazyPermutation

variable {F G A M τ : Type}

/-- How a pair of the cache of `Π` entered it. -/
inductive Origin where
  /-- A new pair from a forward query of the adversary, or from the query of the final check. -/
  | forward
  /-- A new pair from an inverse query of the adversary. -/
  | inverse
  /-- A new pair from a query of the signing oracle, for any nonce it tries. -/
  | signing
  deriving DecidableEq

variable [DecidableEq M] [FinEnum A]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The joint run over tagged caches, with the tags erased, is the joint run over the lazy
permutation.

The tags of the adversary and of the signer may differ. -/
theorem map_jointRun_taggedLazyPermOracle (scheme : Scheme F G A M)
    (adversary : Adversary F G A M) (X : G) (fA iA fS iS : τ) (init : TaggedCache A τ)
    (fresh : M → PermComp A (Option (F × F))) :
    Prod.map id TaggedCache.untag <$>
        jointRun scheme adversary X (taggedLazyPermOracle fA iA) init
          (liftFresh (taggedLazyPermOracle fS iS) fresh) =
      jointRun scheme adversary X lazyPermOracle init.untag (liftFresh lazyPermOracle fresh) :=
  map_jointRun_of_proj scheme adversary X _ _ init _ _ TaggedCache.untag
    (map_run_taggedLazyPermOracle fA iA)
    (map_run_liftFresh_of_proj _ _ TaggedCache.untag (map_run_taggedLazyPermOracle fS iS) fresh)

omit [DecidableEq M] in
/-- A check that accepts leaves the pair of the forgery in the tagged cache.

The pair is `(φ(R), β)`, where `R = (H(m) g + t X) / s` and `ψ(β) = t`.

Its tag is the one that `φ(R)` had before the check, or `fA` if the check asked it first. -/
theorem lookup_of_mem_support_verifyQ_taggedLazyPermOracle (scheme : Scheme F G A M) (fA iA : τ)
    {X : G} {m : M} {t s : F} {c c' : TaggedCache A τ}
    (h : (true, c') ∈ support ((simulateQ (unifSpec.passthrough + taggedLazyPermOracle fA iA)
      (verifyQ scheme X m t s)).run c)) :
    ∃ β, c'.lookupTagged (scheme.encode (s⁻¹ • (scheme.hash m • scheme.g + t • X))) =
      some (β, ((c.lookupTagged (scheme.encode (s⁻¹ • (scheme.hash m • scheme.g + t • X)))).map
        Prod.snd).getD fA) ∧ scheme.reduce β = t := by
  unfold verifyQ at h
  dsimp only at h
  split_ifs at h with hg
  · simp only [conversionQ, simulateQ_map, Functor.map_map, StateT.run_map,
      support_map, Set.mem_image, Prod.mk.injEq] at h
    obtain ⟨⟨b, c₁⟩, hb, hdec, rfl⟩ := h
    have ho := lookup_of_mem_support_taggedLazyPermOracle_forward fA iA
      (by
        rw [MonadAttach.mem_support]
        simpa [HasQuery.instOfMonadLift_query, simulateQ_query, add_apply_inr] using hb)
    exact ⟨b, ho, by simpa using hdec⟩
  · simp at h

/-- A forgery that wins the joint run over a tagged cache has its pair in the final cache.

The pair is `(φ(R), β)`, where `R = (H(m) g + t X) / s` and `ψ(β) = t`.

The adversary's run ends with the cache `c₀`, a suffix of the final one, and leaves `m` unsigned.

The tag of the pair is the one that `φ(R)` had in `c₀`, or `fA` if the check asked it first.

This holds for any signer of new messages. -/
theorem lookup_of_mem_support_jointRun_taggedLazyPermOracle (scheme : Scheme F G A M)
    (adversary : Adversary F G A M) {X : G} (fA iA : τ) {init : TaggedCache A τ}
    {fresh : FreshSigner F M (TaggedCache A τ)} {m : M} {t s : F} {cache : Cache F M}
    {c : TaggedCache A τ}
    (h : (((m, t, s), true, cache), c) ∈
      support (jointRun scheme adversary X (taggedLazyPermOracle fA iA) init fresh)) :
    ∃ (c₀ : TaggedCache A τ) (β : A),
      ((m, t, s), (cache, c₀)) ∈ support ((simulateQ (jointImpl (taggedLazyPermOracle fA iA)
        fresh) (adversary.main X)).run ([], init)) ∧ signed cache m = false ∧ c₀ <:+ c ∧
      c.lookupTagged (scheme.encode (s⁻¹ • (scheme.hash m • scheme.g + t • X))) =
        some (β, ((c₀.lookupTagged (scheme.encode (s⁻¹ • (scheme.hash m • scheme.g + t • X)))).map
          Prod.snd).getD fA) ∧ scheme.reduce β = t := by
  simp only [jointRun, support_bind, Set.mem_iUnion] at h
  obtain ⟨⟨⟨m', t', s'⟩, cache', c₁⟩, hrun, h⟩ := h
  by_cases hs : signed cache' m'
  · simp [hs] at h
  · simp only [hs, Bool.false_eq_true, ite_false, support_map, Set.mem_image,
      Prod.mk.injEq] at h
    obtain ⟨⟨b, c₂⟩, hb, ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩, rfl⟩ := h
    obtain ⟨β, hβ⟩ := lookup_of_mem_support_verifyQ_taggedLazyPermOracle scheme fA iA hb
    exact ⟨c₁, β, hrun, by simpa using hs,
      suffix_of_mem_support_simulateQ_taggedLazyPermOracle fA iA _ c₁ _ hb, hβ⟩

variable [SampleableType F]

/-- The joint lazy game with each pair of the cache of `Π` tagged by its origin.

The adversary tags its pairs `forward` or `inverse`, and the final check `forward`.

The signer tags its pairs `signing`. -/
def taggedJointExperiment (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp (((M × F × F) × Bool × Cache F M) × TaggedCache A Origin) := do
  let x ← $ᵗ F
  jointRun scheme adversary (x • scheme.g) (taggedLazyPermOracle .forward .inverse) []
    (liftFresh (taggedLazyPermOracle .signing .signing) fun m => signFreshQ scheme x m fuel)

/-- Erase the tags of the tagged joint game, and it is the joint lazy game. -/
theorem map_taggedJointExperiment (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    Prod.map id TaggedCache.untag <$> taggedJointExperiment scheme fuel adversary =
      jointExperiment scheme fuel adversary := by
  simp only [taggedJointExperiment, jointExperiment, map_bind]
  exact bind_congr fun x => map_jointRun_taggedLazyPermOracle scheme adversary _ _ _ _ _ [] _

/-- A run of the tagged joint game is a tagged joint run on the key `x g`, for a key `x`.

The signer of that run signs with the same `x`. -/
theorem mem_support_taggedJointExperiment_iff (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) {z : ((M × F × F) × Bool × Cache F M) × TaggedCache A Origin} :
    z ∈ support (taggedJointExperiment scheme fuel adversary) ↔
      ∃ x : F, z ∈ support (jointRun scheme adversary (x • scheme.g)
        (taggedLazyPermOracle .forward .inverse) []
        (liftFresh (taggedLazyPermOracle .signing .signing)
          fun m => signFreshQ scheme x m fuel)) := by
  simp [taggedJointExperiment]

end EthLib.Cryptography.Secp256k1.Security
