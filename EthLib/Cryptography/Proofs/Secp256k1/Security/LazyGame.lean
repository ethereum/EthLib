module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.Game
public import EthLib.Cryptography.Proofs.LazyPermutation

/-!
# Proofs: the ECDSA game with the bijection sampled one answer at a time

The game draws the bijection `Π` up front, and its oracles and its final check read it.

Here they ask a permutation oracle for `Π` instead.

The game becomes a program of that oracle.

With `Π` drawn up front, that program is the game.

With `Π` sampled lazily, the program has the same distribution.

So the advantage of every adversary is the same in the lazy game.

The source is [Fersch, Kiltz, Poettering](https://doi.org/10.1145/2976749.2978413).

The bijection is their bijective random oracle, §4.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The conversion `f = ψ ∘ Π ∘ φ`, with `Π` asked of the oracle. -/
def conversionQ (scheme : Scheme F G A M) (R : G) : PermComp A F :=
  scheme.reduce <$> query (spec := unifSpec + PermSpec A) (.inr (.inl (scheme.encode R)))

/-- The signature of `m` under the key `x` with the nonce `k`, with `Π` asked of the oracle.

It asks for the conversion only of a nonzero nonce, so it asks for `Π` once or never.

The key is secret. -/
def signNonceQ (scheme : Scheme F G A M) (x : F) (m : M) (k : F) : PermComp A (Option (F × F)) :=
  if k = 0 then pure none else
  -- The test of `k` repeats the guard, so that the term matches the game's signature.
  (fun t =>
    let u := scheme.hash m + x * t
    if k = 0 ∨ t = 0 ∨ u = 0 then none else some (t, scheme.normalize (u / k))) <$>
    conversionQ scheme (k • scheme.g)

/-- Whether `(t, s)` is a valid signature on `m` under the key `X`, with `Π` asked of the oracle.

It asks for the conversion only when the key, `t`, `s` and `U` are nonzero.

So it asks for `Π` once or never. -/
def verifyQ (scheme : Scheme F G A M) (X : G) (m : M) (t s : F) : PermComp A Bool :=
  let U := scheme.hash m • scheme.g + t • X
  if X ≠ 0 ∧ t ≠ 0 ∧ s ≠ 0 ∧ U ≠ 0 then
    (fun c => decide (c = t)) <$> conversionQ scheme (s⁻¹ • U)
  else pure false

variable [SampleableType F]

/-- Signing with at most `fuel` uniform nonces, with `Π` asked of the oracle. -/
def signFreshQ (scheme : Scheme F G A M) (x : F) (m : M) : ℕ → PermComp A (Option (F × F))
  | 0 => pure none
  | fuel + 1 => do
    let k ← ($ᵗ F : ProbComp F)
    match ← signNonceQ scheme x m k with
    | some σ => pure (some σ)
    | none => signFreshQ scheme x m fuel

variable [DecidableEq M]

/-- The signing oracle under the key `x`, with `Π` asked of the oracle.

A new message asks for `Π` at most `fuel` times, once per nonzero nonce tried.

The signer does not return the answers for nonces that fail.

A repeated message asks for nothing. -/
def signQ (scheme : Scheme F G A M) (fuel : ℕ) (x : F) (m : M) :
    StateT (Cache F M) (PermComp A) (Option (F × F)) := fun cache =>
  match cache.lookup m with
  | some σ => pure (σ, cache)
  | none => (fun σ => (σ, cache ++ [(m, σ)])) <$> signFreshQ scheme x m fuel

/-- A signing oracle that may ask the permutation oracle, with the cache of its answers. -/
abbrev SignerQ (F A M : Type) := M → StateT (Cache F M) (PermComp A) (Option (F × F))

/-- The oracles of the game with a signing oracle, as a program of the permutation oracle.

Coins, `Π` and its inverse pass to that oracle. -/
def implQ (signer : SignerQ F A M) : QueryImpl (Spec F A M) (StateT (Cache F M) (PermComp A))
  | .inl n => fun cache =>
    (·, cache) <$> query (spec := unifSpec + PermSpec A) (.inl n)
  | .inr (.inl α) => fun cache =>
    (·, cache) <$> query (spec := unifSpec + PermSpec A) (.inr (.inl α))
  | .inr (.inr (.inl β)) => fun cache =>
    (·, cache) <$> query (spec := unifSpec + PermSpec A) (.inr (.inr β))
  | .inr (.inr (.inr m)) => signer m

/-- Run the adversary on the key `X` with a signing oracle, and check its forgery.

The check asks for `Π` itself, once or never, after the adversary's queries.

It asks nothing when the message was signed, since the forgery then loses.

It keeps the forgery, the result and the final signing cache. -/
def runCacheQ (scheme : Scheme F G A M) (adversary : Adversary F G A M) (X : G)
    (signer : SignerQ F A M) : PermComp A ((M × F × F) × Bool × Cache F M) := do
  let ((m, t, s), cache) ← (simulateQ (implQ signer) (adversary.main X)).run []
  if signed cache m then return ((m, t, s), false, cache) else
    (((m, t, s), ·, cache)) <$> verifyQ scheme X m t s

/-- Run the adversary on the key `X` with a signing oracle, and keep the result of the check. -/
def runQ (scheme : Scheme F G A M) (adversary : Adversary F G A M) (X : G)
    (signer : SignerQ F A M) : PermComp A Bool :=
  (fun z => z.2.1) <$> runCacheQ scheme adversary X signer

/-- The game as a program of the permutation oracle, keeping the forgery and the signing cache.

It draws the key, runs, and checks the forgery. -/
def experimentViewQ (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    PermComp A ((M × F × F) × Bool × Cache F M) := do
  let x ← ($ᵗ F : ProbComp F)
  runCacheQ scheme adversary (x • scheme.g) (signQ scheme fuel x)

/-- The game, as a program of the permutation oracle, keeping the result. -/
def experimentQ (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    PermComp A Bool :=
  (fun z => z.2.1) <$> experimentViewQ scheme fuel adversary

variable [FinEnum A]

/-- The game, keeping the forgery, the result, the final signing cache and the permutation `Π`. -/
def experimentView (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp ((M × F × F) × Bool × Cache F M × Equiv.Perm A) := do
  let π ← $ᵗ (Equiv.Perm A)
  let x ← $ᵗ F
  let X := x • scheme.g
  let ((m, t, s), cache) ← (simulateQ (impl scheme fuel π x) (adversary.main X)).run []
  return ((m, t, s), !signed cache m && verify scheme π X m t s, cache, π)

/-- Keep only the result of the game with its forgery, signing cache and `Π`, and it is the game. -/
theorem result_map_experimentView (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    (fun z => z.2.1) <$> experimentView scheme fuel adversary =
      experiment scheme fuel adversary := by
  simp [experimentView, experiment]

/-- The game with `Π` sampled one answer at a time. -/
def lazyExperiment (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp Bool :=
  (simulateQ lazyPermImpl (experimentQ scheme fuel adversary)).run' []

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType F]
  [DecidableEq M] [FinEnum A] in
/-- With `π`, the conversion asked of the oracle is the conversion by `π`. -/
private theorem simulateQ_permImpl_conversionQ (scheme : Scheme F G A M) (π : Equiv.Perm A)
    (R : G) : simulateQ (permImpl π) (conversionQ scheme R) = pure (conversion scheme π R) := by
  simp [conversionQ, conversion, permImpl, permOracle]

omit [DecidableEq G] [SampleableType F] [DecidableEq M] [FinEnum A] in
/-- With `π`, the signature from a nonce asked of the oracle is the signature by `π`. -/
private theorem simulateQ_permImpl_signNonceQ (scheme : Scheme F G A M) (π : Equiv.Perm A)
    (x : F) (m : M) (k : F) :
    simulateQ (permImpl π) (signNonceQ scheme x m k) = pure (signNonce scheme π x m k) := by
  unfold signNonceQ
  split_ifs with hk
  · simp [signNonce, hk]
  · rw [simulateQ_map, simulateQ_permImpl_conversionQ, map_pure]
    rfl

omit [SampleableType F] [DecidableEq M] [FinEnum A] in
/-- With `π`, verification asked of the oracle is verification by `π`. -/
private theorem simulateQ_permImpl_verifyQ (scheme : Scheme F G A M) (π : Equiv.Perm A)
    (X : G) (m : M) (t s : F) :
    simulateQ (permImpl π) (verifyQ scheme X m t s) = pure (verify scheme π X m t s) := by
  unfold verifyQ
  dsimp only
  by_cases h : X ≠ 0 ∧ t ≠ 0 ∧ s ≠ 0 ∧ scheme.hash m • scheme.g + t • X ≠ 0
  · rw [ite_eq_left h, simulateQ_map, simulateQ_permImpl_conversionQ, map_pure]
    simp [verify, h]
  · rw [ite_eq_right h, simulateQ_pure]
    simp only [verify]
    congr 1
    simp only [eq_comm (a := false), decide_eq_false_iff_not]
    tauto

omit [DecidableEq G] [DecidableEq M] [FinEnum A] in
/-- With `π`, signing with fresh nonces asked of the oracle is signing by `π`. -/
private theorem simulateQ_permImpl_signFreshQ (scheme : Scheme F G A M) (π : Equiv.Perm A)
    (x : F) (m : M) (fuel : ℕ) :
    simulateQ (permImpl π) (signFreshQ scheme x m fuel) = signFresh scheme π x m fuel := by
  induction fuel with
  | zero => simp [signFreshQ, signFresh]
  | succ n ih =>
    simp only [signFreshQ, signFresh, simulateQ_bind, simulateQ_permImpl_liftM,
      simulateQ_permImpl_signNonceQ, pure_bind]
    refine bind_congr fun k => ?_
    cases signNonce scheme π x m k with
    | some σ => simp
    | none => exact ih

omit [DecidableEq G] [FinEnum A] in
/-- With `π`, each oracle of the program answers as the oracle of the game. -/
private theorem simulateQ_permImpl_implQ (scheme : Scheme F G A M) (fuel : ℕ)
    (π : Equiv.Perm A) (x : F) (q : (Spec F A M).Domain) (cache : Cache F M) :
    simulateQ (permImpl π) ((implQ (signQ scheme fuel x) q).run cache) =
      (impl scheme fuel π x q).run cache := by
  rcases q with n | α | β | m
  · simp [implQ, impl, StateT.run, permImpl]
  · simp [implQ, impl, StateT.run, permImpl, permOracle]
    rfl
  · simp [implQ, impl, StateT.run, permImpl, permOracle]
    rfl
  · simp only [implQ, impl, signQ, sign, StateT.run]
    cases cache.lookup m with
    | some σ => simp
    | none => simp only [simulateQ_map, simulateQ_permImpl_signFreshQ]

/-- Draw `Π` up front and give it to the oracle.

Then the program with the forgery and the signing cache is the game with them. -/
theorem experimentView_eq_permImpl (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    experimentView scheme fuel adversary =
      (do
        let π ← $ᵗ (Equiv.Perm A)
        let z ← simulateQ (permImpl π) (experimentViewQ scheme fuel adversary)
        pure (z.1, z.2.1, z.2.2, π)) := by
  simp only [experimentView, experimentViewQ, simulateQ_bind, simulateQ_permImpl_liftM, bind_assoc]
  refine bind_congr fun π => bind_congr fun x => ?_
  simp only [runCacheQ, simulateQ_bind, bind_assoc]
  rw [simulateQ_StateT_compose (implQ (signQ scheme fuel x)) (permImpl π) (impl scheme fuel π x)
    (simulateQ_permImpl_implQ scheme fuel π x)]
  refine bind_congr fun z => ?_
  obtain ⟨⟨m, t, s⟩, cache⟩ := z
  by_cases h : signed cache m
  · simp [h]
  · simp only [h, Bool.false_eq_true, ite_false, simulateQ_map,
      simulateQ_permImpl_verifyQ scheme π (x • scheme.g) m t s]
    simp

/-- With `Π` drawn up front and given to the oracle, the program is the game. -/
theorem experiment_evalDistEq_permImpl (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    experiment scheme fuel adversary =ᵈ
      (do
        let π ← $ᵗ (Equiv.Perm A)
        simulateQ (permImpl π) (experimentQ scheme fuel adversary)) := by
  refine EvalDistEq.of_eq ?_
  rw [← result_map_experimentView, experimentView_eq_permImpl]
  simp [experimentQ, simulateQ_map]

/-- The game with `Π` sampled lazily has the same distribution as the game. -/
theorem experiment_evalDistEq_lazyExperiment (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    experiment scheme fuel adversary =ᵈ lazyExperiment scheme fuel adversary :=
  (experiment_evalDistEq_permImpl scheme fuel adversary).trans
    (uniformSample_bind_simulateQ_permImpl_evalDistEq _)

/-- The advantage of every adversary is its chance to win the lazy game. -/
theorem forgeAdvantage_eq_lazyExperiment (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    forgeAdvantage scheme fuel adversary =
      Pr{let b ← lazyExperiment scheme fuel adversary}[b = true] :=
  (experiment_evalDistEq_lazyExperiment scheme fuel adversary).prEvent_eq _

end EthLib.Cryptography.Secp256k1.Security
