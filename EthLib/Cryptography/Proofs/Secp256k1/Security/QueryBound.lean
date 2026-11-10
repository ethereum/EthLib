module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.LazyGame

/-!
# Proofs: how often the ECDSA game asks for `Π`

The game as a program asks the permutation oracle for `Π`, in either direction.

Each query of the adversary to `Π` or its inverse asks once.

Each signing query on a new message asks at most once per nonce, so at most `fuel` times.

The final check asks at most once.

Take an adversary with `q_Π` queries to `Π` or its inverse and `q_S` signing queries.
So the game asks `Π` or its inverse at most `q_Π + fuel · q_S + 1` times.

The bounds are the framework's bounds on the queries of a program to some of its oracles.

The source is [Fersch, Kiltz, Poettering](https://doi.org/10.1145/2976749.2978413).

This is the `Q = Q_s + Q_Π` of their Theorem 1, §4.1, for the chosen-message game.

Their signer tries one nonce, so take `fuel = 1`.

Their Definition 4 assumes the forger asks the final check's query before it answers.

So their `Q_Π` includes that query, and it is at most `q_Π + 1`.

The count here is of queries, not of distinct pairs, so it may be one more than their `Q`.

A later step that swaps the permutation for independent answers in this game needs this count.

That step must count every new pair, also those of the signer and of the check.

The `Q` of their Theorem 2, §4.2, is another count.

It bounds the queries of the key-only forger, at most the `Q_Π` of Theorem 1, so `q_Π + 1`.

This theorem does not give it.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec LazyPermutation

variable {F G A M : Type}

/-- Whether a query of the adversary asks for `Π` or its inverse. -/
def isPermQuery : ℕ ⊕ A ⊕ A ⊕ M → Bool
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | _ => false

/-- Whether a query of the adversary asks for a signature. -/
def isSignQuery : ℕ ⊕ A ⊕ A ⊕ M → Bool
  | .inr (.inr (.inr _)) => true
  | _ => false

/-- Take a simulation where a query of a first kind costs at most one target query.

A query of a second kind costs at most `w` more, and every other query costs none.

Then `n` queries of the first kind and `k` of the second cost at most `n + w k`. -/
theorem isQueryBoundP_simulateQ_run_of_weighted_step {ι ι' σ α : Type}
    {spec : OracleSpec ι} {spec' : OracleSpec ι'} {p r : ι → Prop} [DecidablePred p]
    [DecidablePred r] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} {oa : OracleComp spec α}
    {n k w : ℕ} (hp : IsQueryBoundP oa p n) (hr : IsQueryBoundP oa r k)
    (hstep : ∀ t s, IsQueryBoundP ((impl t).run s) q
      ((if p t then 1 else 0) + (if r t then w else 0)))
    (s : σ) : IsQueryBoundP ((simulateQ impl oa).run s) q (n + w * k) :=
  IsQueryBound.simulateQ_run_of_step (hp.and_isQueryBound_pair hr)
    (combine := (· + ·)) (mapBudget := fun b : ℕ × ℕ => b.1 + w * b.2) (B := ℕ × ℕ) (B' := ℕ)
    (stepBudget := fun t _ => (if p t then 1 else 0) + (if r t then w else 0))
    (fun h h' => isQueryBoundP_bind h fun x _ => h' x)
    (fun t _ s _ => hstep t s)
    (fun t b hb => by
      obtain ⟨h1, h2⟩ := hb
      by_cases hpt : p t <;> by_cases hrt : r t <;> simp_all
      all_goals
        obtain ⟨b1, b2⟩ := b
        cases b2 <;> simp_all [Nat.mul_succ] <;> omega)
    s

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The conversion asks for `Π` at most once. -/
theorem isQueryBoundP_conversionQ (scheme : Scheme F G A M) (R : G) :
    IsQueryBoundP (conversionQ scheme R) (·.isRight = true) 1 := by
  rw [conversionQ, isQueryBoundP_map_iff]
  change IsQueryBoundP (liftM ((unifSpec + PermSpec A).query (.inr (.inl (scheme.encode R))))) _ 1
  rw [isQueryBoundP_query_iff]
  simp

omit [DecidableEq G] in
/-- The signature from a nonce asks for `Π` at most once. -/
theorem isQueryBoundP_signNonceQ (scheme : Scheme F G A M) (x : F) (m : M) (k : F) :
    IsQueryBoundP (signNonceQ scheme x m k) (·.isRight = true) 1 := by
  unfold signNonceQ
  split_ifs
  · simp
  · rw [isQueryBoundP_map_iff]
    exact isQueryBoundP_conversionQ scheme _

/-- The final check asks for `Π` at most once. -/
theorem isQueryBoundP_verifyQ (scheme : Scheme F G A M) (X : G) (m : M) (t s : F) :
    IsQueryBoundP (verifyQ scheme X m t s) (·.isRight = true) 1 := by
  unfold verifyQ
  dsimp only
  split_ifs
  · rw [isQueryBoundP_map_iff]
    exact isQueryBoundP_conversionQ scheme _
  · simp

variable [SampleableType F]

omit [DecidableEq G] in
/-- Signing with at most `fuel` nonces asks for `Π` at most `fuel` times. -/
theorem isQueryBoundP_signFreshQ (scheme : Scheme F G A M) (x : F) (m : M) (fuel : ℕ) :
    IsQueryBoundP (signFreshQ scheme x m fuel) (·.isRight = true) fuel := by
  induction fuel with
  | zero => simp [signFreshQ]
  | succ n ih =>
    simp only [signFreshQ]
    have h := isQueryBoundP_bind (isQueryBoundP_liftM_permComp ($ᵗ F)) fun k _ =>
      isQueryBoundP_bind (isQueryBoundP_signNonceQ scheme x m k) fun σ _ =>
        (show IsQueryBoundP (match σ with
          | some σ => pure (some σ)
          | none => signFreshQ scheme x m n) _ n by
          cases σ with
          | some σ => simp
          | none => exact ih)
    rw [show n + 1 = 0 + (1 + n) by omega]
    exact h

variable [DecidableEq M]

omit [DecidableEq G] in
/-- Each oracle of the game with the real signer asks for `Π` at most as often as its weight. -/
theorem isQueryBoundP_implQ_signQ (scheme : Scheme F G A M) (fuel : ℕ) (x : F)
    (t : (Spec F A M).Domain) (cache : Cache F M) :
    IsQueryBoundP ((implQ (signQ scheme fuel x) t).run cache) (·.isRight = true)
      ((if isPermQuery t = true then 1 else 0) + (if isSignQuery t = true then fuel else 0)) := by
  rcases t with n | α | β | m
  · simp [implQ, isPermQuery, isSignQuery, StateT.run]
  · simp [implQ, isPermQuery, isSignQuery, StateT.run]
  · simp [implQ, isPermQuery, isSignQuery, StateT.run]
  · simp only [implQ, isPermQuery, isSignQuery, Bool.false_eq_true, ite_false, ite_true,
      Nat.zero_add]
    change IsQueryBoundP (signQ scheme fuel x m cache) _ fuel
    unfold signQ
    cases cache.lookup m with
    | some σ => simp
    | none =>
      rw [isQueryBoundP_map_iff]
      exact isQueryBoundP_signFreshQ scheme x m fuel

/-- The game asks the permutation oracle, in either direction, at most `q_Π + fuel · q_S + 1` times.

The adversary asks for `Π` or its inverse at most `q_Π` times, on every key.

It asks for signatures at most `q_S` times, on every key. -/
theorem isQueryBoundP_experimentViewQ (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) {qPerm qSign : ℕ}
    (hPerm : ∀ X, IsQueryBoundP (adversary.main X) (isPermQuery · = true) qPerm)
    (hSign : ∀ X, IsQueryBoundP (adversary.main X) (isSignQuery · = true) qSign) :
    IsQueryBoundP (experimentViewQ scheme fuel adversary) (·.isRight = true)
      (qPerm + fuel * qSign + 1) := by
  have h := isQueryBoundP_bind (isQueryBoundP_liftM_permComp ($ᵗ F)) fun x _ =>
    isQueryBoundP_bind (n := qPerm + fuel * qSign) (m := 1)
      (isQueryBoundP_simulateQ_run_of_weighted_step (hPerm (x • scheme.g)) (hSign (x • scheme.g))
        (isQueryBoundP_implQ_signQ scheme fuel x) [])
      fun z _ => (show IsQueryBoundP (if signed z.2 z.1.1 then
          (pure (z.1, false, z.2) : PermComp A _) else
          ((z.1, ·, z.2)) <$> verifyQ scheme (x • scheme.g) z.1.1 z.1.2.1 z.1.2.2) _ 1 by
        split_ifs
        · simp
        · rw [isQueryBoundP_map_iff]
          exact isQueryBoundP_verifyQ scheme _ _ _ _)
  simpa [experimentViewQ, runCacheQ] using h

end EthLib.Cryptography.Secp256k1.Security
