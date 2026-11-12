module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.Programmed

/-!
# Proofs: the ECDSA game with a signer that has no key

In the game with `Π` programmed, the signer draws a nonce `k`, then the answer `β` at `φ(k g)`.

It returns `t = ψ(β)` and `s = (h + x t) / k`, so it reads the key `x`.

The signer here reads only the public key `X = x g`.

It draws a scalar `c`, and fails with no pair when `c` is `0`.

It draws `β` uniformly, sets `t = ψ(β)` and `U = h g + t X`.

It programs `Π` at `φ(R)` with the answer `β`, where `R` is `U / c`, or `c g` when `U` is `0`.

It returns `(t, c)`, in normal form, when `t` and `U` are nonzero, and fails otherwise.

It records the pair also when `t` or `U` is `0`.

With `X = x g`, the point `U` is `u g` for `u = h + x t`.

When `u` is nonzero, the nonce `k = u / c` gives `R = k g` and `s = c`.

The map from `c` to `u / c` is a bijection of the nonzero scalars, and it keeps `0`.

When `u` is `0`, the nonce `k = c` gives the same pair and the same failure.

So both signers have one law, and the two games have one law.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

This is the step from Game G2 to Game G3 of their Figure 5.

Their Game G3 records a pair only on success, at line 40, after the checks of lines 31, 34 and 36.

Their Game G2 records a pair at line 14, before the checks of lines 16 and 19.

So their claim that the forger wins as often in both games does not follow as written.

The pairs of failed nonces change the later answers of `Π`, and the later conflicts.

Their Game G3 also tests its query for a conflict at line 39, only after a success.

Their Game G2 tests it at line 11, before the test of `t`.

The signer here records the pairs of failed nonces too, and the two games have one law.

It draws `c` before `β`, and draws no `β` when `c` is `0`, as the signer with the key does.

The point `c g` for `U = 0` is not in the source, which forms no point then.

Both choices match the signer with the key, nonce for nonce.

The game here inherits the departures of the game with `Π` programmed from their Game G2.

Its signer tries up to `fuel` nonces, and its key is drawn from all scalars.

Their aborts at lines 29 and 39 are conflicts here, which do not stop the game.

It always checks the forgery.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type} [FinEnum A]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]

variable [SampleableType F]

/-- One nonce of the signer with no key, under the public key `X`.

It draws `c`, and fails with no pair when `c` is `0`.

Otherwise it draws `β` uniformly, and sets `t = ψ(β)` and `U = H(m) g + t X`.

It programs `Π` at `φ(R)` with `β`, where `R` is `U / c`, or `c g` when `U` is `0`.

It returns `(t, c)`, with `c` in normal form, when `t` and `U` are nonzero, and fails otherwise. -/
def keylessNonce (scheme : Scheme F G A M) (X : G) (m : M) :
    StateT (ProgrammedCache A) ProbComp (Option (F × F)) := fun cache => do
  let c ← $ᵗ F
  if c = 0 then pure (none, cache) else do
    let β ← uniformOutside [] (scheme.encode scheme.g)
    let t := scheme.reduce β
    let U := scheme.hash m • scheme.g + t • X
    let R := if U = 0 then c • scheme.g else c⁻¹ • U
    pure (if t = 0 ∨ U = 0 then none else some (t, scheme.normalize c),
      ((scheme.encode R, β), true) :: cache)

/-- The signer with no key: the first of at most `fuel` nonces that signs gives the signature.

It is `none` when every nonce fails. -/
def keylessSign (scheme : Scheme F G A M) (X : G) (m : M) :
    ℕ → StateT (ProgrammedCache A) ProbComp (Option (F × F))
  | 0 => pure none
  | fuel + 1 => do
    match ← keylessNonce scheme X m with
    | some σ => pure (some σ)
    | none => keylessSign scheme X m fuel

/-- The signer with no key over the state of the game: it writes the cache of `Π`.

It leaves the cache of the lazy permutation unchanged. -/
def keylessFresh (scheme : Scheme F G A M) (X : G) (fuel : ℕ) :
    FreshSigner F M (ProgrammedCache A × PermCache A) := fun m s =>
  (fun z => (z.1, (z.2, s.2))) <$> (keylessSign scheme X m fuel).run s.1

/-- The game with the signer that has no key, after Game G3 of the source.

It is the game with `Π` programmed, with the signer above in place of the one with the key.

So it departs from the source as that game does.

Its conflicts do not stop it, its signer tries up to `fuel` nonces, and it always checks.

Its key is drawn from all scalars, and its signer records the pairs of failed nonces. -/
def keylessExperiment (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp (((M × F × F) × Bool) × JointState F M (ProgrammedCache A × PermCache A)) := do
  let x ← $ᵗ F
  (simulateQ (jointImpl overlayLazyOracle (keylessFresh scheme (x • scheme.g) fuel))
    (runWithCheck scheme adversary (x • scheme.g))).run ([], ([], []))

omit [DecidableEq M] in
/-- One nonce of the signer with no key has the law of one nonce of the signer with the key.

The public key must be `x g`, and the base point nonzero. -/
private theorem keylessNonce_evalDistEq {scheme : Scheme F G A M} (hg : scheme.g ≠ 0) (x : F)
    (m : M) (c : ProgrammedCache A) (l : PermCache A) :
    (fun z => (z.1, (z.2, l))) <$> (keylessNonce scheme (x • scheme.g) m).run c =ᵈ
      (($ᵗ F : ProbComp F) >>= fun k =>
        (simulateQ programPermImpl (signNonceQ scheme x m k)).run (c, l)) := by
  let b₀ : ProbComp A := uniformOutside [] (scheme.encode scheme.g)
  let outR : F → A → Option (F × F) × (ProgrammedCache A × PermCache A) := fun k b =>
    if k = 0 then (none, (c, l)) else
      (if k = 0 ∨ scheme.reduce b = 0 ∨ scheme.hash m + x * scheme.reduce b = 0 then none
        else some (scheme.reduce b,
          scheme.normalize ((scheme.hash m + x * scheme.reduce b) / k)),
        (((scheme.encode (k • scheme.g), b), true) :: c, l))
  let outL : F → A → Option (F × F) × (ProgrammedCache A × PermCache A) := fun k b =>
    if k = 0 then (none, (c, l)) else
      (if scheme.reduce b = 0 ∨ scheme.hash m • scheme.g + scheme.reduce b • x • scheme.g = 0
        then none else some (scheme.reduce b, scheme.normalize k),
        (((scheme.encode (if scheme.hash m • scheme.g + scheme.reduce b • x • scheme.g = 0
            then k • scheme.g
            else k⁻¹ • (scheme.hash m • scheme.g + scheme.reduce b • x • scheme.g)), b), true)
          :: c, l))
  have hR : (($ᵗ F : ProbComp F) >>= fun k =>
      (simulateQ programPermImpl (signNonceQ scheme x m k)).run (c, l)) =ᵈ
        (($ᵗ F : ProbComp F) >>= fun k => b₀ >>= fun b => pure (outR k b)) := by
    refine EvalDistEq.bind_right _ fun k => ?_
    by_cases hk : k = 0
    · simp only [outR, hk, ite_true, signNonceQ, simulateQ_pure]
      exact (OracleComp.EvalDistEq.bind_const b₀ _).symm
    · rw [simulateQ_programPermImpl_signNonceQ_run scheme x m hk (c, l),
        uniformOutside_nil_eq _ (scheme.encode scheme.g)]
      refine EvalDistEq.of_eq ?_
      simp only [b₀, map_eq_bind_pure_comp]
      exact bind_congr fun b => by simp [outR, hk]
  have hL : (fun z => (z.1, (z.2, l))) <$> (keylessNonce scheme (x • scheme.g) m).run c =ᵈ
        (($ᵗ F : ProbComp F) >>= fun k => b₀ >>= fun b => pure (outL k b)) := by
    simp only [keylessNonce, StateT.run, map_bind]
    refine EvalDistEq.bind_right _ fun k => ?_
    by_cases hk : k = 0
    · simp only [outL, hk, ite_true, map_pure]
      exact (OracleComp.EvalDistEq.bind_const b₀ _).symm
    · simp only [hk, ite_false, map_bind, map_pure]
      exact EvalDistEq.of_eq (bind_congr fun b => by simp [outL, hk])
  have hb : ∀ b, (($ᵗ F : ProbComp F) >>= fun k => pure (outR k b)) =ᵈ
      (($ᵗ F : ProbComp F) >>= fun k => pure (outL k b)) := by
    intro b
    set u := scheme.hash m + x * scheme.reduce b with hu
    have hU : scheme.hash m • scheme.g + scheme.reduce b • x • scheme.g = u • scheme.g := by
      rw [smul_smul, hu, add_smul, mul_comm]
    have hU0 : u • scheme.g = 0 ↔ u = 0 := by simp [hg]
    let φ : F → F := fun k => if u = 0 then k else u / k
    have hφ : Function.Bijective φ := by
      refine Function.Involutive.bijective fun k => ?_
      by_cases h : u = 0
      · simp [φ, h]
      · simp [φ, h, div_div_cancel₀ h]
    have hkey : ∀ k, outR k b = outL (φ k) b := by
      intro k
      by_cases hk : k = 0
      · by_cases h : u = 0 <;> simp [outR, outL, φ, hk, h]
      by_cases h : u = 0
      · simp only [outR, outL, φ, ← hu, h, hk, hU, zero_smul, ite_true, ite_false, or_true]
      · have hk' : u / k ≠ 0 := div_ne_zero h hk
        have hR : (u / k)⁻¹ • u • scheme.g = k • scheme.g := by
          rw [smul_smul, inv_div, div_mul_cancel₀ _ h]
        simp only [outR, outL, φ, ← hu, h, hk, hk', hU, hU0, hR, ite_false, false_or, or_false]
    have h1 : (($ᵗ F : ProbComp F) >>= fun k => pure (outR k b)) =
        (fun k => outL k b) <$> (φ <$> ($ᵗ F : ProbComp F)) := by
      simp only [bind_pure_comp, Functor.map_map, hkey]
    rw [h1, bind_pure_comp]
    exact (SampleableType.map_uniformSample_evalDistEq_of_bijective hφ).map _
  refine hL.trans ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans
    ((EvalDistEq.bind_right _ fun b => (hb b).symm).trans
    (((OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans hR.symm))))

omit [DecidableEq M] in
/-- **The signer with no key has the law of the signer with the key.**

The public key must be `x g`, and the base point nonzero.

Then both signers have one law on their answer and on the state they leave. -/
theorem keylessFresh_run_evalDistEq_liftFresh {scheme : Scheme F G A M} (hg : scheme.g ≠ 0) (x : F)
    (fuel : ℕ) (m : M) (s : ProgrammedCache A × PermCache A) :
    (keylessFresh scheme (x • scheme.g) fuel m).run s =ᵈ
      (liftFresh programPermOracle (fun m => signFreshQ scheme x m fuel) m).run s := by
  obtain ⟨c, l⟩ := s
  induction fuel generalizing c l with
  | zero => exact EvalDistEq.of_eq rfl
  | succ n ih =>
    have hl : (keylessFresh scheme (x • scheme.g) (n + 1) m).run (c, l) =
        ((fun z => (z.1, (z.2, l))) <$> (keylessNonce scheme (x • scheme.g) m).run c) >>=
          fun z => match z.1 with
            | some σ => pure (some σ, z.2)
            | none => (keylessFresh scheme (x • scheme.g) n m).run z.2 := by
      change (fun z => (z.1, (z.2, l))) <$> (keylessSign scheme (x • scheme.g) m (n + 1)).run c = _
      simp only [keylessSign, StateT.run_bind, map_bind, bind_map_left]
      refine bind_congr fun z => ?_
      rcases z with ⟨_ | σ, c'⟩
      · rfl
      · simp
    have hr : (liftFresh programPermOracle (fun m => signFreshQ scheme x m (n + 1)) m).run (c, l) =
        (($ᵗ F : ProbComp F) >>= fun k =>
          (simulateQ programPermImpl (signNonceQ scheme x m k)).run (c, l)) >>=
          fun z => match z.1 with
            | some σ => pure (some σ, z.2)
            | none =>
              (liftFresh programPermOracle (fun m => signFreshQ scheme x m n) m).run z.2 := by
      change (simulateQ programPermImpl (signFreshQ scheme x m (n + 1))).run (c, l) = _
      rw [signFreshQ, simulateQ_bind, StateT.run_bind, simulateQ_passthrough_add_liftM_run,
        bind_map_left, bind_assoc]
      refine bind_congr fun k => ?_
      rw [simulateQ_bind, StateT.run_bind]
      refine bind_congr fun z => ?_
      rcases z with ⟨_ | σ, s'⟩
      · rfl
      · simp
    rw [hl, hr]
    refine EvalDistEq.bind_congr (keylessNonce_evalDistEq hg x m c l) fun z => ?_
    rcases z with ⟨_ | σ, c', l'⟩
    · exact ih c' l'
    · exact EvalDistEq.rfl

/-- **The game with the signer that has no key has the law of the game with `Π` programmed.**

The base point must be nonzero.

The forgery, the result of the check and the final states have one law in both games. -/
theorem keylessExperiment_evalDistEq_programmedExperiment {scheme : Scheme F G A M}
    (hg : scheme.g ≠ 0) (fuel : ℕ) (adversary : Adversary F G A M) :
    keylessExperiment scheme fuel adversary =ᵈ programmedExperiment scheme fuel adversary := by
  refine EvalDistEq.bind_right _ fun x => ?_
  refine evalDistEq_simulateQ_run _ _ (fun q s => ?_) _ _
  rcases q with n | α | β | m
  · exact EvalDistEq.rfl
  · exact EvalDistEq.rfl
  · exact EvalDistEq.rfl
  · obtain ⟨cache, ps⟩ := s
    dsimp only [jointImpl, StateT.run]
    split
    · exact EvalDistEq.rfl
    · exact (keylessFresh_run_evalDistEq_liftFresh hg x fuel m ps).map _

end EthLib.Cryptography.Secp256k1.Security
