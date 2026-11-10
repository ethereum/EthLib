module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Proofs: the unforgeability game of ECDSA

The source is [Fersch, Kiltz, Poettering](https://doi.org/10.1145/2976749.2978413).

The scheme is GenDSA, their Definition 6 and Figure 3; ECDSA is GenDSA by their §3.1.

The key `x g` signs a hash `h` with a nonce `k`.

The signature is `t = f(k g)` and `s = (h + x t) / k`, where `f` is the conversion.

The conversion is `ψ(Π(φ(R)))`:

- `φ` encodes a point, as its `x` coordinate.
- `Π` is a bijection, the identity of the integers below `2^L` in ECDSA.
- `ψ` maps the result to a scalar, by reduction mod `n`.

The model makes `Π` a uniform permutation, which the adversary evaluates in both directions.

That is the bijective random oracle of their §4.

They map `L`-bit strings to integers below `2^L`; both sets have `2^L` elements.

So `Π` here is a permutation of one set, which stands for both.

The game is existential unforgeability under chosen-message attacks, Game G0 of their Figure 4.

It differs from it in the ways that each definition below states.

Strong unforgeability fails when opposite points share their encoding, as `x` coordinates do.

Verification then accepts `(t, -s)` whenever it accepts `(t, s)`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal

variable {F G A M : Type}

/-- A GenDSA scheme: the base point, the parts of the conversion, the hash and the normal form. -/
structure Scheme (F G A M : Type) where
  /-- The base point.

  The source takes it of prime order and generating the group; theorems assume what they need. -/
  g : G
  /-- The encoding `φ` of a point, the first part of the conversion.

  The source defines it on nonzero points only.

  With a nonzero base point, no signature reads its value at `0`. -/
  encode : G → A
  /-- The map `ψ` onto the scalars, the last part of the conversion. -/
  reduce : A → F
  /-- The hash `H` of a message to a scalar, a public function and not an oracle.

  Their §2.3 draws a key for `H` before each experiment; here the scheme fixes `H`.

  A fixed compressing `H` has collisions, and a collision wins the game.

  So a bound on this game must charge collisions to a named search, such as the one below.

  A message is what `H` hashes, such as a transaction, not a 32-byte digest.

  If `H` only reduces a digest mod `n`, forging needs no signature.

  Pick `a` and `b`, and let `R = a g + b X` and `t = f(R)`.

  When `b`, `t` and `R` are nonzero, `(t, t / b)` is valid on every digest `a t / b` mod `n`. -/
  hash : M → F
  /-- The normal form of `s` in a signature, such as the low-s rule of EIP-2. -/
  normalize : F → F

/-- The encoding is semi-injective, by Definition 2 of the source.

Two nonzero points have one encoding only if they are equal or opposite.

The source also asks that the image be efficiently decidable, which a predicate cannot state. -/
def Scheme.SemiInjective (scheme : Scheme F G A M) [AddGroup G] : Prop :=
  ∀ X Y : G, X ≠ 0 → Y ≠ 0 → scheme.encode X = scheme.encode Y → Y = X ∨ Y = -X

/-- Two nonzero scalars whose multiples of a nonzero `g` share an encoding are equal or opposite.

It holds when the encoding is semi-injective. -/
theorem Scheme.eq_or_eq_neg_of_encode_smul_eq [Field F] [AddCommGroup G] [Module F G]
    {scheme : Scheme F G A M} (hsemi : scheme.SemiInjective) (hg : scheme.g ≠ 0) {a b : F}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : scheme.encode (b • scheme.g) = scheme.encode (a • scheme.g)) :
    b = a ∨ b = -a := by
  rcases hsemi _ _ (smul_ne_zero ha hg) (smul_ne_zero hb hg) h.symm with h' | h'
  · exact Or.inl (smul_left_injective F hg h')
  · exact Or.inr (smul_left_injective F hg (h'.trans (neg_smul a scheme.g).symm))

/-- Opposite points have the same encoding, as the `x` coordinate of a curve point does. -/
def Scheme.EncodeNeg (scheme : Scheme F G A M) [Neg G] : Prop :=
  ∀ X : G, scheme.encode (-X) = scheme.encode X

/-- The normal form keeps `s` or negates it. -/
def Scheme.NormalizeSign (scheme : Scheme F G A M) [Neg F] : Prop :=
  ∀ s : F, scheme.normalize s = s ∨ scheme.normalize s = -s

/-- The oracles of the adversary: uniform coins, `Π`, its inverse, and the signing oracle.

The signing oracle answers `none` when signing fails. -/
abbrev Spec (F A M : Type) :=
  unifSpec + ((A →ₒ A) + ((A →ₒ A) + (M →ₒ Option (F × F))))

/-- An adversary: from the public key, it returns a message and a claimed signature `(t, s)`. -/
structure Adversary (F G A M : Type) where
  /-- The adversary's run, with access to the oracles. -/
  main : G → OracleComp (Spec F A M) (M × F × F)

/-- The answers of the signing oracle so far, one per message, in the order of the requests. -/
abbrev Cache (F M : Type) := List (M × Option (F × F))

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The conversion `f = ψ ∘ Π ∘ φ`, with `Π` the permutation `π`. -/
def conversion (scheme : Scheme F G A M) (π : Equiv.Perm A) (R : G) : F :=
  scheme.reduce (π (scheme.encode R))

/-- The signature of `m` under the key `x` with the nonce `k`, by Figure 3 of the source.

It is `none` when `k`, `t` or `h + x t` is zero, where the source returns its failure symbol.

The key is secret. -/
def signNonce (scheme : Scheme F G A M) (π : Equiv.Perm A) (x : F) (m : M) (k : F) :
    Option (F × F) :=
  let t := conversion scheme π (k • scheme.g)
  let u := scheme.hash m + x * t
  if k = 0 ∨ t = 0 ∨ u = 0 then none else some (t, scheme.normalize (u / k))

/-- Whether `(t, s)` is a valid signature on `m` under the key `X`, by Figure 3 of the source.

`U = H(m) g + t X` must be nonzero, and the conversion of `U / s` must be `t`.

The key must be nonzero too, as SEC 1 v2 §3.2.2.1 asks. -/
def verify (scheme : Scheme F G A M) (π : Equiv.Perm A) (X : G) (m : M) (t s : F) : Bool :=
  let U := scheme.hash m • scheme.g + t • X
  decide (X ≠ 0 ∧ t ≠ 0 ∧ s ≠ 0 ∧ U ≠ 0 ∧ conversion scheme π (s⁻¹ • U) = t)

/-! ## Facts about verification -/

variable {scheme : Scheme F G A M} {π : Equiv.Perm A} {X : G} {m m' : M} {t s : F}

/-- Negating `s` keeps a signature valid, when opposite points share their encoding.

So strong unforgeability fails, and the game counts only messages never signed. -/
theorem verify_neg (hneg : scheme.EncodeNeg) :
    verify scheme π X m t (-s) = verify scheme π X m t s := by
  have hconv (R : G) : conversion scheme π (-R) = conversion scheme π R := by
    simp only [conversion, hneg R]
  simp only [verify, inv_neg, neg_smul, hconv, neg_ne_zero]

/-- Verification reads a message only through its hash.

So a collision of the hash turns a signature on one message into a forgery on another. -/
theorem verify_congr_hash (h : scheme.hash m = scheme.hash m') :
    verify scheme π X m t s = verify scheme π X m' t s := by
  simp only [verify, h]

/-- A signature from a nonce is valid under the key, when the key and the base point are nonzero.

The normal form must keep or negate `s`, and opposite points must share their encoding. -/
theorem verify_signNonce (hneg : scheme.EncodeNeg) (hnorm : scheme.NormalizeSign)
    (hg : scheme.g ≠ 0) {x k : F} (hx : x ≠ 0) (h : signNonce scheme π x m k = some (t, s)) :
    verify scheme π (x • scheme.g) m t s = true := by
  simp only [signNonce] at h
  split_ifs at h with h0
  simp only [not_or] at h0
  obtain ⟨hk, ht, hu⟩ := h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  set t := conversion scheme π (k • scheme.g) with ht_def
  set u := scheme.hash m + x * t with hu_def
  have hU : scheme.hash m • scheme.g + t • x • scheme.g = u • scheme.g := by
    rw [hu_def, smul_smul, add_smul, mul_comm]
  have hR : (u / k)⁻¹ • (u • scheme.g) = k • scheme.g := by
    rw [smul_smul, inv_div, div_mul_cancel₀ _ hu]
  simp only [verify, hU, decide_eq_true_eq]
  rcases hnorm (u / k) with hn | hn <;> rw [hn]
  · exact ⟨smul_ne_zero hx hg, ht, div_ne_zero hu hk, smul_ne_zero hu hg, by rw [hR]⟩
  · refine ⟨smul_ne_zero hx hg, ht, neg_ne_zero.mpr (div_ne_zero hu hk), smul_ne_zero hu hg, ?_⟩
    rw [inv_neg, neg_smul, hR, ht_def, conversion, conversion, hneg]

variable [SampleableType F]

/-- Signing with at most `fuel` uniform nonces: the first nonce that signs gives the signature.

It is `none` when every nonce fails. -/
def signFresh (scheme : Scheme F G A M) (π : Equiv.Perm A) (x : F) (m : M) :
    ℕ → ProbComp (Option (F × F))
  | 0 => pure none
  | fuel + 1 => do
    let k ← $ᵗ F
    match signNonce scheme π x m k with
    | some σ => pure (some σ)
    | none => signFresh scheme π x m fuel

/-- Every signature that signing returns is valid, when the key and the base point are nonzero.

The normal form must keep or negate `s`, and opposite points must share their encoding. -/
theorem verify_of_mem_support_signFresh (hneg : scheme.EncodeNeg)
    (hnorm : scheme.NormalizeSign) (hg : scheme.g ≠ 0) {x : F} (hx : x ≠ 0) {fuel : ℕ}
    (h : some (t, s) ∈ support (signFresh scheme π x m fuel)) :
    verify scheme π (x • scheme.g) m t s = true := by
  induction fuel with
  | zero => simp [signFresh] at h
  | succ n ih =>
    simp only [signFresh, support_bind, Set.mem_iUnion] at h
    obtain ⟨k, -, hk⟩ := h
    split at hk
    · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hk
      subst hk
      exact verify_signNonce hneg hnorm hg hx (by assumption)
    · exact ih hk

variable [DecidableEq M]

/-- Whether the signing oracle returned a signature on `m`. -/
def signed (cache : Cache F M) (m : M) : Bool :=
  match cache.lookup m with
  | some (some _) => true
  | _ => false

/-- The signing oracle under the key `x`.

A new message gets a fresh signature, and a repeated one the answer it got first.

[RFC 6979](https://www.rfc-editor.org/rfc/rfc6979#section-3.2) derives the nonces with HMAC_DRBG.

Its seed holds the private key and the hash.

The model draws them as a random function of the message instead.

That assumes the output of HMAC_DRBG seeded with the private key is pseudorandom.

No theorem proves it.

Two messages with one hash share one signature in RFC 6979, and get two independent ones here.

EthLib's signing tries 16 nonces.

It also fails when `x_R` is at least `n`, which the model leaves out.

An adversary of their Game G0 simulates this oracle with `fuel` times more signing queries.

No theorem states it. -/
def sign (scheme : Scheme F G A M) (fuel : ℕ) (π : Equiv.Perm A) (x : F) (m : M) :
    StateT (Cache F M) ProbComp (Option (F × F)) := fun cache =>
  match cache.lookup m with
  | some σ => pure (σ, cache)
  | none => (fun σ => (σ, cache ++ [(m, σ)])) <$> signFresh scheme π x m fuel

/-- The oracles of the game, with the permutation `π` and the key `x`.

Coins, `π` and its inverse leave the cache unchanged. -/
def impl (scheme : Scheme F G A M) (fuel : ℕ) (π : Equiv.Perm A) (x : F) :
    QueryImpl (Spec F A M) (StateT (Cache F M) ProbComp)
  | .inl n => fun cache => (·, cache) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl α) => (pure (π α) : StateT (Cache F M) ProbComp A)
  | .inr (.inr (.inl β)) => (pure (π.symm β) : StateT (Cache F M) ProbComp A)
  | .inr (.inr (.inr m)) => sign scheme fuel π x m

/-- A signed message other than `m` with the hash of `m`, if the cache holds one.

It is the collision that a forgery on a new message with an old hash exhibits. -/
def collisionOf (scheme : Scheme F G A M) (cache : Cache F M) (m : M) : Option M :=
  (cache.find? fun e =>
    decide (e.1 ≠ m) && e.2.isSome && decide (scheme.hash e.1 = scheme.hash m)).map Prod.fst

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType F] in
/-- A message that the search returns is a collision with `m`. -/
theorem collisionOf_valid {scheme : Scheme F G A M} {cache : Cache F M} {m m' : M}
    (h : collisionOf scheme cache m = some m') : m' ≠ m ∧ scheme.hash m' = scheme.hash m := by
  simp only [collisionOf, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have := List.find?_some he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.2⟩

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType F] in
/-- The empty cache holds no collision. -/
theorem collisionOf_nil (scheme : Scheme F G A M) (m : M) : collisionOf scheme [] m = none :=
  rfl

variable [FinEnum A]

/-- The game: draw `Π` and the key, run the adversary with its oracles, and check the forgery.

The message must have no signature from the oracle.

A failed request gives no signature, so its message stays fresh, as in Game G0 of Figure 4.

The key is uniform over all scalars, where the source's key generation avoids `0`.

The scalar `0` gives the key `0`, which verification rejects.

So the advantage here is the source's times `(n - 1) / n`, where `n` is the number of scalars.

No theorem states it. -/
def experiment (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp Bool := do
  let π ← $ᵗ (Equiv.Perm A)
  let x ← $ᵗ F
  let X := x • scheme.g
  let ((m, t, s), cache) ← (simulateQ (impl scheme fuel π x) (adversary.main X)).run []
  return !signed cache m && verify scheme π X m t s

/-- The probability that the adversary forges. -/
noncomputable def forgeAdvantage (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) : ℝ≥0∞ :=
  Pr{let b ← experiment scheme fuel adversary}[b = true]

/-! ## Two adversaries -/

/-- The adversary that asks for a signature on `m` and returns it with `s` negated.

Its signature is valid when signing succeeds and opposite points share their encoding.

But its message was signed, so it never wins. -/
def replayNeg (m : M) : Adversary F G A M where
  main _ := do
    match ← query (spec := Spec F A M) (.inr (.inr (.inr m))) with
    | some (t, s) => pure (m, t, -s)
    | none => pure (m, 0, 0)

/-- The adversary that asks for a signature on `m₁` and returns it as a signature on `m₂`.

It wins when the messages differ, their hashes collide and signing succeeds. -/
def collision (m₁ m₂ : M) : Adversary F G A M where
  main _ := do
    match ← query (spec := Spec F A M) (.inr (.inr (.inr m₁))) with
    | some (t, s) => pure (m₂, t, s)
    | none => pure (m₂, 0, 0)

/-- Replaying a signature with `s` negated never wins: the message was signed. -/
theorem forgeAdvantage_replayNeg (fuel : ℕ) (m : M) :
    forgeAdvantage scheme fuel (replayNeg m) = 0 := by
  unfold forgeAdvantage
  rw [prEvent_eq_zero_iff]
  rintro b hb rfl
  simp only [experiment, replayNeg, add_apply_inr, HasQuery.instOfMonadLift_query, simulateQ_bind,
    simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, impl, id_map,
    StateT.run_bind, bind_pure_comp, map_bind, MonadAttach.support_bind, support_uniformSample,
    Set.mem_univ, MonadAttach.mem_support, MonadAttach.support_map, Set.iUnion_true,
    Set.mem_iUnion, Set.mem_image, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Prod.exists, exists_prop] at hb
  obtain ⟨π, x, σ, c, h1, m', t, s, c', h2, hs, hv⟩ := hb
  simp only [StateT.run, sign, List.lookup_nil, List.nil_append,
    MonadAttach.canReturn_map_iff, Prod.mk.injEq, ↓existsAndEq, true_and] at h1
  obtain ⟨-, rfl⟩ := h1
  rcases σ with _ | ⟨t₀, s₀⟩
  · obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := by simpa using h2
    simp [verify] at hv
  · obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := by simpa using h2
    simp [signed] at hs

/-- A collision of the hash wins with positive probability.

The hypotheses ask for one permutation, one nonzero key and one nonce that sign `m₁`. -/
theorem forgeAdvantage_collision_pos (hneg : scheme.EncodeNeg) (hnorm : scheme.NormalizeSign)
    (hg : scheme.g ≠ 0) {fuel : ℕ} (hfuel : 0 < fuel) {m₁ m₂ : M} (hne : m₁ ≠ m₂)
    (hhash : scheme.hash m₁ = scheme.hash m₂)
    (hsign : ∃ (π : Equiv.Perm A) (x k : F), x ≠ 0 ∧ (signNonce scheme π x m₁ k).isSome) :
    0 < forgeAdvantage scheme fuel (collision m₁ m₂) := by
  obtain ⟨π, x, k, hx, hk⟩ := hsign
  obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨t, s⟩ := σ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfuel.ne'
  unfold forgeAdvantage
  rw [prEvent_pos_iff]
  refine ⟨true, ?_, rfl⟩
  simp only [experiment, Nat.succ_eq_add_one, collision, add_apply_inr,
    HasQuery.instOfMonadLift_query, simulateQ_bind,
    simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, impl, id_map,
    StateT.run_bind, bind_pure_comp, map_bind, MonadAttach.support_bind, support_uniformSample,
    Set.mem_univ, MonadAttach.mem_support, MonadAttach.support_map, Set.iUnion_true,
    Set.mem_iUnion, Set.mem_image, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Prod.exists, exists_prop]
  refine ⟨π, x, some (t, s), [(m₁, some (t, s))], ?_, m₂, t, s, [(m₁, some (t, s))], ?_, ?_, ?_⟩
  · simp only [StateT.run, sign, List.lookup_nil, List.nil_append, signFresh, map_bind,
      MonadAttach.canReturn_bind_iff, MonadAttach.canReturn_map_iff, Prod.mk.injEq,
      List.cons.injEq, true_and, and_true, and_self, exists_eq_right]
    exact ⟨k, mem_support_uniformSample (α := F), by simp [hσ]⟩
  · simp
  · simp [signed, List.lookup, beq_eq_false_iff_ne.mpr hne.symm]
  · rw [← verify_congr_hash hhash]
    exact verify_signNonce hneg hnorm hg hx hσ

end EthLib.Cryptography.Secp256k1.Security
