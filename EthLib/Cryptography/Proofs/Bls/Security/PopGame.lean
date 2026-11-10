module

public import EthLib.Cryptography.Proofs.Bls.Security.Game

/-!
# Proofs: the unforgeability game of BLS aggregates with proofs of possession

This is the proof-of-possession scheme of the BLS draft, §3.3.

<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-05#section-3.3>

A proof of possession of the key `a • g1` is `a • H'(a • g1)`, with `H'` a second hash into `G2`.

The draft requires `H'` to be domain separated from the message hash `H`, §3.3.1.

Fast aggregate verification sums the keys, then verifies one signature on one message, §3.3.4.

The draft requires a valid proof for every key it sums; otherwise a rogue key forges.

In the game one key is honest, and the adversary chooses all the others.

It receives the honest key and its proof, and asks for signatures under the honest key.

It wins with keys that all carry valid proofs, the honest key among them, and a fresh message.

Its aggregate signature on that message must verify under the sum of the keys.

Both hashes are random oracles.

Unlike the draft, the game does not reject the identity key or an identity sum.

Accepting more outputs only makes the adversary's task easier.

A bound will need two more hypotheses, which the game itself does not impose.

- Every key is a multiple of `g1`, as in a group of prime order.
- The number of key hash calls is at most the characteristic of the scalars.

Without the second, enough copies of the honest key sum to zero.

A key with a known secret then wins.

The draft's Appendix C cites proofs for related constructions, among them Ristenpart and Yilek.

<https://eprint.iacr.org/2007/264>
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security.Pop

open OracleComp OracleSpec ENNReal

variable {F G₁ G₂ M : Type}

/-- The oracles: uniform coins, the message hash `H`, signing, and the key hash `H'`. -/
abbrev Spec (M G₁ G₂ : Type) := unifSpec + (((M →ₒ G₂) + (M →ₒ G₂)) + (G₁ →ₒ G₂))

/-- An adversary against aggregates with proofs of possession.

It receives the honest key and its proof.

It returns pairs of a key and a proof, a message, and an aggregate signature. -/
structure Adversary (G₁ G₂ M : Type) where
  /-- The adversary's run, with access to the oracles. -/
  main : G₁ → G₂ → OracleComp (Spec M G₁ G₂) (List (G₁ × G₂) × M × G₂)

/-- The state of the game. -/
structure State (F G₁ M : Type) where
  /-- The state of the message hash and of signing, as in the game for one key. -/
  msg : Security.State F M
  /-- Each hashed key once, in the order of its first hash call, with the scalar of its hash. -/
  keyTable : List (G₁ × F)
  /-- The number of key hash calls so far, repeated keys included.

  It also counts the hash of the honest proof and the hash of each key at verification. -/
  keyCalls : ℕ

/-- The empty state, at the start of the game. -/
def State.init : State F G₁ M := ⟨Security.State.init, [], 0⟩

/-- The state after the hash of the honest key `pk` with scalar `s`, the first key hash call. -/
def State.withKey (pk : G₁) (s : F) : State F G₁ M := ⟨Security.State.init, [(pk, s)], 1⟩

variable [DecidableEq M] [DecidableEq G₁] [CommRing F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- The random oracle `H'` on keys.

A new key gets `t • g2` for a fresh uniform scalar `t`, and a repeated one its first answer. -/
def keyHash (g₂ : G₂) (x : G₁) : StateT (State F G₁ M) ProbComp G₂ := fun st =>
  match lookup x st.keyTable with
  | some (_, t) => pure (t • g₂, { st with keyCalls := st.keyCalls + 1 })
  | none =>
    (fun t => (t • g₂,
      { st with keyTable := st.keyTable ++ [(x, t)], keyCalls := st.keyCalls + 1 })) <$>
      ($ᵗ F)

omit [DecidableEq M] [AddCommGroup G₁] [Module F G₁] in
/-- A key already in the table hashes to its scalar times `g2`, and only counts the call. -/
theorem keyHash_of_lookup_some {g₂ : G₂} {x : G₁} {st : State F G₁ M} {k : ℕ} {t : F}
    (h : lookup x st.keyTable = some (k, t)) :
    keyHash g₂ x st = pure (t • g₂, { st with keyCalls := st.keyCalls + 1 }) := by
  unfold keyHash
  rw [h]

omit [DecidableEq M] [AddCommGroup G₁] [Module F G₁] in
/-- A new key draws a fresh scalar, which the key table keeps with the key. -/
theorem keyHash_of_lookup_none {g₂ : G₂} {x : G₁} {st : State F G₁ M}
    (h : lookup x st.keyTable = none) :
    keyHash g₂ x st = (fun t => (t • g₂,
      { st with keyTable := st.keyTable ++ [(x, t)], keyCalls := st.keyCalls + 1 })) <$>
      ($ᵗ F) := by
  unfold keyHash
  rw [h]

/-- Run one oracle of the game for one key on the message part of the state. -/
def onMsg {α : Type} (step : StateT (Security.State F M) ProbComp α) :
    StateT (State F G₁ M) ProbComp α := fun st =>
  (fun z => (z.1, { st with msg := z.2 })) <$> step st.msg

/-- The oracles of the game under the secret key `a`. -/
def impl (g₂ : G₂) (a : F) : QueryImpl (Spec M G₁ G₂) (StateT (State F G₁ M) ProbComp)
  | .inl n => fun st => (·, st) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl m)) => (onMsg (hash g₂ m) : StateT (State F G₁ M) ProbComp G₂)
  | .inr (.inl (.inr m)) => (onMsg (sign g₂ a m) : StateT (State F G₁ M) ProbComp G₂)
  | .inr (.inr x) => (keyHash g₂ x : StateT (State F G₁ M) ProbComp G₂)

/-- The adversary's run, then the hash calls that verification makes.

It returns the output, the hash of the message, and the key hash of each key in order. -/
def run (adversary : Adversary G₁ G₂ M) (pk : G₁) (proof : G₂) :
    OracleComp (Spec M G₁ G₂) ((List (G₁ × G₂) × M × G₂) × G₂ × List G₂) := do
  let out ← adversary.main pk proof
  let h ← query (spec := Spec M G₁ G₂) (.inr (.inl (.inl out.2.1)))
  let hs ← out.1.mapM fun k => query (spec := Spec M G₁ G₂) (.inr (.inr k.1))
  return (out, h, hs)

/-- Whether the output wins against the key `pk`, given the hashes that verification computed.

The honest key is among the keys, and the message was never signed.

There is one key hash per key, and every proof verifies on its key hash.

The aggregate verifies on the message hash under the sum of the keys. -/
def wins (scheme : Scheme G₁ G₂) (pk : G₁) (signed : List M)
    (z : (List (G₁ × G₂) × M × G₂) × G₂ × List G₂) : Bool :=
  let ((keys, m, σ), h, hs) := z
  decide (pk ∈ keys.map Prod.fst) && decide (m ∉ signed) && decide (hs.length = keys.length) &&
    (keys.zip hs).all (fun (k, h') => scheme.isDh k.1 h' k.2) &&
    scheme.isDh (keys.map Prod.fst).sum h σ

/-- The game: sample the secret key, give the adversary the key and its proof, run it, check.

The honest proof hashes the honest key first, so that hash is the first entry of the key table.

It also returns the final state, whose counts of hash calls bound the adversary. -/
def experiment (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) :
    ProbComp (Bool × State F G₁ M) := do
  let a ← $ᵗ F
  let pk := a • scheme.g₁
  let (z, st) ← (do
    let hpk ← keyHash scheme.g₂ pk
    simulateQ (impl scheme.g₂ a) (run adversary pk (a • hpk))).run State.init
  return (wins scheme pk st.msg.signed z, st)

variable (F)

/-- The probability that the adversary forges an aggregate. -/
noncomputable def forgeAdvantage (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) :
    ℝ≥0∞ :=
  Pr{let z ← experiment (F := F) scheme adversary}[z.1 = true]

/-- Every run of the game makes at most `q` message hash calls and `qK` key hash calls.

The counts include the calls of signing, of the honest proof, and of verification. -/
def HashCallBound (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) (q qK : ℕ) : Prop :=
  ∀ z ∈ support (experiment (F := F) scheme adversary), z.2.msg.calls ≤ q ∧ z.2.keyCalls ≤ qK

variable {F}

/-! ## The winning condition has content -/

omit [SampleableType F] in
/-- Keys with known secrets carry valid proofs, and their signatures on one hash aggregate.

So whoever knows every secret, the honest one included, meets the winning condition. -/
theorem wins_of_secrets {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F) {a : F}
    {sks : List F} (ha : a ∈ sks) (hk : G₁ → G₂) {signed : List M} {m : M}
    (hm : m ∉ signed) (h : G₂) :
    wins scheme (a • scheme.g₁) signed
      ((sks.map fun sk => (sk • scheme.g₁, sk • hk (sk • scheme.g₁)), m,
          (sks.map (· • h)).sum),
        h, sks.map fun sk => hk (sk • scheme.g₁)) = true := by
  have hsum : ∀ x : G₂, (sks.map (· • x)).sum = sks.sum • x := fun x => (List.sum_smul).symm
  have hkeys : (sks.map (· • scheme.g₁)).sum = sks.sum • scheme.g₁ := (List.sum_smul).symm
  simp only [wins, List.map_map, Function.comp_def, List.length_map, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨List.mem_map_of_mem ha, hm⟩, trivial⟩, ?_⟩, ?_⟩
  · intro x hx
    rw [List.zip_map', List.mem_map] at hx
    obtain ⟨sk, -, rfl⟩ := hx
    exact (hsound sk _ _).mpr rfl
  · rw [hkeys, hsum]
    exact (hsound _ h _).mpr rfl

omit [DecidableEq G₁] [SampleableType F] in
/-- Without the proofs, a rogue key passes the aggregate check.

From the honest key `pk` and any scalar `c`, the key `c • g1 - pk` sums with `pk` to `c • g1`.

Then `c • h` verifies under the sum, for every hash `h`, with no secret known. -/
theorem isDh_rogue {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F) (pk : G₁) (c : F)
    (h : G₂) : scheme.isDh ([pk, c • scheme.g₁ - pk].sum) h (c • h) = true := by
  rw [show [pk, c • scheme.g₁ - pk].sum = c • scheme.g₁ by simp]
  exact (hsound c h _).mpr rfl

end EthLib.Cryptography.Bls.Security.Pop
