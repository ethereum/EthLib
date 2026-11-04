module

public import EthLib.Cryptography.Proofs.Bls.Security.CoCdh
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Proofs: the unforgeability game of BLS signatures

The scheme of [Boneh, Lynn, Shacham](https://hovav.net/ucsd/dist/sigs.pdf), §3.

The key `a • g1` signs a message `m` as `a • H(m)`, with `H` a hash into `G2`.

The game is existential unforgeability under chosen-message attacks, in the random oracle model.

The adversary wins with a valid signature on a message it never asked to sign.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security

open OracleComp OracleSpec ENNReal

variable {F G₁ G₂ M : Type}

/-- A BLS scheme over two groups: their fixed elements, and a test of co-Diffie-Hellman tuples. -/
structure Scheme (G₁ G₂ : Type) where
  /-- The fixed element of `G1`, the base of public keys. -/
  g₁ : G₁
  /-- The fixed element of `G2`, the base of the hash. -/
  g₂ : G₂
  /-- Whether `(g1, pk, h, σ)` is a co-Diffie-Hellman tuple, which is how a signature verifies. -/
  isDh : G₁ → G₂ → G₂ → Bool

/-- The oracles of the adversary: uniform coins, the hash `H`, and the signing oracle. -/
abbrev Spec (M G₂ : Type) := unifSpec + ((M →ₒ G₂) + (M →ₒ G₂))

/-- An adversary: from the public key, it returns a message and a claimed signature. -/
structure Adversary (G₁ G₂ M : Type) where
  /-- The adversary's run, with access to the oracles. -/
  main : G₁ → OracleComp (Spec M G₂) (M × G₂)

/-- The state of the game. -/
structure State (F M : Type) where
  /-- Each hashed message once, in the order of its first hash call.

  The entry keeps the scalar `t` of the hash `t • g2`. -/
  table : List (M × F)
  /-- The messages of the signing requests, in order. -/
  signed : List M
  /-- The number of hash calls so far, repeated messages included. -/
  calls : ℕ

/-- The empty state, at the start of the game. -/
def State.init : State F M := ⟨[], [], 0⟩

variable [DecidableEq M]

/-- The position and the scalar of the entry for `m`, if the table has one. -/
def lookup (m : M) : List (M × F) → Option (ℕ × F)
  | [] => none
  | (m', t) :: rest =>
    if m' = m then some (0, t) else (lookup m rest).map fun (k, t) => (k + 1, t)

variable [CommRing F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂]

variable (F) in
/-- The test of the scheme decides co-Diffie-Hellman tuples.

For a key `a • g1`, it accepts `σ` on `h` exactly when `σ = a • h`. -/
def Scheme.Sound (scheme : Scheme G₁ G₂) : Prop :=
  ∀ (a : F) (h σ : G₂), scheme.isDh (a • scheme.g₁) h σ = true ↔ σ = a • h

/-- The random oracle `H`.

A new message gets `t • g2` for a fresh uniform scalar `t`, and a repeated one its first answer.

Each call counts, repeated messages included. -/
def hash (g₂ : G₂) (m : M) : StateT (State F M) ProbComp G₂ := fun st =>
  match lookup m st.table with
  | some (_, t) => pure (t • g₂, { st with calls := st.calls + 1 })
  | none =>
    (fun t => (t • g₂, { st with table := st.table ++ [(m, t)], calls := st.calls + 1 })) <$>
      ($ᵗ F)

/-- The signing oracle under the secret key `a`: it returns `a • H(m)` and records `m`. -/
def sign (g₂ : G₂) (a : F) (m : M) : StateT (State F M) ProbComp G₂ := fun st =>
  (fun z => (a • z.1, { z.2 with signed := z.2.signed ++ [m] })) <$> hash g₂ m st

/-- The oracles of the game under the secret key `a`.

Coins pass through, and the state is unchanged by them. -/
def impl (g₂ : G₂) (a : F) : QueryImpl (Spec M G₂) (StateT (State F M) ProbComp)
  | .inl n => fun st => (·, st) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl m) => (hash g₂ m : StateT (State F M) ProbComp G₂)
  | .inr (.inr m) => (sign g₂ a m : StateT (State F M) ProbComp G₂)

/-- The adversary's run on the public key, then the hash call that verification makes.

It returns the message, the claimed signature and the hash of the message. -/
def run (adversary : Adversary G₁ G₂ M) (pk : G₁) : OracleComp (Spec M G₂) (M × G₂ × G₂) := do
  let (m, σ) ← adversary.main pk
  let h ← query (spec := Spec M G₂) (.inr (.inl m))
  return (m, σ, h)

/-- The game: sample the secret key, run the adversary with its oracles, and check the forgery.

It also returns the final state, whose count of hash calls bounds the adversary. -/
def experiment (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) :
    ProbComp (Bool × State F M) := do
  let a ← $ᵗ F
  let pk := a • scheme.g₁
  let ((m, σ, h), st) ← (simulateQ (impl scheme.g₂ a) (run adversary pk)).run State.init
  return (decide (m ∉ st.signed) && scheme.isDh pk h σ, st)

variable (F)

/-- The probability that the adversary forges. -/
noncomputable def forgeAdvantage (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) :
    ℝ≥0∞ :=
  Pr{let z ← experiment (F := F) scheme adversary}[z.1 = true]

/-- Every run of the game makes at most `q` hash calls.

That counts the adversary's calls, those of signing, and the one of the final verification. -/
def HashCallBound (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) (q : ℕ) : Prop :=
  ∀ z ∈ support (experiment (F := F) scheme adversary), z.2.calls ≤ q

end EthLib.Cryptography.Bls.Security
