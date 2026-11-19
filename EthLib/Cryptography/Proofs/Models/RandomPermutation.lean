module

public import EthLib.Cryptography.Hash.Keccak
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The random permutation model for Keccak-f[1600]

The ideal object is a uniformly random permutation `pi` of the Keccak-f[1600] states.

Every party queries it through two oracles, `pi` and its inverse.

Bertoni, Daemen, Peeters and Van Assche study the sponge in this model, at EUROCRYPT 2008.

Their paper is "On the Indifferentiability of the Sponge Construction".

The permutation is Keccak-f[1600] of [FIPS 202](https://doi.org/10.6028/NIST.FIPS.202), §3.

The permutation is sampled lazily.

A fresh forward query draws its answer uniformly among the states not yet used as forward answers.

A fresh inverse query draws its answer uniformly among the states not yet used as forward inputs.

Every fresh answer is recorded in a table, so the two oracles stay mutually inverse.

Each entry also keeps the direction of the query that sampled it.

A computation takes its private coins and the permutation as oracles.

The deployed run answers the permutation with a fixed permutation and its inverse.

Adversaries are classical and fixed before the permutation is sampled.

Their budget counts their own permutation queries on every execution path.

The model assumes that the deployed Keccak-f[1600] behaves like a random permutation.

It assumes this also for programs that compute the permutation.

This is an assumption, not a theorem.
-/

@[expose] public section

namespace EthLib.Cryptography.Models.RandomPermutation

open OracleComp OracleSpec ENNReal

open EthLib.Cryptography.Hash.Keccak (State)

/-- The Keccak state is finite: 25 lanes of 64 bits. -/
instance : Fintype State :=
  -- The 25 fields of a state, in order.
  Fintype.ofEquiv (Fin 25 → UInt64)
    { toFun f := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14,
        f 15, f 16, f 17, f 18, f 19, f 20, f 21, f 22, f 23, f 24⟩
      invFun s := ![s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11,
        s.a12, s.a13, s.a14, s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]
      left_inv f := funext fun i => by fin_cases i <;> rfl
      right_inv _ := rfl }

theorem card_state : Fintype.card State = 2 ^ 1600 := by
  refine (Fintype.ofEquiv_card _).trans ?_
  rw [Fintype.card_fun, Fintype.card_fin, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt64,
    ← pow_mul]

/-- The direction of a permutation query. -/
inductive Dir where
  | forward
  | inverse
  deriving DecidableEq

-- A derived Fintype instance fails to elaborate in this module, so it is written out.
instance : Fintype Dir where
  elems := {.forward, .inverse}
  complete d := by cases d <;> simp

/-- The permutation oracles: a query names a direction and a state, and returns a state. -/
abbrev PermSpec := (Dir × State) →ₒ State

/-- The private coins of a party, and the permutation.

Only permutation queries are budgeted. -/
abbrev World := unifSpec + PermSpec

/-- One query to the permutation oracle. -/
def queryPerm {m : Type → Type} [Monad m] [HasQuery PermSpec m] (d : Dir) (s : State) : m State :=
  HasQuery.query (spec := PermSpec) (m := m) (d, s)

/-- One recorded pair `(x, pi x)`, with the direction of the query that sampled it.

A forward query sampled the output, an inverse query the input. -/
structure PermEntry where
  input : State
  output : State
  dir : Dir
  deriving DecidableEq

/-- The state the lazy oracle drew for this pair. -/
def PermEntry.sampled (e : PermEntry) : State :=
  match e.dir with
  | .forward => e.output
  | .inverse => e.input

/-- The recorded pairs, the most recent first. -/
abbrev PermTable := List PermEntry

/-- The answer the table already holds for a query, if any. -/
def PermTable.lookup (t : PermTable) : Dir × State → Option State
  | (.forward, s) => (t.find? (·.input = s)).map (·.output)
  | (.inverse, y) => (t.find? (·.output = y)).map (·.input)

/-- The states the lazy oracle drew, the most recent first. -/
def PermTable.sampled (t : PermTable) : List State := t.map PermEntry.sampled

/-- Lazy sampling of a uniform permutation: answer from the table, or draw a fresh answer.

The fresh answer is uniform among the states unused on that side, and the table records it. -/
noncomputable def lazyImpl : QueryImpl PermSpec (StateT PermTable (OptionT ProbComp))
  | (d, s) => StateT.mk fun t =>
    match t.lookup (d, s), d with
    | some y, _ => pure (y, t)
    | none, .forward => do
      -- The answer avoids every recorded output, so the table stays a partial bijection.
      let y ← ($ (Finset.univ \ (t.map (·.output)).toFinset) : OptionT ProbComp State)
      pure (y, ⟨s, y, .forward⟩ :: t)
    | none, .inverse => do
      let x ← ($ (Finset.univ \ (t.map (·.input)).toFinset) : OptionT ProbComp State)
      pure (x, ⟨x, s, .inverse⟩ :: t)

/-- Run a computation of the world against a lazily sampled permutation, from the empty table. -/
noncomputable def runRpm {α : Type} (oa : OracleComp World α) :
    OptionT ProbComp (α × PermTable) :=
  (simulateQ (unifSpec.passthrough + lazyImpl) oa).run []

/-- Answer permutation queries with fixed functions.

The deployed instance takes Keccak-f[1600] forwards, and only adversaries query the inverse. -/
def fixedImpl (f finv : State → State) : QueryImpl PermSpec Id :=
  fun | (.forward, s) => f s | (.inverse, y) => finv y

/-- Run a computation of the world against a fixed permutation `σ`.

The permutation queries get `σ` and its inverse, and the private coins get `ProbComp` itself. -/
noncomputable def runFixed {α : Type} (σ : Equiv.Perm State) (oa : OracleComp World α) :
    ProbComp α :=
  simulateQ (unifSpec.passthrough + (fixedImpl σ σ.symm).liftTarget ProbComp) oa

/-- The adversary makes at most `Q` permutation queries on every path. -/
def PermQueryBound {α : Type} (oa : OracleComp World α) (Q : Nat) : Prop :=
  IsQueryBoundP oa (fun i => i.isRight) Q

end EthLib.Cryptography.Models.RandomPermutation
