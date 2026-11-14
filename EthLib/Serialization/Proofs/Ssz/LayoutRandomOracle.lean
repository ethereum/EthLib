module

public import EthLib.Serialization.Proofs.Ssz.RandomOracle
public import EthLib.Serialization.Proofs.Ssz.Codec.LayoutSeparation

/-!
# Proofs: the layouts of progressive containers in the random oracle model

An adversary that makes queries outputs two types and a value of each.

It wins with two legal progressive containers of different layouts and one root.

Each win exposes a cache collision, so the birthday bound applies.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2.

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Serialization.Ssz.RandomOracle

open EthLib.Base
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography (evalWithAnswerFn_exceptT_bind evalWithAnswerFn_exceptT_pure
  evalWithAnswerFn_exceptT_lift evalWithAnswerFn_exceptT_liftExcept)
open EthLib.Cryptography.Merkle.RandomOracle (Collision)

/-- What the layout experiment reports: the two types and the roots of their values. -/
structure LayoutOutcome where
  /-- The type of the first value. -/
  firstShape : Desc
  /-- The type of the second value. -/
  secondShape : Desc
  /-- The root of the first value under the oracle. -/
  firstRoot : Except Err Bytes
  /-- The root of the second value under the oracle. -/
  secondRoot : Except Err Bytes

/-- Queries the input of a root's last hash again, if the run found one. -/
def queryLastInput : Except Err (Option Bytes) → OracleComp HashOracle Unit
  | .ok (some input) => do
    let _ ← queryHash (ByteArray.mk input)
    return ()
  | _ => pure ()

/-- The extraction for layouts, run on two types, each with a value.

It computes both roots, then the input of each last hash, and queries each input again. -/
def extractLayouts (first second : Desc × Value) : OracleComp HashOracle LayoutOutcome := do
  let firstRoot ← (hashTreeRootM oracleHasher first.1 first.2).run
  let secondRoot ← (hashTreeRootM oracleHasher second.1 second.2).run
  queryLastInput (← (mixinMessageM oracleHasher first.1 first.2).run)
  queryLastInput (← (mixinMessageM oracleHasher second.1 second.2).run)
  return ⟨first.1, second.1, firstRoot, secondRoot⟩

/-- The adversary wins: two legal progressive containers with different layouts have one root. -/
def LayoutWins (outcome : LayoutOutcome) : Prop :=
  outcome.firstShape.wellFormed = .ok () ∧ outcome.secondShape.wellFormed = .ok () ∧
    (∃ firstActive firstNames firstFields secondActive secondNames secondFields,
      outcome.firstShape = .progressiveContainer firstActive firstNames firstFields ∧
      outcome.secondShape = .progressiveContainer secondActive secondNames secondFields ∧
      firstActive ≠ secondActive) ∧
    ∃ root, outcome.firstRoot = .ok root ∧ outcome.secondRoot = .ok root

/-- The input of a last hash, run against a full answer table, is the input with that table. -/
theorem evalWithAnswerFn_mixinMessageM (f : QueryImpl HashOracle Id) (shape : Desc)
    (value : Value) :
    evalWithAnswerFn f (mixinMessageM oracleHasher shape value).run =
      (mixinMessageM (Hasher.ofHash (m := Id) (tableHash f)) shape value).run := by
  rw [mixinMessageM_id_eq]
  simp only [mixinMessageM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_liftExcept,
    evalWithAnswerFn_layoutChunksAtM f _ (evalWithAnswerFn_hashTreeRootAtM f _)]
  show Except.bind _ _ = Except.bind _ _
  congr 1
  funext layout
  show Except.bind _ _ = Except.bind _ _
  congr 1
  funext chunks
  cases layout.limit <;>
    simp only [evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_lift,
      evalWithAnswerFn_exceptT_pure, evalWithAnswerFn_merkleizeProgressiveUncheckedM,
      evalWithAnswerFn_merkleizeBoundedUncheckedM] <;>
    rfl

/-- A replayed layout extraction caches the input of each last hash, with the table's answer. -/
theorem cached_of_extractLayouts {cache : HashOracle.QueryCache} {f : QueryImpl HashOracle Id}
    (hf : cache.AgreesWithFn f) {first second : Desc × Value} {outcome : LayoutOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractLayouts first second) = some outcome) :
    (∀ input, mixinMessage first.1 first.2 (tableHash f) = some input →
      cache (ByteArray.mk input) = some (f (ByteArray.mk input))) ∧
    ∀ input, mixinMessage second.1 second.2 (tableHash f) = some input →
      cache (ByteArray.mk input) = some (f (ByteArray.mk input)) := by
  simp only [extractLayouts, simulateQ_bind] at hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨firstInput, hfirst, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, hqueryFirst, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨secondInput, hsecond, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, hquerySecond, -⟩ := Option.bind_eq_some_iff.mp hrun
  -- The replayed inputs are the inputs with the table, which agrees with the cache.
  have hfirst' := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hfirst
  have hsecond' := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hsecond
  rw [evalWithAnswerFn_mixinMessageM] at hfirst' hsecond'
  -- An input that the table finds was queried again, and the cache keeps the table's answer.
  have hcached : ∀ {input : Bytes} (result : Except Err (Option Bytes)),
      simulateQ cache.toPartialImpl (queryLastInput result) = some () →
      (match result with
        | .ok message => message
        | .error _ => none) = some input →
      cache (ByteArray.mk input) = some (f (ByteArray.mk input)) := by
    intro input result hquery hfound
    rcases result with _ | (_ | message)
    · cases hfound
    · cases hfound
    · cases hfound
      simp only [queryLastInput, simulateQ_bind] at hquery
      obtain ⟨_, hquery, -⟩ := Option.bind_eq_some_iff.mp hquery
      obtain ⟨digest, hdigest⟩ := cached_of_queryHash hquery
      rw [hdigest, hf hdigest]
  refine ⟨fun input hinput => ?_, fun input hinput => ?_⟩
  · simp only [mixinMessage, hfirst'] at hinput
    exact hcached _ hqueryFirst hinput
  · simp only [mixinMessage, hsecond'] at hinput
    exact hcached _ hquerySecond hinput

/-- A replayed winning layout extraction exposes a collision of the cache.

The layout search of SSZ finds it, run with a table that extends the cache. -/
theorem collision_of_extractLayouts {cache : HashOracle.QueryCache}
    {first second : Desc × Value} {outcome : LayoutOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractLayouts first second) = some outcome)
    (hwins : LayoutWins outcome) : Collision cache := by
  obtain ⟨shape₁, value₁⟩ := first
  obtain ⟨shape₂, value₂⟩ := second
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extractLayouts, evalWithAnswerFn_bind, evalWithAnswerFn_hashTreeRootM,
    evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨hlegal₁, hlegal₂, ⟨active₁, names₁, fields₁, active₂, names₂, fields₂, hshape₁,
    hshape₂, hlayouts⟩, root, hroot₁, hroot₂⟩ := hwins
  dsimp only at hlegal₁ hlegal₂ hshape₁ hshape₂ hroot₁ hroot₂
  subst hshape₁ hshape₂
  -- Under the table, the two layouts are equal, or the layout search finds a collision.
  rcases hashTreeRootM_progressiveContainer_layouts_separate (tableHash f) (tableHash_size f)
    hlegal₁ hlegal₂ hroot₁ hroot₂ with hsame | ⟨a, b, hfound, -, -, hdistinct, hequal⟩
  · exact absurd hsame hlayouts
  · -- Both inputs were queried again, so the cache gives them the answers of the table.
    obtain ⟨ha, hb, -, -⟩ := findMixinCollision_valid hfound
    exact collision_of_cached hdistinct hequal ((cached_of_extractLayouts hf hrun).1 _ ha)
      ((cached_of_extractLayouts hf hrun).2 _ hb)

/-- Two legal progressive containers with different layouts and one root.

The probability is at most `Q^2 / 2^256`.

`Q` bounds the oracle calls of the whole experiment, repeats included.

The extraction computes each root twice, once whole and once up to its last hash.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_layoutWins_le_two_pow
    (adversary : OracleComp (unifSpec + HashOracle) ((Desc × Value) × (Desc × Value))) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith extractLayouts adversary) (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith extractLayouts adversary)).run ∅}[LayoutWins z.1] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_experimentWith_le extractLayouts LayoutWins collision_of_extractLayouts
    adversary hQ
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

end EthLib.Serialization.Ssz.RandomOracle
