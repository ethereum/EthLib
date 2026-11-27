module

public import EthLib.Execution.Proofs.Network.Bodies
public import EthLib.Execution.Proofs.Blocks.RootsRandomOracle

/-!
# Proofs: the check of a block body in the random oracle model

The hash is modelled as one random oracle, for the roots and the ommers hash alike.

An adversary wins with two different bodies that keep their encodings and pass for one header.

The birthday bound of the oracle bounds the probability that it wins.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2.

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Execution.Network.RandomOracle

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Blocks
open EthLib.Execution.Blocks.RandomOracle
open EthLib.Execution.Trie
open EthLib.Execution.Trie.RandomOracle
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography (evalWithAnswerFn_exceptT_bind evalWithAnswerFn_exceptT_liftExcept
  evalWithAnswerFn_exceptT_lift evalWithAnswerFn_exceptT_adapt)
open EthLib.Cryptography.Merkle.RandomOracle (Collision collision_of_cached experimentWith
  prEvent_experimentWith_le card_bytes32)

variable {fork : Fork}

/-! ## The checks against a table -/

/-- The withdrawals root, run against a table, is the root with that table as the hash. -/
theorem evalWithAnswerFn_withdrawalsRootM (f : QueryImpl HashOracle Id)
    (withdrawals : List Withdrawal) :
    evalWithAnswerFn f (withdrawalsRootM queryHash withdrawals).run =
      (withdrawalsRootM (m := Id) (fun x => f x) withdrawals).run := by
  rw [withdrawalsRootM_eq]
  simp only [withdrawalsRootM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_liftExcept,
    evalWithAnswerFn_indexedRootM]
  rfl

/-- The check of the transactions, run against a table, is the check with that table. -/
theorem evalWithAnswerFn_checkTransactionsM (f : QueryImpl HashOracle Id) (header : Header fork)
    (transactions : Encoded) :
    evalWithAnswerFn f (checkTransactionsM queryHash header transactions).run =
      (checkTransactionsM (m := Id) (fun x => f x) header transactions).run := by
  rw [checkTransactionsM_eq]
  simp only [checkTransactionsM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_liftExcept,
    evalWithAnswerFn_exceptT_adapt, evalWithAnswerFn_indexedRootM]
  rfl

/-- The check of the withdrawals, run against a table, is the check with that table. -/
theorem evalWithAnswerFn_checkWithdrawalsM (f : QueryImpl HashOracle Id) (header : Header fork)
    (h : .shapella ≤ fork) (withdrawals : Item) :
    evalWithAnswerFn f (checkWithdrawalsM queryHash header h withdrawals).run =
      (checkWithdrawalsM (m := Id) (fun x => f x) header h withdrawals).run := by
  rw [checkWithdrawalsM_eq]
  simp only [checkWithdrawalsM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_liftExcept,
    evalWithAnswerFn_exceptT_adapt, evalWithAnswerFn_withdrawalsRootM]
  rfl

/-- The check of the ommers, run against a table, is the check with that table. -/
theorem evalWithAnswerFn_checkOmmersM (f : QueryImpl HashOracle Id) (header : Header fork)
    (ommers : Encoded) :
    evalWithAnswerFn f (checkOmmersM queryHash header ommers).run =
      (checkOmmersM (m := Id) (fun x => f x) header ommers).run := by
  rw [checkOmmersM_eq]
  simp only [checkOmmersM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_liftExcept,
    evalWithAnswerFn_exceptT_lift]
  cases ommers.item.toItems with
  | error => rfl
  | ok items => rfl

/-- The check of a body, run against a table, is the check with that table as the hash. -/
theorem evalWithAnswerFn_checkBodyM (f : QueryImpl HashOracle Id) (header : Header fork)
    (body : Encoded) :
    evalWithAnswerFn f (checkBodyM queryHash header body).run =
      (checkBodyM (m := Id) (fun x => f x) header body).run := by
  rw [checkBodyM_eq]
  simp only [checkBodyM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_liftExcept]
  cases body.parts with
  | error => rfl
  | ok items =>
    by_cases hf : .shapella ≤ fork
    · simp only [Except.mapError, Except.bind, hf, ↓reduceDIte]
      rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
      all_goals first
        | rfl
        | simp only [evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_checkTransactionsM,
            evalWithAnswerFn_checkWithdrawalsM, evalWithAnswerFn_checkOmmersM]; rfl
    · simp only [Except.mapError, Except.bind, hf, ↓reduceDIte]
      rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
      all_goals first
        | rfl
        | simp only [evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_checkTransactionsM,
            evalWithAnswerFn_checkOmmersM]; rfl

/-! ## Two bodies that pass for one header -/

/-- The bytes of each withdrawal of an item: the values of the trie of the withdrawals root. -/
def withdrawalValues (withdrawals : Item) : Except RlpError (List ByteArray) := do
  let ws : List Withdrawal ← Codec.ofItem withdrawals
  ws.mapM Codec.encode

/-- Queries the binding inputs of the tries of the bytes of two transactions lists. -/
def queryTransactionWitnesses (first second : Encoded) : OracleComp HashOracle Unit :=
  match transactionValues first, transactionValues second with
  | .ok values₁, .ok values₂ => queryIndexedWitnesses values₁ values₂
  | _, _ => pure ()

/-- Queries the binding inputs of the tries of two withdrawals parts, when each body has one. -/
def queryWithdrawalWitnesses (first second : List Encoded) : OracleComp HashOracle Unit :=
  match first, second with
  | [w₁], [w₂] =>
    match withdrawalValues w₁.item, withdrawalValues w₂.item with
    | .ok values₁, .ok values₂ => queryIndexedWitnesses values₁ values₂
    | _, _ => pure ()
  | _, _ => pure ()

/-- Queries every input of the body search.

These are the binding inputs of the tries of the transactions and of the withdrawals.

Then come both encodings of the ommers, which the ommers hash reads. -/
def queryBodyWitnesses (first second : Encoded) : OracleComp HashOracle Unit :=
  match first.parts, second.parts with
  | .ok (t₁ :: o₁ :: rest₁), .ok (t₂ :: o₂ :: rest₂) => do
    queryTransactionWitnesses t₁ t₂
    queryWithdrawalWitnesses rest₁ rest₂
    let _ ← [o₁.bytes, o₂.bytes].mapM queryHash
    return ()
  | _, _ => pure ()

/-- What the experiment reports: the header, the two bodies, and their checks under the oracle. -/
structure BodyOutcome (fork : Fork) where
  /-- The header of the adversary. -/
  header : Header fork
  /-- The first body of the adversary. -/
  first : Encoded
  /-- The second body of the adversary. -/
  second : Encoded
  /-- The check of the first body under the oracle. -/
  firstResult : Except BodyError Unit
  /-- The check of the second body under the oracle. -/
  secondResult : Except BodyError Unit

/-- The part of the experiment after the adversary, which only calls the hash oracle.

It checks both bodies, then queries every input of the body search. -/
def extractBody (header : Header fork) (first second : Encoded) :
    OracleComp HashOracle (BodyOutcome fork) := do
  let firstResult ← (checkBodyM queryHash header first).run
  let secondResult ← (checkBodyM queryHash header second).run
  queryBodyWitnesses first second
  return ⟨header, first, second, firstResult, secondResult⟩

/-- The experiment: the adversary picks a header and two bodies, then the extraction runs. -/
def bodyExperiment
    (adversary : OracleComp (unifSpec + HashOracle) (Header fork × Encoded × Encoded)) :
    OracleComp (unifSpec + HashOracle) (BodyOutcome fork) :=
  experimentWith (fun claim => extractBody claim.1 claim.2.1 claim.2.2) adversary

/-- The adversary wins: two different bodies keep their encodings and pass for one header. -/
def BodyWins (outcome : BodyOutcome fork) : Prop :=
  encode outcome.first.item = .ok outcome.first.bytes ∧
    encode outcome.second.item = .ok outcome.second.bytes ∧
    outcome.firstResult = .ok () ∧ outcome.secondResult = .ok () ∧
    outcome.first.item ≠ outcome.second.item

/-- A replayed winning extraction exposes a collision of the cache. -/
theorem collision_of_extractBody {cache : HashOracle.QueryCache} {header : Header fork}
    {first second : Encoded} {outcome : BodyOutcome fork}
    (hrun : simulateQ cache.toPartialImpl (extractBody header first second) = some outcome)
    (hwins : BodyWins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extractBody, simulateQ_bind] at hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, hwitnesses, -⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [extractBody, evalWithAnswerFn_bind, evalWithAnswerFn_checkBodyM,
    evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨he₁, he₂, h₁, h₂, hne⟩ := hwins
  -- Two bodies that pass for one header have the same parts, or the search names a collision.
  obtain ⟨t₁, o₁, t₂, o₂, rest₁, rest₂, hp₁, hp₂, htransactions, hommers, hbefore, hafter⟩ :=
    checkBody_binding (fun x => f x) he₁ he₂ h₁ h₂
  -- The replay queried the witnesses of exactly these parts.
  unfold queryBodyWitnesses at hwitnesses
  simp only [hp₁, hp₂, simulateQ_bind] at hwitnesses
  obtain ⟨_, htx, hwitnesses⟩ := Option.bind_eq_some_iff.mp hwitnesses
  obtain ⟨_, hws, hwitnesses⟩ := Option.bind_eq_some_iff.mp hwitnesses
  obtain ⟨_, hencodings, -⟩ := Option.bind_eq_some_iff.mp hwitnesses
  -- The ommers: two different encodings with one answer.
  rcases hommers with hommers | ⟨hdistinct, hequal⟩
  swap
  · have hcached : ∀ x ∈ [o₁.bytes, o₂.bytes], cache x = some (f x) := fun x hx => by
      obtain ⟨answer, hanswer⟩ := cached_of_mapM_queryHash _ hencodings x hx
      rw [hanswer, hf hanswer]
    exact collision_of_cached hdistinct hequal (hcached _ (by simp)) (hcached _ (by simp))
  -- The transactions: the indexed search returns a collision of the queried proofs.
  rcases htransactions with htransactions | ⟨v₁, v₂, _, hv₁, hv₂, hfind, -⟩
  swap
  · unfold queryTransactionWitnesses at htx
    simp only [hv₁, hv₂] at htx
    exact collision_of_queryIndexedWitnesses hf htx hfind
  by_cases hfork : .shapella ≤ fork
  · obtain ⟨w₁, w₂, rfl, rfl, hwithdrawals⟩ := hafter hfork
    rcases hwithdrawals with hwithdrawals | ⟨ws₁, ws₂, v₁, v₂, _, hd₁, hd₂, hv₁, hv₂, hfind, -⟩
    · -- Every part is equal, so the bodies are.
      refine absurd ?_ hne
      rw [Encoded.item_of_parts hp₁, Encoded.item_of_parts hp₂]
      simp [htransactions, hommers, hwithdrawals]
    · have hw₁ : withdrawalValues w₁.item = .ok v₁ := by
        simp [withdrawalValues, hd₁, hv₁, bind, Except.bind]
      have hw₂ : withdrawalValues w₂.item = .ok v₂ := by
        simp [withdrawalValues, hd₂, hv₂, bind, Except.bind]
      unfold queryWithdrawalWitnesses at hws
      simp only [hw₁, hw₂] at hws
      exact collision_of_queryIndexedWitnesses hf hws hfind
  · -- Before Shapella, the bodies hold only their transactions and their ommers.
    obtain ⟨rfl, rfl⟩ := hbefore hfork
    refine absurd ?_ hne
    rw [Encoded.item_of_parts hp₁, Encoded.item_of_parts hp₂]
    simp [htransactions, hommers]

/-- Two different bodies that keep their encodings and pass for one header.

The probability is at most `Q^2 / 2^256`, with each answer of the oracle 32 uniform bytes. -/
theorem prEvent_bodyWins_le
    (adversary : OracleComp (unifSpec + HashOracle) (Header fork × Encoded × Encoded)) {Q : Nat}
    -- `Q` bounds the oracle calls of the whole experiment, repeats included.
    --
    -- It counts the adversary's calls, both checks, and the queries of the two lists and ommers.
    --
    -- Each index of a list rebuilds both proofs, so the calls grow as the square of its length.
    (hQ : IsQueryBoundP (bodyExperiment adversary) (fun t => t.isRight = true) Q) :
    -- The oracle cache starts empty, and the adversary's private sampling is not counted.
    Pr{let z ← (simulateQ HashOracle.romImpl (bodyExperiment adversary)).run ∅}[
      BodyWins z.1] ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_experimentWith_le (fun claim : Header fork × Encoded × Encoded =>
    extractBody claim.1 claim.2.1 claim.2.2) BodyWins
    (fun hrun hwins => collision_of_extractBody hrun hwins) adversary hQ
  rwa [card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound

end EthLib.Execution.Network.RandomOracle
