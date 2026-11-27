module

public import EthLib.Execution.Proofs.State.Root
public import EthLib.Execution.Proofs.Trie.RandomOracle

/-!
# Proofs: the storage and state roots in the random oracle model

The hash is modelled as one random oracle, as for the root of one trie.

An adversary wins with two storages, or two states, with one root that the root binds apart.

That is a key with two words, or an address with two accounts, or two words at a key of an account.

The birthday bound of the oracle bounds the probability that it wins.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2.

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Execution.State.RandomOracle

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Execution.Trie.RandomOracle
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography (evalWithAnswerFn_exceptT_bind evalWithAnswerFn_exceptT_pure
  evalWithAnswerFn_exceptT_liftExcept evalWithAnswerFn_exceptT_mapM)
open EthLib.Cryptography.Merkle.RandomOracle (Collision collision_of_cached experimentWith
  prEvent_experimentWith_le card_bytes32)

/-- A storage: from 32-byte keys to words. -/
abbrev Storage : Type := Std.ExtTreeMap Bytes32 U256

/-! ## The roots against a table -/

/-- The storage root, run against a table, is the storage root with that table as the hash. -/
theorem evalWithAnswerFn_storageRootM (f : QueryImpl HashOracle Id) (storage : Storage) :
    evalWithAnswerFn f (storageRootM queryHash storage).run =
      storageRoot (fun x => f x) storage := by
  rw [storageRoot_eq]
  simp only [storageRootM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_liftExcept,
    evalWithAnswerFn_rootM]
  rfl

/-- The state entries, run against a table, are the entries with that table as the hash. -/
theorem evalWithAnswerFn_stateEntriesM (f : QueryImpl HashOracle Id) (state : State) :
    evalWithAnswerFn f (stateEntriesM queryHash state).run =
      stateEntries (fun x => f x) state := by
  rw [stateEntries_eq]
  simp only [stateEntriesM, evalWithAnswerFn_exceptT_mapM]
  congr 1
  funext entry
  simp only [evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_storageRootM,
    evalWithAnswerFn_exceptT_liftExcept, evalWithAnswerFn_exceptT_pure]
  rfl

/-- The state root, run against a table, is the state root with that table as the hash. -/
theorem evalWithAnswerFn_stateRootM (f : QueryImpl HashOracle Id) (state : State) :
    evalWithAnswerFn f (stateRootM queryHash state).run = stateRoot (fun x => f x) state := by
  rw [stateRoot_eq]
  simp only [stateRootM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_stateEntriesM,
    evalWithAnswerFn_rootM]
  rfl

/-! ## Two storages with one root -/

/-- Queries every input of the storage search: the binding inputs at each key of either storage.

Storages whose entries do not encode have no root, and need no query. -/
def queryStorageWitnesses (first second : Storage) : OracleComp HashOracle Unit :=
  match storageEntries first, storageEntries second with
  | .ok entries₁, .ok entries₂ =>
    (first.keys ++ second.keys).forM fun key =>
      queryWitnesses ⟨true, entries₁⟩ ⟨true, entries₂⟩ ⟨key.toArray⟩
  | _, _ => pure ()

/-- What the storage experiment reports: the two storages and their roots under the oracle. -/
structure StorageOutcome where
  /-- The first storage of the adversary. -/
  first : Storage
  /-- The second storage of the adversary. -/
  second : Storage
  /-- The root of the first storage under the oracle. -/
  firstRoot : Except TrieError Hash32
  /-- The root of the second storage under the oracle. -/
  secondRoot : Except TrieError Hash32

/-- The part of the storage experiment after the adversary, which only calls the hash oracle.

It computes both roots, then queries every input of the storage search. -/
def extractStorage (first second : Storage) : OracleComp HashOracle StorageOutcome := do
  let firstRoot ← (storageRootM queryHash first).run
  let secondRoot ← (storageRootM queryHash second).run
  queryStorageWitnesses first second
  return ⟨first, second, firstRoot, secondRoot⟩

/-- The storage experiment: the adversary picks two storages, then the extraction runs. -/
def storageExperiment (adversary : OracleComp (unifSpec + HashOracle) (Storage × Storage)) :
    OracleComp (unifSpec + HashOracle) StorageOutcome :=
  experimentWith (fun claim => extractStorage claim.1 claim.2) adversary

/-- The adversary wins: two storages with one root give a key two words.

An unset key has the word `0`. -/
def StorageWins (outcome : StorageOutcome) : Prop :=
  (∃ root, outcome.firstRoot = .ok root ∧ outcome.secondRoot = .ok root) ∧
    ∃ key, outcome.first.getD key 0 ≠ outcome.second.getD key 0

/-- A replayed storage query caches both inputs of each pair that the storage search returns.

Each pair it returns under a table that agrees with the cache is then a collision of the cache. -/
theorem collision_of_queryStorageWitnesses {cache : HashOracle.QueryCache}
    {f : QueryImpl HashOracle Id} (hf : cache.AgreesWithFn f) {first second : Storage} {u : Unit}
    (hrun : simulateQ cache.toPartialImpl (queryStorageWitnesses first second) = some u)
    {pair : ByteArray × ByteArray}
    (hfind : findStorageCollision (fun x => f x) first second = some pair) : Collision cache := by
  unfold findStorageCollision at hfind
  unfold queryStorageWitnesses at hrun
  split at hfind
  · rename_i entries₁ entries₂ h₁ h₂
    simp only [h₁, h₂] at hrun
    obtain ⟨key, hkey, hfound⟩ := List.exists_of_findSome?_eq_some hfind
    split at hfound
    · -- The search returns a pair of the witnesses at a key, which the replay cached.
      obtain ⟨_, hwitnesses⟩ := replay_forM _ _ hrun key hkey
      have hcached := cached_of_queryWitnesses hf hwitnesses
      obtain ⟨hmem₁, hmem₂⟩ := mem_witnesses_of_findSecuredCollision _ hfound
      obtain ⟨hne, heq⟩ := findSecuredCollision_valid _ hfound
      exact collision_of_cached hne heq (hcached _ hmem₁) (hcached _ hmem₂)
    · cases hfound
  · cases hfind

/-- A replayed winning storage extraction exposes a collision of the cache. -/
theorem collision_of_extractStorage {cache : HashOracle.QueryCache} {first second : Storage}
    {outcome : StorageOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractStorage first second) = some outcome)
    (hwins : StorageWins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extractStorage, simulateQ_bind] at hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, hwitnesses, -⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [extractStorage, evalWithAnswerFn_bind, evalWithAnswerFn_storageRootM,
    evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨⟨root', hroot₁, hroot₂⟩, key, hkey⟩ := hwins
  -- Two storages with one root and two words at a key leave the search a collision.
  rcases storageRoot_binding (fun x => f x) hroot₁ hroot₂ with hwords | ⟨_, hfind, -⟩
  · exact absurd (hwords key) hkey
  · exact collision_of_queryStorageWitnesses hf hwitnesses hfind

/-- Two storages with one root that give a key two words: probability at most `Q^2 / 2^256`.

Each answer of the oracle is 32 uniform bytes. -/
theorem prEvent_storageWins_le
    (adversary : OracleComp (unifSpec + HashOracle) (Storage × Storage)) {Q : Nat}
    -- `Q` bounds the oracle calls of the whole experiment, repeats included.
    --
    -- It counts the adversary's calls, the two roots, and the queries at each key of the storages.
    --
    -- At each key the extraction rebuilds both proofs, so its calls grow as the square of the size.
    (hQ : IsQueryBoundP (storageExperiment adversary) (fun t => t.isRight = true) Q) :
    -- The oracle cache starts empty, and the adversary's private sampling is not counted.
    Pr{let z ← (simulateQ HashOracle.romImpl (storageExperiment adversary)).run ∅}[
      StorageWins z.1] ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_experimentWith_le (fun claim : Storage × Storage =>
    extractStorage claim.1 claim.2) StorageWins
    (fun hrun hwins => collision_of_extractStorage hrun hwins) adversary hQ
  rwa [card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound

/-! ## Two states with one root -/

/-- Queries every input of the state search, at each address of either state.

These are the binding inputs of the state tries at the address, then those of its two storages.

States whose entries do not encode have no root, and need no further query. -/
def queryStateWitnesses (first second : State) : OracleComp HashOracle Unit := do
  let entries₁ ← (stateEntriesM queryHash first).run
  let entries₂ ← (stateEntriesM queryHash second).run
  match entries₁, entries₂ with
  | .ok entries₁, .ok entries₂ =>
    (first.accounts.keys ++ second.accounts.keys).forM fun address => do
      queryWitnesses ⟨true, entries₁⟩ ⟨true, entries₂⟩ ⟨address.toArray⟩
      queryStorageWitnesses (first.storage.getD address ∅) (second.storage.getD address ∅)
  | _, _ => pure ()

/-- What the state experiment reports: the two states and their roots under the oracle. -/
structure StateOutcome where
  /-- The first state of the adversary. -/
  first : State
  /-- The second state of the adversary. -/
  second : State
  /-- The root of the first state under the oracle. -/
  firstRoot : Except TrieError Hash32
  /-- The root of the second state under the oracle. -/
  secondRoot : Except TrieError Hash32

/-- The part of the state experiment after the adversary, which only calls the hash oracle.

It computes both roots, then queries every input of the state search. -/
def extractState (first second : State) : OracleComp HashOracle StateOutcome := do
  let firstRoot ← (stateRootM queryHash first).run
  let secondRoot ← (stateRootM queryHash second).run
  queryStateWitnesses first second
  return ⟨first, second, firstRoot, secondRoot⟩

/-- The state experiment: the adversary picks two states, then the extraction runs. -/
def stateExperiment (adversary : OracleComp (unifSpec + HashOracle) (State × State)) :
    OracleComp (unifSpec + HashOracle) StateOutcome :=
  experimentWith (fun claim => extractState claim.1 claim.2) adversary

/-- The adversary wins: two states with one root differ at an address.

They give it two accounts.

Or the first state has an account there, and the two storages give a key two words. -/
def StateWins (outcome : StateOutcome) : Prop :=
  (∃ root, outcome.firstRoot = .ok root ∧ outcome.secondRoot = .ok root) ∧
    ∃ address, outcome.first.accounts[address]? ≠ outcome.second.accounts[address]? ∨
      address ∈ outcome.first.accounts ∧ ∃ key,
        (outcome.first.storage.getD address ∅).getD key 0 ≠
          (outcome.second.storage.getD address ∅).getD key 0

/-- A replayed state query caches both inputs of each pair that the state search returns.

Each pair it returns under a table that agrees with the cache is then a collision of the cache. -/
theorem collision_of_queryStateWitnesses {cache : HashOracle.QueryCache}
    {f : QueryImpl HashOracle Id} (hf : cache.AgreesWithFn f) {first second : State} {u : Unit}
    (hrun : simulateQ cache.toPartialImpl (queryStateWitnesses first second) = some u)
    {pair : ByteArray × ByteArray}
    (hfind : findStateCollision (fun x => f x) first second = some pair) : Collision cache := by
  simp only [queryStateWitnesses, simulateQ_bind] at hrun
  obtain ⟨entries₁, hentries₁, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨entries₂, hentries₂, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  -- The replayed entries are the entries with the table, which agrees with the cache.
  have h₁ := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hentries₁
  have h₂ := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hentries₂
  rw [evalWithAnswerFn_stateEntriesM] at h₁ h₂
  unfold findStateCollision at hfind
  rw [h₁, h₂] at hfind
  rcases entries₁ with _ | e₁
  · simp at hfind
  rcases entries₂ with _ | e₂
  · simp at hfind
  simp only at hfind hrun
  · obtain ⟨address, haddress, hfound⟩ := List.exists_of_findSome?_eq_some hfind
    -- The replay queried the witnesses of the state tries and of the storages at the address.
    obtain ⟨_, hstep⟩ := replay_forM _ _ hrun address haddress
    simp only [simulateQ_bind] at hstep
    obtain ⟨_, hwitnesses, hstorage⟩ := Option.bind_eq_some_iff.mp hstep
    have hsecured : ∀ {pair}, findSecuredCollision (fun x => f x) e₁ e₂ ⟨address.toArray⟩ =
        some pair → Collision cache := fun hfound => by
      obtain ⟨hmem₁, hmem₂⟩ := mem_witnesses_of_findSecuredCollision _ hfound
      obtain ⟨hne, heq⟩ := findSecuredCollision_valid _ hfound
      have hcached := cached_of_queryWitnesses hf hwitnesses
      exact collision_of_cached hne heq (hcached _ hmem₁) (hcached _ hmem₂)
    split at hfound
    · exact hsecured hfound
    · split at hfound
      · split at hfound
        · split at hfound
          · exact hsecured hfound
          · exact collision_of_queryStorageWitnesses hf hstorage hfound
        · cases hfound
      · cases hfound

/-- A replayed winning state extraction exposes a collision of the cache. -/
theorem collision_of_extractState {cache : HashOracle.QueryCache} {first second : State}
    {outcome : StateOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractState first second) = some outcome)
    (hwins : StateWins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extractState, simulateQ_bind] at hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨_, hwitnesses, -⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [extractState, evalWithAnswerFn_bind, evalWithAnswerFn_stateRootM,
    evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨⟨root', hroot₁, hroot₂⟩, address, hdiff⟩ := hwins
  -- Two states with one root that differ at an address leave the search a collision.
  rcases stateRoot_binding (fun x => f x) hroot₁ hroot₂ with hsame | ⟨_, hfind, -⟩
  · obtain ⟨haccount, hwords⟩ := hsame address
    rcases hdiff with hne | ⟨hmem, key, hkey⟩
    · exact absurd haccount hne
    · exact absurd (hwords hmem key) hkey
  · exact collision_of_queryStateWitnesses hf hwitnesses hfind

/-- Two states with one root that differ at an address: probability at most `Q^2 / 2^256`.

Each answer of the oracle is 32 uniform bytes. -/
theorem prEvent_stateWins_le
    (adversary : OracleComp (unifSpec + HashOracle) (State × State)) {Q : Nat}
    -- `Q` bounds the oracle calls of the whole experiment, repeats included.
    --
    -- It counts the adversary's calls, the two roots, the entries again, and the address queries.
    --
    -- At each address the extraction rebuilds proofs, so its calls grow as the square of the size.
    (hQ : IsQueryBoundP (stateExperiment adversary) (fun t => t.isRight = true) Q) :
    -- The oracle cache starts empty, and the adversary's private sampling is not counted.
    Pr{let z ← (simulateQ HashOracle.romImpl (stateExperiment adversary)).run ∅}[
      StateWins z.1] ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_experimentWith_le (fun claim : State × State =>
    extractState claim.1 claim.2) StateWins
    (fun hrun hwins => collision_of_extractState hrun hwins) adversary hQ
  rwa [card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound

end EthLib.Execution.State.RandomOracle
