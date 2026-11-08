module

public import EthLib.Execution.Proofs.Trie.Binding
public import EthLib.Cryptography.Proofs.Merkle.RandomOracle
public import EthLib.Cryptography.Proofs.ExceptTAnswers
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Proofs: the trie root in the random oracle model

The hash of the trie is modelled as one random oracle, shared by every node and every key.

An adversary that makes queries outputs two tries and a key.

Then the experiment computes both roots and both proofs of the key with the same oracle.

It also queries the key, every key of both tries, and every node of both proofs.

The adversary wins when two tries of one kind, each with distinct keys, have one root.

They must also give the key different values.

Each win exposes two different queried inputs with one answer, found by the binding searches.

So the birthday bound of the oracle bounds the probability of a win.

The bound counts every query of the experiment, the adversary's and the extraction's.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2.

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Execution.Trie.RandomOracle

open EthLib.Base
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography (evalWithAnswerFn_exceptT_bind evalWithAnswerFn_exceptT_pure
  evalWithAnswerFn_exceptT_throw evalWithAnswerFn_exceptT_lift evalWithAnswerFn_exceptT_liftExcept
  evalWithAnswerFn_exceptT_adapt)
open EthLib.Cryptography.Merkle.RandomOracle (Collision prEvent_collision_le)

/-- The hash of the trie as one oracle from byte strings to 32-byte digests. -/
abbrev HashOracle : OracleSpec ByteArray := ByteArray →ₒ Hash32

/-- One call to the hash oracle. -/
def queryHash (x : ByteArray) : OracleComp HashOracle Hash32 :=
  liftM (HashOracle.query x)

/-- What the experiment reports: the two tries, the key, and the two roots under the oracle. -/
structure Outcome where
  /-- The first trie of the adversary. -/
  first : Trie
  /-- The second trie of the adversary. -/
  second : Trie
  /-- The key on which the adversary claims the tries differ. -/
  key : ByteArray
  /-- The root of the first trie under the oracle. -/
  firstRoot : Except TrieError Hash32
  /-- The root of the second trie under the oracle. -/
  secondRoot : Except TrieError Hash32

/-- Every input whose hash the binding searches compare.

These are the key, the keys of both tries, and the nodes of both proofs of the key. -/
def witnesses (first second : Trie) (key : ByteArray)
    (firstProof secondProof : Except TrieError (List ByteArray)) : List ByteArray :=
  key :: (first.data.map Prod.fst ++ second.data.map Prod.fst ++
    (firstProof.toOption.getD []) ++ (secondProof.toOption.getD []))

/-- The part of the experiment after the adversary, which only calls the hash oracle.

It computes both roots and both proofs, then queries every input of the binding searches. -/
def extract (first second : Trie) (key : ByteArray) : OracleComp HashOracle Outcome := do
  let firstRoot ← (rootM queryHash first).run
  let secondRoot ← (rootM queryHash second).run
  let firstProof ← (getProofM queryHash first key).run
  let secondProof ← (getProofM queryHash second key).run
  let _ ← (witnesses first second key firstProof secondProof).mapM queryHash
  return ⟨first, second, key, firstRoot, secondRoot⟩

/-- The experiment: the adversary picks two tries and a key, then the extraction runs. -/
def experiment (adversary : OracleComp (unifSpec + HashOracle) (Trie × Trie × ByteArray)) :
    OracleComp (unifSpec + HashOracle) Outcome := do
  let (first, second, key) ← adversary
  liftComp (extract first second key) (unifSpec + HashOracle)

/-- The adversary wins: two tries with distinct keys share a root but give the key two values.

Both tries must be secured or both plain, so that they hash their keys alike. -/
def Wins (outcome : Outcome) : Prop :=
  outcome.first.secured = outcome.second.secured ∧
    (outcome.first.data.map Prod.fst).Nodup ∧ (outcome.second.data.map Prod.fst).Nodup ∧
    (∃ root, outcome.firstRoot = .ok root ∧ outcome.secondRoot = .ok root) ∧
    trieGet outcome.first outcome.key ≠ trieGet outcome.second outcome.key

/-! ## The deterministic step -/

/-- The first key of a list with the path of a given key, but different from it.

Only a secured trie can have one, as a key with the hash of the given key. -/
def findLookupCollision (hash : ByteArray → Hash32) (key : ByteArray) :
    List ByteArray → Option (ByteArray × ByteArray)
  | [] => none
  | other :: rest =>
    if other ≠ key ∧ hash other = hash key then some (other, key)
    else findLookupCollision hash key rest

/-- Every pair that the search returns is a collision of a listed key with the given key. -/
theorem findLookupCollision_valid (hash : ByteArray → Hash32) (key : ByteArray) :
    (keys : List ByteArray) → {pair : ByteArray × ByteArray} →
      findLookupCollision hash key keys = some pair →
        pair.1 ∈ keys ∧ pair.2 = key ∧ IsCollision hash pair
  | [], _, h => by cases h
  | other :: rest, pair, h => by
    simp only [findLookupCollision] at h
    split at h
    · rename_i hfound
      cases h
      exact ⟨List.mem_cons_self, rfl, hfound⟩
    · obtain ⟨hmem, hkey, hvalid⟩ := findLookupCollision_valid hash key rest h
      exact ⟨List.mem_cons_of_mem _ hmem, hkey, hvalid⟩

/-- A list that holds only the given key has no lookup collision, so the search can fail. -/
theorem findLookupCollision_self (hash : ByteArray → Hash32) (key : ByteArray) (count : Nat) :
    findLookupCollision hash key (List.replicate count key) = none := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, findLookupCollision, ih]

/-- A failed search leaves no listed key other than the given key with its hash. -/
theorem hash_ne_of_findLookupCollision (hash : ByteArray → Hash32) (key : ByteArray) :
    (keys : List ByteArray) → findLookupCollision hash key keys = none →
      ∀ other ∈ keys, other ≠ key → hash other ≠ hash key
  | [], _, _, hmem, _ => by cases hmem
  | first :: rest, h, other, hmem, hne => by
    simp only [findLookupCollision] at h
    split at h
    · cases h
    · rename_i hfound
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact fun heq => hfound ⟨hne, heq⟩
      · exact hash_ne_of_findLookupCollision hash key rest h other hmem hne

/-- With no lookup collision, the value found by path is the value of the key.

An absent key has no value, and reads as the empty byte string. -/
theorem valueAt_getD (hash : ByteArray → Hash32) {trie : Trie} (key : ByteArray)
    (hsearch : trie.secured = true → findLookupCollision hash key (trie.data.map Prod.fst) = none) :
    (valueAt hash trie key).getD .empty = trieGet trie key := by
  unfold valueAt trieGet
  -- On every listed key, one path with the key means the key itself.
  rw [find?_congr trie.data fun entry hmem => ?_]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, sameBytes_iff]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [keyPath_eq, keyPath_eq] at h
  have hbytes := bytesToNibbleList_injective h
  cases hsecured : trie.secured with
  | false => simpa [hsecured] using hbytes
  | true =>
    simp only [hsecured, ↓reduceIte] at hbytes
    by_contra hne
    exact hash_ne_of_findLookupCollision hash key _ (hsearch hsecured) entry.1
      (List.mem_map_of_mem hmem) hne (hashBytes_injective hbytes)

/-! ## The oracle run against a table -/

/-- The vector map with errors, run against a table, maps the runs. -/
theorem evalWithAnswerFn_mapMVector {ι : Type} {spec : OracleSpec ι} (f : QueryImpl spec Id)
    {ε α β : Type} (g : α → ExceptT ε (OracleComp spec) β) :
    (xs : List α) → evalWithAnswerFn f (mapMVector g xs).run =
      mapMVector (fun x => evalWithAnswerFn f (g x).run) xs
  | [] => rfl
  | x :: rest => by
    simp only [mapMVector, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_mapMVector f g rest,
      evalWithAnswerFn_exceptT_pure]
    rfl

/-- The path of a key, run against a table, is the path with that table as the hash. -/
theorem evalWithAnswerFn_keyPathM (f : QueryImpl HashOracle Id) (secured : Bool)
    (key : ByteArray) :
    evalWithAnswerFn f (keyPathM queryHash secured key) = keyPath (fun x => f x) secured key := by
  cases secured <;> rfl

/-- The prepared data, run against a table, is the data prepared with that table. -/
theorem evalWithAnswerFn_prepareDataM (f : QueryImpl HashOracle Id) (secured : Bool)
    (data : List (ByteArray × ByteArray)) :
    evalWithAnswerFn f (prepareDataM queryHash data secured).run =
      prepareData (fun x => f x) data secured := by
  rw [prepareData_eq]
  induction data with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨preimage, value⟩ := entry
    simp only [prepareDataM, List.mapM_cons] at ih ⊢
    simp only [evalWithAnswerFn_exceptT_bind, ih, evalWithAnswerFn_exceptT_pure]
    by_cases hvalue : value.size = 0
    · simp only [hvalue, ↓reduceIte]
      rfl
    · simp only [hvalue, ↓reduceIte, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_lift,
        evalWithAnswerFn_keyPathM, evalWithAnswerFn_exceptT_pure]
      rfl

/-- Holding a node, run against a table, holds it with that table as the hash. -/
theorem evalWithAnswerFn_encodeInternalNodeM (f : QueryImpl HashOracle Id)
    (node : Option InternalNode) :
    evalWithAnswerFn f (encodeInternalNodeM queryHash node).run =
      encodeInternalNode (fun x => f x) node := by
  rw [encodeInternalNode_eq]
  simp only [encodeInternalNodeM, evalWithAnswerFn_exceptT_bind,
    evalWithAnswerFn_exceptT_liftExcept]
  cases Serialization.Rlp.encode (unencoded node) with
  | error => rfl
  | ok encoded =>
    by_cases hsize : encoded.size < 32 <;>
      simp only [Except.bind, Bind.bind, hsize, ↓reduceIte] <;> rfl

/-- One step of the composition, run against a table, is the step with that table as the hash.

The nested calls must run to the nested calls of the plain step. -/
theorem evalWithAnswerFn_patricializeStepM (f : QueryImpl HashOracle Id)
    {recurse : List (List Nibble × ByteArray) → Nat →
      ExceptT Serialization.Rlp.RlpError (OracleComp HashOracle) (Option InternalNode)}
    {recurse' : List (List Nibble × ByteArray) → Nat →
      Except Serialization.Rlp.RlpError (Option InternalNode)}
    (hrecurse : ∀ obj level, evalWithAnswerFn f (recurse obj level).run = recurse' obj level)
    (obj : List (List Nibble × ByteArray)) (level : Nat) :
    evalWithAnswerFn f (patricializeStepM queryHash recurse obj level).run =
      patricializeStep (fun x => f x) recurse' obj level := by
  match obj with
  | [] => rfl
  | [_] => rfl
  | first :: second :: rest =>
    rw [patricializeStep_cons_cons]
    simp only [patricializeStepM]
    split
    · simp only [evalWithAnswerFn_exceptT_bind, hrecurse, evalWithAnswerFn_encodeInternalNodeM,
        evalWithAnswerFn_exceptT_pure]
      rfl
    · simp only [evalWithAnswerFn_exceptT_bind, hrecurse, evalWithAnswerFn_encodeInternalNodeM,
        evalWithAnswerFn_exceptT_pure, evalWithAnswerFn_mapMVector]
      rfl

/-- The composition with a budget, run against a table, is the composition with that table. -/
theorem evalWithAnswerFn_patricializeAuxM (f : QueryImpl HashOracle Id) :
    (fuel : Nat) → (obj : List (List Nibble × ByteArray)) → (level : Nat) →
      evalWithAnswerFn f (patricializeAuxM queryHash fuel obj level).run =
        patricializeAux (fun x => f x) fuel obj level
  | 0 => evalWithAnswerFn_patricializeStepM f (fun _ _ => rfl)
  | fuel + 1 => evalWithAnswerFn_patricializeStepM f (evalWithAnswerFn_patricializeAuxM f fuel)

/-- The composition, run against a table, is the composition with that table as the hash. -/
theorem evalWithAnswerFn_patricializeM (f : QueryImpl HashOracle Id)
    (obj : List (List Nibble × ByteArray)) (level : Nat) :
    evalWithAnswerFn f (patricializeM queryHash obj level).run =
      patricialize (fun x => f x) obj level :=
  evalWithAnswerFn_patricializeAuxM f _ obj level

/-- The proof below a node, run against a table, is the proof with that table as the hash. -/
theorem evalWithAnswerFn_proofBelowM (f : QueryImpl HashOracle Id) :
    (fuel : Nat) → (obj : List (List Nibble × ByteArray)) → (level : Nat) → (path : List Nibble) →
      evalWithAnswerFn f (proofBelowM queryHash fuel obj level path).run =
        proofBelow (fun x => f x) fuel obj level path
  | 0, _, _, _ => rfl
  | fuel + 1, obj, level, path => by
    rw [proofBelow_succ]
    simp only [proofBelowM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_patricializeM]
    -- Both sides bind the same node, then follow the same child.
    show Except.bind _ _ = Except.bind _ _
    congr 1
    funext node
    rcases node with _ | (⟨_, _⟩ | ⟨keySegment, _⟩ | ⟨_, _⟩)
    · rfl
    · rfl
    · dsimp only
      split
      · simp only [evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_patricializeM,
          evalWithAnswerFn_exceptT_liftExcept, evalWithAnswerFn_proofBelowM f fuel,
          evalWithAnswerFn_exceptT_pure]
        rfl
      · rfl
    · cases path with
      | nil => rfl
      | cons nibble restOfPath =>
        simp only [evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_patricializeM,
          evalWithAnswerFn_exceptT_liftExcept, evalWithAnswerFn_proofBelowM f fuel,
          evalWithAnswerFn_exceptT_pure]
        rfl

/-- The trie root, run against a full answer table, is the root with that table as the hash. -/
theorem evalWithAnswerFn_rootM (f : QueryImpl HashOracle Id) (trie : Trie) :
    evalWithAnswerFn f (rootM queryHash trie).run = root (fun x => f x) trie := by
  simp only [rootM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_prepareDataM,
    evalWithAnswerFn_exceptT_adapt, evalWithAnswerFn_patricializeM,
    evalWithAnswerFn_exceptT_liftExcept, evalWithAnswerFn_exceptT_lift]
  rw [root_eq]
  rfl

/-- The proof of a key, run against a full answer table, is the proof with that table. -/
theorem evalWithAnswerFn_getProofM (f : QueryImpl HashOracle Id) (trie : Trie) (key : ByteArray) :
    evalWithAnswerFn f (getProofM queryHash trie key).run = getProof (fun x => f x) trie key := by
  simp only [getProofM, evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_prepareDataM,
    evalWithAnswerFn_exceptT_lift, evalWithAnswerFn_keyPathM, evalWithAnswerFn_exceptT_adapt,
    evalWithAnswerFn_patricializeM, evalWithAnswerFn_exceptT_liftExcept,
    evalWithAnswerFn_proofBelowM, evalWithAnswerFn_exceptT_pure]
  rw [getProof_eq]
  rfl

/-- A replayed run of queries on a list caches every input of the list. -/
theorem cached_of_mapM_queryHash {cache : HashOracle.QueryCache} :
    (inputs : List ByteArray) → {answers : List Hash32} →
      simulateQ cache.toPartialImpl (inputs.mapM queryHash) = some answers →
        ∀ x ∈ inputs, ∃ answer, cache x = some answer
  | [], _, _, _, hx => by cases hx
  | input :: rest, _, h, x, hx => by
    simp only [List.mapM_cons, simulateQ_bind, queryHash, simulateQ_spec_query,
      QueryCache.toPartialImpl_apply] at h
    obtain ⟨answer, hanswer, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨answers, hanswers, -⟩ := Option.bind_eq_some_iff.mp h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨answer, hanswer⟩
    · exact cached_of_mapM_queryHash rest hanswers x hx

/-- A replayed extraction caches every input of the binding searches, with the table's answer. -/
theorem cached_of_extract {cache : HashOracle.QueryCache} {f : QueryImpl HashOracle Id}
    (hf : cache.AgreesWithFn f) {first second : Trie} {key : ByteArray} {outcome : Outcome}
    (hrun : simulateQ cache.toPartialImpl (extract first second key) = some outcome) :
    ∀ x ∈ witnesses first second key (getProof (fun x => f x) first key)
      (getProof (fun x => f x) second key), cache x = some (f x) := by
  simp only [extract, simulateQ_bind] at hrun
  obtain ⟨firstRoot, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨secondRoot, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨firstProof, hfirst, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨secondProof, hsecond, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨answers, hanswers, -⟩ := Option.bind_eq_some_iff.mp hrun
  -- The replayed proofs are the proofs with the table, which agrees with the cache.
  have hfirst' := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hfirst
  have hsecond' := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hsecond
  rw [evalWithAnswerFn_getProofM] at hfirst' hsecond'
  rw [hfirst', hsecond']
  intro x hx
  obtain ⟨answer, hanswer⟩ := cached_of_mapM_queryHash _ hanswers x hx
  rw [hanswer, hf hanswer]

/-- A replayed winning extraction exposes a collision of the cache.

The binding searches of the trie find it, run with a table that extends the cache. -/
theorem collision_of_extract {cache : HashOracle.QueryCache} {first second : Trie}
    {key : ByteArray} {outcome : Outcome}
    (hrun : simulateQ cache.toPartialImpl (extract first second key) = some outcome)
    (hwins : Wins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hcached := cached_of_extract hf hrun
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extract, evalWithAnswerFn_bind, evalWithAnswerFn_rootM, evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨hsecured, hkeys₁, hkeys₂, ⟨root', hroot₁, hroot₂⟩, hget⟩ := hwins
  dsimp only at hsecured hkeys₁ hkeys₂ hroot₁ hroot₂ hget
  -- Two different witnesses with one answer of the table are a collision of the cache.
  have hcollision : ∀ x y, x ∈ witnesses first second key (getProof (fun x => f x) first key)
      (getProof (fun x => f x) second key) →
      y ∈ witnesses first second key (getProof (fun x => f x) first key)
        (getProof (fun x => f x) second key) →
      IsCollision (fun x => f x) (x, y) → Collision cache :=
    fun x y hx hy hvalid =>
      ⟨x, y, f x, hvalid.1, hcached x hx, (hcached y hy).trans (congrArg some hvalid.2.symm)⟩
  -- A key of either trie with the hash of the key is such a collision.
  have hlookup : ∀ trie : Trie, (∀ k ∈ trie.data.map Prod.fst,
      k ∈ witnesses first second key (getProof (fun x => f x) first key)
        (getProof (fun x => f x) second key)) →
      (trie.secured = true →
        findLookupCollision (fun x => f x) key (trie.data.map Prod.fst) = none) ∨
      Collision cache := by
    intro trie hsub
    cases hsearch : findLookupCollision (fun x => f x) key (trie.data.map Prod.fst) with
    | none => exact .inl fun _ => rfl
    | some pair =>
      obtain ⟨hmem, hkey, hvalid⟩ := findLookupCollision_valid _ key _ hsearch
      refine .inr (hcollision pair.1 pair.2 (hsub _ hmem) ?_ hvalid)
      rw [hkey]
      exact List.mem_cons_self
  rcases root_binding (fun x => f x) hsecured hroot₁ hroot₂ hkeys₁ hkeys₂ key with
    hvalue | ⟨pair, hfind, hvalid⟩ | ⟨pair, hfind, hvalid⟩ | ⟨pair, hfind, hvalid⟩
  · -- One value at the key's path: unless a lookup collision, both tries give the key one value.
    rcases hlookup first (fun k hk => by simp [witnesses, hk]) with hsearch₁ | hc
    · rcases hlookup second (fun k hk => by simp [witnesses, hk]) with hsearch₂ | hc
      · rw [← valueAt_getD (fun x => f x) key hsearch₁,
          ← valueAt_getD (fun x => f x) key hsearch₂, hvalue] at hget
        exact absurd rfl hget
      · exact hc
    · exact hc
  · -- Two different nodes of the proofs with one hash.
    unfold findCollision at hfind
    split at hfind
    · rename_i p q hp hq
      obtain ⟨hmem₁, hmem₂⟩ := mem_of_findProofCollision _ p q hfind
      exact hcollision pair.1 pair.2 (by simp [witnesses, hp, hq, Except.toOption, hmem₁])
        (by simp [witnesses, hp, hq, Except.toOption, hmem₂]) hvalid
    · cases hfind
  · -- Two keys of the first trie with one hash.
    unfold findPathCollision at hfind
    split at hfind
    · obtain ⟨hmem₁, hmem₂⟩ := mem_of_findKeyCollision _ _ hfind
      exact hcollision pair.1 pair.2 (by simp [witnesses, hmem₁]) (by simp [witnesses, hmem₂])
        hvalid
    · cases hfind
  · -- Two keys of the second trie with one hash.
    unfold findPathCollision at hfind
    split at hfind
    · obtain ⟨hmem₁, hmem₂⟩ := mem_of_findKeyCollision _ _ hfind
      exact hcollision pair.1 pair.2 (by simp [witnesses, hmem₁]) (by simp [witnesses, hmem₂])
        hvalid
    · cases hfind

/-! ## The bound -/

/-- There are `2^256` digests. -/
theorem card_hash32 : Nat.card Hash32 = 2 ^ 256 := by
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 32), Nat.card_fun,
    Nat.card_eq_fintype_card (α := UInt8), ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8]
  simp

/-- Two tries of one kind, each with distinct keys and one root, that give a key different values.

The probability is at most `Q^2 / N`, where `N` is the number of digests.

`Q` bounds the oracle calls of the whole experiment, repeats included.

The extraction makes many of them, since each proof level rebuilds its subtree.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_wins_le [SampleableType Hash32]
    (adversary : OracleComp (unifSpec + HashOracle) (Trie × Trie × ByteArray)) {Q : Nat}
    (hQ : IsQueryBoundP (experiment adversary) (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl (experiment adversary)).run ∅}[Wins z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card Hash32) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_collision_le (experiment adversary) hQ)
  intro z hz hwins
  simp only [experiment, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨⟨first, second, key⟩, cache⟩, -, hz⟩ := hz
  -- The extraction calls only the hash, which the random oracle answers with caching.
  rw [QueryImpl.simulateQ_add_liftComp_right] at hz
  -- The final cache replays the extraction without sampling again.
  have hreplay := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    _ (extract first second key) hz
  exact collision_of_extract hreplay hwins

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_wins_le_two_pow
    (adversary : OracleComp (unifSpec + HashOracle) (Trie × Trie × ByteArray)) {Q : Nat}
    (hQ : IsQueryBoundP (experiment adversary) (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl (experiment adversary)).run ∅}[Wins z.1] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_wins_le adversary hQ
  rw [card_hash32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

end EthLib.Execution.Trie.RandomOracle
