module

public import EthLib.Base.Hash32
public import EthLib.Serialization.Proofs.Ssz.Codec.Binding
public import EthLib.Cryptography.Proofs.Merkle.RandomOracle.Collision
public import EthLib.Cryptography.Proofs.ExceptTAnswers
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Proofs: the SSZ root in the random oracle model

The node hash of SSZ is modelled as one random oracle with 32-byte answers.

This module bounds the probability of two different values of one type with one root.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2.

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Serialization.Ssz.RandomOracle

open EthLib.Base
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography (evalWithAnswerFn_exceptT_bind evalWithAnswerFn_exceptT_pure
  evalWithAnswerFn_exceptT_throw evalWithAnswerFn_exceptT_lift evalWithAnswerFn_exceptT_liftExcept
  evalWithAnswerFn_exceptT_mapM)
open EthLib.Cryptography.Merkle.RandomOracle (Collision experimentWith prEvent_experimentWith_le)

/-- The node hash as one oracle from byte strings to 32-byte digests. -/
abbrev HashOracle : OracleSpec ByteArray := ByteArray →ₒ Hash32

/-- One call to the node hash oracle, with its digest as bytes. -/
def queryHash (x : ByteArray) : OracleComp HashOracle ByteArray := do
  let digest ← liftM (HashOracle.query x)
  return ⟨digest.toArray⟩

/-- The hasher of the oracle: every hash and every zero root is computed with oracle calls. -/
def oracleHasher : Hasher (OracleComp HashOracle) :=
  Hasher.ofHash queryHash

/-- The root and the hash inputs of an expanded computation, with each node hashed again. -/
def rehash : CommitmentTree → OracleComp HashOracle (Bytes × List Bytes)
  | .leaf node => pure (node, [])
  | .fork left right => do
    let (leftRoot, leftMessages) ← rehash left
    let (rightRoot, rightMessages) ← rehash right
    let parent ← combineM queryHash leftRoot rightRoot
    return (parent, (leftRoot ++ rightRoot) :: (leftMessages ++ rightMessages))

/-- What the experiment reports: the two values and their roots under the oracle. -/
structure Outcome where
  /-- The first value of the adversary. -/
  first : Value
  /-- The second value of the adversary. -/
  second : Value
  /-- The root of the first value under the oracle. -/
  firstRoot : Except Err Bytes
  /-- The root of the second value under the oracle. -/
  secondRoot : Except Err Bytes

/-- The part of the experiment after the adversary, which only calls the oracle.

It computes both roots, then hashes every node of both expanded computations again. -/
def extract (shape : Desc) (first second : Value) : OracleComp HashOracle Outcome := do
  let firstRoot ← (hashTreeRootM oracleHasher shape first).run
  let secondRoot ← (hashTreeRootM oracleHasher shape second).run
  match valueTree shape first, valueTree shape second with
  | .ok firstTree, .ok secondTree => do
    let _ ← rehash firstTree
    let _ ← rehash secondTree
  | _, _ => pure ()
  return ⟨first, second, firstRoot, secondRoot⟩

/-- The experiment: the adversary picks two values of the type, then the extraction runs. -/
def experiment (shape : Desc) (adversary : OracleComp (unifSpec + HashOracle) (Value × Value)) :
    OracleComp (unifSpec + HashOracle) Outcome :=
  experimentWith (fun pair => extract shape pair.1 pair.2) adversary

/-- The adversary wins: two different values that fit one well-formed type have one root.

Every variable-size count must fit the 256-bit word mixed into its root. -/
def Wins (shape : Desc) (outcome : Outcome) : Prop :=
  shape.wellFormed = .ok () ∧ Fits shape outcome.first ∧ Fits shape outcome.second ∧
    CommitmentSized shape outcome.first ∧ CommitmentSized shape outcome.second ∧
    outcome.first ≠ outcome.second ∧
    ∃ root, outcome.firstRoot = .ok root ∧ outcome.secondRoot = .ok root

/-- The node hash that a full answer table gives, with its digests as bytes. -/
def tableHash (f : QueryImpl HashOracle Id) (x : ByteArray) : ByteArray :=
  ⟨(f x).toArray⟩

/-- Every digest of a full answer table is 32 bytes. -/
theorem tableHash_size (f : QueryImpl HashOracle Id) (x : ByteArray) : (tableHash f x).size = 32 :=
  (f x).size_toArray

/-- One query, run against a full answer table, is the table's digest as bytes. -/
theorem evalWithAnswerFn_queryHash (f : QueryImpl HashOracle Id) (x : ByteArray) :
    evalWithAnswerFn f (queryHash x) = tableHash f x := by
  simp [queryHash, tableHash]

/-- A parent fold, run against a full answer table, is the fold with that table. -/
theorem evalWithAnswerFn_combineM (f : QueryImpl HashOracle Id) (left right : Bytes) :
    evalWithAnswerFn f (combineM queryHash left right) =
      (combineM (m := Id) (tableHash f) left right).run := by
  simp [combineM, evalWithAnswerFn_queryHash]
  rfl

/-- A zero root, run against a full answer table, is the zero root with that table. -/
theorem evalWithAnswerFn_zeroRootM (f : QueryImpl HashOracle Id) (depth : Nat) :
    evalWithAnswerFn f (zeroRootM (combineM queryHash) zeroChunk depth) =
      (zeroRootM (m := Id) (combineM (tableHash f)) zeroChunk depth).run := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    simp only [zeroRootM, evalWithAnswerFn_bind, ih, evalWithAnswerFn_combineM]
    rfl

/-- A perfect subtree, run against a full answer table, is the subtree with that table. -/
theorem evalWithAnswerFn_subtreeAtM (f : QueryImpl HashOracle Id) (chunks : Array Bytes)
    (depth start : Nat) :
    evalWithAnswerFn f (subtreeAtM oracleHasher chunks depth start) =
      (subtreeAtM (Hasher.ofHash (m := Id) (tableHash f)) chunks depth start).run := by
  induction depth generalizing start with
  | zero =>
    unfold subtreeAtM
    split
    · exact evalWithAnswerFn_zeroRootM f 0
    · rfl
  | succ depth ih =>
    unfold subtreeAtM
    split
    · exact evalWithAnswerFn_zeroRootM f _
    · simp only [oracleHasher, Hasher.ofHash] at ih
      simp only [evalWithAnswerFn_bind, ih, oracleHasher, Hasher.ofHash, evalWithAnswerFn_combineM]
      rfl

/-- A progressive spine, run against a full answer table, is the spine with that table. -/
theorem evalWithAnswerFn_merkleizeProgressiveUncheckedM (f : QueryImpl HashOracle Id)
    (chunks : List Bytes) (level : Nat) :
    evalWithAnswerFn f (merkleizeProgressiveUncheckedM oracleHasher chunks level) =
      (merkleizeProgressiveUncheckedM (Hasher.ofHash (m := Id) (tableHash f)) chunks
        level).run := by
  rw [merkleizeProgressiveUncheckedM_unfold oracleHasher chunks level,
    merkleizeProgressiveUncheckedM_unfold (Hasher.ofHash (m := Id) (tableHash f)) chunks level]
  split
  · rfl
  · rename_i hempty
    have hlen : (chunks.drop (4 ^ level)).length < chunks.length := by
      have : 0 < 4 ^ level := Nat.pos_of_neZero (4 ^ level)
      have : 0 < chunks.length := by
        cases chunks with
        | nil => simp at hempty
        | cons _ _ => simp
      simp only [List.length_drop]
      omega
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_subtreeAtM,
      evalWithAnswerFn_merkleizeProgressiveUncheckedM f (chunks.drop (4 ^ level)) (level + 1)]
    simp only [oracleHasher, Hasher.ofHash, evalWithAnswerFn_combineM]
    rfl
termination_by chunks.length

/-- A bounded tree, run against a full answer table, is the tree with that table. -/
theorem evalWithAnswerFn_merkleizeBoundedUncheckedM (f : QueryImpl HashOracle Id)
    (chunks : Array Bytes) (limit : Option Nat) :
    evalWithAnswerFn f (merkleizeBoundedUncheckedM oracleHasher chunks limit).run =
      (merkleizeBoundedUncheckedM (Hasher.ofHash (m := Id) (tableHash f)) chunks limit).run := by
  cases limit with
  | none =>
    simp only [merkleizeBoundedUncheckedM, evalWithAnswerFn_exceptT_lift,
      evalWithAnswerFn_subtreeAtM]
    rfl
  | some capacity =>
    simp only [merkleizeBoundedUncheckedM]
    split
    · rfl
    · simp only [evalWithAnswerFn_exceptT_lift, evalWithAnswerFn_subtreeAtM]
      rfl

/-- The leaves of a layout, run against a full answer table, are the leaves with that table.

The nested roots must run to the nested roots with the table. -/
theorem evalWithAnswerFn_layoutChunksAtM (f : QueryImpl HashOracle Id) (budget : Nat)
    (hroot : ∀ shape value,
      evalWithAnswerFn f (hashTreeRootAtM oracleHasher budget shape value).run =
        (hashTreeRootAtM (Hasher.ofHash (m := Id) (tableHash f)) budget shape value).run)
    (layout : MerkleLayout) (start : Nat) (stop : Option Nat) :
    evalWithAnswerFn f (layoutChunksAtM oracleHasher budget layout start stop).run =
      (layoutChunksAtM (Hasher.ofHash (m := Id) (tableHash f)) budget layout start stop).run := by
  rw [layoutChunksAtM_id_eq]
  simp only [layoutChunksAtM, layoutChunksWithM]
  cases layout.leaves with
  | packed chunks => rfl
  | nested values =>
    simp only [evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_mapM,
      evalWithAnswerFn_exceptT_pure]
    show Except.bind _ _ = Except.bind _ _
    congr 2
    funext slot
    rcases slot with _ | ⟨shape, value⟩
    · rfl
    · exact hroot shape value

/-- The root with a budget, run against a full answer table, is the root with that table. -/
theorem evalWithAnswerFn_hashTreeRootAtM (f : QueryImpl HashOracle Id) (budget : Nat)
    (shape : Desc) (value : Value) :
    evalWithAnswerFn f (hashTreeRootAtM oracleHasher budget shape value).run =
      (hashTreeRootAtM (Hasher.ofHash (m := Id) (tableHash f)) budget shape value).run := by
  induction budget generalizing shape value with
  | zero =>
    rw [hashTreeRootAtM_id_zero]
    simp only [hashTreeRootAtM]
    exact evalWithAnswerFn_exceptT_throw f _
  | succ budget ih =>
    rw [hashTreeRootAtM_id_succ]
    simp only [hashTreeRootAtM_succ, evalWithAnswerFn_exceptT_bind,
      evalWithAnswerFn_exceptT_liftExcept, evalWithAnswerFn_layoutChunksAtM f budget ih]
    show Except.bind _ _ = Except.bind _ _
    congr 1
    funext layout
    show Except.bind _ _ = Except.bind _ _
    congr 1
    funext chunks
    cases layout.limit <;> cases layout.mixin <;>
      simp only [evalWithAnswerFn_exceptT_bind, evalWithAnswerFn_exceptT_lift,
        evalWithAnswerFn_exceptT_pure, evalWithAnswerFn_merkleizeProgressiveUncheckedM,
        evalWithAnswerFn_merkleizeBoundedUncheckedM] <;>
      simp only [mixInM, oracleHasher, Hasher.ofHash, evalWithAnswerFn_combineM] <;>
      rfl

/-- The root under the oracle, run against a full answer table, is the root with that table. -/
theorem evalWithAnswerFn_hashTreeRootM (f : QueryImpl HashOracle Id) (shape : Desc)
    (value : Value) :
    evalWithAnswerFn f (hashTreeRootM oracleHasher shape value).run =
      (hashTreeRootM (Hasher.ofHash (m := Id) (tableHash f)) shape value).run :=
  evalWithAnswerFn_hashTreeRootAtM f shape.nesting shape value

/-- The rehash of a computation, run against a full answer table, gives its root and inputs. -/
theorem evalWithAnswerFn_rehash (f : QueryImpl HashOracle Id) (tree : CommitmentTree) :
    evalWithAnswerFn f (rehash tree) = (tree.root (tableHash f), tree.messages (tableHash f)) := by
  induction tree with
  | leaf node => rfl
  | fork left right ihLeft ihRight =>
    simp only [rehash, evalWithAnswerFn_bind, ihLeft, ihRight, evalWithAnswerFn_combineM,
      evalWithAnswerFn_pure, CommitmentTree.root, CommitmentTree.messages]

/-- A replayed query caches its input. -/
theorem cached_of_queryHash {cache : HashOracle.QueryCache} {x digest : ByteArray}
    (hrun : simulateQ cache.toPartialImpl (queryHash x) = some digest) :
    ∃ answer, cache x = some answer := by
  simp only [queryHash, simulateQ_bind, simulateQ_spec_query,
    QueryCache.toPartialImpl_apply] at hrun
  obtain ⟨answer, hanswer, -⟩ := Option.bind_eq_some_iff.mp hrun
  exact ⟨answer, hanswer⟩

/-- The answer of a replayed query is 32 bytes. -/
theorem size_of_queryHash {cache : HashOracle.QueryCache} {x digest : ByteArray}
    (hrun : simulateQ cache.toPartialImpl (queryHash x) = some digest) :
    digest.data.size = 32 := by
  simp only [queryHash, simulateQ_bind, simulateQ_spec_query,
    QueryCache.toPartialImpl_apply] at hrun
  obtain ⟨answer, -, hanswer⟩ := Option.bind_eq_some_iff.mp hrun
  simp at hanswer
  subst hanswer
  exact answer.size_toArray

/-- A replayed rehash caches every hash input of the computation. -/
theorem cached_of_rehash {cache : HashOracle.QueryCache} {tree : CommitmentTree}
    {result : Bytes × List Bytes}
    (hrun : simulateQ cache.toPartialImpl (rehash tree) = some result) :
    ∀ x ∈ result.2, ∃ digest, cache x = some digest := by
  induction tree generalizing result with
  | leaf node =>
    simp only [rehash, simulateQ_pure] at hrun
    cases hrun
    simp
  | fork left right ihLeft ihRight =>
    simp only [rehash, simulateQ_bind] at hrun
    obtain ⟨leftResult, hleft, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨rightResult, hright, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨parent, hparent, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    simp only [simulateQ_pure] at hrun
    cases hrun
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [combineM] at hparent
      exact cached_of_queryHash hparent
    · rcases List.mem_append.mp hx with hx | hx
      · exact ihLeft hleft x hx
      · exact ihRight hright x hx

/-- A fold of two nodes makes one oracle call. -/
theorem combineM_queryBound (left right : Bytes) :
    IsQueryBoundP (combineM queryHash left right) (fun _ => True) 1 := by
  simp [combineM, queryHash]

/-- The root of an all-zero subtree makes one oracle call per level. -/
theorem zeroRootM_queryBound (depth : Nat) :
    IsQueryBoundP (zeroRootM (combineM queryHash) zeroChunk depth) (fun _ => True) depth := by
  induction depth with
  | zero => trivial
  | succ depth ih => exact isQueryBoundP_bind ih fun below _ => combineM_queryBound below below

/-- The root of a perfect subtree makes at most one oracle call per inner node.

A half past the data is an all-zero subtree, whose one call per level is within that count. -/
theorem subtreeAtM_queryBound (chunks : Array Bytes) (depth start : Nat) :
    IsQueryBoundP (subtreeAtM oracleHasher chunks depth start) (fun _ => True)
      (2 ^ depth - 1) := by
  induction depth generalizing start with
  | zero =>
    unfold subtreeAtM
    split
    · exact zeroRootM_queryBound 0
    · trivial
  | succ depth ih =>
    have below : depth + 1 < 2 ^ (depth + 1) := Nat.lt_two_pow_self
    have half : 1 ≤ 2 ^ depth := Nat.one_le_two_pow
    unfold subtreeAtM
    split
    · exact (zeroRootM_queryBound (depth + 1)).mono (by omega)
    · refine (isQueryBoundP_bind (ih start) fun _ _ =>
        isQueryBoundP_bind (ih (start + 2 ^ depth)) fun _ _ =>
          combineM_queryBound _ _).mono ?_
      rw [Nat.pow_succ]
      omega

/-- A replayed subtree root caches every message of its perfect tree, with the answer of the table.

It needs the table to agree with the cache. -/
theorem cached_of_subtreeAtM {cache : HashOracle.QueryCache} {f : QueryImpl HashOracle Id}
    (hf : cache.AgreesWithFn f) {chunks : Array Bytes} {depth start : Nat} {root : Bytes}
    (hrun : simulateQ cache.toPartialImpl (subtreeAtM oracleHasher chunks depth start) =
      some root) :
    ∀ x ∈ (CommitmentTree.perfect depth fun i => padded zeroChunk chunks (start + i)).messages
        (tableHash f),
      cache x = some (f x) := by
  induction depth generalizing start root with
  | zero => simp [CommitmentTree.perfect, CommitmentTree.messages]
  | succ depth ih =>
    -- Both halves are replayed, and the parent hashes their two roots.
    obtain ⟨left, right, hleft, hright, hparent⟩ : ∃ left right,
        simulateQ cache.toPartialImpl (subtreeAtM oracleHasher chunks depth start) = some left ∧
        simulateQ cache.toPartialImpl (subtreeAtM oracleHasher chunks depth (start + 2 ^ depth)) =
          some right ∧
        simulateQ cache.toPartialImpl (combineM queryHash left right) = some root := by
      unfold subtreeAtM at hrun
      split at hrun
      · rename_i past
        -- Past the data, both halves are the all-zero subtree one level below.
        have zero : ∀ position, position ≥ chunks.size →
            subtreeAtM oracleHasher chunks depth position
              = zeroRootM (combineM queryHash) zeroChunk depth := by
          intro position beyond
          unfold subtreeAtM
          rw [ite_eq_left_of_eq_true _ _ (eq_true beyond)]
          rfl
        simp only [oracleHasher, Hasher.ofHash, zeroRootM, simulateQ_bind] at hrun
        obtain ⟨below, hbelow, hroot⟩ := Option.bind_eq_some_iff.mp hrun
        exact ⟨below, below, by rw [zero start past]; exact hbelow,
          by rw [zero _ (Nat.le_add_right_of_le past)]; exact hbelow, hroot⟩
      · simp only [simulateQ_bind] at hrun
        obtain ⟨left, hleft, hrun⟩ := Option.bind_eq_some_iff.mp hrun
        obtain ⟨right, hright, hroot⟩ := Option.bind_eq_some_iff.mp hrun
        exact ⟨left, right, hleft, hright, hroot⟩
    -- Each replayed half is the root of its perfect tree under the table.
    have rooted : ∀ {position : Nat} {node : Bytes},
        simulateQ cache.toPartialImpl (subtreeAtM oracleHasher chunks depth position) =
          some node →
        (CommitmentTree.perfect depth fun i => padded zeroChunk chunks (position + i)).root
          (tableHash f) = node := by
      intro position node hnode
      rw [CommitmentTree.perfect_subtreeAtM, ← evalWithAnswerFn_subtreeAtM]
      exact cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hnode
    intro x hx
    simp only [CommitmentTree.perfect, CommitmentTree.messages, List.mem_cons, List.mem_append,
      show ∀ i, start + (i + 2 ^ depth) = start + 2 ^ depth + i from fun i => by omega] at hx
    rcases hx with rfl | hx | hx
    · rw [rooted hleft, rooted hright]
      simp only [combineM] at hparent
      obtain ⟨digest, hdigest⟩ := cached_of_queryHash hparent
      rw [hdigest, hf hdigest]
    · exact ih hleft x hx
    · exact ih hright x hx

/-- Two different inputs with one digest of a table collide in a cache.

The cache must give both inputs the answers of the table. -/
theorem collision_of_cached {cache : HashOracle.QueryCache} {f : QueryImpl HashOracle Id}
    {a b : Bytes} (hdistinct : a ≠ b)
    (hequal : tableHash f a = tableHash f b)
    (ha : cache a = some (f a))
    (hb : cache b = some (f b)) : Collision cache := by
  refine ⟨a, b, f a, hdistinct, ha, ?_⟩
  rw [hb]
  exact congrArg some (Vector.toArray_inj.mp (ByteArray.mk.inj hequal)).symm

/-- Two replayed queries with one answer have one input, or the cache has a collision. -/
theorem collision_or_eq_of_queryHash {cache : HashOracle.QueryCache}
    {x y first second : ByteArray}
    (hx : simulateQ cache.toPartialImpl (queryHash x) = some first)
    (hy : simulateQ cache.toPartialImpl (queryHash y) = some second)
    (same : first.data = second.data) : Collision cache ∨ x.data = y.data := by
  simp only [queryHash, simulateQ_bind, simulateQ_spec_query,
    QueryCache.toPartialImpl_apply] at hx hy
  obtain ⟨firstAnswer, hfirst, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨secondAnswer, hsecond, hy⟩ := Option.bind_eq_some_iff.mp hy
  simp at hx hy
  subst hx hy
  by_cases equal : x = y
  · exact .inr (congrArg ByteArray.data equal)
  · refine .inl ⟨x, y, firstAnswer, equal, hfirst, ?_⟩
    rw [hsecond]
    exact congrArg some (Vector.toArray_inj.mp same).symm

/-- A replayed winning extraction exposes a collision of the cache.

The binding search of SSZ finds it, run with a table that extends the cache. -/
theorem collision_of_extract {cache : HashOracle.QueryCache} {shape : Desc} {first second : Value}
    {outcome : Outcome}
    (hrun : simulateQ cache.toPartialImpl (extract shape first second) = some outcome)
    (hwins : Wins shape outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extract, evalWithAnswerFn_bind, evalWithAnswerFn_hashTreeRootM] at hout
  split at hout
  · rename_i firstTree secondTree hfirstTree hsecondTree
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hout
    subst hout
    obtain ⟨hsound, hfits₁, hfits₂, hsized₁, hsized₂, hne, root, hroot₁, hroot₂⟩ := hwins
    dsimp only at hfits₁ hfits₂ hsized₁ hsized₂ hne hroot₁ hroot₂
    obtain ⟨tree₁, htree₁, hsame₁, hcomplete₁⟩ :=
      valueTree_of_hashTreeRootM (tableHash f) shape first root hroot₁
    obtain ⟨tree₂, htree₂, hsame₂, hcomplete₂⟩ :=
      valueTree_of_hashTreeRootM (tableHash f) shape second root hroot₂
    rw [hfirstTree, Except.ok.injEq] at htree₁
    rw [hsecondTree, Except.ok.injEq] at htree₂
    subst htree₁ htree₂
    -- The replay rehashes both computations, so it caches every one of their hash inputs.
    simp only [extract, simulateQ_bind] at hrun
    obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨_, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    simp only [hfirstTree, hsecondTree, simulateQ_bind] at hrun
    obtain ⟨result₁, hresult₁, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨result₂, hresult₂, -⟩ := Option.bind_eq_some_iff.mp hrun
    have hcached : ∀ {tree : CommitmentTree} {result : Bytes × List Bytes},
        simulateQ cache.toPartialImpl (rehash tree) = some result →
        ∀ x ∈ tree.messages (tableHash f), cache x = some (f x) := by
      intro tree result hreplay x hx
      have heval := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hreplay
      rw [evalWithAnswerFn_rehash] at heval
      subst heval
      obtain ⟨digest, hdigest⟩ := cached_of_rehash hreplay x hx
      rw [hdigest, hf hdigest]
    have hwidth := tableHash_size f
    -- A collision between the two expanded computations is a collision of the cache.
    cases hsearch : findMessageCollision (firstTree.messages (tableHash f))
        (secondTree.messages (tableHash f)) (tableHash f) with
    | some pair =>
      obtain ⟨hmem₁, hmem₂, -, -, hdistinct, hequal⟩ := findMessageCollision_valid hsearch
      exact collision_of_cached hdistinct hequal (hcached hresult₁ _ hmem₁)
        (hcached hresult₂ _ hmem₂)
    | none =>
      -- With no collision, the two values are equal, against the win.
      have hclean : CommitmentTree.NoCollision firstTree secondTree (tableHash f) := by
        rintro ⟨a, ha, b, hb, hab, hequal⟩
        exact findMessageCollision_eq_none_iff.mp hsearch a ha b hb
          ⟨CommitmentTree.messages_size_of_width _ hwidth _ hcomplete₁ a ha,
            CommitmentTree.messages_size_of_width _ hwidth _ hcomplete₂ b hb, hab, hequal⟩
      exact absurd (valueTreeAt_eq_of_noCollision shape.nesting le_rfl hsound hfits₁ hfits₂
        hsized₁ hsized₂ hfirstTree hsecondTree hclean (hsame₁.trans hsame₂.symm) hwidth) hne
  · rename_i hnot
    simp only [evalWithAnswerFn_pure] at hout
    subst hout
    -- Both roots exist, so both expanded computations exist.
    obtain ⟨-, -, -, -, -, -, root, hroot₁, hroot₂⟩ := hwins
    obtain ⟨tree₁, htree₁, -⟩ := valueTree_of_hashTreeRootM (tableHash f) shape first root hroot₁
    obtain ⟨tree₂, htree₂, -⟩ := valueTree_of_hashTreeRootM (tableHash f) shape second root hroot₂
    exact (hnot tree₁ tree₂ htree₁ htree₂).elim

/-- Two different values of one type with one root, at probability at most `Q^2 / N`.

`N` is the number of digests.

`Q` bounds the oracle calls of the whole experiment, repeats included.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_wins_le [SampleableType Hash32] (shape : Desc)
    (adversary : OracleComp (unifSpec + HashOracle) (Value × Value)) {Q : Nat}
    -- The extraction alone hashes every node of the padded tree of each value.
    --
    -- So for a list type, `Q` grows with the capacity of the type.
    --
    -- It does not grow with the length of the values.
    (hQ : IsQueryBoundP (experiment shape adversary) (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl (experiment shape adversary)).run ∅}[Wins shape z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  -- Each win exposes two different queried inputs with one answer, found by the binding search.
  --
  -- So the birthday bound of the oracle bounds the probability of a win.
  prEvent_experimentWith_le (fun pair : Value × Value => extract shape pair.1 pair.2) (Wins shape)
    (fun {_} {claim} {_} hrun hwins =>
      collision_of_extract (first := claim.1) (second := claim.2) hrun hwins) adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_wins_le_two_pow (shape : Desc)
    (adversary : OracleComp (unifSpec + HashOracle) (Value × Value)) {Q : Nat}
    (hQ : IsQueryBoundP (experiment shape adversary) (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl (experiment shape adversary)).run ∅}[Wins shape z.1] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_wins_le shape adversary hQ
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- A second value with the root of an honest value fixed before the run.

The honest root is computed with the same oracle inside the experiment.

The bound is the same birthday bound, `Q^2 / 2^256`. -/
theorem prEvent_secondValue_le_two_pow (shape : Desc) (honest : Value)
    (adversary : OracleComp (unifSpec + HashOracle) Value) {Q : Nat}
    (hQ : IsQueryBoundP (experiment shape (Prod.mk honest <$> adversary))
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experiment shape (Prod.mk honest <$> adversary))).run ∅}[Wins shape z.1] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_wins_le_two_pow shape _ hQ

end EthLib.Serialization.Ssz.RandomOracle
