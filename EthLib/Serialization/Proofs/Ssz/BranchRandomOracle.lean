module

public import EthLib.Serialization.Proofs.Ssz.RandomOracle
public import EthLib.Serialization.Proofs.Ssz.Merkle.Branch
public import EthLib.Serialization.Ssz.Typed.Basic

/-!
# Proofs: two branches of one root in the random oracle model

An adversary queries the oracle, then outputs one index and two leaves, each with a branch.

The depth of the branches is fixed before the run.

The adversary wins when the leaves differ, both branches have that depth, and both reach one root.

The experiment climbs both branches as the branch check does, with the oracle as the node hash.

Each win exposes two different queried inputs with one answer, so the birthday bound applies.

The root of 48 bytes, the size of a commitment or a public key, is one call of the oracle.

The root of a list of them makes at most one call per vector, per inner node and for the count.

Two different lists of them with one root expose two different queried inputs with one answer.

That result needs the limit of the list below `2^256`.

The root of a vector of them is the tree over their roots, with no count mixed in.

Two different vectors of them with one root do the same, at every length.

The root of 96 bytes, the size of a signature, is three hashes.

The roots of 32 bytes and of a 64-bit integer are their bytes padded to one node, with no hash.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Serialization.Ssz.RandomOracle

open EthLib.Base
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Merkle.RandomOracle (Collision experimentWith experimentWith_queryBound
  prEvent_experimentWith_le)

/-- What the adversary outputs: one index, and two leaves with a branch each. -/
structure BranchClaim where
  /-- The index of both leaves among the nodes of their depth. -/
  index : Nat
  /-- The first leaf. -/
  firstLeaf : Vector UInt8 32
  /-- The nodes of the first branch, from the leaf up. -/
  firstBranch : List (Vector UInt8 32)
  /-- The second leaf. -/
  secondLeaf : Vector UInt8 32
  /-- The nodes of the second branch, from the leaf up. -/
  secondBranch : List (Vector UInt8 32)

/-- What the branch experiment reports: the claim and the roots of its two branches. -/
structure BranchOutcome where
  /-- The index, leaves and branches of the adversary. -/
  claim : BranchClaim
  /-- The root that the first branch climbs to, as a node. -/
  firstRoot : Except Err (Vector UInt8 32)
  /-- The root that the second branch climbs to, as a node. -/
  secondRoot : Except Err (Vector UInt8 32)

/-- The extraction for branches, with a node hash in any monad.

It climbs the first `depth` nodes of each branch from its leaf, as the branch check does.

The experiment runs it with the oracle. -/
def extractBranches {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray) (depth : Nat)
    (claim : BranchClaim) : m BranchOutcome := do
  let firstRoot ← climbBranchM hash claim.index 0 claim.firstLeaf.toArray
    ((claim.firstBranch.take depth).map Vector.toArray)
  let secondRoot ← climbBranchM hash claim.index 0 claim.secondLeaf.toArray
    ((claim.secondBranch.take depth).map Vector.toArray)
  return ⟨claim, toChunk firstRoot, toChunk secondRoot⟩

/-- The adversary wins: two different leaves at one index climb to one root.

A win also needs both branches to have `depth` nodes. -/
def BranchWins (depth : Nat) (outcome : BranchOutcome) : Prop :=
  outcome.claim.firstLeaf ≠ outcome.claim.secondLeaf ∧
    outcome.claim.firstBranch.length = depth ∧ outcome.claim.secondBranch.length = depth ∧
    ∃ root, outcome.firstRoot = .ok root ∧ outcome.secondRoot = .ok root

/-- A climb, run against a full answer table, is the climb with that table. -/
theorem evalWithAnswerFn_climbBranchM (f : QueryImpl HashOracle Id) (index level : Nat)
    (node : Bytes) (branch : List Bytes) :
    evalWithAnswerFn f (climbBranchM queryHash index level node branch) =
      (climbBranchM (m := Id) (tableHash f) index level node branch).run := by
  unfold climbBranchM
  rw [Cryptography.Merkle.climb_map_monad (fun _ => combineM queryHash)
    (fun {β} (x : OracleComp HashOracle β) => (evalWithAnswerFn f x : Id β))
    (fun _ => rfl) (fun _ _ => evalWithAnswerFn_bind _ _ _)]
  exact congrArg (fun hash => Cryptography.Merkle.climb hash ⟨level, index >>> level⟩ node branch)
    (by funext _ left right; exact evalWithAnswerFn_combineM f left right)

/-- A replayed climb caches every message it hashes, with the answer of the table.

It needs the table to agree with the cache. -/
theorem cached_of_climbBranchM {cache : HashOracle.QueryCache} {f : QueryImpl HashOracle Id}
    (hf : cache.AgreesWithFn f) {index level : Nat} {node root : Bytes} {branch : List Bytes}
    (hrun : simulateQ cache.toPartialImpl (climbBranchM queryHash index level node branch) =
      some root) :
    ∀ x ∈ branchMessages index level node branch (tableHash f),
      cache (ByteArray.mk x) = some (f (ByteArray.mk x)) := by
  -- Each level queries its pair, and the levels above climb from the parent of the table.
  have climbed : ∀ (branch : List Bytes) (p : Cryptography.Merkle.Position) (node : Bytes)
      {root : Bytes},
      simulateQ cache.toPartialImpl
          (Cryptography.Merkle.climb (fun _ => combineM queryHash) p node branch) =
        some root →
      ∀ x ∈ Cryptography.Merkle.climbPairs (fun _ => combineM (m := Id) (tableHash f)) p
          node branch,
        cache (ByteArray.mk (x.1 ++ x.2)) = some (f (ByteArray.mk (x.1 ++ x.2))) := by
    intro branch
    induction branch with
    | nil =>
      intro _ _ _ _ x hx
      simp [Cryptography.Merkle.climbPairs] at hx
    | cons sibling rest ih =>
      intro p node root hrun x hx
      simp only [Cryptography.Merkle.climb, simulateQ_bind] at hrun
      obtain ⟨parent, hparent, hrun⟩ := Option.bind_eq_some_iff.mp hrun
      -- The replayed parent is the parent with the table, which agrees with the cache.
      have heval := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hparent
      rw [evalWithAnswerFn_combineM] at heval
      simp only [Cryptography.Merkle.climbPairs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · -- This level queried its pair, so the cache holds the answer of the table.
        simp only [combineM, simulateQ_bind] at hparent
        obtain ⟨_, hquery, -⟩ := Option.bind_eq_some_iff.mp hparent
        obtain ⟨digest, hdigest⟩ := cached_of_queryHash hquery
        rw [hdigest, hf hdigest]
      · rw [← heval] at hrun
        exact ih p.parent _ hrun x hx
  intro x hx
  simp only [branchMessages, List.mem_map] at hx
  obtain ⟨pair, hpair, rfl⟩ := hx
  exact climbed branch ⟨level, index >>> level⟩ node hrun pair hpair

/-- A replayed winning branch extraction exposes a collision of the cache.

The search over the two climbs finds it, run with a table that extends the cache. -/
theorem collision_of_extractBranches {depth : Nat} {cache : HashOracle.QueryCache}
    {claim : BranchClaim} {outcome : BranchOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractBranches queryHash depth claim) = some outcome)
    (hwins : BranchWins depth outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed climb.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
    evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨hleaves, hfirst, hsecond, root, hroot₁, hroot₂⟩ := hwins
  dsimp only at hleaves hfirst hsecond hroot₁ hroot₂
  rw [toChunk_ok_iff] at hroot₁ hroot₂
  -- Under the table, the leaves are equal, or the search over the two climbs finds a collision.
  rcases climbBranchM_binding (tableHash f) (by simp [hfirst, hsecond])
      (hroot₁.trans hroot₂.symm) with hsame | hfound
  · exact absurd (Vector.toArray_inj.mp hsame) hleaves
  · obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.mp hfound
    -- Every leaf and every branch node is a 32-byte vector.
    have widths : ∀ (nodes : List (Vector UInt8 32)),
        ∀ node ∈ nodes.map Vector.toArray, node.size = bytesPerChunk := by
      intro nodes node member
      obtain ⟨vector, -, rfl⟩ := List.mem_map.mp member
      exact vector.size_toArray
    obtain ⟨-, -, hdistinct, hequal⟩ := findBranchCollision_valid_of_width (tableHash f)
      (tableHash_size f) (by simp) (by simp) (widths _) (widths _) hab
    obtain ⟨ha, hb⟩ := findBranchCollision_mem hab
    -- Both climbs were replayed, so the cache gives their messages the answers of the table.
    simp only [extractBranches, simulateQ_bind] at hrun
    obtain ⟨_, hrun₁, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨_, hrun₂, -⟩ := Option.bind_eq_some_iff.mp hrun
    exact collision_of_cached hdistinct hequal (cached_of_climbBranchM hf hrun₁ a ha)
      (cached_of_climbBranchM hf hrun₂ b hb)

/-- A climb makes at most one oracle call per branch node. -/
private theorem climbBranchM_queryBound (index level : Nat) (node : Bytes) (branch : List Bytes) :
    IsQueryBoundP (climbBranchM queryHash index level node branch) (fun _ => True)
      branch.length := by
  unfold climbBranchM
  generalize (⟨level, index >>> level⟩ : Cryptography.Merkle.Position) = p
  induction branch generalizing p node with
  | nil => trivial
  | cons sibling rest ih =>
    simp only [Cryptography.Merkle.climb]
    refine (isQueryBoundP_bind (n := 1) ?_ fun parent _ => ih parent p.parent).mono
      (by simp [Nat.add_comm])
    exact combineM_queryBound _ _

/-- The extraction makes at most `2 * depth` oracle calls, one per climbed node.

It climbs at most `depth` nodes of each branch. -/
theorem extractBranches_queryBound (depth : Nat) (claim : BranchClaim) :
    IsQueryBoundP (extractBranches queryHash depth claim) (fun _ => True) (2 * depth) := by
  -- Each climb takes at most `depth` branch nodes, with one call per node.
  have climbs : ∀ (leaf : Vector UInt8 32) (branch : List (Vector UInt8 32)),
      IsQueryBoundP (climbBranchM queryHash claim.index 0 leaf.toArray
        ((branch.take depth).map Vector.toArray)) (fun _ => True) depth := fun _ _ =>
    (climbBranchM_queryBound _ _ _ _).mono (by simp)
  exact (isQueryBoundP_bind (climbs _ _) fun _ _ =>
    isQueryBoundP_bind (climbs _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)

/-- The experiment makes the adversary's oracle calls and at most one call per climbed node.

The extraction climbs at most `depth` nodes of each branch. -/
theorem experimentWith_extractBranches_queryBound (depth : Nat)
    {adversary : OracleComp (unifSpec + HashOracle) BranchClaim} {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractBranches queryHash depth) adversary)
      (fun t => t.isRight = true) (q + 2 * depth) :=
  experimentWith_queryBound hq (extractBranches_queryBound depth)

/-- Two different leaves at one index with one root, at probability at most `Q^2 / N`.

A win needs both branches to have `depth` nodes, and `N` is the number of digests.

The roots are computed with the oracle as the node hash.

`Q` bounds the oracle calls of the whole experiment, repeats included.

The extraction climbs each branch with one call per node, so it adds at most `2 * depth` calls.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_branchWins_le [SampleableType Hash32] (depth : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) BranchClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBranches queryHash depth) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBranches queryHash depth) adversary)).run ∅}[BranchWins depth z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  prEvent_experimentWith_le (extractBranches queryHash depth) (BranchWins depth)
    collision_of_extractBranches adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_branchWins_le_two_pow (depth : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) BranchClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBranches queryHash depth) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBranches queryHash depth) adversary)).run ∅}[BranchWins depth z.1] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_branchWins_le depth adversary hQ
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- The same bound with the adversary's oracle calls `q` counted alone.

A win has probability at most `(q + 2 * depth)^2 / 2^256`. -/
theorem prEvent_branchWins_le_of_adversary (depth : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) BranchClaim) {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBranches queryHash depth) adversary)).run ∅}[BranchWins depth z.1] ≤
      (q + 2 * depth : Nat) * (((q + 2 * depth : Nat) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_branchWins_le_two_pow depth adversary
    (experimentWith_extractBranches_queryBound depth hq)

/-- With SHA-256 in the identity monad, the extraction climbs as the branch check does. -/
theorem extractBranches_sha256 (depth : Nat) (claim : BranchClaim) :
    (extractBranches (m := Id) Cryptography.Hash.Sha256.hash depth claim).run =
      ⟨claim, toChunk (climbBranch claim.index 0 claim.firstLeaf.toArray
          ((claim.firstBranch.take depth).map Vector.toArray)),
        toChunk (climbBranch claim.index 0 claim.secondLeaf.toArray
          ((claim.secondBranch.take depth).map Vector.toArray))⟩ :=
  rfl

/-- With SHA-256 as the node hash, a win is two valid branches of two different leaves.

The two branches have one depth, one index and one root.

The roots of the outcome are then computed with SHA-256, not with the oracle.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem. -/
theorem branchWins_sha256_iff {depth : Nat} {claim : BranchClaim} :
    BranchWins depth (extractBranches (m := Id) Cryptography.Hash.Sha256.hash depth claim).run ↔
      claim.firstLeaf ≠ claim.secondLeaf ∧ ∃ root,
        isValidMerkleBranch claim.firstLeaf claim.firstBranch depth claim.index root = true ∧
        isValidMerkleBranch claim.secondLeaf claim.secondBranch depth claim.index root = true := by
  rw [extractBranches_sha256]
  simp only [BranchWins, isValidMerkleBranch_eq_true_iff, toChunk_ok_iff]
  -- A branch of `depth` nodes keeps all of them, so the extraction climbs the whole branch.
  constructor
  · rintro ⟨differ, firstCount, secondCount, root, firstClimbed, secondClimbed⟩
    rw [List.take_of_length_le firstCount.le] at firstClimbed
    rw [List.take_of_length_le secondCount.le] at secondClimbed
    exact ⟨differ, root, ⟨firstCount, firstClimbed⟩, secondCount, secondClimbed⟩
  · rintro ⟨differ, root, ⟨firstCount, firstClimbed⟩, secondCount, secondClimbed⟩
    refine ⟨differ, firstCount, secondCount, root, ?_, ?_⟩
    · rw [List.take_of_length_le firstCount.le]
      exact firstClimbed
    · rw [List.take_of_length_le secondCount.le]
      exact secondClimbed

/-- The 48 bytes of a vector and 16 zero bytes form its two packed nodes. -/
private theorem packBytes_bytes48 (bytes : Vector UInt8 48) :
    padded zeroChunk (Serialization.Ssz.packBytes bytes.toArray) 0 ++
        padded zeroChunk (Serialization.Ssz.packBytes bytes.toArray) 1 =
      bytes.toArray ++ Array.replicate 16 0 := by
  have size : bytes.toArray.size = 48 := bytes.size_toArray
  simp [padded, Serialization.Ssz.packBytes, size, bytesPerChunk, ← Array.append_assoc,
    Array.extract_append_extract, Array.extract_eq_self_of_le]

/-- A perfect tree of depth 1 over two nodes is one hash of the two nodes, with any hasher. -/
private theorem subtreeAtM_two {m : Type → Type} [Monad m] [LawfulMonad m] (hasher : Hasher m)
    {chunks : Array Bytes} (count : chunks.size = 2) :
    subtreeAtM hasher chunks 1 0 =
      combineM hasher.hash (padded zeroChunk chunks 0) (padded zeroChunk chunks 1) := by
  simp only [subtreeAtM, count]
  simp

/-- The root of 48 bytes, with any budget above zero, is one hash of those bytes and 16 zero bytes.

A field of a container is rooted with such a budget.

It holds for a hasher in any lawful monad. -/
theorem hashTreeRootAtM_bytes48 {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) (budget : Nat) (bytes : Vector UInt8 48) :
    (hashTreeRootAtM hasher (budget + 1) (.byteVector 48) (.bytes bytes.toArray)).run = (do
      return .ok (← hasher.hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data) := by
  have size : bytes.toArray.size = 48 := bytes.size_toArray
  have count : (Serialization.Ssz.packBytes bytes.toArray).size = 2 := by
    simp [size, bytesPerChunk]
  simp only [hashTreeRootAtM, merkleLayout, size, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, liftM_pure, pure_bind]
  simp only [layoutChunksAtM, MerkleLayout.packing, Option.getD_none, Leaves.count,
    Array.extract_size, pure_bind, bind_pure, merkleizeBoundedUncheckedM, Nat.lt_irrefl,
    ↓reduceIte, ExceptT.run_lift]
  rw [count, show depthFor 2 = 1 from depthFor_pow 1, subtreeAtM_two hasher count, combineM,
    packBytes_bytes48]
  simp only [map_bind, map_pure]

/-- The root of 48 bytes is one hash of those bytes and 16 zero bytes.

It holds for a hasher in any lawful monad. -/
theorem hashTreeRootM_bytes48 {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) (bytes : Vector UInt8 48) :
    (hashTreeRootM hasher (SszType.desc (Vector UInt8 48)) (SszType.toValue bytes)).run = (do
      return .ok (← hasher.hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data) :=
  hashTreeRootAtM_bytes48 hasher 0 bytes

/-- The root of 48 bytes makes one oracle call. -/
theorem hashTreeRootM_bytes48_queryBound (bytes : Vector UInt8 48) :
    IsQueryBoundP (hashTreeRootM (Hasher.ofHash queryHash) (SszType.desc (Vector UInt8 48))
      (SszType.toValue bytes)).run (fun _ => True) 1 := by
  rw [hashTreeRootM_bytes48]
  simp [Hasher.ofHash, queryHash]

/-- A replayed root of 48 bytes caches its message, and is the answer of the table to it.

It needs the table to agree with the cache. -/
theorem cached_of_hashTreeRootM_bytes48 {cache : HashOracle.QueryCache}
    {f : QueryImpl HashOracle Id} (hf : cache.AgreesWithFn f) {bytes : Vector UInt8 48}
    {root : Except Err Bytes}
    (hrun : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (SszType.desc (Vector UInt8 48)) (SszType.toValue bytes)).run = some root) :
    cache ⟨bytes.toArray ++ Array.replicate 16 0⟩ =
        some (f ⟨bytes.toArray ++ Array.replicate 16 0⟩) ∧
      root = .ok (tableHash f ⟨bytes.toArray ++ Array.replicate 16 0⟩).data := by
  have heval := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  rw [hashTreeRootM_bytes48] at hrun heval
  simp only [Hasher.ofHash, evalWithAnswerFn_bind, evalWithAnswerFn_queryHash,
    evalWithAnswerFn_pure] at heval
  simp only [Hasher.ofHash, simulateQ_bind] at hrun
  obtain ⟨_, hquery, -⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨digest, hdigest⟩ := cached_of_queryHash hquery
  exact ⟨by rw [hdigest, hf hdigest], heval.symm⟩

/-- The elements of a sequence of 48-byte vectors are rooted with one hash each, and never fail. -/
private theorem mapM_hashTreeRootAtM_bytes48 {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) (list : List (Vector UInt8 48)) :
    (list.mapM fun bytes => hashTreeRootAtM hasher 1 (.byteVector 48)
      (SszType.toValue bytes)).run =
      Except.ok <$> list.mapM fun bytes => do
        return (← hasher.hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data := by
  induction list with
  | nil => simp
  | cons bytes rest ih =>
    have root : (hashTreeRootAtM hasher 1 (.byteVector 48) (SszType.toValue bytes)).run =
        (do return .ok (← hasher.hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data) :=
      hashTreeRootM_bytes48 hasher bytes
    simp only [List.mapM_cons, ExceptT.run_bind, root, ih, bind_assoc, pure_bind, map_bind,
      bind_map_left, map_pure, ExceptT.run_pure]

/-- The root of a list of 48-byte vectors is the tree over their roots, with the count mixed in.

Each vector is rooted with one hash, and a list over its limit fails.

It holds for a hasher in any lawful monad. -/
theorem hashTreeRootM_bytes48List {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) (limit : Nat) (vectors : List (Vector UInt8 48)) :
    (hashTreeRootM hasher (.list (SszType.desc (Vector UInt8 48)) limit)
        (.seq (vectors.map SszType.toValue))).run =
      if limit < vectors.length then pure (.error (.overLimit limit vectors.length)) else do
        let roots ← vectors.mapM fun bytes => do
          return (← hasher.hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data
        let root ← subtreeAtM hasher roots.toArray (depthFor limit) 0
        return .ok (← mixInM hasher root (lengthWord vectors.length)) := by
  show (hashTreeRootAtM hasher 2 (.list (.byteVector 48) limit)
    (.seq (vectors.map SszType.toValue))).run = _
  have lift : ∀ {α : Type} (x : Except Err α),
      (liftM x : ExceptT Err m α) = ExceptT.mk (pure x) := fun _ => rfl
  by_cases over : limit < vectors.length
  · simp only [hashTreeRootAtM, merkleLayout, List.length_map, gt_iff_lt, over, ↓reduceIte]
    rw [lift]
    simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]
    rfl
  · have layout : sequenceLayout (.byteVector 48) (vectors.map SszType.toValue) (some limit)
        (some (lengthWord vectors.length)) =
      .ok (.nesting ((vectors.map SszType.toValue).map fun value => some (.byteVector 48, value))
        (some limit) (some (lengthWord vectors.length))) := rfl
    simp only [hashTreeRootAtM, merkleLayout, List.length_map, gt_iff_lt, over, ↓reduceIte, layout]
    rw [lift]
    simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]
    simp only [layoutChunksAtM, MerkleLayout.nesting, Option.getD_none, Leaves.count,
      List.length_map, List.drop_zero, Nat.sub_zero, merkleizeBoundedUncheckedM]
    rw [List.take_of_length_le (by simp)]
    simp only [List.mapM_map, Function.comp_def, ExceptT.run_bind, mapM_hashTreeRootAtM_bytes48,
      bind_map_left, bind_assoc, pure_bind, ExceptT.run_pure]
    -- The rest of the root reads the count of the roots only, which is the count of the vectors.
    refine mapM_bind_congr_length _ vectors fun roots count => ?_
    simp only [List.size_toArray, count, over, ↓reduceIte, ExceptT.run_lift, bind_map_left,
      bind_pure_comp]

/-- The root of a vector of 48-byte vectors is the tree over their roots, with no count mixed in.

Each vector is rooted with one hash.

The width of the tree is the least power of two at least the length.

It needs the sequence to have the length of the vector.

It holds for a hasher in any lawful monad. -/
theorem hashTreeRootM_bytes48Vector {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) {length : Nat} {vectors : List (Vector UInt8 48)}
    (count : vectors.length = length) :
    (hashTreeRootM hasher (.vector (SszType.desc (Vector UInt8 48)) length)
        (.seq (vectors.map SszType.toValue))).run = (do
      let roots ← vectors.mapM fun bytes => do
        return (← hasher.hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data
      return .ok (← subtreeAtM hasher roots.toArray (depthFor length) 0)) := by
  subst count
  show (hashTreeRootAtM hasher 2 (.vector (.byteVector 48) vectors.length)
    (.seq (vectors.map SszType.toValue))).run = _
  have lift : ∀ {α : Type} (x : Except Err α),
      (liftM x : ExceptT Err m α) = ExceptT.mk (pure x) := fun _ => rfl
  have layout : sequenceLayout (.byteVector 48) (vectors.map SszType.toValue)
      (some vectors.length) = .ok (.nesting ((vectors.map SszType.toValue).map fun value =>
        some (.byteVector 48, value)) (some vectors.length)) := rfl
  simp only [hashTreeRootAtM, merkleLayout, List.length_map, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, layout]
  rw [lift]
  simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]
  simp only [layoutChunksAtM, MerkleLayout.nesting, Option.getD_none, Leaves.count,
    List.length_map, List.drop_zero, Nat.sub_zero, merkleizeBoundedUncheckedM]
  rw [List.take_of_length_le (by simp)]
  simp only [List.mapM_map, Function.comp_def, ExceptT.run_bind, mapM_hashTreeRootAtM_bytes48,
    bind_map_left, bind_assoc, pure_bind, ExceptT.run_pure]
  refine mapM_bind_congr_length _ vectors fun roots count => ?_
  simp only [List.size_toArray, count, Nat.lt_irrefl, ↓reduceIte, ExceptT.run_lift,
    bind_map_left, bind_pure_comp]

/-- The roots of 48-byte vectors make one oracle call each. -/
private theorem mapM_bytes48_queryBound (list : List (Vector UInt8 48)) :
    IsQueryBoundP (list.mapM fun bytes => do
      return (← (Hasher.ofHash queryHash).hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data)
      (fun _ => True) list.length := by
  induction list with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons bytes rest ih =>
    rw [List.mapM_cons]
    refine (isQueryBoundP_bind (n := 1) ?_ fun _ _ =>
      isQueryBoundP_bind ih fun _ _ => isQueryBoundP_pure _ _ 0).mono (by simp [Nat.add_comm])
    simp [Hasher.ofHash, queryHash]

/-- The root of a list of 48-byte vectors makes at most `limit + width` oracle calls.

The tree of the list has `width` leaves, the least power of two at least `limit`.

It makes one call per vector, at most one per inner node of the tree, and one for the count.

So the count grows with the limit, not with the vectors that the list holds. -/
theorem hashTreeRootM_bytes48List_queryBound (limit : Nat) (vectors : List (Vector UInt8 48)) :
    IsQueryBoundP (hashTreeRootM (Hasher.ofHash queryHash)
      (.list (SszType.desc (Vector UInt8 48)) limit) (.seq (vectors.map SszType.toValue))).run
      (fun _ => True) (limit + 2 ^ depthFor limit) := by
  rw [hashTreeRootM_bytes48List]
  by_cases over : limit < vectors.length
  · simp only [over, ↓reduceIte]
    exact isQueryBoundP_pure _ _ _
  · simp only [over, ↓reduceIte]
    have tree := Nat.one_le_two_pow (n := depthFor limit)
    refine (isQueryBoundP_bind (mapM_bytes48_queryBound vectors) fun _ _ =>
      isQueryBoundP_bind (subtreeAtM_queryBound _ _ _) fun _ _ =>
        isQueryBoundP_bind (combineM_queryBound _ _) fun _ _ =>
          isQueryBoundP_pure _ _ 0).mono (by omega)

/-- The root of a vector of 48-byte vectors makes at most `length + width - 1` oracle calls.

The tree of the vector has `width` leaves, the least power of two at least `length`.

It makes one call per vector, and at most one per inner node of the tree.

It needs the sequence to have the length of the vector. -/
theorem hashTreeRootM_bytes48Vector_queryBound {length : Nat}
    {vectors : List (Vector UInt8 48)} (count : vectors.length = length) :
    IsQueryBoundP (hashTreeRootM (Hasher.ofHash queryHash)
      (.vector (SszType.desc (Vector UInt8 48)) length) (.seq (vectors.map SszType.toValue))).run
      (fun _ => True) (length + 2 ^ depthFor length - 1) := by
  rw [hashTreeRootM_bytes48Vector _ count]
  have tree := Nat.one_le_two_pow (n := depthFor length)
  refine (isQueryBoundP_bind (mapM_bytes48_queryBound vectors) fun _ _ =>
    isQueryBoundP_bind (subtreeAtM_queryBound _ _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by omega)

/-- Two sequences of 48-byte vectors with one replayed tree root are equal, or the cache collides.

The trees are over the roots of the vectors, with one depth.

It needs both sequences of one length, at most the width of the trees. -/
private theorem collision_or_eq_of_subtreeAtM_bytes48 {cache : HashOracle.QueryCache}
    {depth : Nat} {first second : List (Vector UInt8 48)}
    (sameLength : first.length = second.length) (fits : first.length ≤ 2 ^ depth)
    {firstRoots secondRoots : List Bytes} {node : Bytes}
    (hfirstRoots : simulateQ cache.toPartialImpl (first.mapM fun bytes => do
      return (← (Hasher.ofHash queryHash).hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data) =
        some firstRoots)
    (hfirst : simulateQ cache.toPartialImpl
      (subtreeAtM (Hasher.ofHash queryHash) firstRoots.toArray depth 0) = some node)
    (hsecondRoots : simulateQ cache.toPartialImpl (second.mapM fun bytes => do
      return (← (Hasher.ofHash queryHash).hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data) =
        some secondRoots)
    (hsecond : simulateQ cache.toPartialImpl
      (subtreeAtM (Hasher.ofHash queryHash) secondRoots.toArray depth 0) = some node) :
    Collision cache ∨ first = second := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  -- Each digest is the replayed root of one vector, so the lemma of one vector applies to it.
  have elements : ∀ {list : List (Vector UInt8 48)} {roots : List Bytes},
      simulateQ cache.toPartialImpl (list.mapM fun bytes => do
        return (← (Hasher.ofHash queryHash).hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data) =
          some roots →
      roots = list.map (fun bytes => (tableHash f ⟨bytes.toArray ++ Array.replicate 16 0⟩).data) ∧
        ∀ bytes ∈ list, cache ⟨bytes.toArray ++ Array.replicate 16 0⟩ =
          some (f ⟨bytes.toArray ++ Array.replicate 16 0⟩) := by
    intro list
    induction list with
    | nil =>
      intro roots hroots
      simp only [List.mapM_nil, simulateQ_pure] at hroots
      cases hroots
      simp
    | cons bytes rest ih =>
      intro roots hroots
      rw [List.mapM_cons, simulateQ_bind] at hroots
      obtain ⟨digest, hdigest, hroots⟩ := Option.bind_eq_some_iff.mp hroots
      rw [simulateQ_bind] at hroots
      obtain ⟨others, hothers, hroots⟩ := Option.bind_eq_some_iff.mp hroots
      simp only [simulateQ_pure] at hroots
      cases hroots
      simp only [Hasher.ofHash, simulateQ_bind, simulateQ_pure] at hdigest
      obtain ⟨answer, hanswer, hdata⟩ := Option.bind_eq_some_iff.mp hdigest
      have hroot : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
          (SszType.desc (Vector UInt8 48)) (SszType.toValue bytes)).run =
            some (.ok digest) := by
        rw [hashTreeRootM_bytes48]
        simp only [Hasher.ofHash, simulateQ_bind, simulateQ_pure, hanswer]
        exact congrArg (Option.map Except.ok) hdata
      obtain ⟨cachedRoot, rooted⟩ := cached_of_hashTreeRootM_bytes48 hf hroot
      obtain ⟨rfl, cached⟩ := ih hothers
      refine ⟨by rw [Except.ok.inj rooted]; rfl, fun other member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact cachedRoot
      · exact cached other member
  obtain ⟨rfl, firstElements⟩ := elements hfirstRoots
  obtain ⟨rfl, secondElements⟩ := elements hsecondRoots
  -- Each tree is the perfect tree over the roots, and its replay caches all its messages.
  have rooted : ∀ {roots : Array Bytes}, simulateQ cache.toPartialImpl
      (subtreeAtM (Hasher.ofHash queryHash) roots depth 0) = some node →
      (CommitmentTree.perfect depth fun i => padded zeroChunk roots (0 + i)).root
        (tableHash f) = node := fun hnode => by
    rw [CommitmentTree.perfect_subtreeAtM, ← evalWithAnswerFn_subtreeAtM]
    exact cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hnode
  -- Every leaf of both trees is a digest of the table, so both trees are complete.
  have complete : ∀ list : List (Vector UInt8 48),
      (CommitmentTree.perfect depth fun i => padded zeroChunk
        (list.map fun bytes =>
          (tableHash f ⟨bytes.toArray ++ Array.replicate 16 0⟩).data).toArray (0 + i)).Complete :=
    fun list => CommitmentTree.perfect_complete _ _ fun _ _ =>
      padded_size _ (fun chunk member => by
        obtain ⟨bytes, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp member)
        exact (f _).size_toArray) _
  -- One root of two perfect trees of one depth: equal leaves, or a collision inside the trees.
  rcases CommitmentTree.binding _ _ (complete first) (complete second)
      (CommitmentTree.perfect_shape _ _ _) ((rooted hfirst).trans (rooted hsecond).symm)
      (tableHash_size f) with same | ⟨a, ha, b, hb, hab, hequal⟩
  · -- Equal leaves give a position where the vectors differ and their digests agree.
    have leaves := CommitmentTree.perfect_injective _ same
    have read : ∀ (list : List (Vector UInt8 48)) (i : Nat) (inside : i < list.length),
        padded zeroChunk (list.map fun bytes =>
          (tableHash f ⟨bytes.toArray ++ Array.replicate 16 0⟩).data).toArray (0 + i) =
          (tableHash f ⟨list[i].toArray ++ Array.replicate 16 0⟩).data := by
      intro list i inside
      simp [padded, inside]
    by_cases equal : ∀ i (inFirst : i < first.length) (inSecond : i < second.length),
        first[i] = second[i]
    · exact .inr (List.ext_getElem sameLength equal)
    · simp only [not_forall] at equal
      obtain ⟨i, inFirst, inSecond, unequal⟩ := equal
      have digest := (read first i inFirst).symm.trans
        ((leaves i (Nat.lt_of_lt_of_le inFirst fits)).trans (read second i inSecond))
      exact .inl (collision_of_cached (fun same => unequal (Vector.toArray_inj.mp
        (Array.append_inj same (by simp)).1)) (ByteArray.ext digest)
        (firstElements _ (by simp)) (secondElements _ (by simp)))
  · exact .inl (collision_of_cached hab hequal (cached_of_subtreeAtM hf hfirst a ha)
      (cached_of_subtreeAtM hf hsecond b hb))

/-- Two different lists of 48-byte vectors with one root under the oracle expose a collision.

It needs the limit below `2^256`, so that the count mixed into the root is exact. -/
theorem collision_of_hashTreeRootM_bytes48List {cache : HashOracle.QueryCache} {limit : Nat}
    (fits : limit < 2 ^ 256) {first second : List (Vector UInt8 48)} (differ : first ≠ second)
    {root : Bytes}
    (hfirst : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (.list (SszType.desc (Vector UInt8 48)) limit) (.seq (first.map SszType.toValue))).run =
        some (.ok root))
    (hsecond : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (.list (SszType.desc (Vector UInt8 48)) limit) (.seq (second.map SszType.toValue))).run =
        some (.ok root)) :
    Collision cache := by
  rw [hashTreeRootM_bytes48List] at hfirst hsecond
  by_cases firstOver : limit < first.length
  · simp [firstOver] at hfirst
  by_cases secondOver : limit < second.length
  · simp [secondOver] at hsecond
  simp only [firstOver, secondOver, ↓reduceIte, simulateQ_bind, simulateQ_pure] at hfirst hsecond
  obtain ⟨firstRoots, hfirstRoots, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨firstNode, hfirstNode, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨firstMixed, hfirstMixed, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨secondRoots, hsecondRoots, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨secondNode, hsecondNode, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨secondMixed, hsecondMixed, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  simp only [mixInM, Hasher.ofHash, combineM, simulateQ_bind,
    simulateQ_pure] at hfirstMixed hsecondMixed
  obtain ⟨firstDigest, hfirstDigest, hfirstMixed⟩ := Option.bind_eq_some_iff.mp hfirstMixed
  obtain ⟨secondDigest, hsecondDigest, hsecondMixed⟩ := Option.bind_eq_some_iff.mp hsecondMixed
  cases hfirstMixed
  cases hsecondMixed
  -- Two different mixed messages with one root already collide.
  refine (collision_or_eq_of_queryHash hfirstDigest hsecondDigest
    (Except.ok.inj (Option.some.inj (hfirst.trans hsecond.symm)))).elim id fun sameMix => ?_
  -- One mixed message: one node of the trees, and one count, since counts fit the word.
  obtain ⟨rfl, sameWord⟩ := Array.append_inj' sameMix (by simp)
  have sameLength : first.length = second.length :=
    lengthWord_injective (by omega) (by omega) sameWord
  exact (collision_or_eq_of_subtreeAtM_bytes48 sameLength
    (Nat.le_trans (by omega) (le_two_pow_depthFor limit)) hfirstRoots hfirstNode hsecondRoots
    hsecondNode).elim id fun same => absurd same differ

/-- Two vectors of 48-byte vectors with one replayed root are equal, or the cache has a collision.

It needs both sequences to have the length of the vector, and holds at every length. -/
theorem collision_or_eq_of_hashTreeRootM_bytes48Vector {cache : HashOracle.QueryCache}
    {length : Nat} {first second : List (Vector UInt8 48)} (firstCount : first.length = length)
    (secondCount : second.length = length) {root : Except Err Bytes}
    (hfirst : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (.vector (SszType.desc (Vector UInt8 48)) length) (.seq (first.map SszType.toValue))).run =
        some root)
    (hsecond : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (.vector (SszType.desc (Vector UInt8 48)) length) (.seq (second.map SszType.toValue))).run =
        some root) :
    Collision cache ∨ first = second := by
  rw [hashTreeRootM_bytes48Vector _ firstCount] at hfirst
  rw [hashTreeRootM_bytes48Vector _ secondCount] at hsecond
  simp only [simulateQ_bind, simulateQ_pure] at hfirst hsecond
  obtain ⟨firstRoots, hfirstRoots, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨firstNode, hfirstNode, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨secondRoots, hsecondRoots, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨secondNode, hsecondNode, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain rfl : firstNode = secondNode :=
    Except.ok.inj (Option.some.inj (hfirst.trans hsecond.symm))
  exact collision_or_eq_of_subtreeAtM_bytes48 (firstCount.trans secondCount.symm)
    (firstCount ▸ le_two_pow_depthFor length) hfirstRoots hfirstNode hsecondRoots hsecondNode

/-- The root of 96 bytes is three hashes.

The first 64 bytes form one message, and the last 32 bytes with 32 zero bytes the other.

The third hash joins the two digests.

It holds for a hash in any lawful monad. -/
theorem hashTreeRootM_bytes96 {m : Type → Type} [Monad m] [LawfulMonad m]
    (hash : ByteArray → m ByteArray) (bytes : Vector UInt8 96) :
    (hashTreeRootM (Hasher.ofHash hash) (SszType.desc (Vector UInt8 96))
      (SszType.toValue bytes)).run = (do
      let low ← hash ⟨bytes.toArray.extract 0 64⟩
      let high ← hash ⟨bytes.toArray.extract 64 96 ++ Array.replicate 32 0⟩
      return .ok (← hash ⟨low.data ++ high.data⟩).data) := by
  have size : bytes.toArray.size = 96 := bytes.size_toArray
  have count : (Serialization.Ssz.packBytes bytes.toArray).size = 3 := by
    simp [size, bytesPerChunk]
  show (hashTreeRootAtM (Hasher.ofHash hash) 1 (.byteVector 96) (.bytes bytes.toArray)).run = _
  simp only [hashTreeRootAtM, merkleLayout, size, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, liftM_pure, pure_bind]
  simp only [layoutChunksAtM, MerkleLayout.packing, Option.getD_none, Leaves.count,
    Array.extract_size, pure_bind, bind_pure, merkleizeBoundedUncheckedM, Nat.lt_irrefl,
    ↓reduceIte, ExceptT.run_lift]
  rw [count, show depthFor 3 = 2 by simp [depthFor],
    subtreeAtM_ofHash_four hash (by omega) (by omega)]
  simp [combineM, padded, Serialization.Ssz.packBytes, size, bytesPerChunk, zeroChunk,
    Array.extract_append_extract]

/-- The root of 32 bytes is those bytes, with no hash.

It holds for a hasher in any lawful monad. -/
theorem hashTreeRootM_bytes32 {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) (bytes : Vector UInt8 32) :
    (hashTreeRootM hasher (SszType.desc (Vector UInt8 32)) (SszType.toValue bytes)).run =
      pure (.ok bytes.toArray) := by
  have size : bytes.toArray.size = 32 := bytes.size_toArray
  have count : (Serialization.Ssz.packBytes bytes.toArray).size = 1 := by
    simp [size, bytesPerChunk]
  show (hashTreeRootAtM hasher 1 (.byteVector 32) (.bytes bytes.toArray)).run = _
  simp only [hashTreeRootAtM, merkleLayout, size, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, liftM_pure, pure_bind]
  simp only [layoutChunksAtM, MerkleLayout.packing, Option.getD_none, Leaves.count, pure_bind,
    merkleizeBoundedUncheckedM, count, show depthFor 1 = 0 from depthFor_pow 0]
  simp [subtreeAtM, padded, Serialization.Ssz.packBytes, size, bytesPerChunk,
    Array.extract_eq_self_of_le]

/-- The root of a 64-bit integer is its 8 bytes and 24 zero bytes, with no hash.

It holds for a hasher in any lawful monad. -/
theorem hashTreeRootM_uint64 {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) (value : UInt64) :
    (hashTreeRootM hasher (SszType.desc UInt64) (SszType.toValue value)).run =
      pure (.ok (uintBytes 8 value.toNat ++ Array.replicate 24 0)) := by
  have fits : uintFits 8 value.toNat = true := (uintFits_iff 8 _).mpr value.toNat_lt
  have size : (uintBytes 8 value.toNat).size = 8 := uintBytes_size 8 _
  have count : (Serialization.Ssz.packBytes (uintBytes 8 value.toNat)).size = 1 := by
    simp [size, bytesPerChunk]
  have encoded : serialize (.uint 8) (.uint value.toNat) = pure (uintBytes 8 value.toNat) := by
    simp only [serialize, fits, ↓reduceIte]
    rfl
  show (hashTreeRootAtM hasher 1 (.uint 8) (.uint value.toNat)).run = _
  simp only [hashTreeRootAtM, merkleLayout, fixedLeaf, encoded, pure_bind, liftM_pure]
  simp only [layoutChunksAtM, MerkleLayout.packing, Option.getD_none, Leaves.count, pure_bind,
    merkleizeBoundedUncheckedM, count, show depthFor 1 = 0 from depthFor_pow 0]
  simp [subtreeAtM, padded, Serialization.Ssz.packBytes, size, bytesPerChunk,
    Array.extract_eq_self_of_le]

end EthLib.Serialization.Ssz.RandomOracle
