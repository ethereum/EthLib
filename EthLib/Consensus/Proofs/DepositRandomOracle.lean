module

public import EthLib.Consensus.Containers.Operations
public import EthLib.Serialization.Proofs.Ssz.BranchRandomOracle
import EthLib.Consensus.Proofs.Containers.Misc

/-!
# Proofs: two deposits of one index and one deposit root in the random oracle model

An adversary wins with two deposits of different data whose proofs reach one root at one index.

Every hash of the experiment is an oracle call.

A win exposes two different queried messages with one answer, so the birthday bound applies.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Serialization.Ssz.RandomOracle
open OracleComp OracleSpec ENNReal
open Cryptography.Merkle.RandomOracle (Collision experimentWith experimentWith_queryBound
  prEvent_experimentWith_le)

/-- What the adversary outputs: one index, one deposit root and two deposits. -/
structure DepositClaim where
  /-- The index of both deposits among the leaves of the deposit tree. -/
  index : Nat
  /-- The deposit root that both proofs must reach. -/
  root : Root
  /-- The first deposit. -/
  first : Deposit
  /-- The second deposit. -/
  second : Deposit

/-- What the deposit experiment reports: the claim, and the climbs of both proofs.

The climbs are absent when the root of the data of a deposit cannot be read as a node. -/
structure DepositOutcome where
  /-- The index, the deposit root and the two deposits of the adversary. -/
  claim : DepositClaim
  /-- The roots of the data, the proofs and the roots that the proofs climb to. -/
  climbs : Option BranchOutcome

/-- The extraction for deposits, with a node hash in any monad.

It roots the data of both deposits, then climbs both proofs from those roots at the claimed index.

The climbs take the depth of the deposit check, one level more than the deposit tree.

The experiment runs it with the oracle. -/
def extractDeposits {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (claim : DepositClaim) : m DepositOutcome := do
  let firstRoot ← (hashTreeRootM (Hasher.ofHash hash) (SszType.desc DepositData)
    (SszType.toValue claim.first.data)).run
  let secondRoot ← (hashTreeRootM (Hasher.ofHash hash) (SszType.desc DepositData)
    (SszType.toValue claim.second.data)).run
  let climbs ← (match firstRoot >>= toChunk, secondRoot >>= toChunk with
    | .ok firstLeaf, .ok secondLeaf => do
      let climbs ← extractBranches hash (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
        ⟨claim.index, firstLeaf, claim.first.proof.toList, secondLeaf, claim.second.proof.toList⟩
      pure (some climbs)
    | _, _ => pure none)
  return ⟨claim, climbs⟩

/-- The adversary wins: two deposits with different data, whose proofs climb to the claimed root.

Both climbs start from the roots of the data, at the claimed index. -/
def DepositWins (outcome : DepositOutcome) : Prop :=
  outcome.claim.first.data ≠ outcome.claim.second.data ∧
    ∃ climbs, outcome.climbs = some climbs ∧
      climbs.firstRoot = .ok outcome.claim.root ∧ climbs.secondRoot = .ok outcome.claim.root

/-- The root of deposit data is seven hashes.

It holds for a hash in any lawful monad. -/
theorem hashTreeRootM_depositData {m : Type → Type} [Monad m] [LawfulMonad m]
    (hash : ByteArray → m ByteArray) (data : DepositData) :
    (hashTreeRootM (Hasher.ofHash hash) (SszType.desc DepositData)
      (SszType.toValue data)).run = (do
      -- The public key takes one hash.
      let pubkey ← hash ⟨data.pubkey.toArray ++ Array.replicate 16 0⟩
      -- The signature takes three.
      let low ← hash ⟨data.signature.toArray.extract 0 64⟩
      let high ← hash ⟨data.signature.toArray.extract 64 96 ++ Array.replicate 32 0⟩
      let signature ← hash (low ++ high)
      -- Three more hashes join the four field roots.
      --
      -- The withdrawal credentials are their own node.
      let left ← hash (pubkey ++ ⟨data.withdrawalCredentials.toArray⟩)
      -- The amount is its 8 bytes and 24 zero bytes.
      let right ← hash (uintBytes 8 data.amount.toNat ++ ⟨Array.replicate 24 0⟩ ++ signature)
      let root ← hash (left ++ right)
      return .ok root) := by
  -- The roots of the four fields, each stated for its SSZ shape.
  have pubkey : (hashTreeRootAtM (Hasher.ofHash hash) 1 (.byteVector 48)
      (.bytes ⟨data.pubkey.toArray⟩)).run = (do
        return .ok (← hash ⟨data.pubkey.toArray ++ Array.replicate 16 0⟩)) :=
    hashTreeRootM_bytes48 (Hasher.ofHash hash) data.pubkey
  have credentials : (hashTreeRootAtM (Hasher.ofHash hash) 1 (.byteVector 32)
      (.bytes ⟨data.withdrawalCredentials.toArray⟩)).run = _ :=
    hashTreeRootM_bytes32 (Hasher.ofHash hash) data.withdrawalCredentials
  have amount : (hashTreeRootAtM (Hasher.ofHash hash) 1 (.uint 8)
      (.uint data.amount.toNat)).run = _ :=
    hashTreeRootM_uint64 (Hasher.ofHash hash) data.amount
  have signature : (hashTreeRootAtM (Hasher.ofHash hash) 1 (.byteVector 96)
      (.bytes ⟨data.signature.toArray⟩)).run = _ :=
    hashTreeRootM_bytes96 hash data.signature
  show (hashTreeRootAtM (Hasher.ofHash hash) 2 (.container ["pubkey", "withdrawal_credentials",
    "amount", "signature"] [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96])
    (.seq [.bytes ⟨data.pubkey.toArray⟩, .bytes ⟨data.withdrawalCredentials.toArray⟩,
      .uint data.amount.toNat, .bytes ⟨data.signature.toArray⟩])).run = _
  unfold hashTreeRootAtM
  simp only [merkleLayout, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, liftM_pure, pure_bind, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, MerkleLayout.nesting, layoutChunksWithM, Leaves.count,
    Option.getD_none, List.drop_zero, Nat.sub_zero, List.take_succ_cons, List.take_zero,
    List.mapM_cons, List.mapM_nil]
  simp only [ExceptT.run_bind, ExceptT.run_pure, bind_assoc, pubkey, credentials, amount,
    signature, pure_bind]
  simp only [merkleizeBoundedUncheckedM, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte, ExceptT.run_lift,
    show depthFor 4 = 2 from depthFor_pow 2]
  simp [subtreeAtM_ofHash_four hash, combineM, padded]

/-- Two replayed equal roots of deposit data come from equal data, or the cache has a collision.

The chase runs from the root down, since two hashes with one answer have one message or collide. -/
private theorem collision_or_eq_of_hashTreeRootM_depositData {cache : HashOracle.QueryCache}
    {first second : DepositData} {root : Except Err Bytes}
    (hfirst : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (SszType.desc DepositData) (SszType.toValue first)).run = some root)
    (hsecond : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (SszType.desc DepositData) (SszType.toValue second)).run = some root) :
    Collision cache ∨ first = second := by
  obtain ⟨pubkey₁, credentials₁, amount₁, signature₁⟩ := first
  obtain ⟨pubkey₂, credentials₂, amount₂, signature₂⟩ := second
  rw [hashTreeRootM_depositData] at hfirst hsecond
  simp only [simulateQ_bind, simulateQ_pure] at hfirst hsecond
  obtain ⟨publicRoot₁, hpublic₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨low₁, hlow₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨high₁, hhigh₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨signed₁, hsigned₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨left₁, hleft₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨right₁, hright₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨top₁, htop₁, hfirst⟩ := Option.bind_eq_some_iff.mp hfirst
  obtain ⟨publicRoot₂, hpublic₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨low₂, hlow₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨high₂, hhigh₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨signed₂, hsigned₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨left₂, hleft₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨right₂, hright₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  obtain ⟨top₂, htop₂, hsecond⟩ := Option.bind_eq_some_iff.mp hsecond
  have sameTop : top₁.data = top₂.data :=
    congrArg ByteArray.data (Except.ok.inj (Option.some.inj (hfirst.trans hsecond.symm)))
  -- Each step: one answer of two hashes gives one message, or a collision of the cache.
  refine (collision_or_eq_of_queryHash htop₁ htop₂ sameTop).elim .inl fun top => ?_
  -- A message is two nodes joined, so its array is the arrays of the two joined.
  simp only [ByteArray.data_append] at top
  obtain ⟨sameLeft, sameRight⟩ := Array.append_inj top
    ((size_of_queryHash hleft₁).trans (size_of_queryHash hleft₂).symm)
  refine (collision_or_eq_of_queryHash hleft₁ hleft₂ sameLeft).elim .inl fun left => ?_
  simp only [ByteArray.data_append] at left
  obtain ⟨samePublic, sameCredentials⟩ := Array.append_inj left
    ((size_of_queryHash hpublic₁).trans (size_of_queryHash hpublic₂).symm)
  refine (collision_or_eq_of_queryHash hpublic₁ hpublic₂ samePublic).elim .inl fun key => ?_
  refine (collision_or_eq_of_queryHash hright₁ hright₂ sameRight).elim .inl fun right => ?_
  simp only [ByteArray.data_append] at right
  obtain ⟨sameAmount, sameSigned⟩ := Array.append_inj right (by simp [uintBytes_size])
  refine (collision_or_eq_of_queryHash hsigned₁ hsigned₂ sameSigned).elim .inl fun signed => ?_
  simp only [ByteArray.data_append] at signed
  obtain ⟨sameLow, sameHigh⟩ := Array.append_inj signed
    ((size_of_queryHash hlow₁).trans (size_of_queryHash hlow₂).symm)
  refine (collision_or_eq_of_queryHash hlow₁ hlow₂ sameLow).elim .inl fun low => ?_
  refine (collision_or_eq_of_queryHash hhigh₁ hhigh₂ sameHigh).elim .inl fun high => ?_
  -- No step collides, so every field of the two data is equal.
  refine .inr ?_
  have whole : ∀ signature : Vector UInt8 96,
      signature.toArray = signature.toArray.extract 0 64 ++ signature.toArray.extract 64 96 := by
    intro signature
    rw [Array.extract_append_extract]
    exact (Array.extract_eq_self_of_le (by simp)).symm
  have amounts := uintBytes_injective (by simpa using amount₁.toNat_lt)
    (by simpa using amount₂.toNat_lt) (ByteArray.ext ((Array.append_left_inj _).mp sameAmount))
  have low : signature₁.toArray.extract 0 64 = signature₂.toArray.extract 0 64 := low
  have high : signature₁.toArray.extract 64 96 = signature₂.toArray.extract 64 96 :=
    (Array.append_left_inj _).mp high
  simp only [DepositData.mk.injEq]
  refine ⟨Vector.toArray_inj.mp ((Array.append_left_inj _).mp key),
    Vector.toArray_inj.mp sameCredentials, UInt64.toNat_inj.mp amounts, Vector.toArray_inj.mp ?_⟩
  rw [whole signature₁, whole signature₂, low, high]

/-- A replayed winning deposit extraction exposes a collision of the cache.

Two different data with one root give a collision among the messages of the two roots.

Two different roots that climb to the claimed root give the collision of the two climbs. -/
theorem collision_of_extractDeposits {cache : HashOracle.QueryCache} {claim : DepositClaim}
    {outcome : DepositOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractDeposits queryHash claim) = some outcome)
    (hwins : DepositWins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed climb.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  simp only [extractDeposits, simulateQ_bind] at hrun
  obtain ⟨firstRoot, hfirst, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨secondRoot, hsecond, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨climbs, hclimbs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  cases hrun
  obtain ⟨differ, climbed, present, firstClimbed, secondClimbed⟩ := hwins
  dsimp only at differ present firstClimbed secondClimbed
  subst present
  split at hclimbs
  · rename_i firstLeaf secondLeaf hfirstLeaf hsecondLeaf
    simp only [simulateQ_bind, simulateQ_pure] at hclimbs
    obtain ⟨_, hbranches, hclimbs⟩ := Option.bind_eq_some_iff.mp hclimbs
    cases hclimbs
    by_cases sameLeaf : firstLeaf = secondLeaf
    · -- One root of two different data, so the chase down both roots finds a collision.
      subst sameLeaf
      rw [eq_ok_of_bind_toChunk hfirstLeaf] at hfirst
      rw [eq_ok_of_bind_toChunk hsecondLeaf] at hsecond
      exact (collision_or_eq_of_hashTreeRootM_depositData hfirst hsecond).elim id
        fun same => absurd same differ
    · -- Two different roots climb to one root, so the search finds a collision of the climbs.
      have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hbranches
      simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
        evalWithAnswerFn_pure] at hout
      subst hout
      exact collision_of_extractBranches hbranches ⟨sameLeaf, by simp, by simp, _, firstClimbed,
        secondClimbed⟩
  · simp only [simulateQ_pure] at hclimbs
    cases hclimbs

/-- The root of deposit data makes seven oracle calls. -/
private theorem hashTreeRootM_depositData_queryBound (data : DepositData) :
    IsQueryBoundP (hashTreeRootM (Hasher.ofHash queryHash) (SszType.desc DepositData)
      (SszType.toValue data)).run (fun _ => True) 7 := by
  rw [hashTreeRootM_depositData]
  simp [queryHash]

/-- The extraction makes at most 80 oracle calls.

It makes seven calls per root of deposit data, and climbs at most 33 nodes of each proof. -/
theorem extractDeposits_queryBound (claim : DepositClaim) :
    IsQueryBoundP (extractDeposits queryHash claim) (fun _ => True) 80 := by
  unfold extractDeposits
  refine (isQueryBoundP_bind (hashTreeRootM_depositData_queryBound _) fun _ _ =>
    isQueryBoundP_bind (hashTreeRootM_depositData_queryBound _) fun _ _ =>
      isQueryBoundP_bind (n := 2 * (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)) (m := 0) ?_
        fun _ _ => isQueryBoundP_pure _ _ 0).mono (by decide)
  split
  · exact (isQueryBoundP_bind (extractBranches_queryBound _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by omega)
  · exact isQueryBoundP_pure _ _ _

/-- The experiment makes at most `q + 80` oracle calls.

It needs the adversary to make at most `q` oracle calls. -/
theorem experimentWith_extractDeposits_queryBound
    {adversary : OracleComp (unifSpec + HashOracle) DepositClaim} {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractDeposits queryHash) adversary)
      (fun t => t.isRight = true) (q + 80) :=
  experimentWith_queryBound hq extractDeposits_queryBound

/-- An adversary that outputs two deposits wins with probability at most `Q^2 / N`.

A win is different data, and both proofs climbing to the claimed root at the claimed index.

`Q` bounds the oracle calls of the whole experiment, repeats included, and `N` counts digests.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_depositWins_le [SampleableType Hash32]
    (adversary : OracleComp (unifSpec + HashOracle) DepositClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractDeposits queryHash) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractDeposits queryHash) adversary)).run ∅}[DepositWins z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  prEvent_experimentWith_le (extractDeposits queryHash) DepositWins collision_of_extractDeposits
    adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_depositWins_le_two_pow
    (adversary : OracleComp (unifSpec + HashOracle) DepositClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractDeposits queryHash) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractDeposits queryHash) adversary)).run ∅}[DepositWins z.1] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_depositWins_le adversary hQ
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- The same bound with the adversary's oracle calls `q` counted alone.

At the check depth of 33, a win has probability at most `(q + 80)^2 / 2^256`.

It needs the adversary to make at most `q` oracle calls. -/
theorem prEvent_depositWins_le_of_adversary
    (adversary : OracleComp (unifSpec + HashOracle) DepositClaim) {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractDeposits queryHash) adversary)).run ∅}[DepositWins z.1] ≤
      (q + 80 : Nat) * (((q + 80 : Nat) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_depositWins_le_two_pow adversary (experimentWith_extractDeposits_queryBound hq)

/-- With SHA-256, the extraction roots the data of each deposit as the spec does. -/
theorem extractDeposits_sha256 (claim : DepositClaim) :
    (extractDeposits (m := Id) Cryptography.Hash.Sha256.hash claim).run =
      ⟨claim, match SszType.hashTreeRoot claim.first.data,
          SszType.hashTreeRoot claim.second.data with
        | .ok firstLeaf, .ok secondLeaf =>
          some (extractBranches (m := Id) Cryptography.Hash.Sha256.hash
            (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
            ⟨claim.index, firstLeaf, claim.first.proof.toList, secondLeaf,
              claim.second.proof.toList⟩).run
        | _, _ => none⟩ := by
  simp only [extractDeposits, ofHash_sha256, SszType.hashTreeRoot_eq]
  rfl

/-- With SHA-256 as the node hash, a win is two deposits that the deposit check accepts.

The two deposits have different data, and both checks read the claimed index and root.

The roots of the outcome are then computed with SHA-256, not with the oracle.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem. -/
theorem depositWins_sha256_iff {claim : DepositClaim} :
    DepositWins (extractDeposits (m := Id) Cryptography.Hash.Sha256.hash claim).run ↔
      claim.first.data ≠ claim.second.data ∧
        (∃ leaf, SszType.hashTreeRoot claim.first.data = .ok leaf ∧
          isValidMerkleBranch leaf claim.first.proof.toList
            (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1) claim.index claim.root = true) ∧
        ∃ leaf, SszType.hashTreeRoot claim.second.data = .ok leaf ∧
          isValidMerkleBranch leaf claim.second.proof.toList
            (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1) claim.index claim.root = true := by
  rw [extractDeposits_sha256]
  simp only [DepositWins]
  refine and_congr_right fun _ => ?_
  -- A proof of the check depth keeps all its nodes, so the extraction climbs all of them.
  have whole : ∀ (deposit : Deposit),
      deposit.proof.toList.take (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1) =
        deposit.proof.toList :=
    fun _ => List.take_of_length_le (by simp)
  cases firstRoot : SszType.hashTreeRoot claim.first.data <;>
    cases secondRoot : SszType.hashTreeRoot claim.second.data <;>
    simp [extractBranches_sha256, whole, isValidMerkleBranch_eq_true_iff, toChunk_ok_iff]

end EthLib.Consensus
