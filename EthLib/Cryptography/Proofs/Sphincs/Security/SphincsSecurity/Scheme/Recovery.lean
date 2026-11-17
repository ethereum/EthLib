module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Lemmas
public import Mathlib.Data.Nat.Bitwise

/-!
# Recovery: the verifier recomputes what the signer built

The one-time recovery of the verifier returns the leaf that the signer built.

Each FORS path leads to the root of its tree, so the verifier recovers the FORS public key.

Other files add the surrogate spine and compose these facts into correctness.

Once the oracle is fixed, every algorithm is deterministic.

So this file works under a fixed answer function `f` and reads each algorithm as a function.

No statement here is probabilistic or uses that the answers are uniform.
-/

@[expose] public section

open OracleComp

set_option maxRecDepth 100000

namespace SphincsSecurity.Completeness

variable [Params]

open Concrete Seeded
open EthLib.Cryptography

-- The attempt limits are `2^32`, so unfolding them would unfold the loops that many times.
attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

variable (f : QueryImpl HashSpec Id)

/-! ## Evaluating the hash wrappers -/

omit [Params] in
@[simp] theorem eval_oracleHash (input : HashInput) :
    evalWithAnswerFn f (oracleHash input : OracleComp HashSpec HashOutput) = f input := by
  simp only [oracleHash, HasQuery.query]
  exact simulateQ_spec_query f input

@[simp] theorem eval_tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    evalWithAnswerFn f (tweakableHash parameter domain payload : OracleComp HashSpec Digest)
      = truncateHash (f (tweakableHashInput parameter domain payload)) := by
  simp [tweakableHash]

@[simp] theorem eval_deriveKey (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    evalWithAnswerFn f (deriveKey parameter domain seed : OracleComp HashSpec Digest)
      = truncateHash (f (keygenHashInput parameter domain seed)) := by
  simp [deriveKey]

omit [Params] in
@[simp] theorem eval_sequenceFin {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn f (sequenceFin computation)
      = fun index => evalWithAnswerFn f (computation index) := by
  induction n with
  | zero => funext index; exact index.elim0
  | succ n ih =>
      funext index
      simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
      cases index using Fin.cases <;> rfl

/-!
## The chain

Chain steps compose.

So the verifier walks the rest of a chain from the signed digit to the endpoint of the full walk.
-/

theorem chainWalk_add (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    chainWalk (m := OracleComp HashSpec) parameter lay tree leaf chainIdx start (a + b) value
      = (do
          let mid ←
            chainWalk (m := OracleComp HashSpec) parameter lay tree leaf chainIdx start a value
          chainWalk parameter lay tree leaf chainIdx (start + a) b mid) := by
  induction b with
  | zero => simp [chainWalk]
  | succ b ih =>
      show chainWalk (m := OracleComp HashSpec) parameter lay tree leaf chainIdx start
        (a + b + 1) value = _
      simp only [chainWalk, ih, bind_assoc, Nat.add_assoc]

/-- The value that the chain reaches after `steps` steps from position `start`. -/
def walk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value)

theorem walk_add (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    walk f parameter lay tree leaf chainIdx start (a + b) value
      = walk f parameter lay tree leaf chainIdx (start + a) b
          (walk f parameter lay tree leaf chainIdx start a value) := by
  simp only [walk, chainWalk_add, evalWithAnswerFn_bind]

/-- The verifier's recovery of a signed chain value reaches the public endpoint. -/
theorem eval_recoverChain_walk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) (secret : Digest) :
    evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
        (walk f parameter lay tree leaf chainIdx 0 digit.val secret))
      = walk f parameter lay tree leaf chainIdx 0 (chainLength - 1) secret := by
  have hdigit : digit.val ≤ chainLength - 1 := Nat.le_of_lt_succ digit.isLt
  have hsplit : chainLength - 1 = digit.val + (chainLength - 1 - digit.val) :=
    (Nat.add_sub_cancel' hdigit).symm
  rw [show walk f parameter lay tree leaf chainIdx 0 (chainLength - 1) secret
      = walk f parameter lay tree leaf chainIdx 0 (digit.val + (chainLength - 1 - digit.val)) secret
      from by rw [← hsplit]]
  rw [walk_add, Nat.zero_add]
  rfl

/-!
## The one-time signature

The signer walks each chain to the digit that the encoding names.

The verifier walks the rest of the chain.
-/

/-- The secret of one chain, from its own seed derivation. -/
def otsSecret (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (chainIdx : ChainIndex) : Digest :=
  evalWithAnswerFn f (otsStart parameter lay tree leaf chainIdx seed : OracleComp HashSpec Digest)

theorem otsSecret_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (chainIdx : ChainIndex) :
    otsSecret f parameter lay tree leaf seed chainIdx =
      truncateHash (f (keygenHashInput parameter (.ots lay tree leaf chainIdx) seed)) := by
  simp only [otsSecret, otsStart, eval_deriveKey]

/-- The 64 seed derivations of a one-time key give the secrets of its 64 chains. -/
@[simp] theorem eval_otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    evalWithAnswerFn f
        (otsSecrets parameter lay tree leaf seed : OracleComp HashSpec (ChainIndex → Digest))
      = otsSecret f parameter lay tree leaf seed := by
  funext chainIdx
  simp only [otsSecrets, otsSecret_eq, eval_sequenceFin, eval_deriveKey]

/-- The public endpoint of one chain. -/
def otsEndpoint (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (chainIdx : ChainIndex) : Digest :=
  walk f parameter lay tree leaf chainIdx 0 (chainLength - 1)
    (otsSecret f parameter lay tree leaf seed chainIdx)

@[simp] theorem eval_oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf seed
        : OracleComp HashSpec (ChainIndex → Digest))
      = otsEndpoint f parameter lay tree leaf seed := by
  funext chainIdx
  simp only [oneTimePublicKey, otsEndpoint, walk, eval_sequenceFin,
    evalWithAnswerFn_bind, eval_otsSecrets]

/-- A successful counter search returns a counter that encodes the message.

Each chain value is the walk from the derived secret to the digit of the encoding. -/
theorem otsSignFrom_spec (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput) :
    ∀ (attempts start : Nat) {counter : Counter} {values : ChainIndex → Digest},
      evalWithAnswerFn f (otsSignFrom parameter lay tree leaf seed message attempts start
          : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
        some (counter, values) →
      ∃ encoding, evalWithAnswerFn f (encode parameter lay tree leaf message counter
            : OracleComp HashSpec (Option Encoding)) = some encoding ∧
        ∀ chainIdx, values chainIdx = walk f parameter lay tree leaf chainIdx 0
          (encoding chainIdx).val (otsSecret f parameter lay tree leaf seed chainIdx) := by
  intro attempts
  induction attempts with
  | zero => intro start counter values h; simp [otsSignFrom] at h
  | succ attempts ih =>
      intro start counter values h
      rw [otsSignFrom, evalWithAnswerFn_bind] at h
      cases hencode : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none => rw [hencode] at h; exact ih (start + 1) h
      | some encoding =>
          rw [hencode] at h
          simp only [eval_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hcounter, hvalues⟩ := h
          refine ⟨encoding, ?_, ?_⟩
          · rw [← hcounter]; exact hencode
          · intro chainIdx
            rw [← hvalues]
            simp only [walk, eval_otsSecrets]

/-- The leaf that the verifier recovers is the leaf that the signer built the tree from. -/
theorem eval_otsLeaf_of_otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput) {counter : Counter}
    {values : ChainIndex → Digest}
    (h : evalWithAnswerFn f (otsSign parameter lay tree leaf seed message
        : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
      some (counter, values)) :
    evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values
        : OracleComp HashSpec (Option Digest))
      = some (evalWithAnswerFn f (leafHash parameter lay tree leaf
          (otsEndpoint f parameter lay tree leaf seed) : OracleComp HashSpec Digest)) := by
  obtain ⟨encoding, hencode, hvalues⟩ :=
    otsSignFrom_spec f parameter lay tree leaf seed message encodingAttemptLimit 0 h
  have hendpoints : (fun chainIdx => evalWithAnswerFn f
      (recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
        : OracleComp HashSpec Digest))
      = otsEndpoint f parameter lay tree leaf seed := by
    funext chainIdx
    rw [hvalues chainIdx, eval_recoverChain_walk]
    rfl
  rw [otsLeaf, evalWithAnswerFn_bind, hencode]
  simp only [eval_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hendpoints]

/-!
## The Merkle tree of a layer

The authentication path of the signer holds the sibling at every level.

So the fold of the signed leaf through it climbs the honest tree.

At each level, the verifier hashes the same pair as the honest node.
-/

theorem leafOfNat_val (leaf : LeafIndex) : leafOfNat leaf.val = leaf :=
  Fin.ext (Nat.mod_eq_of_lt leaf.isLt)

/-- The honest value at a node of a layer's tree. -/
def node (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed)
    (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (Seeded.treeNode parameter lay tree seed level nodeIdx)

theorem node_succ (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (level nodeIdx : Nat) :
    node f parameter lay tree seed (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
          (nodePayload (node f parameter lay tree seed level (2 * nodeIdx))
            (node f parameter lay tree seed level (2 * nodeIdx + 1))))) := by
  simp only [node, Seeded.treeNode_succ, evalWithAnswerFn_bind, eval_tweakableHash]

theorem node_zero (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) :
    node f parameter lay tree seed 0 leaf.val
      = evalWithAnswerFn f (leafHash parameter lay tree leaf
          (otsEndpoint f parameter lay tree leaf seed) : OracleComp HashSpec Digest) := by
  simp only [node, Seeded.treeNode_zero, Seeded.treeLeaf, evalWithAnswerFn_bind, leafOfNat_val,
    eval_oneTimePublicKey]

omit [Params] in
/-- Climbing from a leaf with the siblings of its ancestors reaches its ancestor, under the answers.

It is the completeness of a Merkle tree, read through the fixed answers. -/
theorem eval_climb_siblings
    {hash : Merkle.Position → Digest → Digest → OracleComp HashSpec Digest}
    {leaves : Nat → OracleComp HashSpec Digest} (j : Nat) (path : Nat → Digest) (levels : Nat)
    (hpath : ∀ level, level < levels → path level =
      evalWithAnswerFn f (Merkle.node hash leaves ⟨level, Nat.xor (j / 2 ^ level) 1⟩)) :
    evalWithAnswerFn f (Merkle.climb hash ⟨0, j⟩ (evalWithAnswerFn f (leaves j))
        (List.ofFn fun level : Fin levels => path level.val))
      = evalWithAnswerFn f (Merkle.node hash leaves ⟨levels, j / 2 ^ levels⟩) := by
  -- Read the node hash and the leaves through the answers.
  let φ : ∀ {β : Type}, OracleComp HashSpec β → Id β := fun x => evalWithAnswerFn f x
  have hbind : ∀ {β γ : Type} (x : OracleComp HashSpec β) (g : β → OracleComp HashSpec γ),
      φ (x >>= g) = φ x >>= fun b => φ (g b) := fun _ _ => evalWithAnswerFn_bind _ _ _
  have hnode := Merkle.node_map hash φ hbind leaves
  -- The path holds the honest siblings, one per level.
  have hsiblings : (List.ofFn fun level : Fin levels => path level.val) =
      (Merkle.siblings (fun q left right => φ (hash q left right)) (fun i => φ (leaves i))
        ⟨0, j⟩ levels).run.toList := by
    rw [← Merkle.ofFn_take_siblings _ _ _ levels levels le_rfl, List.take_of_length_le (by simp)]
    congr 1
    funext level
    rw [hpath level.val level.isLt, Merkle.Position.ancestor_mk_zero]
    exact hnode _
  -- The climb from the honest leaf with the honest siblings reaches the honest ancestor.
  refine (Merkle.climb_map_monad hash φ (fun _ => rfl) hbind _ ⟨0, j⟩ _).trans ?_
  rw [hsiblings]
  refine (Merkle.climb_siblings (fun q left right => φ (hash q left right))
    (fun i => φ (leaves i)) levels ⟨0, j⟩).trans ?_
  rw [Merkle.Position.ancestor_mk_zero]
  exact (hnode _).symm

/-- Folding the honest leaf through the honest siblings reaches the honest node above it. -/
theorem eval_treeFold_path (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels : Nat, (∀ level, level < levels →
        path level = node f parameter lay tree seed level (Nat.xor (leaf.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (treeFold parameter lay tree leaf path levels
          (node f parameter lay tree seed 0 leaf.val) : OracleComp HashSpec Digest)
        = node f parameter lay tree seed levels (leaf.val / 2 ^ levels) :=
  fun levels hpath => eval_climb_siblings f leaf.val path levels hpath

/-!
## FORS

The opened secret hashes to the honest leaf, and the fold climbs the honest tree to its root.

`T_k` of the `k` roots is the FORS public key that the bottom layer signed.
-/

section Tree

variable (parameter : PublicParameter) (index : Index) (κ : FTree) (seed : MasterSeed)

/-- The secret of a FORS leaf, from its seed derivation. -/
def forsSecretValue (leaf : FLeaf) : Digest :=
  evalWithAnswerFn f (Seeded.forsSecret parameter index κ leaf seed : OracleComp HashSpec Digest)

theorem forsSecretValue_eq (leaf : FLeaf) :
    forsSecretValue f parameter index κ seed leaf =
      truncateHash (f (keygenHashInput parameter (.fors index κ leaf) seed)) := by
  simp only [forsSecretValue, Seeded.forsSecret, eval_deriveKey]

/-- The honest value of a FORS node at tree level `level`. -/
def forsNodeValue (level node : Nat) : Digest :=
  evalWithAnswerFn f
    (Seeded.forsNode parameter index κ seed level node : OracleComp HashSpec Digest)

/-- The honest leaf of a FORS tree: the hash of its secret. -/
def forsLeafValue (leaf : FLeaf) : Digest :=
  truncateHash (f (tweakableHashInput parameter (.forsLeaf index κ leaf)
    (bytesLE 16 (forsSecretValue f parameter index κ seed leaf))))

private theorem forsNodeValue_zero_mod (node : Nat) :
    forsNodeValue f parameter index κ seed 0 node =
      forsLeafValue f parameter index κ seed
        ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
  simp only [forsNodeValue, Seeded.forsNode_zero, Seeded.forsLeaf, forsLeafHash,
    evalWithAnswerFn_bind, eval_tweakableHash, forsLeafValue, forsSecretValue]

theorem forsNodeValue_zero (leaf : FLeaf) :
    forsNodeValue f parameter index κ seed 0 leaf.val =
      forsLeafValue f parameter index κ seed leaf := by
  have hl : (⟨leaf.val % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : FLeaf) = leaf :=
    Fin.ext (Nat.mod_eq_of_lt leaf.isLt)
  rw [forsNodeValue_zero_mod, hl]

theorem forsNodeValue_succ (level node : Nat) (hlevel : level < forsHeight) :
    forsNodeValue f parameter index κ seed (level + 1) node
      = truncateHash (f (tweakableHashInput parameter
          (.forsNode index κ ⟨level, hlevel⟩
            ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
          (nodePayload (forsNodeValue f parameter index κ seed level (2 * node))
            (forsNodeValue f parameter index κ seed level (2 * node + 1))))) := by
  simp only [forsNodeValue, Seeded.forsNode_succ, evalWithAnswerFn_bind, dite_eq_left hlevel,
    eval_tweakableHash]

/-- Folding the honest leaf through the honest siblings reaches the honest node above it. -/
theorem eval_forsFold_path (leaf : FLeaf) (path : Fin forsHeight → Digest) :
    ∀ levels : Nat, levels ≤ forsHeight →
      (∀ (level : Nat) (hlevel : level < forsHeight), level < levels →
        path ⟨level, hlevel⟩ =
          forsNodeValue f parameter index κ seed level (Nat.xor (leaf.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (forsFold parameter index κ leaf path levels
          (forsNodeValue f parameter index κ seed 0 leaf.val) : OracleComp HashSpec Digest)
        = forsNodeValue f parameter index κ seed levels (leaf.val / 2 ^ levels) :=
  fun levels hheight hpath => eval_climb_siblings f leaf.val (extendPath path) levels
    fun level hlevel => by
      rw [extendPath, dite_eq_left (by omega)]
      exact hpath level (by omega) hlevel

end Tree

section Key

variable (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

/-- The honest root of a FORS tree, its node at level `a`: its part of the FORS key. -/
def rootValue (κ : FTree) : Digest :=
  forsNodeValue f parameter index κ seed forsHeight 0

@[simp] theorem eval_forsPublicKey (roots : ForsKey) :
    evalWithAnswerFn f (forsPublicKey parameter index roots : OracleComp HashSpec Digest)
      = truncateHash
          (f (tweakableHashInput parameter (.forsRoots index) (rootsPayload roots))) := by
  simp [forsPublicKey]

/-- The FORS public key is `T_k` of the honest roots. -/
theorem forsKey_eq :
    evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec Digest) =
      evalWithAnswerFn f (forsPublicKey parameter index fun κ => rootValue f parameter index seed κ
        : OracleComp HashSpec Digest) := by
  simp only [Seeded.forsKey, evalWithAnswerFn_bind, eval_sequenceFin]
  rfl

/-- The honest opening of one tree. -/
theorem eval_treeOpen (κ : FTree) (leaf : FLeaf) :
    evalWithAnswerFn f
        (Seeded.treeOpen parameter index κ leaf seed : OracleComp HashSpec TreeOpening)
      = ⟨forsSecretValue f parameter index κ seed leaf,
          fun level => forsNodeValue f parameter index κ seed level.val
            (Nat.xor (leaf.val / 2 ^ level.val) 1)⟩ := by
  simp only [Seeded.treeOpen, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin]
  rfl

/-- The verifier recovers the honest root of every tree. -/
theorem eval_treeRecover (κ : FTree) (leaf : FLeaf) :
    evalWithAnswerFn f (treeRecover parameter index κ leaf
        (evalWithAnswerFn f
          (Seeded.treeOpen parameter index κ leaf seed : OracleComp HashSpec TreeOpening))
        : OracleComp HashSpec Digest)
      = rootValue f parameter index seed κ := by
  rw [eval_treeOpen]
  have hleaf : evalWithAnswerFn f (forsLeafHash parameter index κ leaf
      (forsSecretValue f parameter index κ seed leaf) : OracleComp HashSpec Digest) =
      forsNodeValue f parameter index κ seed 0 leaf.val := by
    rw [forsNodeValue_zero, forsLeafHash, eval_tweakableHash]
    rfl
  simp only [treeRecover, evalWithAnswerFn_bind, hleaf]
  rw [eval_forsFold_path f parameter index κ seed leaf _ forsHeight le_rfl
    (fun level hlevel _ => rfl), Nat.div_eq_of_lt leaf.isLt]
  rfl

/-- The verifier recovers the honest roots. -/
theorem eval_forsRecover (leaves : FTree → FLeaf) :
    evalWithAnswerFn f (forsRecover parameter index leaves
        (evalWithAnswerFn f (Seeded.forsOpen parameter index leaves seed
          : OracleComp HashSpec (FTree → TreeOpening))) : OracleComp HashSpec ForsKey)
      = fun κ => rootValue f parameter index seed κ := by
  simp only [forsRecover, Seeded.forsOpen, eval_sequenceFin, eval_treeRecover]

/-- The verifier recovers the FORS public key that the bottom layer signed. -/
theorem eval_forsPublicKey_forsRecover (leaves : FTree → FLeaf) :
    evalWithAnswerFn f (forsPublicKey parameter index
        (evalWithAnswerFn f (forsRecover parameter index leaves
          (evalWithAnswerFn f (Seeded.forsOpen parameter index leaves seed
            : OracleComp HashSpec (FTree → TreeOpening))) : OracleComp HashSpec ForsKey))
        : OracleComp HashSpec Digest)
      = evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec Digest) := by
  rw [eval_forsRecover, forsKey_eq]

end Key

end SphincsSecurity.Completeness
