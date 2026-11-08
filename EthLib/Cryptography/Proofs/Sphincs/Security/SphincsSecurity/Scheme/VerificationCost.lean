module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Layout
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Code
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Correctness

/-!
# The verification cost

This file counts the compressions of the hash calls that verification makes, for three hashes.

An addressed hash input is `PK.seed || ADRS || payload`, which is `48 + |payload|` bytes.

A digest call hashes 84 bytes.

Every hash takes its input of `n` bytes as it is, and the model charges each call as follows:

- Keccak-256: `n / 136 + 1` permutations, since the padding adds at least one byte.
- BLAKE2s: `ceil(n / 64)` compressions, since the last block is padded with zeros.
- SHA-256: `ceil((n + 9) / 64)` compressions, since the padding adds at least 9 bytes.

The answers of the oracle stay arbitrary, and only the byte lengths count.

An accepted signature costs exactly the closed-form verification cost.

Every other signature costs at most that.
-/

@[expose] public section

-- The byte-length lemmas must see the digest and parameter widths as `8 * n` to match.
set_option backward.isDefEq.respectTransparency false

open OracleComp OracleSpec Finset

namespace SphincsSecurity.Cost

variable [Params]

open Concrete

/-- The three hash functions that the cost model covers. -/
inductive HashFn where
  | keccak256
  | blake2s
  | sha256
deriving DecidableEq

/-- The compressions of one call on an `n`-byte input. -/
def HashFn.cost : HashFn → Nat → Nat
  | .keccak256, n => n / 136 + 1
  | .blake2s, n => (n + 63) / 64
  | .sha256, n => (n + 9 + 63) / 64

variable (H : HashFn)

/-- The hash inputs of a run under a fixed answer function, in order. -/
def hashTrace {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) :
    List HashInput := ((simulateQ f.withLogging oa).run).2.map Sigma.fst

/-- The compressions of a run under a fixed answer function.

Each input length includes the parameter and the address. -/
def compressions {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) : Nat :=
  ((hashTrace f oa).map (fun input => H.cost input.length)).sum

omit [Params] in
@[simp] theorem hashTrace_pure {α : Type} (f : QueryImpl HashSpec Id) (x : α) :
    hashTrace f (pure x) = [] := rfl

omit [Params] in
@[simp] theorem hashTrace_query_bind {α : Type} (f : QueryImpl HashSpec Id)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    hashTrace f (liftM (HashSpec.query input) >>= next) =
      input :: hashTrace f (next (f input)) := by
  simp [hashTrace, QueryImpl.withLogging_apply, WriterT.run_bind, WriterT.run_tell]
  rfl

omit [Params] in
theorem hashTrace_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    hashTrace f (oa >>= next) = hashTrace f oa ++
      hashTrace f (next (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind input rest ih =>
      rw [bind_assoc, hashTrace_query_bind, hashTrace_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, List.cons_append]

omit [Params] in
@[simp] theorem compressions_pure {α : Type} (f : QueryImpl HashSpec Id) (x : α) :
    compressions H f (pure x) = 0 := rfl

omit [Params] in
theorem compressions_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    compressions H f (oa >>= next) = compressions H f oa +
      compressions H f (next (evalWithAnswerFn f oa)) := by
  simp [compressions, hashTrace_bind]

omit [Params] in
@[simp] theorem compressions_oracleHash (f : QueryImpl HashSpec Id) (input : HashInput) :
    compressions H f (oracleHash input : OracleComp HashSpec HashOutput) = H.cost input.length := by
  simpa [compressions, oracleHash] using
    congrArg (fun trace => (trace.map fun input => H.cost input.length).sum)
      (hashTrace_query_bind f input (pure : HashOutput → OracleComp HashSpec HashOutput))

@[simp] theorem compressions_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    compressions H f (Concrete.tweakableHash parameter domain payload) =
      H.cost (48 + payload.length) := by
  rw [Concrete.tweakableHash, compressions_bind, compressions_oracleHash,
    compressions_pure, Nat.add_zero, tweakableHashInput_length]

omit [Params] in
theorem compressions_sequenceFin {α : Type} {n : Nat} (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α) :
    compressions H f (sequenceFin computation) = ∑ i : Fin n, compressions H f (computation i) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, compressions_bind]
      simp only [compressions_bind, compressions_pure, Nat.add_zero, ih, Fin.sum_univ_succ]

/-- The cost of a chain step, which hashes 64 bytes. -/
abbrev stepCost : Nat := H.cost 64

/-- The cost of a tree node, which hashes 80 bytes. -/
abbrev nodeCost : Nat := H.cost 80

theorem compressions_chainWalk (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    compressions H f (chainWalk parameter lay tree leaf chain start steps value) =
      steps * stepCost H := by
  induction steps with
  | zero => simp [chainWalk]
  | succ steps ih =>
      rw [chainWalk, compressions_bind, dite_eq_left (by omega), compressions_tweakableHash,
        bytesLE_length, ih (by omega), Nat.succ_mul]

@[simp] theorem compressions_recoverChain (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (value : Digest) :
    compressions H f (recoverChain parameter lay tree leaf chain digit value) =
      (chainLength - 1 - digit.val) * stepCost H := by
  apply compressions_chainWalk
  have := digit.isLt
  omega

/-- A one-time leaf hashes its 64 chain ends: 1,072 bytes. -/
@[simp] theorem compressions_leafHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    compressions H f (leafHash parameter lay tree leaf endpoints) = H.cost 1072 := by
  rw [leafHash, compressions_tweakableHash, leafPayload_length]

/-- The encoding hashes the message and the counter: `48 + |M| + 4` bytes. -/
@[simp] theorem compressions_encode (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) :
    compressions H f (encode parameter lay tree leaf message counter) =
      H.cost (48 + (message.length + 4)) := by
  simp only [encode, compressions_bind, compressions_tweakableHash, List.length_append,
    bytesBE_length, compressions_pure, Nat.add_zero]

theorem compressions_treeFold (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (path : Nat → Digest)
    (levels : Nat) (value : Digest) :
    compressions H f (treeFold parameter lay tree leaf path levels value) =
      levels * nodeCost H := by
  induction levels with
  | zero => simp [treeFold]
  | succ levels ih =>
      rw [treeFold, compressions_bind, ih, Nat.succ_mul]
      dsimp only
      split <;> simp [compressions_tweakableHash, nodePayload, bytesLE_length]

/-- The cost of one FORS tree: the leaf, which hashes 64 bytes, and `a` folds up to the root. -/
def treeCost : Nat := stepCost H + forsHeight * nodeCost H

section Tree

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (κ : FTree)

@[simp] theorem compressions_forsLeafHash (leaf : FLeaf) (secret : Digest) :
    compressions H f (forsLeafHash parameter index κ leaf secret) = stepCost H := by
  rw [forsLeafHash, compressions_tweakableHash, bytesLE_length]

theorem compressions_forsFold (leaf : FLeaf) (path : Fin forsHeight → Digest)
    (levels : Nat) (hlevels : levels ≤ forsHeight) (value : Digest) :
    compressions H f (forsFold parameter index κ leaf path levels value) = levels * nodeCost H := by
  induction levels with
  | zero => simp [forsFold]
  | succ levels ih =>
      rw [forsFold, compressions_bind, ih (by omega), dite_eq_left (by omega), Nat.succ_mul]
      dsimp only
      split <;> simp [compressions_tweakableHash, nodePayload, bytesLE_length]

@[simp] theorem compressions_treeRecover (leaf : FLeaf) (opening : TreeOpening) :
    compressions H f (treeRecover parameter index κ leaf opening) = treeCost H := by
  rw [treeRecover, compressions_bind, compressions_forsLeafHash,
    compressions_forsFold H f parameter index κ _ _ _ le_rfl, treeCost]

end Tree

/-- The FORS recovery costs `k` trees. -/
@[simp] theorem compressions_forsRecover (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) :
    compressions H f (forsRecover parameter index leaves opening) = forsTrees * treeCost H := by
  rw [forsRecover, compressions_sequenceFin]
  simp only [compressions_treeRecover, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The FORS public key `T_k` hashes the `k` roots, `48 + 16 k` bytes. -/
@[simp] theorem compressions_forsPublicKey (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (roots : ForsKey) :
    compressions H f (forsPublicKey parameter index roots) = H.cost (48 + 16 * forsTrees) := by
  rw [forsPublicKey, compressions_tweakableHash, rootsPayload_length]

/-- Every digest call hashes 84 bytes. -/
@[simp] theorem compressions_messageDigest (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    compressions H f (messageDigest parameter root message randomness) =
      digestCalls * H.cost 84 := by
  simp only [messageDigest, compressions_bind, compressions_sequenceFin, messageDigestCall,
    compressions_oracleHash, messageDigestInput, List.length_append,
    bytesLE_length, bytesBE_length, compressions_pure, Nat.add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem encode_valid (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput)
    (counter : Counter) (word : Encoding)
    (hword : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) = some word) : TargetSum.Valid word := by
  simp only [encode, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hword
  unfold TargetSum.decodeDigest at hword
  split at hword
  next hvalid =>
    cases Option.some.inj hword
    exact hvalid
  next => simp at hword

/-- The cost of a one-time recovery after an accepted encoding.

It is the encoding, the 64 chain steps that the verifier walks, and the leaf. -/
def otsCost (messageLength : Nat) : Nat :=
  H.cost (48 + (messageLength + 4)) + 64 * stepCost H + H.cost 1072

/-- A one-time recovery that returns a leaf costs the cost above.

A recovery that returns nothing costs the encoding alone. -/
theorem compressions_otsLeaf (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput)
    (counter : Counter) (values : ChainIndex → Digest) :
    compressions H f (otsLeaf parameter lay tree leaf message counter values) =
      if (evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values
        : OracleComp HashSpec (Option Digest))).isSome then otsCost H message.length
      else H.cost (48 + (message.length + 4)) := by
  cases henc : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) with
  | none =>
      simp only [otsLeaf, compressions_bind, compressions_encode, evalWithAnswerFn_bind,
        henc, evalWithAnswerFn_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        compressions_pure, Nat.add_zero]
  | some word =>
      have hvalid := encode_valid f parameter lay tree leaf message counter word henc
      simp only [otsLeaf, compressions_bind, compressions_encode, evalWithAnswerFn_bind,
        henc, evalWithAnswerFn_pure, Option.isSome_some, ↓reduceIte,
        compressions_sequenceFin, compressions_recoverChain, compressions_leafHash,
        compressions_pure, Nat.add_zero, ← Finset.sum_mul,
        Completeness.verification_chain_steps word hvalid, otsCost]
      ring

/-- The cost of one layer of the walk.

It is the one-time recovery of its 16-byte message and the fold of its path. -/
def layerCost (lay : Layer) : Nat :=
  otsCost H 16 + layerHeight lay * nodeCost H

attribute [local irreducible] otsLeaf encode sequenceFin chainWalk recoverChain leafHash
  forsRecover forsPublicKey treeFold messageDigest

/-- The walk from the layer `k` steps above the bottom costs at most the sum of its layer costs.

If the walk returns a root, the cost is exactly that sum. -/
theorem compressions_verifyLayers (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (signature : Signature) :
    ∀ n k (message : HashInput), k + n = numLayers → 0 < n → message.length = 16 →
      (compressions H f (verifyLayers parameter index signature n message) ≤
        ∑ j ∈ Finset.Ico k numLayers, layerCost H (layerUp j)) ∧
      ((evalWithAnswerFn f (verifyLayers parameter index signature n message
          : OracleComp HashSpec (Option Digest))).isSome →
        compressions H f (verifyLayers parameter index signature n message) =
          ∑ j ∈ Finset.Ico k numLayers, layerCost H (layerUp j)) := by
  intro n
  induction n with
  | zero => intro k _ _ hn; exact absurd hn (Nat.lt_irrefl 0)
  | succ n ih =>
      intro k message hkn _ hlen
      have hn : n < numLayers := by omega
      have hlay : (⟨n, hn⟩ : Layer) = layerUp k := by
        apply Fin.ext; simp only [layerUp]; omega
      have hsplit : ∑ j ∈ Finset.Ico k numLayers, layerCost H (layerUp j) =
          layerCost H (layerUp k) +
            ∑ j ∈ Finset.Ico (k + 1) numLayers, layerCost H (layerUp j) :=
        Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      rw [verifyLayers, dite_eq_left hn, hlay, compressions_bind, compressions_otsLeaf]
      simp only [evalWithAnswerFn_bind]
      cases hleaf : evalWithAnswerFn f
          (otsLeaf parameter (layerUp k) (treeIndexAt index (layerUp k))
            (leafIndexAt index (layerUp k)) message (signature.layers (layerUp k)).counter
            (signature.layers (layerUp k)).chainValues : OracleComp HashSpec (Option Digest)) with
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, evalWithAnswerFn_pure,
            compressions_pure, Nat.add_zero, IsEmpty.forall_iff, and_true]
          rw [hsplit, layerCost, otsCost, hlen]
          omega
      | some value =>
          simp only [Option.isSome_some, ↓reduceIte, compressions_bind, compressions_treeFold]
          by_cases hzero : n = 0
          · subst hzero
            have hk : k + 1 = numLayers := by omega
            simp only [↓reduceIte, compressions_pure, evalWithAnswerFn_pure, Option.isSome_some,
              Nat.add_zero, forall_const, evalWithAnswerFn_bind]
            have hrest : ∑ j ∈ Finset.Ico (k + 1) numLayers, layerCost H (layerUp j) = 0 := by
              rw [hk, Finset.Ico_self, Finset.sum_empty]
            rw [hsplit, hrest, layerCost, hlen]
            exact ⟨le_of_eq (by ring), by ring⟩
          · simp only [hzero, ↓reduceIte]
            have hmsg : (rootPayload (evalWithAnswerFn f (treeFold parameter (layerUp k)
                (treeIndexAt index (layerUp k)) (leafIndexAt index (layerUp k))
                (signaturePath signature (layerUp k)) (layerHeight (layerUp k)) value
                  : OracleComp HashSpec Digest))).length = 16 := rootPayload_length _
            obtain ⟨hle, heq⟩ := ih (k + 1) _ (by omega) (Nat.pos_of_ne_zero hzero) hmsg
            rw [hsplit, layerCost, hlen]
            refine ⟨by omega, fun hsome => ?_⟩
            simp only [evalWithAnswerFn_bind] at hsome
            rw [heq hsome]
            ring

/-- The cost of verifying an accepted signature.

It adds the 84-byte digest calls, the `k` FORS trees and `T_k` of their roots (`48 + 16 k` bytes).

It adds, at every layer, the 68-byte encoding of its 16-byte message.

It adds the 64 chain steps and the one-time leaf of every layer.

It adds one node per level of the key, `h` in all. -/
def verifyCost : Nat :=
  digestCalls * H.cost 84 + forsTrees * treeCost H + H.cost (48 + 16 * forsTrees) +
    numLayers * (H.cost 68 + 64 * stepCost H + H.cost 1072) + totalHeight * nodeCost H

/-- The cost of every layer of the walk, in closed form. -/
theorem sum_layerCost :
    ∑ j ∈ Finset.Ico 0 numLayers, layerCost H (layerUp j) =
      numLayers * (H.cost 68 + 64 * stepCost H + H.cost 1072) + totalHeight * nodeCost H := by
  have hheights : ∑ j ∈ Finset.Ico 0 numLayers, layerHeight (layerUp j) = totalHeight := by
    rw [← Finset.range_eq_Ico, ← Fin.sum_univ_eq_sum_range (fun j => layerHeight (layerUp j))]
    rw [Function.Bijective.sum_comp layerUp_bijective (fun lay => layerHeight lay), sum_layerHeight]
  simp only [layerCost, otsCost, Finset.sum_add_distrib, ← Finset.sum_mul, hheights,
    Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.sub_zero]
  ring

attribute [local semireducible] Concrete.verify

/-- The compressions of one verification. -/
def verifyCompressions (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : Nat :=
  compressions H f (Concrete.verify pk message signature : OracleComp HashSpec Bool)

theorem verify_compressions_split (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    verifyCompressions H f pk message signature =
      digestCalls * H.cost 84 + forsTrees * treeCost H + H.cost (48 + 16 * forsTrees) +
        compressions H f (verifyLayers pk.parameter
          (digestIndex (evalWithAnswerFn f (messageDigest pk.parameter pk.root message
            signature.randomness : OracleComp HashSpec MessageDigest))) signature numLayers
          (rootPayload (evalWithAnswerFn f (forsPublicKey pk.parameter
            (digestIndex (evalWithAnswerFn f (messageDigest pk.parameter pk.root message
              signature.randomness : OracleComp HashSpec MessageDigest)))
            (evalWithAnswerFn f (forsRecover pk.parameter
              (digestIndex (evalWithAnswerFn f (messageDigest pk.parameter pk.root message
                signature.randomness : OracleComp HashSpec MessageDigest)))
              (digestLeaves (evalWithAnswerFn f (messageDigest pk.parameter pk.root message
                signature.randomness : OracleComp HashSpec MessageDigest))) signature.fors
              : OracleComp HashSpec ForsKey)) : OracleComp HashSpec Digest)))) := by
  rw [verifyCompressions, Concrete.verify, compressions_bind, compressions_messageDigest,
    compressions_bind, compressions_forsRecover, compressions_bind, compressions_forsPublicKey,
    compressions_bind]
  split <;> simp only [compressions_pure] <;> ring

/-- Every accepted signature costs exactly the verification cost in compressions. -/
theorem verification_compressions (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature)
    (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions H f pk message signature = verifyCost H := by
  rw [verify_compressions_split]
  set digest := evalWithAnswerFn f (messageDigest pk.parameter pk.root message
    signature.randomness : OracleComp HashSpec MessageDigest)
  set key := evalWithAnswerFn f (forsPublicKey pk.parameter (digestIndex digest)
    (evalWithAnswerFn f (forsRecover pk.parameter (digestIndex digest) (digestLeaves digest)
      signature.fors : OracleComp HashSpec ForsKey)) : OracleComp HashSpec Digest)
  have hwalk := compressions_verifyLayers H f pk.parameter (digestIndex digest) signature
    numLayers 0 (rootPayload key) (Nat.zero_add _) numLayers_pos (rootPayload_length _)
  simp only [Concrete.verify, evalWithAnswerFn_bind] at haccept
  split at haccept
  next root hroot =>
    rw [hwalk.2 (by rw [hroot]; rfl), sum_layerCost, verifyCost]
    ring
  next => simp at haccept

/-- No signature, malformed or not, costs more than the verification cost. -/
theorem verification_compressions_le (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    verifyCompressions H f pk message signature ≤ verifyCost H := by
  rw [verify_compressions_split]
  set digest := evalWithAnswerFn f (messageDigest pk.parameter pk.root message
    signature.randomness : OracleComp HashSpec MessageDigest)
  set key := evalWithAnswerFn f (forsPublicKey pk.parameter (digestIndex digest)
    (evalWithAnswerFn f (forsRecover pk.parameter (digestIndex digest) (digestLeaves digest)
      signature.fors : OracleComp HashSpec ForsKey)) : OracleComp HashSpec Digest)
  have hwalk := compressions_verifyLayers H f pk.parameter (digestIndex digest) signature
    numLayers 0 (rootPayload key) (Nat.zero_add _) numLayers_pos (rootPayload_length _)
  have := hwalk.1

  rw [sum_layerCost] at this
  rw [verifyCost]
  omega

end SphincsSecurity.Cost
