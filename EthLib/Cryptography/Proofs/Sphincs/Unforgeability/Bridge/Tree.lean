module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Ots

/-!
# Proofs: EthLib's one-time keys and trees are the model's

EthLib computes a one-time key, a tree node, a path and a fold with the same calls as the model.

The calls come in the same order, so each routine with the query is the model's, value for value.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity.Concrete (tweakableHash sequenceFin)

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSig.HashSpec m]

/-! ## One-time keys -/

omit [HasQuery HashSig.HashSpec m] in
/-- A vector computed in order is the model's function computed in order, over equal lengths. -/
theorem ofFnInOrder_eq_sequenceFin_cast {α β : Type} {n n' : Nat} (h : n = n')
    (c : Fin n' → m α) (g : α → β) :
    ofFnInOrder n (fun i => g <$> c (Fin.cast h i))
      = (fun f => Vector.ofFn fun i => g (f (Fin.cast h i))) <$> sequenceFin c := by
  subst h
  exact ofFnInOrder_eq_sequenceFin n c g

/-- The starts of a key's chains are the model's secrets. -/
theorem chainStarts_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) :
    chainStarts (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S)) (keyOf lay tree leaf)
      = ofChains <$> SphincsSecurity.Seeded.otsSecrets (m := m) P lay tree leaf S := by
  have h : V / 2 = 32 := rfl
  unfold chainStarts SphincsSecurity.Seeded.otsSecrets
  have hprf : (fun j : Fin (V / 2) => seedPrf (queryH (m := m)) (ofSeed S) (ofParam P)
      (addrPrf (keyOf lay tree leaf) j) .empty) = fun j => (ofOutput <$>
        SphincsSecurity.deriveOutput (m := m) P (.ots lay tree leaf (Fin.cast h j)) S :
          m EthLib.Cryptography.Sphincs.HashOutput) :=
    funext fun j => otsPrf_queryH S P lay tree leaf (Fin.cast h j)
  rw [hprf, ofFnInOrder_eq_sequenceFin_cast (β := EthLib.Cryptography.Sphincs.HashOutput) h
    (fun pair : SphincsSecurity.ChainPair =>
      SphincsSecurity.deriveOutput (m := m) P (.ots lay tree leaf pair) S) ofOutput]
  simp only [map_bind, map_pure]
  refine (bind_map_left _ _ _).trans (bind_congr fun outs => ?_)
  refine congrArg pure (Vector.ext fun i hi => ?_)
  simp only [ofChains, Vector.getElem_ofFn]
  erw [Vector.getElem_ofFn]
  exact halfOf_mod_two_ofOutput _ i

/-- The leaf of a key, from its seed derivations, is the model's leaf of its chain ends. -/
theorem otsPublicLeaf_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) :
    otsPublicLeaf (queryH (m := m)) (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S))
        (keyOf lay tree leaf)
      = ofDigest <$> (SphincsSecurity.Seeded.oneTimePublicKey (m := m) P lay tree leaf S >>=
          SphincsSecurity.Concrete.leafHash P lay tree leaf) := by
  unfold otsPublicLeaf SphincsSecurity.Seeded.oneTimePublicKey
  rw [chainStarts_queryH, bind_map_left]
  simp only [bind_assoc, map_bind]
  refine bind_congr fun secrets => ?_
  have hchains : (ofFnInOrder V fun i => chain (queryH (m := m)) (ofParam P) (keyOf lay tree leaf)
      i 0 (CHAIN_LENGTH - 1) (by decide) (ofChains secrets)[i])
      = ofFnInOrder V fun i => ofDigest <$> SphincsSecurity.Concrete.chainWalk (m := m) P lay
          tree leaf ⟨i.val, i.isLt⟩ 0 (SphincsSecurity.chainLength - 1) (secrets ⟨i.val, i.isLt⟩) :=
    congrArg (ofFnInOrder V) (funext fun i => by
      simp only [ofChains, Fin.getElem_fin, Vector.getElem_ofFn]
      exact chain_queryH P lay tree leaf i 0 _ _ _)
  rw [hchains, ofFnInOrder_eq_sequenceFin V (fun i : Fin V =>
    SphincsSecurity.Concrete.chainWalk (m := m) P lay tree leaf ⟨i.val, i.isLt⟩ 0
      (SphincsSecurity.chainLength - 1) (secrets ⟨i.val, i.isLt⟩)) ofDigest, bind_map_left]
  refine bind_congr fun ends => ?_
  exact otsLeafHash_queryH P lay tree leaf ends

/-- A model counter as EthLib's. -/
def ofCounter (c : SphincsSecurity.Counter) : UInt32 :=
  UInt32.ofNat c.toNat

/-- A model one-time signature as EthLib's. -/
def ofOts (s : SphincsSecurity.Counter × (SphincsSecurity.ChainIndex → SphincsSecurity.Digest)) :
    UInt32 × Vector Digest V :=
  (ofCounter s.1, ofChains s.2)

/-- The counter search, then the chains, is the model's search from the same counter. -/
theorem findCounter_bind_queryH (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex) (msg : ByteArray) :
    ∀ (fuel c : Nat),
      (Internal.findCounter (queryH (m := m)) (ofParam P) (keyOf lay tree leaf) msg c fuel >>=
        fun r => match r with
          | none => pure none
          | some (counter, x) => do
            let starts ← chainStarts (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S))
              (keyOf lay tree leaf)
            let y ← ofFnInOrder V fun i =>
              chain (queryH (m := m)) (ofParam P) (keyOf lay tree leaf) i 0 x[i] (by simp)
                starts[i]
            pure (some (counter, y)))
        = Option.map ofOts <$> SphincsSecurity.Seeded.otsSignFrom (m := m) P lay tree leaf S
            msg.data.toList fuel c
  | 0, c => by
    simp [Internal.findCounter, Wots.findFirst, SphincsSecurity.Seeded.otsSignFrom]
  | fuel + 1, c => by
    have hcounter : BitVec.ofNat 32 (UInt32.ofNat c).toNat
        = BitVec.ofNat SphincsSecurity.counterBits c := by
      apply BitVec.eq_of_toNat_eq
      simp [SphincsSecurity.counterBits]
    have ih := findCounter_bind_queryH S P lay tree leaf msg fuel (c + 1)
    unfold Internal.findCounter at ih ⊢
    rw [Wots.findFirst, encode_queryH, hcounter]
    simp only [SphincsSecurity.Seeded.otsSignFrom, bind_map_left, bind_assoc, map_bind]
    refine bind_congr fun r => ?_
    cases r with
    | none => simpa using ih
    | some enc =>
      simp only [Option.map_some, pure_bind]
      rw [chainStarts_queryH, bind_map_left, map_bind]
      refine bind_congr fun secrets => ?_
      have hchains : (ofFnInOrder V fun i => chain (queryH (m := m)) (ofParam P)
          (keyOf lay tree leaf) i 0 (ofEncoding enc)[i] (by simp) (ofChains secrets)[i])
          = ofFnInOrder V fun i => ofDigest <$> SphincsSecurity.Concrete.chainWalk (m := m) P
              lay tree leaf ⟨i.val, i.isLt⟩ 0 (enc ⟨i.val, i.isLt⟩).val
              (secrets ⟨i.val, i.isLt⟩) :=
        congrArg (ofFnInOrder V) (funext fun i => by
          simp only [ofChains, ofEncoding, Fin.getElem_fin, Vector.getElem_ofFn]
          exact chain_queryH P lay tree leaf i 0 _ _ _)
      rw [hchains, ofFnInOrder_eq_sequenceFin V (fun i : Fin V =>
        SphincsSecurity.Concrete.chainWalk (m := m) P lay tree leaf ⟨i.val, i.isLt⟩ 0
          (enc ⟨i.val, i.isLt⟩).val (secrets ⟨i.val, i.isLt⟩)) ofDigest, bind_map_left,
        map_bind]
      refine bind_congr fun values => ?_
      simp only [map_pure, Option.map_some, ofOts, ofCounter]
      congr 3
      apply UInt32.toNat.inj
      simp [SphincsSecurity.counterBits]

/-- EthLib's one-time signature is the model's. -/
theorem otsSign_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) (msg : ByteArray) :
    otsSign (queryH (m := m)) (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S))
        (keyOf lay tree leaf) msg
      = Option.map ofOts <$> SphincsSecurity.Seeded.otsSign (m := m) P lay tree leaf S
          msg.data.toList := by
  rw [otsSign, SphincsSecurity.Seeded.otsSign,
    show SphincsSecurity.encodingAttemptLimit = MAX_COUNTER_TRIALS from rfl,
    ← findCounter_bind_queryH]
  refine bind_congr fun r => ?_
  rcases r with _ | ⟨c, x⟩ <;> rfl

/-! ## Nodes and roots -/

/-- A node of a tree whose leaves are in the tree is the model's node. -/
theorem node_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex) :
    ∀ (level j : Nat), level ≤ TOP_HEIGHT → j < 2 ^ (TOP_HEIGHT - level) →
      Merkle.node (nodeHash (queryH (m := m)) (ofParam P) (layerOf lay) tree.val)
          (leaves (queryH (m := m)) (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S))
            (layerOf lay) tree.val) level j
        = ofDigest <$> SphincsSecurity.Seeded.treeNode (m := m) P lay tree S level j
  | 0, j, _, hj => by
    have hleaf : keyOf lay tree (SphincsSecurity.Concrete.leafOfNat j)
        = ⟨layerOf lay, tree.val, j⟩ := by
      simp only [keyOf, SphincsSecurity.Concrete.leafOfNat, OtsKey.mk.injEq, true_and]
      exact Nat.mod_eq_of_lt hj
    rw [Merkle.node, leaves, ← hleaf, otsPublicLeaf_queryH]
    rfl
  | level + 1, j, hlevel, hj => by
    have hpow : 2 ^ (TOP_HEIGHT - level) = 2 * 2 ^ (TOP_HEIGHT - (level + 1)) := by
      rw [show TOP_HEIGHT - level = TOP_HEIGHT - (level + 1) + 1 by omega, pow_succ]
      ring
    rw [Merkle.node, node_queryH S P lay tree level (2 * j) (by omega) (by omega),
      node_queryH S P lay tree level (2 * j + 1) (by omega) (by omega)]
    simp only [SphincsSecurity.Seeded.treeNode, bind_map_left, map_bind]
    refine bind_congr fun left => bind_congr fun right => ?_
    exact nodeHash_queryH P lay tree (level + 1) j hlevel left right

/-- In EthLib's configuration the kept part of every tree is the whole tree. -/
theorem keptHeight_eq (lay : SphincsSecurity.Layer) :
    SphincsSecurity.keptHeight lay = SphincsSecurity.layerHeight lay := by
  fin_cases lay <;> decide

/-- In EthLib's configuration the kept part of every tree sits at position 0. -/
theorem keptPosition_eq (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer) :
    SphincsSecurity.keptPosition P lay = 0 := by
  unfold SphincsSecurity.keptPosition SphincsSecurity.subtreePosition
  split <;> simp [SphincsSecurity.totalHeight, SphincsSecurity.subtreeHeight, Nat.mod_one]

/-- The root of a tree is the model's root. -/
theorem treeRoot_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex) :
    treeRoot (queryH (m := m)) (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S)) (layerOf lay)
        tree.val
      = ofDigest <$> SphincsSecurity.Seeded.treeRoot (m := m) P lay tree S := by
  have hh := height_layerOf lay
  have hle : (layerOf lay).height ≤ TOP_HEIGHT := Layer.height_le _
  rw [treeRoot, Merkle.root, node_queryH S P lay tree _ 0 hle (Nat.two_pow_pos _),
    SphincsSecurity.Seeded.treeRoot, keptHeight_eq, Nat.sub_self,
    SphincsSecurity.Seeded.spineNode, keptHeight_eq, keptPosition_eq, hh]

/-! ## Paths -/

/-- A model path as EthLib's. -/
def ofPath {n : Nat} (g : Fin n → SphincsSecurity.Digest) : Vector Digest n :=
  Vector.ofFn fun i => ofDigest (g i)

/-- The siblings above a leaf in the tree are the model's nodes, level by level. -/
theorem siblings_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex) (e : Nat)
    (he : e < 2 ^ TOP_HEIGHT) :
    ∀ (n level : Nat), level + n ≤ TOP_HEIGHT →
      Merkle.siblings (nodeHash (queryH (m := m)) (ofParam P) (layerOf lay) tree.val)
          (leaves (queryH (m := m)) (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S))
            (layerOf lay) tree.val) level (e / 2 ^ level) n
        = ofPath <$> sequenceFin (m := m) fun i : Fin n =>
            SphincsSecurity.Seeded.treeNode P lay tree S (level + i.val)
              (Nat.xor (e / 2 ^ (level + i.val)) 1)
  | 0, level, _ => by
    simp only [Merkle.siblings, sequenceFin, map_pure]
    congr 1
  | n + 1, level, hn => by
    -- The node below level `TOP_HEIGHT - level` has index below `2^(TOP_HEIGHT - level)`.
    have hlt : e / 2 ^ level < 2 ^ (TOP_HEIGHT - level) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      exact he.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hsib : (e / 2 ^ level) ^^^ 1 < 2 ^ (TOP_HEIGHT - level) :=
      Nat.xor_lt_two_pow hlt (Nat.one_lt_two_pow (by omega))
    have hdiv : e / 2 ^ level / 2 = e / 2 ^ (level + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    rw [Merkle.siblings, node_queryH S P lay tree level _ (by omega) hsib, hdiv,
      siblings_queryH S P lay tree e he n (level + 1) (by omega)]
    simp only [sequenceFin, map_bind, bind_map_left, map_pure, Fin.val_zero, Nat.add_zero]
    refine bind_congr fun head => ?_
    have htail : (fun i : Fin n => SphincsSecurity.Seeded.treeNode (m := m) P lay tree S
        (level + 1 + i.val) (Nat.xor (e / 2 ^ (level + 1 + i.val)) 1))
        = fun i : Fin n => SphincsSecurity.Seeded.treeNode (m := m) P lay tree S
          (level + i.succ.val) (Nat.xor (e / 2 ^ (level + i.succ.val)) 1) := by
      funext i
      rw [Fin.val_succ, Nat.add_right_comm, Nat.add_assoc]
    rw [htail]
    refine bind_congr fun tail => ?_
    congr 1
    apply Vector.ext
    intro i hi
    cases i with
    | zero => simp [ofPath]
    | succ i => simp [ofPath]

/-- The path of a leaf is the model's nodes along it. -/
theorem path_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) :
    path (queryH (m := m)) (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S)) (layerOf lay)
        tree.val leaf.val
      = ofPath <$> sequenceFin (m := m) fun i : Fin (layerOf lay).height =>
          SphincsSecurity.Seeded.treeNode P lay tree S i.val
            (Nat.xor (leaf.val / 2 ^ i.val) 1) := by
  have h := siblings_queryH (m := m) S P lay tree leaf.val leaf.isLt (layerOf lay).height 0
    (by simpa using Layer.height_le (layerOf lay))
  simp only [pow_zero, Nat.div_one, Nat.zero_add] at h
  exact h

/-! ## Folding a path -/

/-- The climb from a level is the model's fold, continued from that level. -/
theorem climb_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex)
    (path : Nat → SphincsSecurity.Digest) (v : SphincsSecurity.Digest) :
    ∀ (n level : Nat), level + n ≤ TOP_HEIGHT →
      ofDigest <$> SphincsSecurity.Concrete.treeFold (m := m) P lay tree leaf path (level + n) v
        = SphincsSecurity.Concrete.treeFold (m := m) P lay tree leaf path level v >>= fun c =>
            Merkle.climb (nodeHash (queryH (m := m)) (ofParam P) (layerOf lay) tree.val) level
              (leaf.val / 2 ^ level) (ofDigest c)
              (List.ofFn fun i : Fin n => ofDigest (path (level + i.val)))
  | 0, level, _ => by simp [Merkle.climb]
  | n + 1, level, hn => by
    rw [show level + (n + 1) = level + 1 + n by omega,
      climb_queryH P lay tree leaf path v n (level + 1) (by omega)]
    simp only [SphincsSecurity.Concrete.treeFold, bind_assoc, List.ofFn_succ, Fin.val_zero,
      Nat.add_zero, Fin.val_succ]
    refine bind_congr fun c => ?_
    have hdiv : leaf.val / 2 ^ level / 2 = leaf.val / 2 ^ (level + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    have hlist : (List.ofFn fun i : Fin n => ofDigest (path (level + (i.val + 1))))
        = List.ofFn fun i : Fin n => ofDigest (path (level + 1 + i.val)) :=
      congrArg List.ofFn (funext fun i => by rw [Nat.add_right_comm, Nat.add_assoc])
    rw [Merkle.climb, hdiv, hlist, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (leaf.val / 2 ^ level) with h | h
    · simp only [h, Merkle.ordered, ↓reduceIte, Nat.zero_ne_one, decide_false,
        Bool.false_eq_true]
      rw [nodeHash_queryH P lay tree (level + 1) _ (by omega), bind_map_left]
    · simp only [h, Merkle.ordered, ↓reduceIte, Nat.one_ne_zero, decide_true]
      rw [nodeHash_queryH P lay tree (level + 1) _ (by omega), bind_map_left]

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
