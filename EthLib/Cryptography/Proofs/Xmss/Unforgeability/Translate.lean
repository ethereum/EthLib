import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Address
import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Codeword
import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Scheme

/-!
# Proofs: EthLib's hashing is the model's

The security proof runs over a model of leanXMSS (`XmssSecurity`), written over bit vectors.

EthLib's algorithms take the hash `H` as an argument.

Passed `queryH`, a query to the model's oracle, each hashing routine is the model's, call for call.

```text
    EthLib's routine (queryH) (ofBV x)  =  ofBV <$> the model's routine x
```

The model keeps the two layers apart.

Bottom keys are leaf indices below `2^32`, and top keys are indices below `2^16`.

So each routine has one statement per layer.

The equalities hold in every lawful monad with a query to the oracle.
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery XmssSecurity.HashSpec m]

/-! ## Bytes of hash inputs -/

@[simp] theorem toList_data_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

omit [Monad m] [LawfulMonad m] [HasQuery XmssSecurity.HashSpec m] in
/-- A list of functions' values, each a list, flattened. -/
theorem flatMap_ofFn {α β : Type} {n : Nat} (g : α → List β) (f : Fin n → α) :
    (List.ofFn f).flatMap g = (List.ofFn fun i => g (f i)).flatten := by
  simp [List.flatMap, List.map_ofFn, Function.comp_def]

/-- The bytes of 58 digests, as the model's leaf payload. -/
theorem toList_packDigests_ofChains (f : XmssSecurity.ChainIndex → XmssSecurity.Digest) :
    (packDigests (ofChains f)).data.toList = XmssSecurity.Concrete.leafPayload f := by
  -- The packed digests are their lists, flattened.
  have hflat : (packDigests (ofChains f)).data.toList
      = ((ofChains f).toList.map Vector.toList).flatten := by
    simp [packDigests, packBytes, Vector.flatten, Array.toList_flatten, Vector.toList]
    rfl
  calc (packDigests (ofChains f)).data.toList
      = (List.ofFn fun i : Fin V => (ofDigest (f (chainOf i))).toList).flatten := by
        rw [hflat, ofChains, Vector.toList_ofFn, List.map_ofFn]
        rfl
    -- Digest by digest, EthLib's bytes are the model's.
    _ = (List.ofFn fun i : XmssSecurity.ChainIndex => XmssSecurity.bytesLE 16 (f i)).flatten :=
        congrArg (fun g => (List.ofFn g).flatten) (funext fun i => toList_ofDigest (f i))
    _ = XmssSecurity.Concrete.leafPayload f := (flatMap_ofFn (XmssSecurity.bytesLE 16) f).symm

/-! ## Computing in order -/

omit [HasQuery XmssSecurity.HashSpec m] in
/-- EthLib's vector computed in order is the model's function computed in order. -/
theorem ofFnInOrder_eq_sequenceFin {α β : Type} :
    ∀ (n : Nat) (c : Fin n → m α) (g : α → β),
      ofFnInOrder n (fun i => g <$> c i)
        = (fun f => Vector.ofFn fun i => g (f i)) <$> XmssSecurity.Concrete.sequenceFin c
  | 0, c, g => by
    simp only [ofFnInOrder, XmssSecurity.Concrete.sequenceFin, map_pure]
    congr 1
  | n + 1, c, g => by
    simp only [ofFnInOrder, XmssSecurity.Concrete.sequenceFin, map_bind, bind_map_left, map_pure]
    refine bind_congr fun head => ?_
    rw [ofFnInOrder_eq_sequenceFin n (fun i => c i.succ) g]
    simp only [bind_map_left]
    refine bind_congr fun tail => ?_
    congr 1
    apply Vector.ext
    intro i hi
    -- Entry 0 is the head, entry `i + 1` is entry `i` of the tail.
    cases i with
    | zero => simp
    | succ i => simp

omit [HasQuery XmssSecurity.HashSpec m] in
/-- A vector computed in order is the model's function computed in order, as a vector. -/
theorem ofFnInOrder_eq_map_sequenceFin {α : Type} (n : Nat) (c : Fin n → m α) :
    ofFnInOrder n c = (fun f => Vector.ofFn f) <$> XmssSecurity.Concrete.sequenceFin c := by
  have h := ofFnInOrder_eq_sequenceFin n c id
  simp only [id_map] at h
  exact h

omit [LawfulMonad m] [HasQuery XmssSecurity.HashSpec m] in
/-- Vectors computed in order from equal computations are equal. -/
theorem ofFnInOrder_congr {α : Type} {n : Nat} {c c' : Fin n → m α} (h : ∀ i, c i = c' i) :
    ofFnInOrder n c = ofFnInOrder n c' := by
  rw [funext h]

omit [Monad m] [LawfulMonad m] [HasQuery XmssSecurity.HashSpec m] in
/-- An address is the model's when its four fields are. -/
theorem fieldBytes_congr {a b c d a' b' c' d' : Nat} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') :
    XmssSecurity.fieldBytes (XmssSecurity.tweakFields a b c d)
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields a' b' c' d') := by
  subst ha hb hc hd
  rfl

/-! ## The tweakable hash -/

/-- EthLib's `Th` with `queryH` is the model's, at the same address and payload bytes. -/
theorem th_queryH (P : XmssSecurity.PublicParameter) (A : Address) (payload : ByteArray)
    (domain : XmssSecurity.HashDomain) (msg : XmssSecurity.HashInput)
    (hA : A.toList = XmssSecurity.tweakBytes domain)
    (hpayload : payload.data.toList = msg ++ XmssSecurity.domainSuffix domain) :
    th (queryH (m := m)) (ofParam P) A payload
      = ofDigest <$> XmssSecurity.Concrete.tweakableHash (m := m) P domain msg := by
  simp only [th, queryH, XmssSecurity.Concrete.tweakableHash, thInput, toList_data_append,
    toList_data_packBytes, toList_ofParam, hA, hpayload, XmssSecurity.tweakableHashInput,
    List.append_assoc, bind_map_left, map_bind, map_pure, halfOf_zero_ofOutput]

/-! ## Chains -/

/-- One step of a bottom chain. -/
theorem chainStep_bottom (P : XmssSecurity.PublicParameter) (idx : XmssSecurity.LeafIndex)
    (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) (v : XmssSecurity.Digest) :
    chainStep (queryH (m := m)) (ofParam P) .bottom (ofLeafIndex idx) i mu (ofDigest v)
      = ofDigest <$> XmssSecurity.Concrete.chainHash (m := m) P idx (chainOf i) mu v := by
  unfold chainStep XmssSecurity.Concrete.chainHash
  refine th_queryH P _ _ _ _ ?_ ?_
  · rw [toList_addrChain]
    exact fieldBytes_congr rfl rfl (by simp [Layer.toNat]) (toNat_ofLeafIndex idx)
  · simp only [toList_data_append, toList_data_packBytes, toList_ofDigest, toList_littleEndian]
    rfl

/-- One step of a top chain. -/
theorem chainStep_top (P : XmssSecurity.PublicParameter) (key : XmssSecurity.TopIndex)
    (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) (v : XmssSecurity.Digest) :
    chainStep (queryH (m := m)) (ofParam P) .top (ofTopIndex key) i mu (ofDigest v)
      = ofDigest <$> XmssSecurity.Concrete.topChainHash (m := m) P key (chainOf i) mu v := by
  unfold chainStep XmssSecurity.Concrete.topChainHash
  refine th_queryH P _ _ _ _ ?_ ?_
  · rw [toList_addrChain]
    exact fieldBytes_congr rfl rfl (by simp [Layer.toNat, XmssSecurity.topFlag])
      (toNat_ofTopIndex key)
  · simp only [toList_data_append, toList_data_packBytes, toList_ofDigest, toList_littleEndian]
    rfl

/-- A walk along a bottom chain. -/
theorem chain_bottom (P : XmssSecurity.PublicParameter) (idx : XmssSecurity.LeafIndex) (i : Fin V)
    (start : Nat) : ∀ (steps : Nat) (h : start + steps < CHAIN_LENGTH) (v : XmssSecurity.Digest),
    chain (queryH (m := m)) (ofParam P) .bottom (ofLeafIndex idx) i start steps h (ofDigest v)
      = ofDigest <$> XmssSecurity.Concrete.chainWalk (m := m) P idx (chainOf i) start steps v
  | 0, _, v => by simp [chain, XmssSecurity.Concrete.chainWalk]
  | s + 1, h, v => by
    rw [chain, chain_bottom P idx i start s (by omega) v, bind_map_left]
    simp only [XmssSecurity.Concrete.chainWalk, map_bind]
    refine bind_congr fun prev => ?_
    -- The step stays on the chain, so the model takes the step too.
    have hs : start + s < XmssSecurity.chainLength - 1 := by
      simp only [XmssSecurity.chainLength, XmssSecurity.winternitzBits, CHAIN_LENGTH] at *
      omega
    simp only [hs, ↓reduceDIte]
    rw [chainStep_bottom]
    rfl

/-- A walk along a top chain. -/
theorem chain_top (P : XmssSecurity.PublicParameter) (key : XmssSecurity.TopIndex) (i : Fin V)
    (start : Nat) : ∀ (steps : Nat) (h : start + steps < CHAIN_LENGTH) (v : XmssSecurity.Digest),
    chain (queryH (m := m)) (ofParam P) .top (ofTopIndex key) i start steps h (ofDigest v)
      = ofDigest <$> XmssSecurity.Concrete.topChainWalk (m := m) P key (chainOf i) start steps v
  | 0, _, v => by simp [chain, XmssSecurity.Concrete.topChainWalk]
  | s + 1, h, v => by
    rw [chain, chain_top P key i start s (by omega) v, bind_map_left]
    simp only [XmssSecurity.Concrete.topChainWalk, map_bind]
    refine bind_congr fun prev => ?_
    -- The step stays on the chain, so the model takes the step too.
    have hs : start + s < XmssSecurity.chainLength - 1 := by
      simp only [XmssSecurity.chainLength, XmssSecurity.winternitzBits, CHAIN_LENGTH] at *
      omega
    simp only [hs, ↓reduceDIte]
    rw [chainStep_top]
    rfl

/-! ## Leaves -/

/-- A bottom key's leaf, from its chain ends. -/
theorem otsLeafHash_bottom (P : XmssSecurity.PublicParameter) (idx : XmssSecurity.LeafIndex)
    (ends : XmssSecurity.ChainIndex → XmssSecurity.Digest) :
    otsLeafHash (queryH (m := m)) (ofParam P) .bottom (ofLeafIndex idx) (ofChains ends)
      = ofDigest <$> XmssSecurity.Concrete.leafHash (m := m) P idx ends := by
  rw [otsLeafHash, XmssSecurity.Concrete.leafHash]
  refine th_queryH P _ _ _ _ ?_ ?_
  · rw [toList_addrLeaf]
    exact fieldBytes_congr rfl rfl (by simp [Layer.toNat]) (toNat_ofLeafIndex idx)
  · rw [toList_packDigests_ofChains]
    exact (List.append_nil _).symm

/-- A top key's leaf, from its chain ends. -/
theorem otsLeafHash_top (P : XmssSecurity.PublicParameter) (key : XmssSecurity.TopIndex)
    (ends : XmssSecurity.ChainIndex → XmssSecurity.Digest) :
    otsLeafHash (queryH (m := m)) (ofParam P) .top (ofTopIndex key) (ofChains ends)
      = ofDigest <$> XmssSecurity.Concrete.topLeafHash (m := m) P key ends := by
  rw [otsLeafHash, XmssSecurity.Concrete.topLeafHash]
  refine th_queryH P _ _ _ _ ?_ ?_
  · rw [toList_addrLeaf]
    exact fieldBytes_congr rfl rfl (by simp [Layer.toNat, XmssSecurity.topFlag])
      (toNat_ofTopIndex key)
  · rw [toList_packDigests_ofChains]
    exact (List.append_nil _).symm

/-! ## The digest a key signs -/

/-- The digest a bottom key signs: the message, then the randomizer. -/
theorem messageDigest_bottom (P : XmssSecurity.PublicParameter) (idx : XmssSecurity.LeafIndex)
    (msg : XmssSecurity.Message) (rho : XmssSecurity.Randomness) :
    messageDigest (queryH (m := m)) (ofParam P) .bottom (ofLeafIndex idx)
        (packBytes (ofMessage msg)) (ofRandomizer rho)
      = ofDigest <$> XmssSecurity.Concrete.encodingHash (m := m) P idx msg rho := by
  rw [messageDigest, XmssSecurity.Concrete.encodingHash]
  refine th_queryH P _ _ _ _ ?_ ?_
  · rw [toList_addrMsg]
    exact fieldBytes_congr rfl rfl (by simp [Layer.toNat]) (toNat_ofLeafIndex idx)
  · simp only [toList_data_append, toList_data_packBytes, toList_ofMessage, toList_ofRandomizer]
    rfl

/-- The digest a top key signs: the bottom root, then the randomizer. -/
theorem messageDigest_top (P : XmssSecurity.PublicParameter) (key : XmssSecurity.TopIndex)
    (root : XmssSecurity.Digest) (rho : XmssSecurity.Randomness) :
    messageDigest (queryH (m := m)) (ofParam P) .top (ofTopIndex key) (packBytes (ofDigest root))
        (ofRandomizer rho)
      = ofDigest <$> XmssSecurity.Concrete.topEncodingHash (m := m) P key root rho := by
  rw [messageDigest, XmssSecurity.Concrete.topEncodingHash]
  refine th_queryH P _ _ _ _ ?_ ?_
  · rw [toList_addrMsg]
    exact fieldBytes_congr rfl rfl (by simp [Layer.toNat, XmssSecurity.topFlag])
      (toNat_ofTopIndex key)
  · simp only [toList_data_append, toList_data_packBytes, toList_ofDigest, toList_ofRandomizer]
    rfl

/-! ## Nodes -/

/-- A bottom node, from its two children. -/
theorem nodeHash_bottom (P : XmssSecurity.PublicParameter) (level : XmssSecurity.MerkleLevel)
    (node : XmssSecurity.MerkleNode) (left right : XmssSecurity.Digest) :
    nodeHash (queryH (m := m)) (ofParam P) .bottom ⟨level.val + 1, by
        have := level.isLt; simp only [XmssSecurity.treeHeight, LAYER_HEIGHT] at *; omega⟩
        node.val (ofDigest left) (ofDigest right)
      = ofDigest <$> XmssSecurity.Concrete.nodeHash (m := m) P level node left right := by
  rw [nodeHash, XmssSecurity.Concrete.nodeHash]
  refine th_queryH P _ _ _ _ ?_ ?_
  · rw [toList_addrNode]
    refine fieldBytes_congr rfl rfl (by simp [Layer.toNat]) ?_
    have h32 : node.val < 4294967296 := lt_of_lt_of_le node.isLt (by decide)
    simp [Nat.mod_eq_of_lt h32]
  · simp only [toList_data_append, toList_data_packBytes, toList_ofDigest]
    exact (List.append_nil _).symm

/-- A top node, from its two children. -/
theorem nodeHash_top (P : XmssSecurity.PublicParameter) (level : XmssSecurity.MerkleLevel)
    (node : XmssSecurity.TopNode) (left right : XmssSecurity.Digest) :
    nodeHash (queryH (m := m)) (ofParam P) .top ⟨level.val + 1, by
        have := level.isLt; simp only [XmssSecurity.treeHeight, LAYER_HEIGHT] at *; omega⟩
        node.val (ofDigest left) (ofDigest right)
      = ofDigest <$> XmssSecurity.Concrete.topNodeHash (m := m) P level node left right := by
  rw [nodeHash, XmssSecurity.Concrete.topNodeHash]
  refine th_queryH P _ _ _ _ ?_ ?_
  · rw [toList_addrNode]
    refine fieldBytes_congr rfl rfl (by simp [Layer.toNat, XmssSecurity.topFlag]; omega) ?_
    have h32 : node.val < 4294967296 := lt_of_lt_of_le node.isLt (by decide)
    simp [Nat.mod_eq_of_lt h32]
  · simp only [toList_data_append, toList_data_packBytes, toList_ofDigest]
    exact (List.append_nil _).symm

/-! ## Climbing a path -/

/-- One level of a bottom path, in the order bit `l` of the key names. -/
theorem climbStep_bottom (P : XmssSecurity.PublicParameter) (idx : XmssSecurity.LeafIndex)
    (l : Fin LAYER_HEIGHT) (current sibling : XmssSecurity.Digest) :
    Internal.climbStep (queryH (m := m)) (ofParam P) .bottom idx.val l (ofDigest current)
        (ofDigest sibling)
      = ofDigest <$> XmssSecurity.Concrete.authenticationNodeHash (m := m) P idx l.val current
          sibling := by
  have hl : l.val < XmssSecurity.treeHeight := l.isLt
  have hbit : (idx.val >>> l.val % 2 == 0) = !idx.val.testBit l.val := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (idx.val / 2 ^ l.val) with h | h <;> simp [h]
  -- The parent's index is the model's node index one level up.
  have hnode : idx.val >>> (l.val + 1) = (XmssSecurity.Concrete.nodeIndex idx l.val).val := by
    rw [Nat.shiftRight_eq_div_pow]
    rfl
  unfold Internal.climbStep XmssSecurity.Concrete.authenticationNodeHash
  rw [hbit, hnode]
  simp only [hl, ↓reduceDIte]
  cases idx.val.testBit l.val <;>
  · simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    exact nodeHash_bottom P ⟨l.val, hl⟩ _ _ _

/-- One level of a top path, in the order bit `l` of the key names. -/
theorem climbStep_top (P : XmssSecurity.PublicParameter) (key : XmssSecurity.TopIndex)
    (l : Fin LAYER_HEIGHT) (current sibling : XmssSecurity.Digest) :
    Internal.climbStep (queryH (m := m)) (ofParam P) .top key.val l (ofDigest current)
        (ofDigest sibling)
      = ofDigest <$> (if key.val.testBit l.val then
          XmssSecurity.Concrete.topNodeHash (m := m) P ⟨l.val, l.isLt⟩
            (XmssSecurity.Concrete.topNodeIndex key l.val) sibling current
        else
          XmssSecurity.Concrete.topNodeHash P ⟨l.val, l.isLt⟩
            (XmssSecurity.Concrete.topNodeIndex key l.val) current sibling) := by
  have hbit : (key.val >>> l.val % 2 == 0) = !key.val.testBit l.val := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (key.val / 2 ^ l.val) with h | h <;> simp [h]
  -- The parent's index is the model's node index one level up.
  have hnode : key.val >>> (l.val + 1) = (XmssSecurity.Concrete.topNodeIndex key l.val).val := by
    rw [Nat.shiftRight_eq_div_pow]
    rfl
  unfold Internal.climbStep
  rw [hbit, hnode]
  cases key.val.testBit l.val <;>
  · simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    exact nodeHash_top P ⟨l.val, l.isLt⟩ _ _ _

/-- A bottom leaf, climbed up the bottom `levels` levels of a signature's path. -/
theorem climbUpto_bottom (P : XmssSecurity.PublicParameter) (idx : XmssSecurity.LeafIndex)
    (σ : XmssSecurity.Signature) (leaf : XmssSecurity.Digest) :
    ∀ (levels : Nat) (h : levels ≤ LAYER_HEIGHT),
      Internal.climbUpto (queryH (m := m)) (ofParam P) .bottom idx.val (ofPath σ.authPath)
          (ofDigest leaf) levels h
        = ofDigest <$> XmssSecurity.Concrete.authenticationRoot (m := m) P idx σ levels leaf
  | 0, _ => by simp [Internal.climbUpto, XmssSecurity.Concrete.authenticationRoot]
  | l + 1, h => by
    unfold Internal.climbUpto
    rewrite [climbUpto_bottom P idx σ leaf l (by omega), bind_map_left]
    simp only [XmssSecurity.Concrete.authenticationRoot, map_bind]
    refine bind_congr fun current => ?_
    -- The sibling on level `l` is entry `l` of the path.
    have hl : l < XmssSecurity.treeHeight := by
      simp only [XmssSecurity.treeHeight, LAYER_HEIGHT] at *
      omega
    rw [show (ofPath σ.authPath)[l] = ofDigest (σ.authPath ⟨l, hl⟩) from Vector.getElem_ofFn _,
      climbStep_bottom]
    simp only [XmssSecurity.Concrete.signaturePath, hl, ↓reduceDIte]

/-- A top leaf, climbed up the bottom `levels` levels of a path. -/
theorem climbUpto_top (P : XmssSecurity.PublicParameter) (key : XmssSecurity.TopIndex)
    (path : Fin XmssSecurity.treeHeight → XmssSecurity.Digest) (leaf : XmssSecurity.Digest) :
    ∀ (levels : Nat) (h : levels ≤ LAYER_HEIGHT),
      Internal.climbUpto (queryH (m := m)) (ofParam P) .top key.val (ofPath path) (ofDigest leaf)
          levels h
        = ofDigest <$> XmssSecurity.Concrete.topAuthenticationRoot (m := m) P key path levels leaf
  | 0, _ => by simp [Internal.climbUpto, XmssSecurity.Concrete.topAuthenticationRoot]
  | l + 1, h => by
    unfold Internal.climbUpto
    rewrite [climbUpto_top P key path leaf l (by omega), bind_map_left]
    simp only [XmssSecurity.Concrete.topAuthenticationRoot, map_bind]
    refine bind_congr fun current => ?_
    -- The sibling on level `l` is entry `l` of the path.
    have hl : l < XmssSecurity.treeHeight := by
      simp only [XmssSecurity.treeHeight, LAYER_HEIGHT] at *
      omega
    rw [show (ofPath path)[l] = ofDigest (path ⟨l, hl⟩) from Vector.getElem_ofFn _,
      climbStep_top]
    simp only [hl, ↓reduceDIte]

/-! ## A layer's root -/

/-- `UInt32.ofNat` of a leaf index is EthLib's leaf index. -/
theorem ofNat_val_leafIndex (idx : XmssSecurity.LeafIndex) :
    UInt32.ofNat idx.val = ofLeafIndex idx :=
  UInt32.toNat.inj (by
    simp [Nat.mod_eq_of_lt (lt_of_lt_of_le idx.isLt
      (show XmssSecurity.lifetime ≤ 4294967296 by decide))])

/-- `UInt32.ofNat` of a top key is EthLib's top key. -/
theorem ofNat_val_topIndex (key : XmssSecurity.TopIndex) :
    UInt32.ofNat key.val = ofTopIndex key :=
  UInt32.toNat.inj (by
    simp [Nat.mod_eq_of_lt (lt_of_lt_of_le key.isLt
      (show XmssSecurity.topLifetime ≤ 4294967296 by decide))])

/-- The root a bottom layer's signature leads to, from the message it signs.

Up to the leaf in the model's routines, then EthLib's fold up the path. -/
theorem layerRoot_bottom (P : XmssSecurity.PublicParameter) (idx : XmssSecurity.LeafIndex)
    (msg : XmssSecurity.Message) (σ : XmssSecurity.Signature) :
    layerRoot (queryH (m := m)) (ofParam P) .bottom idx.val (packBytes (ofMessage msg))
        (ofLayerSig ⟨σ.randomness, σ.chainValue, σ.authPath⟩)
      = (do
          let digest ← XmssSecurity.Concrete.encodingHash (m := m) P idx msg σ.randomness
          match XmssSecurity.TargetSum.decodeDigest digest with
          | none => pure none
          | some encoding => do
            let endpoints ← XmssSecurity.Concrete.recoverEndpoints P idx encoding σ
            let leaf ← XmssSecurity.Concrete.leafHash P idx endpoints
            some <$> fold queryH (ofParam P) .bottom idx.val (ofDigest leaf)
              (ofPath σ.authPath)) := by
  unfold layerRoot otsLeaf
  dsimp only [ofLayerSig]
  rw [ofNat_val_leafIndex, messageDigest_bottom, bind_assoc, bind_map_left]
  refine bind_congr fun digest => ?_
  rw [codeword?_ofDigest]
  cases XmssSecurity.TargetSum.decodeDigest digest with
  | none => simp
  | some enc =>
    simp only [Option.map_some, bind_assoc]
    -- Chain `i` is walked from its digit to position 3.
    rewrite [ofFnInOrder_congr (c' := fun i : Fin V => ofDigest <$>
      XmssSecurity.Concrete.recoverChain (m := m) P idx (chainOf i) (enc (chainOf i))
        (σ.chainValue (chainOf i)))
      fun i => by
        rewrite [show (ofChains σ.chainValue)[i] = ofDigest (σ.chainValue (chainOf i)) from
          Vector.getElem_ofFn _, chain_bottom, XmssSecurity.Concrete.recoverChain]
        -- The digit is the model's, now outside any bound.
        rewrite [show ((ofEncoding enc)[i] : Nat) = (enc (chainOf i)).val from
          congrArg Fin.val (Vector.getElem_ofFn _)]
        rfl]
    rewrite [ofFnInOrder_eq_sequenceFin, bind_map_left]
    simp only [XmssSecurity.Concrete.recoverEndpoints]
    -- `ends` typed by the model's chains, so the leaf lemma applies by rewriting.
    refine bind_congr fun (ends : XmssSecurity.ChainIndex → XmssSecurity.Digest) => ?_
    rewrite [show (Vector.ofFn fun i : Fin V => ofDigest (ends i)) = ofChains ends from rfl,
      otsLeafHash_bottom, bind_map_left]
    refine bind_congr fun leaf => ?_
    simp [map_eq_bind_pure_comp]

/-- The root a top layer's signature leads to, from the bottom root it signs. -/
theorem layerRoot_top (P : XmssSecurity.PublicParameter) (key : XmssSecurity.TopIndex)
    (root : XmssSecurity.Digest) (part : XmssSecurity.LayerSignature) :
    layerRoot (queryH (m := m)) (ofParam P) .top key.val (packBytes (ofDigest root))
        (ofLayerSig part)
      = Option.map ofDigest <$> (do
          let digest ← XmssSecurity.Concrete.topEncodingHash (m := m) P key root part.randomness
          match XmssSecurity.TargetSum.decodeDigest digest with
          | none => pure none
          | some encoding => do
            let endpoints ← XmssSecurity.Concrete.sequenceFin fun chain =>
              XmssSecurity.Concrete.topChainWalk P key chain (encoding chain).val
                (XmssSecurity.chainLength - 1 - (encoding chain).val) (part.chainValue chain)
            let leaf ← XmssSecurity.Concrete.topLeafHash P key endpoints
            let topRoot ← XmssSecurity.Concrete.topAuthenticationRoot P key part.authPath
              XmssSecurity.treeHeight leaf
            pure (some topRoot)) := by
  unfold layerRoot otsLeaf
  dsimp only [ofLayerSig]
  rw [ofNat_val_topIndex, messageDigest_top, bind_assoc, bind_map_left, map_bind]
  refine bind_congr fun digest => ?_
  rw [codeword?_ofDigest]
  cases XmssSecurity.TargetSum.decodeDigest digest with
  | none => simp
  | some enc =>
    simp only [Option.map_some, bind_assoc]
    -- Chain `i` is walked from its digit to position 3.
    rewrite [ofFnInOrder_congr (c' := fun i : Fin V => ofDigest <$>
      XmssSecurity.Concrete.topChainWalk (m := m) P key (chainOf i) (enc (chainOf i)).val
        (XmssSecurity.chainLength - 1 - (enc (chainOf i)).val) (part.chainValue (chainOf i)))
      fun i => by
        rewrite [show (ofChains part.chainValue)[i] = ofDigest (part.chainValue (chainOf i)) from
          Vector.getElem_ofFn _, chain_top]
        -- The digit is the model's, now outside any bound.
        rewrite [show ((ofEncoding enc)[i] : Nat) = (enc (chainOf i)).val from
          congrArg Fin.val (Vector.getElem_ofFn _)]
        rfl]
    rewrite [ofFnInOrder_eq_sequenceFin, bind_map_left]
    simp only [map_bind]
    -- `ends` typed by the model's chains, so the leaf lemma applies by rewriting.
    refine bind_congr fun (ends : XmssSecurity.ChainIndex → XmssSecurity.Digest) => ?_
    rewrite [show (Vector.ofFn fun i : Fin V => ofDigest (ends i)) = ofChains ends from rfl,
      otsLeafHash_top, bind_map_left]
    refine bind_congr fun leaf => ?_
    simp only [pure_bind, fold]
    rw [climbUpto_top]
    -- EthLib's tree height is the model's.
    simp [LAYER_HEIGHT, XmssSecurity.treeHeight]

/-- Two digests are equal exactly when their bytes are. -/
theorem ofDigest_eq_iff (x y : XmssSecurity.Digest) : ofDigest x = ofDigest y ↔ x = y :=
  ⟨ofBV_inj (by simp [XmssSecurity.digestBits, DIGEST_LEN]), fun h => h ▸ rfl⟩

/-- The bottom tree of a leaf index is the model's top key. -/
theorem bottomTree_ofLeafIndex (idx : XmssSecurity.LeafIndex) :
    bottomTree (ofLeafIndex idx) = (XmssSecurity.topKeyOf idx).val := by
  simp [bottomTree, XmssSecurity.topKeyOf, LAYER_HEIGHT, XmssSecurity.treeHeight]

omit [LawfulMonad m] in
/-- The model's verifier is EthLib's, by definition. -/
theorem verifyWith_queryH (pk : XmssSecurity.PublicKey) (idx : XmssSecurity.LeafIndex)
    (msg : XmssSecurity.Message) (σ : XmssSecurity.Signature) :
    verifyWith (queryH (m := m)) (ofPublicKey pk) (ofMessage msg) (ofSignature idx σ)
      = XmssSecurity.Concrete.verify (m := m) pk idx msg σ :=
  rfl

/-- The top layer's check, in the model's routines. -/
theorem _root_.XmssSecurity.Concrete.verifyTop_eq (pk : XmssSecurity.PublicKey)
    (key : XmssSecurity.TopIndex) (root : XmssSecurity.Digest)
    (part : XmssSecurity.LayerSignature) :
    XmssSecurity.Concrete.verifyTop (m := m) pk key root part = (do
      let digest ← XmssSecurity.Concrete.topEncodingHash pk.parameter key root part.randomness
      let some encoding := XmssSecurity.TargetSum.decodeDigest digest | return false
      let endpoints ← XmssSecurity.Concrete.sequenceFin fun chain =>
        XmssSecurity.Concrete.topChainWalk pk.parameter key chain (encoding chain).val
          (XmssSecurity.chainLength - 1 - (encoding chain).val) (part.chainValue chain)
      let leaf ← XmssSecurity.Concrete.topLeafHash pk.parameter key endpoints
      let topRoot ← XmssSecurity.Concrete.topAuthenticationRoot pk.parameter key part.authPath
        XmssSecurity.treeHeight leaf
      return decide (topRoot = pk.root)) := by
  unfold XmssSecurity.Concrete.verifyTop
  rw [layerRoot_top, bind_map_left]
  simp only [bind_assoc]
  refine bind_congr fun digest => ?_
  cases XmssSecurity.TargetSum.decodeDigest digest with
  | none => simp
  | some enc =>
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun endpoints => ?_
    refine bind_congr fun leaf => ?_
    refine bind_congr fun topRoot => ?_
    simp [ofDigest_eq_iff]

/-- The bottom fold, then the top layer's check, in the model's routines. -/
theorem _root_.XmssSecurity.Concrete.verifyAfterLeaf_eq (pk : XmssSecurity.PublicKey)
    (idx : XmssSecurity.LeafIndex) (σ : XmssSecurity.Signature) (leaf : XmssSecurity.Digest) :
    XmssSecurity.Concrete.verifyAfterLeaf (m := m) pk idx σ leaf = (do
      let root ← XmssSecurity.Concrete.authenticationRoot pk.parameter idx σ
        XmssSecurity.treeHeight leaf
      XmssSecurity.Concrete.verifyTop pk (XmssSecurity.topKeyOf idx) root σ.top) := by
  unfold XmssSecurity.Concrete.verifyAfterLeaf fold
  rw [climbUpto_bottom, bind_map_left]
  -- EthLib's tree height is the model's.
  simp only [toDigest_ofDigest, LAYER_HEIGHT, XmssSecurity.treeHeight]

/-- `Ver(pk, idx, m, sigma)`, in the model's routines.

The bottom layer up to its leaf, then the rest.

The security proof reasons on this form. -/
theorem _root_.XmssSecurity.Concrete.verify_eq (pk : XmssSecurity.PublicKey)
    (idx : XmssSecurity.LeafIndex) (msg : XmssSecurity.Message) (σ : XmssSecurity.Signature) :
    XmssSecurity.Concrete.verify (m := m) pk idx msg σ = (do
      let digest ← XmssSecurity.Concrete.encodingHash pk.parameter idx msg σ.randomness
      let some encoding := XmssSecurity.TargetSum.decodeDigest digest | return false
      let endpoints ← XmssSecurity.Concrete.recoverEndpoints pk.parameter idx encoding σ
      let leaf ← XmssSecurity.Concrete.leafHash pk.parameter idx endpoints
      XmssSecurity.Concrete.verifyAfterLeaf pk idx σ leaf) := by
  unfold XmssSecurity.Concrete.verify verifyWith XmssSecurity.Concrete.verifyAfterLeaf
    XmssSecurity.Concrete.verifyTop
  simp only [ofSignature_leafIndex, toNat_ofLeafIndex, ofSignature_bottom, ofPublicKey_publicParam,
    bottomTree_ofLeafIndex, ofSignature_top, ofPublicKey_root]
  rw [layerRoot_bottom]
  simp only [bind_assoc]
  refine bind_congr fun digest => ?_
  cases XmssSecurity.TargetSum.decodeDigest digest with
  | none => simp
  | some enc =>
    simp only [bind_assoc, bind_map_left]
    refine bind_congr fun endpoints => ?_
    refine bind_congr fun leaf => ?_
    refine bind_congr fun root => ?_
    -- The top layer signs the bytes of the bottom root, which round trip.
    simp only [ofDigest_toDigest]
    rfl

end EthLib.Cryptography.Xmss.Unforgeability
