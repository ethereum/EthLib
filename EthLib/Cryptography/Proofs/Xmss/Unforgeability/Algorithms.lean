import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Address
import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Codeword
import EthLib.Cryptography.Proofs.Xmss.Security.LeanXmss.Compat

/-!
# Proofs: EthLib's algorithms are the security proof's

The security proof writes leanXMSS over a hash oracle `H` in any monad with a query to it.

EthLib's algorithms take `H` as an argument.

Passed `queryH`, a query to the same oracle, each of them is the proof's algorithm, call for call.

```text
    EthLib's algorithm (queryH) (ofBV x)  =  ofBV <$> the proof's algorithm x
```

The equalities hold in every lawful monad, so they need nothing about the oracle.
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery LeanXmss.HashSpec m]

/-- `H` as a query to the proof's oracle.

The input's bytes go in, and the answer's 32 bytes come out. -/
def queryH (input : ByteArray) : m (Vector UInt8 32) :=
  ofOutput <$> LeanXmss.Concrete.oracleHash (m := m) input.data.toList

/-! ## Bytes of hash inputs -/

@[simp] theorem toList_data_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

/-- The 58 values of a function on chains, as EthLib's vector of digests. -/
def ofChains (f : LeanXmss.ChainIndex → LeanXmss.Digest) : Vector Digest V :=
  Vector.ofFn fun i => ofDigest (f (chainOf i))

/-! ## Computing in order -/

omit [HasQuery LeanXmss.HashSpec m] in
/-- EthLib's vector computed in order is the proof's function computed in order. -/
theorem ofFnInOrder_eq_sequenceFin {α β : Type} :
    ∀ (n : Nat) (c : Fin n → m α) (g : α → β),
      ofFnInOrder n (fun i => g <$> c i)
        = (fun f => Vector.ofFn fun i => g (f i)) <$> LeanXmss.Concrete.sequenceFin c
  | 0, c, g => by
    simp only [ofFnInOrder, LeanXmss.Concrete.sequenceFin, map_pure]
    congr 1
  | n + 1, c, g => by
    simp only [ofFnInOrder, LeanXmss.Concrete.sequenceFin, map_bind, bind_map_left, map_pure]
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

omit [LawfulMonad m] [HasQuery LeanXmss.HashSpec m] in
/-- Vectors computed in order from equal computations are equal. -/
theorem ofFnInOrder_congr {α : Type} {n : Nat} {c c' : Fin n → m α} (h : ∀ i, c i = c' i) :
    ofFnInOrder n c = ofFnInOrder n c' := by
  rw [funext h]

/-! ## The tweakable hash -/

/-- EthLib's `Th` with `queryH` is the proof's `Th`, at the same address bytes. -/
theorem th_queryH (P : LeanXmss.PublicParameter) (A : Address) (F : LeanXmss.TweakFields)
    (hA : A.toList = LeanXmss.fieldBytes F) (payload : ByteArray) :
    th (queryH (m := m)) (ofParam P) A payload
      = ofDigest <$> LeanXmss.Concrete.th (m := m) P F payload.data.toList := by
  simp only [th, queryH, LeanXmss.Concrete.th, thInput, toList_data_append, toList_data_packBytes,
    toList_ofParam, hA, bind_map_left, map_bind, map_pure, halfOf_zero_ofOutput]
  rfl

/-! ## Chains -/

/-- One step of a chain. -/
theorem chainStep_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (e : UInt32) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (v : LeanXmss.Digest) :
    chainStep (queryH (m := m)) (ofParam P) layer e i mu (ofDigest v)
      = ofDigest <$> LeanXmss.Concrete.tweakableHash (m := m) P
          (.chain (layerOf layer) (keyOf e) mu) (LeanXmss.Concrete.chainPayload (chainOf i) v) := by
  rw [chainStep, th_queryH P _ _ (toList_addrChain layer e mu)]
  simp only [toList_data_append, toList_data_packBytes, toList_ofDigest, toList_littleEndian,
    LeanXmss.Concrete.chainPayload]
  rfl

/-- A walk along a chain. -/
theorem chain_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (e : UInt32) (i : Fin V)
    (start : Nat) : ∀ (steps : Nat) (h : start + steps < CHAIN_LENGTH) (v : LeanXmss.Digest),
    chain (queryH (m := m)) (ofParam P) layer e i start steps h (ofDigest v)
      = ofDigest <$> LeanXmss.Concrete.chainWalk (m := m) P (layerOf layer) (keyOf e) (chainOf i)
          start steps v
  | 0, _, v => by simp [chain, LeanXmss.Concrete.chainWalk, LeanXmss.Concrete.walkChain]
  | s + 1, h, v => by
    rw [chain, chain_queryH P layer e i start s (by omega) v, bind_map_left]
    simp only [LeanXmss.Concrete.chainWalk, LeanXmss.Concrete.walkChain, map_bind]
    refine bind_congr fun prev => ?_
    -- The step stays on the chain, so the proof takes the step too.
    have hs : start + s < LeanXmss.chainLength - 1 := by
      simp only [LeanXmss.chainLength, LeanXmss.winternitzBits, CHAIN_LENGTH] at *
      omega
    simp only [hs, ↓reduceDIte]
    rw [chainStep_queryH]
    rfl

/-- The 29 hashes that start the 58 chains of a key. -/
theorem chainStarts_queryH (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed) (layer : Layer)
    (e : UInt32) :
    chainStarts (queryH (m := m)) (ofParam P) (ofSeed S) layer e
      = ofChains <$> LeanXmss.Seeded.otsSecrets (m := m) P (layerOf layer) (keyOf e) S := by
  have hpair : ∀ j : Fin (V / 2),
      queryH (m := m) (thInput (ofParam P) (addrPrf layer e j) (packBytes (ofSeed S)))
      = ofOutput <$> LeanXmss.Concrete.thPair (m := m) P
          (LeanXmss.keygenDomainFields (.ots (layerOf layer) (keyOf e) (pairOf j)))
          (LeanXmss.bytesLE 32 S) := by
    intro j
    simp only [queryH, thInput, toList_data_append, toList_data_packBytes, toList_ofParam,
      toList_ofSeed, toList_addrPrf]
    rfl
  unfold chainStarts LeanXmss.Seeded.otsSecrets
  rewrite [show (fun j : Fin (V / 2) => queryH (m := m) (thInput (ofParam P) (addrPrf layer e j)
      (packBytes (ofSeed S)))) = fun j => ofOutput <$> LeanXmss.Concrete.thPair (m := m) P
        (LeanXmss.keygenDomainFields (.ots (layerOf layer) (keyOf e) (pairOf j)))
        (LeanXmss.bytesLE 32 S) from funext hpair]
  rewrite [ofFnInOrder_eq_sequenceFin, bind_map_left, map_bind]
  refine bind_congr fun outputs => ?_
  rewrite [map_pure]
  -- Chain `i` takes half `i mod 2` of hash `floor(i / 2)`, in both.
  refine congrArg pure (Vector.ext fun i hi => ?_)
  simp only [Vector.getElem_ofFn, ofChains]
  rw [halfOf_mod_two_ofOutput]
  rfl

/-! ## One-time keys -/

omit [Monad m] [LawfulMonad m] [HasQuery LeanXmss.HashSpec m] in
/-- A list of functions' values, each a list, flattened. -/
theorem flatMap_ofFn {α β : Type} {n : Nat} (g : α → List β) (f : Fin n → α) :
    (List.ofFn f).flatMap g = (List.ofFn fun i => g (f i)).flatten := by
  simp [List.flatMap, List.map_ofFn, Function.comp_def]

/-- The bytes of 58 digests, as the proof's leaf payload. -/
theorem toList_packDigests_ofChains (f : LeanXmss.ChainIndex → LeanXmss.Digest) :
    (packDigests (ofChains f)).data.toList = LeanXmss.Concrete.leafPayload f := by
  -- The packed digests are their lists, flattened.
  have hflat : (packDigests (ofChains f)).data.toList
      = ((ofChains f).toList.map Vector.toList).flatten := by
    simp [packDigests, packBytes, Vector.flatten, Array.toList_flatten, Vector.toList]
    rfl
  calc (packDigests (ofChains f)).data.toList
      = (List.ofFn fun i : Fin V => (ofDigest (f (chainOf i))).toList).flatten := by
        rw [hflat, ofChains, Vector.toList_ofFn, List.map_ofFn]
        rfl
    -- Digest by digest, EthLib's bytes are the proof's.
    _ = (List.ofFn fun i : LeanXmss.ChainIndex => LeanXmss.bytesLE 16 (f i)).flatten :=
        congrArg (fun g => (List.ofFn g).flatten) (funext fun i => toList_ofDigest (f i))
    _ = LeanXmss.Concrete.leafPayload f := (flatMap_ofFn (LeanXmss.bytesLE 16) f).symm

/-- A key's leaf, from its chain ends. -/
theorem otsLeafHash_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (e : UInt32)
    (ends : LeanXmss.ChainIndex → LeanXmss.Digest) :
    otsLeafHash (queryH (m := m)) (ofParam P) layer e (ofChains ends)
      = ofDigest <$> LeanXmss.Concrete.leafHash (m := m) P (layerOf layer) (keyOf e) ends := by
  rw [otsLeafHash, th_queryH P _ _ (toList_addrLeaf layer e), toList_packDigests_ofChains]
  rfl

/-- A key's leaf, from the seed: 29 hashes, 58 walked chains, one leaf hash. -/
theorem otsPublicLeaf_queryH (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed)
    (layer : Layer) (e : UInt32) :
    otsPublicLeaf (queryH (m := m)) (ofParam P) (ofSeed S) layer e
      = ofDigest <$> (do
          let ends ← LeanXmss.Seeded.oneTimePublicKey (m := m) P (layerOf layer) (keyOf e) S
          LeanXmss.Concrete.leafHash P (layerOf layer) (keyOf e) ends) := by
  unfold otsPublicLeaf LeanXmss.Seeded.oneTimePublicKey
  rewrite [chainStarts_queryH, bind_map_left, map_bind, bind_assoc]
  refine bind_congr fun starts => ?_
  -- Each chain is walked from its start to position 3.
  rewrite [show (fun i : Fin V => chain (queryH (m := m)) (ofParam P) layer e i 0 (CHAIN_LENGTH - 1)
      (by decide) (ofChains starts)[i])
        = fun i => ofDigest <$> LeanXmss.Concrete.chainWalk (m := m) P
        (layerOf layer) (keyOf e) (chainOf i) 0 (CHAIN_LENGTH - 1) (starts (chainOf i)) from
      funext fun i => by
        rw [show (ofChains starts)[i] = ofDigest (starts (chainOf i)) from Vector.getElem_ofFn _,
          chain_queryH]]
  rewrite [ofFnInOrder_eq_sequenceFin, bind_map_left]
  refine bind_congr fun ends => ?_
  exact otsLeafHash_queryH P layer e ends

/-! ## The digest a key signs -/

theorem messageDigest_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (rho : LeanXmss.Randomness) :
    messageDigest (queryH (m := m)) (ofParam P) layer e msg (ofRandomizer rho)
      = ofDigest <$> LeanXmss.Concrete.messageDigest (m := m) P (layerOf layer) (keyOf e)
          msg.data.toList rho := by
  rw [messageDigest, th_queryH P _ _ (toList_addrMsg layer e)]
  simp only [toList_data_append, toList_data_packBytes, toList_ofRandomizer]
  rfl

theorem randomizerBase_queryH (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed)
    (layer : Layer) (e : UInt32) (msg : ByteArray) :
    randomizerBase (queryH (m := m)) (ofParam P) (ofSeed S) layer e msg
      = ofRandomizer <$> LeanXmss.Concrete.th (m := m) P
          (LeanXmss.tweakFields 7 0 (LeanXmss.layerHi (layerOf layer) 0) (keyOf e))
          (LeanXmss.bytesLE 32 S ++ msg.data.toList) := by
  rw [randomizerBase, th_queryH P _ _ (toList_addrRnd layer e)]
  simp only [toList_data_append, toList_data_packBytes, toList_ofSeed]
  rfl

/-! ## Trees -/

/-- A node of a layer's tree, from the seed. -/
theorem node_queryH (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed) (layer : Layer) :
    ∀ (level : Nat) (h : level ≤ LAYER_HEIGHT) (j : Nat),
      node (queryH (m := m)) (ofParam P) (ofSeed S) layer level h j
        = ofDigest <$> LeanXmss.Seeded.treeNode (m := m) P (layerOf layer) S level j
  | 0, _, j => by
    rw [node, otsPublicLeaf_queryH]
    rfl
  | l + 1, h, j => by
    unfold node
    rewrite [node_queryH P S layer l (by omega) (2 * j), bind_map_left]
    simp only [LeanXmss.Seeded.treeNode, LeanXmss.Concrete.buildTree, map_bind]
    refine bind_congr fun left => ?_
    rewrite [node_queryH P S layer l (by omega) (2 * j + 1), bind_map_left]
    refine bind_congr fun right => ?_
    rw [nodeHash, th_queryH P _ _ (toList_addrNode layer ⟨l + 1, by omega⟩ j)]
    simp only [toList_data_append, toList_data_packBytes, toList_ofDigest]
    rfl

/-- A path as the proof writes it, as EthLib's vector of 16 digests. -/
def ofPath (f : Fin LeanXmss.layerHeight → LeanXmss.Digest) : Vector Digest LAYER_HEIGHT :=
  Vector.ofFn fun l => ofDigest (f ⟨l.val, l.isLt⟩)

/-- A key below `2^32`, as the proof writes it. -/
def keyOfNat (e : Nat) (he : e < 2 ^ 32) : LeanXmss.KeyIndex :=
  ⟨e, by simpa [LeanXmss.lifetime, LeanXmss.numLayers, LeanXmss.layerHeight] using he⟩

/-- A key's path: the sibling of its ancestor on each level, level 0 first. -/
theorem path_queryH (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed) (layer : Layer)
    (e : Nat) (he : e < 2 ^ 32) :
    path (queryH (m := m)) (ofParam P) (ofSeed S) layer e
      = ofPath <$> LeanXmss.Seeded.treePath (m := m) P (layerOf layer) S (keyOfNat e he) := by
  unfold path LeanXmss.Seeded.treePath
  rewrite [show (fun level : Fin LAYER_HEIGHT => node (queryH (m := m)) (ofParam P) (ofSeed S) layer
      level.val (by omega) (siblingIndex e level)) = fun level => ofDigest <$>
        LeanXmss.Seeded.treeNode (m := m) P (layerOf layer) S level.val
          (Nat.xor ((keyOfNat e he).val / 2 ^ level.val) 1) from
      funext fun level => by
        rw [node_queryH, siblingIndex, Nat.shiftRight_eq_div_pow]
        rfl]
  rewrite [ofFnInOrder_eq_sequenceFin]
  rfl

/-- One level of a path fold: the held node and its sibling, in the order bit `l` names. -/
theorem climbStep_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (e : Nat)
    (l : Fin LAYER_HEIGHT) (current sibling : LeanXmss.Digest) :
    Internal.climbStep (queryH (m := m)) (ofParam P) layer e l (ofDigest current) (ofDigest sibling)
      = ofDigest <$> LeanXmss.Concrete.tweakableHash (m := m) P (.node (layerOf layer) (l.val + 1)
          (e / 2 ^ (l.val + 1)))
          (if e.testBit l.val then LeanXmss.Concrete.nodePayload sibling current
            else LeanXmss.Concrete.nodePayload current sibling) := by
  have hbit : (e >>> l.val % 2 == 0) = !e.testBit l.val := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ l.val) with h | h <;> simp [h]
  unfold Internal.climbStep
  rw [hbit, Nat.shiftRight_eq_div_pow]
  cases e.testBit l.val <;>
  · simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, nodeHash]
    rw [th_queryH P _ _ (toList_addrNode layer ⟨l.val + 1, by omega⟩ (e / 2 ^ (l.val + 1)))]
    simp only [toList_data_append, toList_data_packBytes, toList_ofDigest]
    rfl

/-- Folding a leaf up a path. -/
theorem climbUpto_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (e : Nat)
    (pi : Fin LeanXmss.layerHeight → LeanXmss.Digest) (leaf : LeanXmss.Digest) :
    ∀ (levels : Nat) (h : levels ≤ LAYER_HEIGHT),
      Internal.climbUpto (queryH (m := m)) (ofParam P) layer e (ofPath pi) (ofDigest leaf) levels h
        = ofDigest <$> LeanXmss.Concrete.foldPath (m := m)
            (fun level nodeIdx => LeanXmss.Concrete.tweakableHash P
              (.node (layerOf layer) (level + 1) nodeIdx)) e
            (fun level => if h : level < LeanXmss.layerHeight then pi ⟨level, h⟩ else 0) levels leaf
  | 0, _ => by simp [Internal.climbUpto, LeanXmss.Concrete.foldPath]
  | l + 1, h => by
    unfold Internal.climbUpto
    rewrite [climbUpto_queryH P layer e pi leaf l (by omega), bind_map_left]
    simp only [LeanXmss.Concrete.foldPath, map_bind]
    refine bind_congr fun current => ?_
    -- The sibling on level `l` is entry `l` of the path.
    have hl : l < LeanXmss.layerHeight := by
      simp only [LeanXmss.layerHeight, LAYER_HEIGHT] at *
      omega
    rw [show (ofPath pi)[l] = ofDigest (pi ⟨l, hl⟩) from Vector.getElem_ofFn _, climbStep_queryH]
    simp only [hl, ↓reduceDIte]

/-- `Tree.fold`. -/
theorem fold_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (e : Nat) (he : e < 2 ^ 32)
    (pi : Fin LeanXmss.layerHeight → LeanXmss.Digest) (leaf : LeanXmss.Digest) :
    fold (queryH (m := m)) (ofParam P) layer e (ofDigest leaf) (ofPath pi)
      = ofDigest <$> LeanXmss.Concrete.treeFold (m := m) P (layerOf layer) (keyOfNat e he) pi
          LeanXmss.layerHeight leaf := by
  rw [fold, climbUpto_queryH]
  rfl

/-! ## Verification -/

/-- `Ots.leaf`: the leaf a one-time signature leads to, or nothing. -/
theorem otsLeaf_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (rho : LeanXmss.Randomness) (values : LeanXmss.ChainIndex → LeanXmss.Digest) :
    otsLeaf (queryH (m := m)) (ofParam P) layer e msg (ofRandomizer rho) (ofChains values)
      = Option.map ofDigest <$> LeanXmss.Concrete.otsLeaf (m := m) P (layerOf layer) (keyOf e)
          msg.data.toList rho values := by
  unfold otsLeaf LeanXmss.Concrete.otsLeaf
  rewrite [messageDigest_queryH, bind_map_left, map_bind]
  refine bind_congr fun digest => ?_
  rw [codeword?_ofDigest]
  cases LeanXmss.Codeword.decode digest with
  | none => simp
  | some enc =>
    simp only [Option.map_some]
    -- Chain `i` is walked from its digit to position 3.
    rewrite [ofFnInOrder_congr (c' := fun i : Fin V => ofDigest <$> LeanXmss.Concrete.recoverChain
      (m := m) P (layerOf layer) (keyOf e) (chainOf i) (enc (chainOf i)) (values (chainOf i)))
      fun i => by
        rewrite [show (ofChains values)[i] = ofDigest (values (chainOf i)) from
          Vector.getElem_ofFn _, chain_queryH, LeanXmss.Concrete.recoverChain]
        -- The digit is the proof's, now outside any bound.
        rewrite [show ((ofEncoding enc)[i] : Nat) = (enc (chainOf i)).val from
          congrArg Fin.val (Vector.getElem_ofFn _)]
        rfl]
    rewrite [ofFnInOrder_eq_sequenceFin, bind_map_left, map_bind]
    refine bind_congr fun ends => ?_
    -- `exact`, not `rw`: `ends` is indexed by `Fin V`, which is the proof's chain index.
    exact (congrArg (· >>= fun v => (pure (some v) : m _))
        (otsLeafHash_queryH P layer e ends)).trans
      (by simp only [bind_map_left, map_bind, map_pure, Option.map_some])

/-! ## Keys and signatures -/

/-- A public key as EthLib's. -/
@[simps] def ofPublicKey (pk : LeanXmss.PublicKey) : PublicKey where
  root := ofDigest pk.root
  publicParam := ofParam pk.parameter

/-- One layer's signature as EthLib's. -/
@[simps] def ofLayerSig (s : LeanXmss.LayerSignature) : LayerSignature where
  randomizer := ofRandomizer s.randomness
  chainValues := ofChains s.chainValues
  path := ofPath s.path

/-- A leaf index below `2^32` as EthLib's. -/
def ofLeafIndex (idx : LeanXmss.LeafIndex) : LeafIndex :=
  UInt32.ofNatLT idx.val
    (by simpa [LeanXmss.lifetime, LeanXmss.numLayers, LeanXmss.layerHeight] using idx.isLt)

/-- A signature as EthLib's: the leaf index, then the bottom layer's and the top layer's. -/
@[simps] def ofSignature (σ : LeanXmss.Signature) : Signature where
  leafIndex := ofLeafIndex σ.leafIndex
  bottom := ofLayerSig (σ.layers LeanXmss.bottomLayer)
  top := ofLayerSig (σ.layers LeanXmss.topLayer)

@[simp] theorem toNat_ofLeafIndex (idx : LeanXmss.LeafIndex) :
    (ofLeafIndex idx).toNat = idx.val := by
  simp [ofLeafIndex]

/-- EthLib's key `UInt32.ofNat e` is the proof's key `e`. -/
theorem keyOf_ofNat (key : LeanXmss.KeyIndex) : keyOf (UInt32.ofNat key.val) = key := by
  apply Fin.ext
  simp only [val_keyOf, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa [LeanXmss.lifetime, LeanXmss.numLayers, LeanXmss.layerHeight]
    using key.isLt)

theorem keyOfNat_val (key : LeanXmss.KeyIndex) (h : key.val < 2 ^ 32) : keyOfNat key.val h = key :=
  rfl

theorem key_lt (key : LeanXmss.KeyIndex) : key.val < 2 ^ 32 := by
  simpa [LeanXmss.lifetime, LeanXmss.numLayers, LeanXmss.layerHeight] using key.isLt

/-- A layer's root: the recovered leaf, folded up the path. -/
theorem layerRoot_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (key : LeanXmss.KeyIndex)
    (msg : ByteArray) (part : LeanXmss.LayerSignature) :
    layerRoot (queryH (m := m)) (ofParam P) layer key.val msg (ofLayerSig part)
      = Option.map ofDigest <$> LeanXmss.Concrete.layerRoot (m := m) P (layerOf layer) key
          msg.data.toList part := by
  unfold layerRoot LeanXmss.Concrete.layerRoot
  rewrite [ofLayerSig_randomizer, ofLayerSig_chainValues, otsLeaf_queryH, keyOf_ofNat,
    bind_map_left, map_bind]
  refine bind_congr fun leaf => ?_
  cases leaf with
  | none => simp
  | some leaf =>
    simp only [Option.map_some]
    rewrite [ofLayerSig_path, fold_queryH P layer key.val (key_lt key) part.path leaf, keyOfNat_val]
    simp only [bind_map_left, map_bind, map_pure, Option.map_some]

/-- Two digests are equal exactly when their bytes are. -/
theorem ofDigest_eq_iff (x y : LeanXmss.Digest) : ofDigest x = ofDigest y ↔ x = y :=
  ⟨ofBV_inj (by simp [LeanXmss.digestBits, DIGEST_LEN]), fun h => h ▸ rfl⟩

/-- `Ver(pk, m, sigma)`. -/
theorem verifyWith_queryH (pk : LeanXmss.PublicKey) (msg : LeanXmss.Message)
    (σ : LeanXmss.Signature) :
    verifyWith (queryH (m := m)) (ofPublicKey pk) (ofMessage msg) (ofSignature σ)
      = LeanXmss.Concrete.verify (m := m) pk msg σ := by
  unfold verifyWith LeanXmss.Concrete.verify
  dsimp only
  -- The bottom key is the leaf index itself.
  have hbottom : (ofSignature σ).leafIndex.toNat
      = (LeanXmss.keyAt σ.leafIndex LeanXmss.bottomLayer).val := by
    simp [ofSignature, LeanXmss.keyAt, LeanXmss.bottomLayer]
  -- The top key is the leaf index's bottom tree.
  have htop : bottomTree (ofSignature σ).leafIndex
      = (LeanXmss.keyAt σ.leafIndex LeanXmss.topLayer).val := by
    simp [ofSignature, bottomTree, LeanXmss.keyAt, LeanXmss.topLayer, LeanXmss.layerHeight,
      LAYER_HEIGHT]
  rewrite [hbottom, ofSignature_bottom, ofPublicKey_publicParam, layerRoot_queryH,
    bind_map_left]
  simp only [toList_data_packBytes, toList_ofMessage]
  refine bind_congr fun bottomRoot => ?_
  cases bottomRoot with
  | none => rfl
  | some bottomRoot =>
    simp only [Option.map_some]
    rewrite [htop, ofSignature_top, layerRoot_queryH, bind_map_left]
    simp only [toList_data_packBytes, toList_ofDigest]
    refine bind_congr fun root => ?_
    cases root with
    | none => rfl
    | some root =>
      simp only [Option.map_some, ofPublicKey_root, ofDigest_eq_iff]

/-! ## Signing -/

/-- The proof's randomizer search alone, without opening the chains.

It returns the first trial whose digest is a codeword, with the codeword. -/
def searchFrom (P : LeanXmss.PublicParameter) (lay : LeanXmss.Layer) (key : LeanXmss.KeyIndex)
    (msg : LeanXmss.HashInput) (base : LeanXmss.Randomness) :
    Nat → Nat → m (Option (LeanXmss.Randomness × LeanXmss.Encoding))
  | 0, _ => pure none
  | fuel + 1, trial => do
    let rho := base + BitVec.ofNat LeanXmss.digestBits trial
    let digest ← LeanXmss.Concrete.messageDigest P lay key msg rho
    match LeanXmss.Codeword.decode digest with
    | some enc => pure (some (rho, enc))
    | none => searchFrom P lay key msg base fuel (trial + 1)

/-- EthLib's search is the proof's, its results translated. -/
theorem findCodeword_queryH (P : LeanXmss.PublicParameter) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : LeanXmss.Randomness) :
    ∀ (fuel c : Nat),
      Internal.findCodeword (queryH (m := m)) (ofParam P) layer e msg (ofRandomizer base) c fuel
      = Option.map (fun r => (ofRandomizer r.1, ofEncoding r.2)) <$>
          searchFrom (m := m) P (layerOf layer) (keyOf e) msg.data.toList base fuel c
  | 0, c => by simp [Internal.findCodeword, searchFrom]
  | fuel + 1, c => by
    unfold Internal.findCodeword searchFrom
    rewrite [trialRandomizer_ofRandomizer]
    dsimp only
    rewrite [messageDigest_queryH, bind_map_left, map_bind]
    refine bind_congr fun digest => ?_
    rw [codeword?_ofDigest]
    cases LeanXmss.Codeword.decode digest with
    | none => exact findCodeword_queryH P layer e msg base fuel (c + 1)
    | some enc => simp

/-- The proof's signer is its search, then the opening of the chains at the codeword. -/
theorem otsSignFrom_eq_searchFrom (P : LeanXmss.PublicParameter) (lay : LeanXmss.Layer)
    (key : LeanXmss.KeyIndex) (S : LeanXmss.MasterSeed) (msg : LeanXmss.HashInput)
    (base : LeanXmss.Randomness) :
    ∀ (fuel c : Nat), LeanXmss.Seeded.otsSignFrom (m := m) P lay key S msg base fuel c
      = searchFrom P lay key msg base fuel c >>= fun r => match r with
        | none => pure none
        | some (rho, enc) => do
          let secrets ← LeanXmss.Seeded.otsSecrets P lay key S
          let values ← LeanXmss.Concrete.sequenceFin fun i =>
            LeanXmss.Concrete.chainWalk P lay key i 0 (enc i).val (secrets i)
          pure (some (rho, values))
  | 0, c => by simp [LeanXmss.Seeded.otsSignFrom, searchFrom]
  | fuel + 1, c => by
    unfold LeanXmss.Seeded.otsSignFrom searchFrom
    dsimp only
    rw [bind_assoc]
    refine bind_congr fun digest => ?_
    cases LeanXmss.Codeword.decode digest with
    | none => exact otsSignFrom_eq_searchFrom P lay key S msg base fuel (c + 1)
    | some enc => simp

/-- `Ots.sign`: the least admissible trial, then each chain opened at its digit. -/
theorem otsSign_queryH (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed) (layer : Layer)
    (key : LeanXmss.KeyIndex) (msg : ByteArray) :
    otsSign (queryH (m := m)) (ofParam P) (ofSeed S) layer (UInt32.ofNat key.val) msg
      = Option.map (fun r => (ofRandomizer r.1, ofChains r.2)) <$>
          LeanXmss.Seeded.otsSign (m := m) P (layerOf layer) key S msg.data.toList := by
  unfold otsSign LeanXmss.Seeded.otsSign
  rewrite [randomizerBase_queryH, keyOf_ofNat, bind_map_left, map_bind]
  refine bind_congr fun base => ?_
  rewrite [findCodeword_queryH, keyOf_ofNat, otsSignFrom_eq_searchFrom, bind_map_left, map_bind]
  refine bind_congr fun r => ?_
  cases r with
  | none => simp
  | some r =>
    obtain ⟨rho, enc⟩ := r
    simp only [Option.map_some]
    rewrite [chainStarts_queryH, keyOf_ofNat, bind_map_left, map_bind]
    refine bind_congr fun starts => ?_
    -- Chain `i` is opened at its digit.
    rewrite [ofFnInOrder_congr (c' := fun i : Fin V => ofDigest <$> LeanXmss.Concrete.chainWalk
      (m := m) P (layerOf layer) (keyOf (UInt32.ofNat key.val)) (chainOf i) 0
      (enc (chainOf i)).val (starts (chainOf i)))
      fun i => by
        rewrite [show (ofChains starts)[i] = ofDigest (starts (chainOf i)) from
          Vector.getElem_ofFn _, chain_queryH]
        rewrite [show ((ofEncoding enc)[i] : Nat) = (enc (chainOf i)).val from
          congrArg Fin.val (Vector.getElem_ofFn _)]
        rfl]
    rewrite [keyOf_ofNat, ofFnInOrder_eq_sequenceFin, bind_map_left, map_bind]
    refine bind_congr fun values => ?_
    simp only [map_pure, Option.map_some]
    rfl

/-- EthLib's result of one layer, from the proof's.

It is the signature, or the error of a key without a codeword. -/
def ofLayerResult (layer : Layer) (e : Nat) :
    Option LeanXmss.LayerSignature → Except XmssError LayerSignature
  | none => .error (.noAdmissibleEncoding layer e)
  | some s => .ok (ofLayerSig s)

/-- One layer's signature: the one-time signature and the key's path. -/
theorem signLayer_queryH (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed) (layer : Layer)
    (key : LeanXmss.KeyIndex) (msg : ByteArray) :
    signLayer (queryH (m := m)) (ofParam P) (ofSeed S) layer key.val msg
      = ofLayerResult layer key.val <$>
          LeanXmss.Seeded.signLayer (m := m) ⟨S, P⟩ (layerOf layer) key msg.data.toList := by
  unfold signLayer LeanXmss.Seeded.signLayer
  rewrite [otsSign_queryH, bind_map_left, map_bind]
  refine bind_congr fun r => ?_
  cases r with
  | none => simp [ofLayerResult]
  | some r =>
    obtain ⟨rho, values⟩ := r
    simp only [Option.map_some]
    rewrite [path_queryH P S layer key.val (key_lt key), keyOfNat_val, bind_map_left, map_bind]
    refine bind_congr fun p => ?_
    simp only [map_pure, ofLayerResult]
    rfl

/-! ## Key generation and signing from the seed -/

omit [LawfulMonad m] in
/-- `S = H("leanXMSS" | S_0)`. -/
theorem schemeSeed_queryH (S0 : LeanXmss.MasterSeed) :
    schemeSeed (queryH (m := m)) (ofSeed S0)
      = ofSeed <$> LeanXmss.Concrete.taggedSeed (m := m) LeanXmss.seedTag S0 := by
  simp only [schemeSeed, queryH, toList_data_append, toList_data_packBytes, toList_ofSeed,
    LeanXmss.Concrete.taggedSeed]
  -- A hash value is a seed, and the scheme's name is the proof's tag, byte for byte.
  show (ofSeed <$> LeanXmss.Concrete.oracleHash (m := m) (SEED_TAG ++ LeanXmss.bytesLE 32 S0)) = _
  rw [seed_tag_eq]
  rfl

/-- `P = Th(0^128, A_param, S)`.

The proof's `Th` returns a digest, `BitVec digestBits`, and a parameter is `BitVec 128`.

The conversion is applied at the parameter's type.

So the lemmas about `ofParam P` apply to the result. -/
theorem publicParamOf_queryH (S : LeanXmss.MasterSeed) :
    publicParamOf (queryH (m := m)) (ofSeed S)
      = (fun P : LeanXmss.PublicParameter => ofParam P) <$> LeanXmss.Concrete.th (m := m) 0
          (LeanXmss.keygenDomainFields .parameter) (LeanXmss.bytesLE 32 S) := by
  -- The all-zero parameter is the bytes of the zero bit vector.
  have hzero : Vector.replicate PUBLIC_PARAM_LEN (0 : UInt8)
      = ofParam (0 : LeanXmss.PublicParameter) := by
    rw [ofParam, ofBV_eq_littleEndian]
    apply Vector.ext
    intro i hi
    simp [littleEndian]
  rw [publicParamOf, hzero, th_queryH 0 _ _ toList_addrParam]
  simp only [toList_data_packBytes, toList_ofSeed]
  rfl

/-- `Sig(sk, idx, m)` from the seed `S_0`.

It re-derives the scheme seed and the parameter with two hash calls.

Then it runs the proof's signer with them as its key. -/
theorem signWith_queryH (S0 : LeanXmss.MasterSeed) (idx : LeanXmss.LeafIndex)
    (msg : LeanXmss.Message) :
    Except.toOption <$> signWith (queryH (m := m)) ⟨ofSeed S0⟩ (ofLeafIndex idx) (ofMessage msg)
      = (do
          let S ← LeanXmss.Concrete.taggedSeed (m := m) LeanXmss.seedTag S0
          let P ← LeanXmss.Concrete.th (m := m) 0 (LeanXmss.keygenDomainFields .parameter)
            (LeanXmss.bytesLE 32 S)
          Option.map ofSignature <$> LeanXmss.Seeded.sign (m := m) ⟨S, P⟩ idx msg) := by
  -- The bottom key is the leaf index, the top key its bottom tree.
  have hbottom : (ofLeafIndex idx).toNat = (LeanXmss.keyAt idx LeanXmss.bottomLayer).val := by
    simp [LeanXmss.keyAt, LeanXmss.bottomLayer]
  have htop : bottomTree (ofLeafIndex idx) = (LeanXmss.keyAt idx LeanXmss.topLayer).val := by
    simp [bottomTree, LeanXmss.keyAt, LeanXmss.topLayer, LeanXmss.layerHeight, LAYER_HEIGHT]
  unfold signWith LeanXmss.Seeded.sign
  rewrite [map_bind, schemeSeed_queryH, bind_map_left]
  refine bind_congr fun S => ?_
  rewrite [map_bind, publicParamOf_queryH]
  -- `refine`, typing `P` as a parameter: the proof's `Th` returns it as a digest.
  refine (bind_map_left _ _ _).trans (bind_congr fun (P : LeanXmss.PublicParameter) => ?_)
  dsimp only
  -- The bottom layer signs the message.
  rewrite [hbottom, signLayer_queryH, bind_map_left, map_bind, map_bind]
  simp only [toList_data_packBytes, toList_ofMessage]
  refine bind_congr fun bottom => ?_
  cases bottom with
  | none => simp [ofLayerResult, Except.toOption]
  | some bottom =>
    simp only [ofLayerResult, pure_bind]
    -- The root of bottom tree `b`, from the whole tree.
    rewrite [htop, node_queryH, bind_map_left, map_bind, map_bind]
    refine bind_congr fun bottomRoot => ?_
    -- The top key signs that root.
    rewrite [signLayer_queryH, bind_map_left, map_bind]
    simp only [toList_data_packBytes, toList_ofDigest, map_bind]
    refine bind_congr fun top => ?_
    cases top with
    | none => simp [ofLayerResult, Except.toOption]
    | some top =>
      simp only [ofLayerResult, map_pure, Except.toOption, Option.map_some]
      -- The proof's signature picks each layer by comparing it with the bottom one.
      simp [ofSignature, LeanXmss.bottomLayer, LeanXmss.topLayer]

/-- `Gen` from the seed `S_0`: EthLib's secret key is the seed, its public key the proof's. -/
theorem keyGenWith_queryH (S0 : LeanXmss.MasterSeed) :
    keyGenWith (queryH (m := OracleComp LeanXmss.HashSpec)) (ofSeed S0)
      = (fun keys => ((⟨ofSeed S0⟩ : SecretKey), ofPublicKey keys.1)) <$>
          LeanXmss.Seeded.keygenFromSeed S0 := by
  unfold keyGenWith LeanXmss.Seeded.keygenFromSeed
  rewrite [schemeSeed_queryH, bind_map_left, map_bind]
  refine bind_congr fun S => ?_
  rewrite [publicParamOf_queryH, map_bind]
  -- `refine`, typing `P` as a parameter: the proof's `Th` returns it as a digest.
  refine (bind_map_left _ _ _).trans (bind_congr fun (P : LeanXmss.PublicParameter) => ?_)
  rewrite [node_queryH, bind_map_left, map_bind]
  refine bind_congr fun root => ?_
  simp only [map_pure]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability
