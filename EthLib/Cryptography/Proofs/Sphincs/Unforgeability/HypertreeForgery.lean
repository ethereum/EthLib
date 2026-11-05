module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.ForsForgery
public import EthLib.Cryptography.Proofs.Sphincs.Correctness
public import EthLib.Cryptography.Proofs.Sphincs.Encoding
public import EthLib.Cryptography.Proofs.Wots.Binding

/-!
# Proofs: what an accepted signature contains

Verification walks the hypertree from the bottom up.

This file reads it from the top down, one layer at a time.

At a layer, the signature leads to the honest root of its key's tree.

Then one of four things holds:

- A search finds a node of that tree where verification left the honest values.
  It is a tree node, the key's leaf or a chain step, with a valid offer.
- The signature reveals a chain value of the key below the position its honest signature reveals.
  When the key has no honest signature, the value is below the end of its chain.
- The counter and the message of the layer encode to the key's honest codeword at another input.
- The layer signature is the key's honest signature of its honest message.

In the last case the layer below signed what the honest key signs, so the walk goes on below it.

Below the bottom layer, FORS openings recover the honest FORS key.

The FORS extraction then gives the honest openings, or a valid offer at a FORS node.

So FORS is reached only through an honest bottom layer signature.

Every statement holds for every hash `f` and every source of secrets, in the identity monad.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants

/-! ## The honest values of the hypertree -/

variable (f : ByteArray → Vector UInt8 32) (P : PublicParam) (prf : SeedPrf Id)

/-- The honest value at position `mu` of chain `i` of a key. -/
def chainValue (key : OtsKey) (i : Fin V) (mu : Nat) : Digest :=
  Wots.honestValue (chainStep (pureHash f) P key i) (chainStarts P prf key).run[i] mu

/-- The honest ends of the 64 chains of a key. -/
def honestEnds (key : OtsKey) : Vector Digest V :=
  Vector.ofFn fun i => chainValue f P prf key i (CHAIN_LENGTH - 1)

/-- The honest children values of a node.

- A chain step has the honest value of its chain at its position.
- A key's leaf has the honest ends of its chains.
- A tree node on level `level + 1` has its two children on level `level`.
- A FORS node has its FORS children values.

An encoding has no honest values here. -/
def honestChildren : Node → List Digest
  | .chain key i mu => [chainValue f P prf key.toOtsKey i mu.val]
  | .otsLeaf key => (honestEnds f P prf key.toOtsKey).toList
  | .treeNode layer tree level j =>
      [(node (pureHash f) P prf layer tree.val level.val (2 * j.val)).run,
        (node (pureHash f) P prf layer tree.val level.val (2 * j.val + 1)).run]
  | k => forsChildren f P prf k

variable {f P prf}

/-- One step up a chain from its honest value gives the next honest value. -/
theorem chainStep_chainValue (key : OtsKey) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) :
    (chainStep (pureHash f) P key i mu (chainValue f P prf key i mu.val)).run =
      chainValue f P prf key i (mu.val + 1) :=
  (Wots.honestValue_succ _ _ mu.isLt).symm

/-- A walk from the start of a chain reaches the honest value at its length. -/
theorem chain_chainStarts (key : OtsKey) (i : Fin V) (steps : Nat)
    (h : 0 + steps < CHAIN_LENGTH) :
    (chain (pureHash f) P key i 0 steps h (chainStarts P prf key).run[i]).run =
      chainValue f P prf key i steps := by
  exact (Wots.chain_honestValue (chainStep (pureHash f) P key i)
    (chainStarts P prf key).run[i] steps 0 (Nat.le_sub_one_of_lt h)).trans
      (congrArg _ (Nat.zero_add steps))

/-- The leaf of a key is the leaf hash of its honest ends. -/
theorem otsPublicLeaf_run (key : OtsKey) :
    (otsPublicLeaf (pureHash f) P prf key).run =
      (otsLeafHash (pureHash f) P key (honestEnds f P prf key)).run := by
  rw [otsPublicLeaf, Id.run_bind, Id.run_bind, HashSig.ofFnInOrder_run]
  refine congrArg (fun ends => (otsLeafHash (pureHash f) P key ends).run)
    (Vector.ext fun i hi => ?_)
  simp only [Vector.getElem_ofFn, honestEnds]
  exact chain_chainStarts key ⟨i, hi⟩ _ _

/-! ## The value of a node -/

/-- A chain step's value at a value is the chain step of that value. -/
theorem valueAt_chain (key : GraphKey) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) (v : Digest) :
    (Node.chain key i mu).valueAt f P [v] = (chainStep (pureHash f) P key.toOtsKey i mu v).run := by
  simp only [Node.valueAt, Node.address, Node.suffix, digestsBytes_singleton,
    ByteArray.append_empty]
  rfl

/-- A key's leaf at chain ends is the leaf hash of those ends. -/
theorem valueAt_otsLeaf (key : GraphKey) (ends : Vector Digest V) :
    (Node.otsLeaf key).valueAt f P ends.toList =
      (otsLeafHash (pureHash f) P key.toOtsKey ends).run := by
  simp only [Node.valueAt, Node.address, Node.suffix, digestsBytes_toList, ByteArray.append_empty]
  rfl

/-- A tree node's value at two children is the node hash of those children. -/
theorem valueAt_treeNode (layer : Layer) (tree : Fin (2 ^ 18)) (level : Fin TOP_HEIGHT)
    (j : Fin (2 ^ TOP_HEIGHT)) (a b : Digest) :
    (Node.treeNode layer tree level j).valueAt f P [a, b] =
      (nodeHash (pureHash f) P layer tree.val (level.val + 1) j.val a b).run := by
  simp only [Node.valueAt, Node.address, Node.suffix, digestsBytes_pair, ByteArray.append_empty]
  rfl

/-- A chain step has one child. -/
theorem length_children_chain (key : GraphKey) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) :
    ((Node.chain key i mu).children P).length = 1 := by
  simp only [Node.children]
  split <;> rfl

/-- A tree node has two children. -/
theorem length_children_treeNode (layer : Layer) (tree : Fin (2 ^ 18)) (level : Fin TOP_HEIGHT)
    (j : Fin (2 ^ TOP_HEIGHT)) : ((Node.treeNode layer tree level j).children P).length = 2 := by
  simp only [Node.children]
  split <;> rfl

/-- A valid offer depends on the honest values only at its own node. -/
theorem NodePreimage.valid_congr {honest honest' : Node → List Digest} {w : NodePreimage}
    (h : honest w.node = honest' w.node) :
    w.Valid f P honest ↔ w.Valid f P honest' := by
  simp only [NodePreimage.Valid, h]

/-! ## The keys on the way up -/

/-- The key of a layer on the way from instance `idx` up, as a key of the graph. -/
def GraphKey.ofIndex (layer : Layer) (idx : Fin (2 ^ HEIGHT)) : GraphKey where
  layer := layer
  tree := ⟨(OtsKey.ofIndex layer idx.val).tree, by
    have := idx.isLt
    cases layer <;>
      simp only [OtsKey.ofIndex, Layer.below, Layer.height, Nat.shiftRight_eq_div_pow, HEIGHT,
        TOP_HEIGHT, LOWER_HEIGHT] at * <;> omega⟩
  leaf := ⟨(OtsKey.ofIndex layer idx.val).leaf, lt_of_lt_of_le (OtsKey.ofIndex_leaf_lt _ _)
    (Nat.pow_le_pow_right (by decide) (Layer.height_le layer))⟩

/-- The graph key on the way up is the scheme's key. -/
theorem GraphKey.toOtsKey_ofIndex (layer : Layer) (idx : Fin (2 ^ HEIGHT)) :
    (GraphKey.ofIndex layer idx).toOtsKey = OtsKey.ofIndex layer idx.val :=
  rfl

/-! ## The searches of one layer -/

variable (f P prf)

/-- The chain ends a one-time signature leads to, at a codeword. -/
def otsEnds (key : OtsKey) (x : Codeword) (y : Vector Digest V) : Vector Digest V :=
  Vector.ofFn fun i =>
    (chain (pureHash f) P key i x[i] (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega)
      y[i]).run

/-- The tree node at which a climb from the leaf of key `idx` of a layer leaves the honest tree.

The climb is the one of verification, with the path's nodes. -/
def findPathPreimage (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (leaf : Digest)
    (path : List Digest) : Option NodePreimage :=
  match Merkle.findSecondPreimage
      (nodeHash (pureHash f) P layer (OtsKey.ofIndex layer idx.val).tree)
      (leaves (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree) 0
      (OtsKey.ofIndex layer idx.val).leaf leaf path with
  | some w =>
    if h : w.level < TOP_HEIGHT ∧ w.j < 2 ^ TOP_HEIGHT then
      some ⟨.treeNode layer (GraphKey.ofIndex layer idx).tree ⟨w.level, h.1⟩ ⟨w.j, h.2⟩,
        [w.y.1, w.y.2]⟩
    else none
  | none => none

/-- The chain step at which a walk of chain `i` from position `x` leaves the honest values. -/
def findChainNodePreimage (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (i : Fin V)
    (x : Fin CHAIN_LENGTH) (y : Digest) : Option NodePreimage :=
  match Wots.findChainPreimage (chainStep (pureHash f) P (OtsKey.ofIndex layer idx.val) i)
      (chainValue f P prf (OtsKey.ofIndex layer idx.val) i) x.val (CHAIN_LENGTH - 1 - x.val)
      (by have := x.isLt; omega) y with
  | some w =>
    if h : w.pos < CHAIN_LENGTH - 1 then
      some ⟨.chain (GraphKey.ofIndex layer idx) i ⟨w.pos, h⟩, [w.value]⟩
    else none
  | none => none

/-- The node at which the chains of a one-time signature leave the honest values.

When the walked ends differ from the honest ends but give the honest leaf, it is the key's leaf.

Otherwise it is the first chain step where a walk leaves the honest values. -/
def findOtsPreimage (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (x : Codeword)
    (y : Vector Digest V) : Option NodePreimage :=
  if otsEnds f P (OtsKey.ofIndex layer idx.val) x y ≠
        honestEnds f P prf (OtsKey.ofIndex layer idx.val) ∧
      (otsLeafHash (pureHash f) P (OtsKey.ofIndex layer idx.val)
          (otsEnds f P (OtsKey.ofIndex layer idx.val) x y)).run =
        (otsLeafHash (pureHash f) P (OtsKey.ofIndex layer idx.val)
          (honestEnds f P prf (OtsKey.ofIndex layer idx.val))).run then
    some ⟨.otsLeaf (GraphKey.ofIndex layer idx),
      (otsEnds f P (OtsKey.ofIndex layer idx.val) x y).toList⟩
  else (List.finRange V).findSome? fun i => findChainNodePreimage f P prf layer idx i x[i] y[i]

/-- The node at which a layer signature leaves the honest values of its key's tree, if any.

The path is searched first, then the key's leaf and its chains. -/
def findLayerPreimage (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (msg : ByteArray)
    (sig : LayerSignature layer) : Option NodePreimage :=
  match (encode (pureHash f) P (OtsKey.ofIndex layer idx.val) msg sig.counter).run with
  | none => none
  | some x =>
    (findPathPreimage f P prf layer idx (otsLeafHash (pureHash f) P (OtsKey.ofIndex layer idx.val)
        (otsEnds f P (OtsKey.ofIndex layer idx.val) x sig.chainValues)).run sig.path.toList).or
      (findOtsPreimage f P prf layer idx x sig.chainValues)

variable {f P prf}

/-! ## Every offer the searches return is valid -/

/-- A second preimage of a climb in a layer's tree is below level 10 and index `2^10`. -/
private theorem bounds_of_findSecondPreimage {layer : Layer} {idx : Fin (2 ^ HEIGHT)} {b : Digest}
    {q : List Digest} (hq : q.length ≤ layer.height) {w : Merkle.SecondPreimage Digest}
    (hw : Merkle.findSecondPreimage
      (nodeHash (pureHash f) P layer (OtsKey.ofIndex layer idx.val).tree)
      (leaves (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree) 0
      (OtsKey.ofIndex layer idx.val).leaf b q = some w) :
    w.level < TOP_HEIGHT ∧ w.j < 2 ^ TOP_HEIGHT := by
  obtain ⟨-, k, hk, hlevel, hj⟩ := Merkle.findSecondPreimage_valid _ _ q 0 _ b w hw
  have hh := Layer.height_le layer
  refine ⟨by omega, ?_⟩
  rw [hj]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (GraphKey.ofIndex layer idx).leaf.isLt

/-- Every tree node the path search returns is a valid offer. -/
theorem findPathPreimage_valid {layer : Layer} {idx : Fin (2 ^ HEIGHT)} {leaf : Digest}
    {path : List Digest} {w : NodePreimage}
    (hw : findPathPreimage f P prf layer idx leaf path = some w) :
    w.Valid f P (honestChildren f P prf) := by
  unfold findPathPreimage at hw
  split at hw
  · rename_i w' hw'
    split at hw
    · cases hw
      obtain ⟨⟨hne, heq⟩, -⟩ := Merkle.findSecondPreimage_valid _ _ _ 0 _ _ w' hw'
      refine ⟨by rw [length_children_treeNode]; rfl, ?_, ?_⟩
      · -- The pair differs from the honest children.
        intro h
        apply hne
        simp only [honestChildren, List.cons.injEq, and_true] at h
        exact Prod.ext h.1 h.2
      · -- The pair hashes to the honest node, the hash of the honest children.
        simp only [honestChildren, valueAt_treeNode]
        exact heq.trans (Merkle.node_succ_run _ _ _ _)
    · cases hw
  · cases hw

/-- Every chain step the chain search returns is a valid offer. -/
theorem findChainNodePreimage_valid {layer : Layer} {idx : Fin (2 ^ HEIGHT)} {i : Fin V}
    {x : Fin CHAIN_LENGTH} {y : Digest} {w : NodePreimage}
    (hw : findChainNodePreimage f P prf layer idx i x y = some w) :
    w.Valid f P (honestChildren f P prf) := by
  unfold findChainNodePreimage at hw
  split at hw
  · rename_i w' hw'
    split at hw
    · cases hw
      obtain ⟨⟨hpos, hne, heq⟩, -⟩ := Wots.findChainPreimage_valid _ _ _ _ _ _ w' hw'
      refine ⟨by rw [length_children_chain]; rfl, ?_, ?_⟩
      · -- The value differs from the honest one.
        simp only [honestChildren, ne_eq, List.cons.injEq, and_true]
        exact hne
      · -- The value steps to the next honest value.
        simp only [honestChildren, valueAt_chain, GraphKey.toOtsKey_ofIndex]
        rw [chainStep_chainValue]
        exact heq
    · cases hw
  · cases hw

/-- Every node the search of a one-time signature returns is a valid offer. -/
theorem findOtsPreimage_valid {layer : Layer} {idx : Fin (2 ^ HEIGHT)} {x : Codeword}
    {y : Vector Digest V} {w : NodePreimage}
    (hw : findOtsPreimage f P prf layer idx x y = some w) :
    w.Valid f P (honestChildren f P prf) := by
  unfold findOtsPreimage at hw
  split at hw
  · rename_i h
    cases hw
    refine ⟨by simp [Node.children], ?_, ?_⟩
    · -- The ends differ from the honest ends.
      simp only [honestChildren, GraphKey.toOtsKey_ofIndex, ne_eq, Vector.toList_inj]
      exact h.1
    · -- The ends hash to the honest leaf.
      simp only [honestChildren, valueAt_otsLeaf, GraphKey.toOtsKey_ofIndex]
      exact h.2
  · obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some hw
    exact findChainNodePreimage_valid hi

/-- Every node the search of a layer signature returns is a valid offer. -/
theorem findLayerPreimage_valid {layer : Layer} {idx : Fin (2 ^ HEIGHT)} {msg : ByteArray}
    {sig : LayerSignature layer} {w : NodePreimage}
    (hw : findLayerPreimage f P prf layer idx msg sig = some w) :
    w.Valid f P (honestChildren f P prf) := by
  unfold findLayerPreimage at hw
  split at hw
  · cases hw
  · rcases Option.or_eq_some_iff.1 hw with hp | ⟨-, ho⟩
    · exact findPathPreimage_valid hp
    · exact findOtsPreimage_valid ho

/-! ## The honest layer signature

The searches find nothing in a key's honest signature of its honest message. -/

/-- The path search finds nothing on an honest climb. -/
theorem findPathPreimage_honest (layer : Layer) (idx : Fin (2 ^ HEIGHT)) :
    findPathPreimage f P prf layer idx
      (node (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree 0
        (OtsKey.ofIndex layer idx.val).leaf).run
      (path (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree
        (OtsKey.ofIndex layer idx.val).leaf).run.toList = none := by
  unfold findPathPreimage
  rw [show (path (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree
      (OtsKey.ofIndex layer idx.val).leaf).run.toList = (Merkle.siblings
        (nodeHash (pureHash f) P layer (OtsKey.ofIndex layer idx.val).tree)
        (leaves (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree) 0
        (OtsKey.ofIndex layer idx.val).leaf layer.height).run.toList from rfl]
  rw [show (node (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree 0
      (OtsKey.ofIndex layer idx.val).leaf).run = (Merkle.node
        (nodeHash (pureHash f) P layer (OtsKey.ofIndex layer idx.val).tree)
        (leaves (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree) 0
        (OtsKey.ofIndex layer idx.val).leaf).run from rfl]
  rw [Merkle.findSecondPreimage_honest]

/-- The chain search finds nothing on an honest walk. -/
theorem findChainNodePreimage_honest (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (i : Fin V)
    (x : Fin CHAIN_LENGTH) :
    findChainNodePreimage f P prf layer idx i x
      (chainValue f P prf (OtsKey.ofIndex layer idx.val) i x.val) = none := by
  unfold findChainNodePreimage chainValue
  rw [Wots.findChainPreimage_honest]

/-- The honest chain values of a codeword walk to the honest ends. -/
theorem otsEnds_chainValue (key : OtsKey) (x : Codeword) :
    otsEnds f P key x (Vector.ofFn fun i => chainValue f P prf key i x[i]) =
      honestEnds f P prf key := by
  refine Vector.ext fun i hi => ?_
  simp only [otsEnds, honestEnds, Fin.getElem_fin, Vector.getElem_ofFn]
  have hx := (x[i]'hi).isLt
  exact (Wots.chain_honestValue (chainStep (pureHash f) P key ⟨i, hi⟩)
    (chainStarts P prf key).run[i] (CHAIN_LENGTH - 1 - x[i]) x[i] (by omega)).trans
      (congrArg _ (by omega))

/-- The search of a one-time signature finds nothing in the honest chain values. -/
theorem findOtsPreimage_honest (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (x : Codeword) :
    findOtsPreimage f P prf layer idx x
      (Vector.ofFn fun i => chainValue f P prf (OtsKey.ofIndex layer idx.val) i x[i]) = none := by
  unfold findOtsPreimage
  rw [otsEnds_chainValue]
  simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
  rw [List.findSome?_eq_none_iff]
  intro i _
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact findChainNodePreimage_honest layer idx i x[i]

/-- A one-time signature of the signer holds the honest chain values at its codeword. -/
theorem otsSign_eq_some {key : OtsKey} {msg : ByteArray} {c : UInt32} {y : Vector Digest V}
    (h : (otsSign (pureHash f) P prf key msg).run = some (c, y)) :
    ∃ x, (encode (pureHash f) P key msg c).run = some x ∧
      y = Vector.ofFn fun i => chainValue f P prf key i x[i] := by
  rw [otsSign_run, Option.map_eq_some_iff] at h
  obtain ⟨⟨c', x⟩, hfind, hxy⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
  rw [Internal.findCounter] at hfind
  obtain ⟨-, -, -, -, hcw, -⟩ := Wots.findFirst_spec hfind
  refine ⟨x, hcw, Vector.ext fun i hi => ?_⟩
  simp only [Vector.getElem_ofFn]
  exact chain_chainStarts key ⟨i, hi⟩ _ _

/-- The search of a layer finds nothing in the key's honest signature of any message. -/
theorem findLayerPreimage_honest {layer : Layer} {idx : Fin (2 ^ HEIGHT)} {msg : ByteArray}
    {sig : LayerSignature layer}
    (h : (signLayer (pureHash f) P prf layer idx.val msg).run = .ok sig) :
    findLayerPreimage f P prf layer idx msg sig = none := by
  obtain ⟨hots, hpath⟩ := signLayer_eq_ok h
  obtain ⟨x, hx, hy⟩ := otsSign_eq_some hots
  unfold findLayerPreimage
  rw [hx]
  dsimp only
  rw [hy, otsEnds_chainValue, ← otsPublicLeaf_run, hpath]
  rw [show (otsPublicLeaf (pureHash f) P prf (OtsKey.ofIndex layer idx.val)).run =
      (node (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree 0
        (OtsKey.ofIndex layer idx.val).leaf).run from rfl]
  rw [findPathPreimage_honest, findOtsPreimage_honest]
  rfl

/-! ## One layer -/

/-- An encoding is the codeword of its tweakable hash, if any. -/
theorem encode_run (key : OtsKey) (msg : ByteArray) (c : UInt32) :
    (encode (pureHash f) P key msg c).run = codeword? (th (pureHash f) P (addrEncoding key)
      (msg ++ packBytes (uintToBytes COUNTER_LEN c.toNat))).run := by
  rw [encode, Id.run_map]

/-- Every codeword has a digit below the end of its chain.

Its 64 digits sum to 128, below `64 * 3`. -/
theorem exists_lt_of_codeword {d : Digest} {x : Codeword} (h : codeword? d = some x) :
    ∃ i : Fin V, (x[i] : Nat) < CHAIN_LENGTH - 1 := by
  by_contra hall
  simp only [not_exists, not_lt] at hall
  have hle : ∑ _i : Fin V, (CHAIN_LENGTH - 1) ≤ ∑ i : Fin V, (x[i] : Nat) :=
    Finset.sum_le_sum fun i _ => hall i
  rw [sum_of_codeword h] at hle
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  simp only [V, CHAIN_LENGTH, TARGET_SUM] at hle
  omega

variable (f P prf)

/-- The layer signature holds an honest chain value that the key's honest signature hides.

It holds the honest value of chain `i` at the digit `x_i` of its codeword.

That digit is below the end of the chain.

When the key has an honest signature, the digit is also below the one it reveals on chain `i`. -/
def HiddenChainValue (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (msg : ByteArray)
    (sig : LayerSignature layer) : Prop :=
  ∃ x, (encode (pureHash f) P (OtsKey.ofIndex layer idx.val) msg sig.counter).run = some x ∧
    ∃ i : Fin V, sig.chainValues[i] = chainValue f P prf (OtsKey.ofIndex layer idx.val) i x[i] ∧
      (x[i] : Nat) < CHAIN_LENGTH - 1 ∧
      ∀ sigH, (signLayer (pureHash f) P prf layer idx.val
          (layerMessage (pureHash f) P prf layer idx.val).run).run = .ok sigH →
        ∀ xH, (encode (pureHash f) P (OtsKey.ofIndex layer idx.val)
          (layerMessage (pureHash f) P prf layer idx.val).run sigH.counter).run = some xH →
        (x[i] : Nat) < xH[i]

/-- The layer encodes another input to the codeword of the key's honest signature.

The input is the message and the counter of the layer signature. -/
def CodewordHit (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (msg : ByteArray)
    (sig : LayerSignature layer) : Prop :=
  ∃ sigH, (signLayer (pureHash f) P prf layer idx.val
      (layerMessage (pureHash f) P prf layer idx.val).run).run = .ok sigH ∧
    (msg, sig.counter) ≠ ((layerMessage (pureHash f) P prf layer idx.val).run, sigH.counter) ∧
    (encode (pureHash f) P (OtsKey.ofIndex layer idx.val) msg sig.counter).run =
      (encode (pureHash f) P (OtsKey.ofIndex layer idx.val)
        (layerMessage (pureHash f) P prf layer idx.val).run sigH.counter).run

/-- A layer signature that leaves the honest values of its key. -/
def LayerFault (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (msg : ByteArray)
    (sig : LayerSignature layer) : Prop :=
  (∃ w, findLayerPreimage f P prf layer idx msg sig = some w ∧
      w.Valid f P (honestChildren f P prf)) ∨
    HiddenChainValue f P prf layer idx msg sig ∨ CodewordHit f P prf layer idx msg sig

/-- The key's honest signature of its honest message. -/
def LayerHonest (layer : Layer) (idx : Fin (2 ^ HEIGHT)) (msg : ByteArray)
    (sig : LayerSignature layer) : Prop :=
  msg = (layerMessage (pureHash f) P prf layer idx.val).run ∧
    (signLayer (pureHash f) P prf layer idx.val msg).run = .ok sig

variable {f P prf}

/-- The key's honest signature of its honest message is not a fault.

So the two cases of the binding below never both hold. -/
theorem not_layerFault_of_layerHonest {layer : Layer} {idx : Fin (2 ^ HEIGHT)} {msg : ByteArray}
    {sig : LayerSignature layer} (h : LayerHonest f P prf layer idx msg sig) :
    ¬LayerFault f P prf layer idx msg sig := by
  obtain ⟨rfl, hs⟩ := h
  rintro (⟨w, hw, -⟩ | ⟨x, hx, i, -, -, hlt⟩ | ⟨sigH, hsH, hne, -⟩)
  · -- The search finds nothing in an honest signature.
    rw [findLayerPreimage_honest hs] at hw
    cases hw
  · -- The digit cannot be below itself.
    exact lt_irrefl _ (hlt sig hs x hx)
  · -- The honest signature has the honest input.
    rw [hs] at hsH
    cases hsH
    exact hne rfl

/-- Two layer signatures with the same fields are equal. -/
private theorem LayerSignature.ext_fields {layer : Layer} {a b : LayerSignature layer}
    (hc : a.counter = b.counter) (hy : a.chainValues = b.chainValues) (hp : a.path = b.path) :
    a = b := by
  cases a
  cases b
  simp only at hc hy hp
  rw [hc, hy, hp]

/-- **Binding of one layer.**

Take a layer signature that leads to the honest root of its key's tree.

It leaves the honest values of the key, or it is the key's honest signature of its message. -/
theorem layerRoot_binding {layer : Layer} {idx : Fin (2 ^ HEIGHT)} {msg : ByteArray}
    {sig : LayerSignature layer}
    (h : (layerRoot (pureHash f) P layer idx.val msg sig).run =
      some (treeRoot (pureHash f) P prf layer (OtsKey.ofIndex layer idx.val).tree).run) :
    LayerFault f P prf layer idx msg sig ∨ LayerHonest f P prf layer idx msg sig := by
  cases hw : findLayerPreimage f P prf layer idx msg sig with
  | some w => exact .inl (.inl ⟨w, hw, findLayerPreimage_valid hw⟩)
  | none =>
  unfold findLayerPreimage at hw
  -- Short names for the key and the ends the signature walks to.
  set key := OtsKey.ofIndex layer idx.val with hkey
  rw [layerRoot_run, otsLeaf_run] at h
  cases hx : (encode (pureHash f) P key msg sig.counter).run with
  | none => rw [hx] at h; cases h
  | some x =>
  rw [hx] at h
  simp only [Option.map_some, Option.some_inj] at h
  set ends := otsEnds f P key x sig.chainValues with hends
  have hends' : (Vector.ofFn fun i : Fin V => (chain (pureHash f) P key i x[i]
      (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega) sig.chainValues[i]).run) = ends :=
    rfl
  rw [hends'] at h
  rw [hx] at hw
  dsimp only at hw
  rw [← hends, Option.or_eq_none_iff] at hw
  obtain ⟨hpath, hots⟩ := hw
  -- The climb reaches the honest root, so the leaf and the path are honest.
  have hleafIdx := OtsKey.ofIndex_leaf_lt layer idx.val
  rcases Merkle.climb_binding_node (nodeHash (pureHash f) P layer key.tree)
      (leaves (pureHash f) P prf layer key.tree) layer.height 0 key.leaf
      (otsLeafHash (pureHash f) P key ends).run sig.path.toList (by simp)
      (by rw [Nat.zero_add, Nat.div_eq_of_lt hleafIdx]; exact h) with ⟨hleaf, hsibs⟩ | hsome
  swap
  · -- A second preimage on the path is a tree node the search returns.
    exfalso
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 hsome
    have hb := bounds_of_findSecondPreimage (by simp) hw'
    unfold findPathPreimage at hpath
    rw [hw'] at hpath
    simp only [hb, and_self, ↓reduceDIte, reduceCtorEq] at hpath
  -- The ends are honest, or the search returns the key's leaf.
  have hleaf' : (otsLeafHash (pureHash f) P key ends).run =
      (otsLeafHash (pureHash f) P key (honestEnds f P prf key)).run := by
    rw [hleaf, ← otsPublicLeaf_run]
    rfl
  have hendsEq : ends = honestEnds f P prf key := by
    by_contra hne
    unfold findOtsPreimage at hots
    rw [ite_eq_left ⟨hne, hleaf'⟩] at hots
    cases hots
  -- Each chain walks to its honest end, so it starts at the honest value of its digit.
  have hchains : ∀ i : Fin V, sig.chainValues[i] = chainValue f P prf key i x[i] := by
    intro i
    have hend := congrArg (fun v : Vector Digest V => v[i]) hendsEq
    simp only [hends, otsEnds, honestEnds, Fin.getElem_fin, Vector.getElem_ofFn] at hend
    have hxi := (x[i]).isLt
    rcases Wots.chain_binding (chainStep (pureHash f) P key i) (chainValue f P prf key i)
        (CHAIN_LENGTH - 1 - x[i]) x[i] (by omega) sig.chainValues[i]
        (hend.trans (congrArg (chainValue f P prf key i) (by omega))) with hv | hsome
    · exact hv
    · -- A second preimage on chain `i` is a chain step the search returns.
      exfalso
      obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 hsome
      obtain ⟨⟨hpos, -⟩, -⟩ := Wots.findChainPreimage_valid _ _ _ _ _ _ w' hw'
      unfold findOtsPreimage at hots
      rw [ite_eq_right fun hc => hc.1 hendsEq,
        List.findSome?_eq_none_iff] at hots
      have := hots i (List.mem_finRange _)
      unfold findChainNodePreimage at this
      rw [hw'] at this
      simp only [hpos, ↓reduceDIte, reduceCtorEq] at this
  -- Compare with the key's honest signature of its honest message.
  cases hs : (signLayer (pureHash f) P prf layer idx.val
      (layerMessage (pureHash f) P prf layer idx.val).run).run with
  | error e =>
    -- No honest signature: some digit is below the end of its chain.
    obtain ⟨i, hi⟩ := exists_lt_of_codeword ((encode_run key msg sig.counter).symm.trans hx)
    refine .inl (.inr (.inl ⟨x, hx, i, hchains i, hi, fun sigH hsigH => ?_⟩))
    rw [hs] at hsigH
    cases hsigH
  | ok sigH =>
  obtain ⟨hotsH, hpathH⟩ := signLayer_eq_ok hs
  obtain ⟨xH, hxH, hyH⟩ := otsSign_eq_some hotsH
  by_cases hcw : x = xH
  · subst hcw
    by_cases hin : (msg, sig.counter) = ((layerMessage (pureHash f) P prf layer idx.val).run,
        sigH.counter)
    · -- The same input: the layer signature is the honest one.
      obtain ⟨hmsg, hc⟩ := Prod.mk.inj hin
      have hy : sig.chainValues = sigH.chainValues := by
        rw [hyH]
        exact Vector.ext fun i hi => by
          simp only [Vector.getElem_ofFn]
          exact hchains ⟨i, hi⟩
      have hp : sig.path = sigH.path := by
        rw [hpathH]
        exact Vector.toList_inj.1 hsibs
      refine .inr ⟨hmsg, ?_⟩
      rw [LayerSignature.ext_fields hc hy hp]
      subst hmsg
      exact hs
    · -- Another input with the honest codeword.
      exact .inl (.inr (.inr ⟨sigH, hs, hin, hx.trans hxH.symm⟩))
  · -- Another codeword has a digit below the honest one.
    obtain ⟨⟨i, hi⟩, -⟩ := codeword_incomparable ((encode_run key msg sig.counter).symm.trans hx)
      ((encode_run key _ sigH.counter).symm.trans hxH) hcw
    refine .inl (.inr (.inl ⟨x, hx, i, hchains i,
      lt_of_lt_of_le hi (Nat.le_sub_one_of_lt (xH[i]).isLt), fun sigH' hsigH' xH' hxH' => ?_⟩))
    rw [hs] at hsigH'
    cases hsigH'
    rw [hxH] at hxH'
    cases hxH'
    exact hi

/-! ## The whole signature -/

/-- The FORS key bytes fix the FORS key. -/
theorem forsKeyBytes_injective : Function.Injective forsKeyBytes := by
  intro a b h
  have hl := digestsBytes_injective (by simp)
    ((digestsBytes_toList _).trans (h.trans (digestsBytes_toList _).symm))
  have hv := Vector.toList_inj.1 hl
  refine Vector.ext fun kappa hk => Prod.ext ?_ ?_
  · have := congrArg (fun v : Vector Digest (2 * FORS_TREES) => v[2 * kappa]'(by omega)) hv
    simpa using this
  · have := congrArg (fun v : Vector Digest (2 * FORS_TREES) => v[2 * kappa + 1]'(by omega)) hv
    have e : (2 * kappa + 1) / 2 = kappa := by omega
    simpa [Nat.add_mod, e] using this

/-- The tree search of FORS returns only FORS nodes, where the honest values are the FORS ones. -/
theorem honestChildren_of_findTreePreimage {idx : Fin (2 ^ HEIGHT)} {kappa : Fin FORS_TREES}
    {l : Fin (2 ^ FORS_HEIGHT)} {o : TreeOpening} {w : NodePreimage}
    (hw : findTreePreimage f P prf idx kappa l o = some w) :
    honestChildren f P prf w.node = forsChildren f P prf w.node := by
  unfold findTreePreimage at hw
  split at hw
  · split at hw
    · cases hw
      rfl
    · cases hw
  · split at hw
    · cases hw
      rfl
    · cases hw

/-- Every node the FORS search returns is a valid offer against the honest values. -/
theorem findForsPreimage_valid' {idx : Fin (2 ^ HEIGHT)}
    {leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES}
    {openings : Vector TreeOpening FORS_TREES} {w : NodePreimage}
    (hw : findForsPreimage f P prf idx leaves openings = some w) :
    w.Valid f P (honestChildren f P prf) := by
  rw [findForsPreimage] at hw
  obtain ⟨kappa, -, hkappa⟩ := List.exists_of_findSome?_eq_some hw
  exact (NodePreimage.valid_congr (honestChildren_of_findTreePreimage hkappa)).2
    (findTreePreimage_valid hkappa)

variable (f P) in
/-- The digest of a signature's message under a parameter. -/
def sigDigest (m : Message) (σ : Signature) : MessageDigest :=
  (messageDigest (pureHash f) P m σ.randomizer).run

variable (f P) in
/-- The FORS instance a signature's digest picks. -/
def sigIndex (m : Message) (σ : Signature) : Fin (2 ^ HEIGHT) :=
  ⟨digestIndex (sigDigest f P m σ), digestIndex_lt _⟩

variable (f P) in
/-- The FORS key a signature's openings recover. -/
def sigForsKey (m : Message) (σ : Signature) : ForsKey :=
  (forsRecover (pureHash f) P (sigIndex f P m σ).val (digestLeaves (sigDigest f P m σ))
    σ.fors).run

/-- **What an accepted signature contains.**

Take a signature that the honest public key of `P` and `prf` accepts.

Verification finds a bottom root and a middle root on the way up.

From the top layer down, each layer leaves the honest values of its key, or it is honest.

An honest layer signs the honest message, so the layer below leads to its key's honest root.

Below an honest bottom layer, the openings are the honest ones at the digest's leaves.

Otherwise the FORS search finds a valid offer. -/
theorem verifyWith_binding {pk : PublicKey} {m : Message} {σ : Signature}
    (hP : pk.publicParam = P) (hroot : pk.root = (treeRoot (pureHash f) P prf .top 0).run)
    (h : (verifyWith (pureHash f) pk m σ).run = true) :
    ∃ bottomRoot middleRoot,
      (layerRoot (pureHash f) P .bottom (sigIndex f P m σ).val
        (forsKeyBytes (sigForsKey f P m σ)) σ.bottom).run = some bottomRoot ∧
      (layerRoot (pureHash f) P .middle (sigIndex f P m σ).val (packBytes bottomRoot)
        σ.middle).run = some middleRoot ∧
      (LayerFault f P prf .top (sigIndex f P m σ) (packBytes middleRoot) σ.top ∨
        LayerHonest f P prf .top (sigIndex f P m σ) (packBytes middleRoot) σ.top ∧
        (LayerFault f P prf .middle (sigIndex f P m σ) (packBytes bottomRoot) σ.middle ∨
          LayerHonest f P prf .middle (sigIndex f P m σ) (packBytes bottomRoot) σ.middle ∧
          (LayerFault f P prf .bottom (sigIndex f P m σ) (forsKeyBytes (sigForsKey f P m σ))
              σ.bottom ∨
            LayerHonest f P prf .bottom (sigIndex f P m σ) (forsKeyBytes (sigForsKey f P m σ))
              σ.bottom ∧
            (σ.fors = (forsSign (pureHash f) P prf (sigIndex f P m σ).val
                (digestLeaves (sigDigest f P m σ))).run ∨
              ∃ w, findForsPreimage f P prf (sigIndex f P m σ) (digestLeaves (sigDigest f P m σ))
                  σ.fors = some w ∧ w.Valid f P (honestChildren f P prf))))) := by
  rw [verify_iff, signatureRoot, hP] at h
  -- The three layers lead to a bottom root, a middle root and the public key's root.
  change ((layerRoot (pureHash f) P .bottom (sigIndex f P m σ).val
      (forsKeyBytes (sigForsKey f P m σ)) σ.bottom).run.bind fun bottomRoot =>
    (layerRoot (pureHash f) P .middle (sigIndex f P m σ).val (packBytes bottomRoot)
      σ.middle).run.bind fun middleRoot =>
    (layerRoot (pureHash f) P .top (sigIndex f P m σ).val (packBytes middleRoot)
      σ.top).run) = _ at h
  obtain ⟨bottomRoot, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨middleRoot, hm, ht⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨bottomRoot, middleRoot, hb, hm, ?_⟩
  -- The top layer leads to the root of the one top tree.
  rw [hroot, ← OtsKey.ofIndex_top_tree (sigIndex f P m σ).isLt] at ht
  rcases layerRoot_binding ht with htop | htop
  · exact .inl htop
  refine .inr ⟨htop, ?_⟩
  -- The top key signed the middle root of the index, so the middle layer leads to it.
  have hmr : middleRoot = (treeRoot (pureHash f) P prf .middle
      (OtsKey.ofIndex .middle (sigIndex f P m σ).val).tree).run :=
    Base.packBytes_injective (htop.1.trans layerMessage_run)
  rw [hmr] at hm
  rcases layerRoot_binding hm with hmid | hmid
  · exact .inl hmid
  refine .inr ⟨hmid, ?_⟩
  -- The middle key signed the bottom root of the index, so the bottom layer leads to it.
  have hbr : bottomRoot = (treeRoot (pureHash f) P prf .bottom
      (OtsKey.ofIndex .bottom (sigIndex f P m σ).val).tree).run :=
    Base.packBytes_injective (hmid.1.trans layerMessage_run)
  rw [hbr] at hb
  rcases layerRoot_binding hb with hbot | hbot
  · exact .inl hbot
  refine .inr ⟨hbot, ?_⟩
  -- The bottom key signed the FORS key of the index, so the openings recover it.
  have hkey : (forsRecover (pureHash f) P (sigIndex f P m σ).val
      (digestLeaves (sigDigest f P m σ)) σ.fors).run =
        (forsKey (pureHash f) P prf (sigIndex f P m σ).val).run :=
    forsKeyBytes_injective (hbot.1.trans layerMessage_run)
  rcases forsRecover_binding hkey with hfors | ⟨w, hw, -⟩
  · exact .inl hfors
  · exact .inr ⟨w, hw, findForsPreimage_valid' hw⟩

end EthLib.Cryptography.Sphincs.Unforgeability
