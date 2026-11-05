module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.HalvedGame
public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel

/-!
# Proofs: the canonical graph of leanSPHINCS

Every tweakable hash that the honest algorithms compute is a node of one fixed graph.

A node is a call site: its address, and for an encoding also its counter.

Its children are the values that its payload is made of, in order.

- A child is a derivation half, such as a chain start or a FORS secret.
- Or a child is another node, such as the previous chain step or the two nodes below.

The point of a node, at values of its children, is half 0 of the input `P | A | payload`.

The payload is the children's values, then the counter of an encoding.

The graph is the one of a key with public parameter `P`, so `P` is part of every point.

Distinct nodes, or one node at distinct children values, have distinct points.

This is the input of VCVio's canonical relabelling.

There, a node's value is a label, drawn once its children are drawn.

The nodes are those of every key with parameter `P`:

- each step of each chain of each one-time key, and the key's leaf;
- each node of each hypertree tree, levels 1 to its height;
- each counter of each one-time key's encoding;
- each leaf of each FORS tree of each instance, and its nodes on levels 1 to 9.

A node's fields are bounded by types that every honest node fits.

So the graph also has nodes that no honest computation reaches.

This changes nothing: their points are distinct from all others.

Their children are again nodes or derivation halves.

The derivation halves are cells of the table: the chain starts, the FORS secrets, the randomizer.

The message digest is not a node: no tweakable hash reads it.

It only picks the index and the FORS leaves.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp

/-! ## Payloads made of digests -/

/-- The bytes of a list of digests, in order. -/
def digestsBytes (vs : List Digest) : ByteArray :=
  ⟨(vs.flatMap Vector.toList).toArray⟩

/-- A list of digests takes 16 bytes per digest. -/
theorem size_digestsBytes (vs : List Digest) : (digestsBytes vs).size = N * vs.length := by
  change (vs.flatMap Vector.toList).toArray.size = _
  rw [List.size_toArray]
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [List.flatMap_cons, List.length_append, ih, Vector.length_toList, List.length_cons]
    simp only [N]
    ring

/-- Two lists of digests of one length with the same bytes are equal. -/
theorem digestsBytes_injective {vs vs' : List Digest} (hl : vs.length = vs'.length)
    (h : digestsBytes vs = digestsBytes vs') : vs = vs' := by
  have h' : vs.flatMap Vector.toList = vs'.flatMap Vector.toList := by
    have := congrArg (fun b : ByteArray => b.data.toList) h
    simpa [digestsBytes] using this
  clear h
  induction vs generalizing vs' with
  | nil => exact (List.length_eq_zero_iff.1 hl.symm).symm
  | cons v vs ih =>
    obtain _ | ⟨v', vs'⟩ := vs'
    · exact absurd hl (by simp)
    · rw [List.flatMap_cons, List.flatMap_cons] at h'
      obtain ⟨hv, hrest⟩ := List.append_inj h' (by simp)
      rw [Vector.toList_inj.1 hv, ih (Nat.succ.inj hl) hrest]

/-- One digest, as a payload. -/
theorem digestsBytes_singleton (v : Digest) : digestsBytes [v] = packBytes v := by
  refine ByteArray.ext (Array.ext' ?_)
  simp [digestsBytes, packBytes]
  rfl

/-- Two digests side by side, as a payload. -/
theorem digestsBytes_pair (l r : Digest) : digestsBytes [l, r] = packBytes l ++ packBytes r := by
  refine ByteArray.ext (Array.ext' ?_)
  simp [digestsBytes, packBytes]
  rfl

/-- A vector of digests, as a payload. -/
theorem digestsBytes_toList {n : Nat} (ds : Vector Digest n) :
    digestsBytes ds.toList = packDigests ds := by
  refine ByteArray.ext (Array.ext' ?_)
  simp [digestsBytes, packDigests, packBytes, Vector.flatten, Array.toList_flatten, List.flatMap]
  rfl

/-! ## The one-time keys of the graph -/

/-- A one-time key of the graph: its layer, its tree and its leaf.

The bottom layer has the most trees, `2^18`, and the top tree the most leaves, `2^10`. -/
structure GraphKey where
  /-- The layer of the key. -/
  layer : Layer
  /-- The tree of the layer that holds the key. -/
  tree : Fin (2 ^ 18)
  /-- The key's leaf in that tree. -/
  leaf : Fin (2 ^ TOP_HEIGHT)
  deriving DecidableEq

/-- The key as the scheme names it. -/
def GraphKey.toOtsKey (key : GraphKey) : OtsKey :=
  ⟨key.layer, key.tree.val, key.leaf.val⟩

/-- A key of the graph fits the 32-bit fields of an address. -/
theorem GraphKey.fits (key : GraphKey) : key.toOtsKey.Fits :=
  ⟨lt_of_lt_of_le key.tree.isLt (by decide), lt_of_lt_of_le key.leaf.isLt (by decide)⟩

/-- A key of the graph is fixed by the key the scheme names. -/
theorem GraphKey.toOtsKey_injective : Function.Injective GraphKey.toOtsKey := by
  rintro ⟨l, t, e⟩ ⟨l', t', e'⟩ h
  simp only [toOtsKey, OtsKey.mk.injEq] at h
  obtain ⟨rfl, ht, he⟩ := h
  rw [Fin.ext ht, Fin.ext he]

/-- The FORS instance under a bottom key: tree `t`, leaf `l` is instance `2^8 t + l`. -/
def GraphKey.instance (key : GraphKey) : Fin (2 ^ HEIGHT) :=
  Fin.ofNat _ (key.tree.val * 2 ^ LOWER_HEIGHT + key.leaf.val)

/-! ## Nodes -/

/-- A node of the graph: one call site of a tweakable hash. -/
inductive Node where
  /-- Step `mu` of chain `i` of a key, from position `mu` to `mu + 1`. -/
  | chain (key : GraphKey) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1))
  /-- The leaf of a key, from the ends of its 64 chains. -/
  | otsLeaf (key : GraphKey)
  /-- Node `j` on level `level + 1` of a tree of a layer, from its two children. -/
  | treeNode (layer : Layer) (tree : Fin (2 ^ 18)) (level : Fin TOP_HEIGHT)
      (j : Fin (2 ^ TOP_HEIGHT))
  /-- The encoding of what a key signs, at one counter. -/
  | encoding (key : GraphKey) (counter : UInt32)
  /-- Leaf `l` of tree `kappa` of a FORS instance, from its secret. -/
  | forsLeaf (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT))
  /-- Node `j` on level `level + 1` of tree `kappa` of a FORS instance, from its two children. -/
  | forsNode (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES) (level : Fin (FORS_HEIGHT - 1))
      (j : Fin (2 ^ FORS_HEIGHT))
  deriving DecidableEq

namespace Node

/-- The address of a node's call. -/
def address : Node → Address
  | .chain key i mu => addrChain key.toOtsKey i mu
  | .otsLeaf key => addrLeaf key.toOtsKey
  | .treeNode layer tree level j => addrNode layer tree.val (Fin.ofNat _ (level.val + 1)) j.val
  | .encoding key _ => addrEncoding key.toOtsKey
  | .forsLeaf idx kappa l => addrForsLeaf idx.val kappa l
  | .forsNode idx kappa level j =>
      addrForsNode idx.val kappa (Fin.ofNat _ (level.val + 1)) (forsIndex j.val)

/-- What a node's payload ends with: the counter of an encoding, nothing otherwise. -/
def suffix : Node → ByteArray
  | .encoding _ counter => packBytes (uintToBytes COUNTER_LEN counter.toNat)
  | _ => .empty

/-- The type of a node's address. -/
def type : Node → AddressType
  | .chain .. => .chain
  | .otsLeaf _ => .leaf
  | .treeNode .. => .node
  | .encoding .. => .encoding
  | .forsLeaf .. => .forsLeaf
  | .forsNode .. => .forsNode

/-- A node's address has the node's type. -/
theorem exists_address_eq (k : Node) :
    ∃ step layer tree hi lo, k.address = encodeAddress k.type.code step layer tree hi lo := by
  cases k <;> exact ⟨_, _, _, _, _, rfl⟩

/-- Nodes at one address have one type. -/
theorem type_eq_of_address_eq {k k' : Node} (h : k.address = k'.address) : k.type = k'.type := by
  obtain ⟨_, _, _, _, _, hk⟩ := k.exists_address_eq
  obtain ⟨_, _, _, _, _, hk'⟩ := k'.exists_address_eq
  rw [hk, hk'] at h
  exact AddressType.code_injective (encodeAddress_inj.mp h).1

/-- A number below `2^n` with `n ≤ 32` fits a 32-bit field. -/
private theorem lt_two_pow_32 {n x : Nat} (hx : x < 2 ^ n) (hn : n ≤ 32) : x < 2 ^ 32 :=
  lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hn)

/-- A node is fixed by its address and its suffix. -/
theorem eq_of_address_eq {k k' : Node} (h : k.address = k'.address) (hs : k.suffix = k'.suffix) :
    k = k' := by
  have ht := type_eq_of_address_eq h
  cases k <;> cases k' <;> simp only [type, reduceCtorEq] at ht <;> simp only [address] at h
  · obtain ⟨hk, hi, hmu⟩ := addrChain_inj (GraphKey.fits _) (GraphKey.fits _) h
    rw [GraphKey.toOtsKey_injective hk, hi, hmu]
  · rw [GraphKey.toOtsKey_injective (addrLeaf_inj (GraphKey.fits _) (GraphKey.fits _) h)]
  · rename_i layer tree level j layer' tree' level' j'
    obtain ⟨hl, ht, hlev, hj⟩ := addrNode_inj (lt_two_pow_32 tree.isLt (by decide))
      (lt_two_pow_32 tree'.isLt (by decide)) (lt_two_pow_32 j.isLt (by decide))
      (lt_two_pow_32 j'.isLt (by decide)) h
    have hlev := congrArg Fin.val hlev
    have := level.isLt
    have := level'.isLt
    simp only [Fin.ofNat, TOP_HEIGHT] at hlev this
    have e : level = level' := Fin.ext (by simp only [TOP_HEIGHT] at *; omega)
    rw [hl, Fin.ext ht, Fin.ext hj, e]
  · rename_i key c key' c'
    rw [GraphKey.toOtsKey_injective (addrEncoding_inj (GraphKey.fits _) (GraphKey.fits _) h)]
    have hc := congrArg bytesToUint (Base.packBytes_injective hs)
    rw [Base.bytesToUint_uintToBytes, Base.bytesToUint_uintToBytes,
      Nat.mod_eq_of_lt (lt_of_lt_of_le c.toNat_lt (by decide)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le c'.toNat_lt (by decide))] at hc
    rw [UInt32.toNat_inj.1 hc]
  · rename_i idx kappa l idx' kappa' l'
    obtain ⟨hi, hk, hl⟩ := addrForsLeaf_inj (lt_two_pow_32 idx.isLt (by decide))
      (lt_two_pow_32 idx'.isLt (by decide)) h
    rw [Fin.ext hi, hk, hl]
  · rename_i idx kappa level j idx' kappa' level' j'
    obtain ⟨hi, hk, hlev, hj⟩ := addrForsNode_inj (lt_two_pow_32 idx.isLt (by decide))
      (lt_two_pow_32 idx'.isLt (by decide)) h
    have hlev := congrArg Fin.val hlev
    have hj := congrArg Fin.val hj
    have := level.isLt
    have := level'.isLt
    have := j.isLt
    have := j'.isLt
    simp only [Fin.val_ofNat, forsIndex, FORS_HEIGHT] at hlev hj this
    have e : level = level' := Fin.ext (by simp only [FORS_HEIGHT] at *; omega)
    have e' : j = j' := Fin.ext (by simp only [FORS_HEIGHT] at *; omega)
    rw [Fin.ext hi, hk, e, e']

/-- The suffix of a node is empty, or the four bytes of a counter. -/
theorem size_suffix (k : Node) :
    k.suffix.size = if k.type = .encoding then COUNTER_LEN else 0 := by
  cases k <;> simp [suffix, type]

end Node

/-! ## Children -/

/-- The derivation half that starts chain `i` of a key.

It is half `i mod 2` of derivation `floor(i / 2)`. -/
def startCell (P : PublicParam) (key : GraphKey) (i : Fin V) : DerivationInput × Fin 2 :=
  (⟨(P, addrPrf key.toOtsKey ⟨i.val / 2, by have := i.isLt; simp only [V] at *; omega⟩, .empty),
    isDerivationAddress_addrPrf _ _⟩, ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩)

/-- The derivation half that is the secret of FORS leaf `l`.

It is half `l mod 2` of derivation `floor(l / 2)`. -/
def secretCell (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) : DerivationInput × Fin 2 :=
  (⟨(P, addrForsPrf idx.val kappa
      ⟨l.val / 2, by have := l.isLt; simp only [FORS_HEIGHT] at *; omega⟩, .empty),
    isDerivationAddress_addrForsPrf _ _ _⟩, ⟨l.val % 2, Nat.mod_lt _ (by decide)⟩)

/-- A cell of the graph: a derivation half or a node. -/
abbrev Cell := (DerivationInput × Fin 2) ⊕ Node

/-- What a key signs, as cells.

- A bottom key signs the FORS key of its instance: the two level-9 nodes of each tree.
- A middle key signs the root of the bottom tree below it.
- The top key signs the root of the middle tree below it. -/
def GraphKey.message (key : GraphKey) : List Cell :=
  match key.layer with
  | .bottom => List.ofFn fun e : Fin (2 * FORS_TREES) =>
      .inr (.forsNode key.instance ⟨e.val / 2, by have := e.isLt; omega⟩
        ⟨FORS_HEIGHT - 2, by decide⟩ ⟨e.val % 2,
          lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)⟩)
  | .middle => [.inr (.treeNode .bottom
      (Fin.ofNat _ (key.tree.val * 2 ^ LOWER_HEIGHT + key.leaf.val))
      ⟨LOWER_HEIGHT - 1, by decide⟩ 0)]
  | .top => [.inr (.treeNode .middle (Fin.ofNat _ key.leaf.val) ⟨LOWER_HEIGHT - 1, by decide⟩ 0)]

/-- The children of a node, in the order its payload lists their values. -/
def Node.children (P : PublicParam) : Node → List Cell
  | .chain key i mu =>
      if mu.val = 0 then [.inl (startCell P key i)]
      else [.inr (.chain key i ⟨mu.val - 1, by omega⟩)]
  | .otsLeaf key => List.ofFn fun i : Fin V => .inr (.chain key i ⟨CHAIN_LENGTH - 2, by decide⟩)
  | .treeNode layer tree level j =>
      if level.val = 0 then
        [.inr (.otsLeaf ⟨layer, tree, Fin.ofNat _ (2 * j.val)⟩),
          .inr (.otsLeaf ⟨layer, tree, Fin.ofNat _ (2 * j.val + 1)⟩)]
      else
        [.inr (.treeNode layer tree ⟨level.val - 1, by omega⟩ (Fin.ofNat _ (2 * j.val))),
          .inr (.treeNode layer tree ⟨level.val - 1, by omega⟩ (Fin.ofNat _ (2 * j.val + 1)))]
  | .encoding key _ => key.message
  | .forsLeaf idx kappa l => [.inl (secretCell P idx kappa l)]
  | .forsNode idx kappa level j =>
      if level.val = 0 then
        [.inr (.forsLeaf idx kappa (Fin.ofNat _ (2 * j.val))),
          .inr (.forsLeaf idx kappa (Fin.ofNat _ (2 * j.val + 1)))]
      else
        [.inr (.forsNode idx kappa ⟨level.val - 1, by omega⟩ (Fin.ofNat _ (2 * j.val))),
          .inr (.forsNode idx kappa ⟨level.val - 1, by omega⟩ (Fin.ofNat _ (2 * j.val + 1)))]

/-- The children of an encoding do not depend on its counter. -/
theorem Node.children_encoding (P : PublicParam) (key : GraphKey) (c c' : UInt32) :
    (Node.encoding key c).children P = (Node.encoding key c').children P :=
  rfl

/-- Nodes at one address have as many children. -/
theorem Node.length_children_eq_of_address_eq (P : PublicParam) {k k' : Node}
    (h : k.address = k'.address) : (k.children P).length = (k'.children P).length := by
  have ht := Node.type_eq_of_address_eq h
  cases k <;> cases k' <;> simp only [Node.type, reduceCtorEq] at ht
  case encoding.encoding key c key' c' =>
    simp only [Node.address] at h
    rw [GraphKey.toOtsKey_injective (addrEncoding_inj (GraphKey.fits _) (GraphKey.fits _) h),
      Node.children_encoding P key' c c']
  all_goals rw [Node.eq_of_address_eq h rfl]

/-! ## Points -/

/-- The bytes of a node's point at children values: `P | A | values | suffix`. -/
def pointBytes (P : PublicParam) (k : Node) (vs : List Digest) : List UInt8 :=
  (thInput P k.address (digestsBytes vs ++ k.suffix)).data.toList

/-- Two equal points, at children values of the right lengths, are of one node.

They are also at the same children values. -/
theorem pointBytes_inj (P : PublicParam) {k k' : Node} {vs vs' : List Digest}
    (hl : vs.length = (k.children P).length) (hl' : vs'.length = (k'.children P).length)
    (h : pointBytes P k vs = pointBytes P k' vs') : k = k' ∧ vs = vs' := by
  obtain ⟨-, hA, hpay⟩ := thInput_inj (byteArray_eq_of_toList_eq h)
  have hlen : vs.length = vs'.length := by
    rw [hl, hl', Node.length_children_eq_of_address_eq P hA]
  obtain ⟨hvs, hs⟩ := Xmss.byteArray_append_inj hpay
    (by rw [size_digestsBytes, size_digestsBytes, hlen])
  exact ⟨Node.eq_of_address_eq hA hs, digestsBytes_injective hlen hvs⟩

/-- The canonical graph of leanSPHINCS with public parameter `P`.

Its points are half 0 of the inputs of the tweakable hash.

So their answers are the 16-byte values that the scheme keeps. -/
def graph (P : PublicParam) :
    CanonicalGraph (List UInt8 × Fin 2 →ₒ Digest) (DerivationInput × Fin 2) Node Digest where
  ch := Node.children P
  pt k vs := (pointBytes P k vs, 0)
  range_eq _ _ := rfl
  pt_inj hl hl' h := pointBytes_inj P hl hl' (Prod.ext_iff.1 h).1

/-! ## Node keys

A public point is at the key of a node when it is half 0 of an input `P | A | payload | suffix`.

Here `A` and the suffix are the node's, and the payload is any.

A second preimage of a node's value is such a point.

So the target collisions that VCVio charges are at these keys. -/

/-- An input at a node's address that ends with its suffix fixes the node. -/
theorem Node.eq_of_thInput_eq {P P' : PublicParam} {k k' : Node} {payload payload' : ByteArray}
    (h : thInput P k.address (payload ++ k.suffix) =
      thInput P' k'.address (payload' ++ k'.suffix)) : k = k' := by
  obtain ⟨-, hA, hpay⟩ := thInput_inj h
  have hs : k.suffix.size = k'.suffix.size := by
    rw [Node.size_suffix, Node.size_suffix, Node.type_eq_of_address_eq hA]
  have hp : payload.size = payload'.size := by
    have := congrArg ByteArray.size hpay
    rw [ByteArray.size_append, ByteArray.size_append, hs] at this
    omega
  exact Node.eq_of_address_eq hA (Xmss.byteArray_append_inj hpay hp).2

open Classical in
/-- The node at whose key a public point is, if any. -/
noncomputable def nodeAt (P : PublicParam) (t : List UInt8 × Fin 2) : Option Node :=
  if h : ∃ k : Node, ∃ payload : ByteArray,
      t = ((thInput P k.address (payload ++ k.suffix)).data.toList, 0) then
    some h.choose
  else none

/-- A point of the input `P | A | payload | suffix` of a node is at that node's key. -/
theorem nodeAt_thInput (P : PublicParam) (k : Node) (payload : ByteArray) :
    nodeAt P ((thInput P k.address (payload ++ k.suffix)).data.toList, 0) = some k := by
  have hex : ∃ k' : Node, ∃ payload' : ByteArray,
      (((thInput P k.address (payload ++ k.suffix)).data.toList, 0) : List UInt8 × Fin 2) =
        ((thInput P k'.address (payload' ++ k'.suffix)).data.toList, 0) := ⟨k, payload, rfl⟩
  rw [nodeAt, dite_eq_left hex]
  obtain ⟨payload', h⟩ := hex.choose_spec
  exact congrArg some (Node.eq_of_thInput_eq (byteArray_eq_of_toList_eq (Prod.ext_iff.1 h).1)).symm

/-- The node keys of the graph. -/
noncomputable def nodeKeys (P : PublicParam) : (graph P).NodeKeys where
  node := nodeAt P
  node_pt _ := nodeAt_thInput P _ _
  range_eq _ := rfl

/-- A point at the key of a node has that node's address and suffix. -/
theorem exists_thInput_of_nodeAt_eq_some {P : PublicParam} {t : List UInt8 × Fin 2} {k : Node}
    (h : nodeAt P t = some k) :
    ∃ payload : ByteArray, t = ((thInput P k.address (payload ++ k.suffix)).data.toList, 0) := by
  unfold nodeAt at h
  split at h
  · rename_i hex
    obtain rfl := Option.some_inj.1 h
    exact hex.choose_spec
  · exact absurd h (by simp)

/-! ## The honest calls are at the points of the graph

Each tweakable hash of the honest algorithms, at parameter `P`, is at the point of one node.

The node's children values are the values that its payload is made of. -/

/-- A chain step is at the point of its node, at the value it steps from. -/
theorem pointBytes_chain (P : PublicParam) (key : GraphKey) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (v : Digest) :
    pointBytes P (.chain key i mu) [v] =
      (thInput P (addrChain key.toOtsKey i mu) (packBytes v)).data.toList := by
  simp only [pointBytes, Node.address, Node.suffix, digestsBytes_singleton, ByteArray.append_empty]

/-- A key's leaf is at the point of its node, at the ends of its chains. -/
theorem pointBytes_otsLeaf (P : PublicParam) (key : GraphKey) (ends : Vector Digest V) :
    pointBytes P (.otsLeaf key) ends.toList =
      (thInput P (addrLeaf key.toOtsKey) (packDigests ends)).data.toList := by
  simp only [pointBytes, Node.address, Node.suffix, digestsBytes_toList, ByteArray.append_empty]

/-- A tree node is at the point of its node, at its two children. -/
theorem pointBytes_treeNode (P : PublicParam) (layer : Layer) (tree : Fin (2 ^ 18))
    (level : Fin TOP_HEIGHT) (j : Fin (2 ^ TOP_HEIGHT)) (l r : Digest) :
    pointBytes P (.treeNode layer tree level j) [l, r] =
      (thInput P (addrNode layer tree.val (Fin.ofNat _ (level.val + 1)) j.val)
        (packBytes l ++ packBytes r)).data.toList := by
  simp only [pointBytes, Node.address, Node.suffix, digestsBytes_pair, ByteArray.append_empty]

/-- An encoding is at the point of its node, at the digests of the message it encodes. -/
theorem pointBytes_encoding (P : PublicParam) (key : GraphKey) (counter : UInt32)
    (ms : List Digest) :
    pointBytes P (.encoding key counter) ms =
      (thInput P (addrEncoding key.toOtsKey)
        (digestsBytes ms ++ packBytes (uintToBytes COUNTER_LEN counter.toNat))).data.toList :=
  rfl

/-- A FORS leaf is at the point of its node, at its secret. -/
theorem pointBytes_forsLeaf (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) (secret : Digest) :
    pointBytes P (.forsLeaf idx kappa l) [secret] =
      (thInput P (addrForsLeaf idx.val kappa l) (packBytes secret)).data.toList := by
  simp only [pointBytes, Node.address, Node.suffix, digestsBytes_singleton, ByteArray.append_empty]

/-- A FORS node is at the point of its node, at its two children. -/
theorem pointBytes_forsNode (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (level : Fin (FORS_HEIGHT - 1)) (j : Fin (2 ^ FORS_HEIGHT)) (l r : Digest) :
    pointBytes P (.forsNode idx kappa level j) [l, r] =
      (thInput P (addrForsNode idx.val kappa (Fin.ofNat _ (level.val + 1)) (forsIndex j.val))
        (packBytes l ++ packBytes r)).data.toList := by
  simp only [pointBytes, Node.address, Node.suffix, digestsBytes_pair, ByteArray.append_empty]

/-- In the game of halves, a tweakable hash asks both halves of its input and keeps half 0. -/
theorem simulateQ_halves_th (pp : PublicParam) (A : Address) (payload : ByteArray) :
    simulateQ halves (th (liftH DerivationInput) pp A payload) = (do
      let u ← HalvedWorld.query (.inl (.inr ((thInput pp A payload).data.toList, 0)))
      let _ ← HalvedWorld.query (.inl (.inr ((thInput pp A payload).data.toList, 1)))
      return u) := by
  change simulateQ halves (liftH DerivationInput (thInput pp A payload) >>= fun x =>
    pure (halfOf 0 x)) = _
  rw [simulateQ_bind, simulateQ_halves_liftH]
  simp only [bind_assoc, pure_bind, simulateQ_pure, halfOf_zero_hashHalves_symm]

end EthLib.Cryptography.Sphincs.Unforgeability
