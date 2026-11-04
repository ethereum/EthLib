module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.IdealStatement
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Wots

/-!
Proof-side mirrors of the sealed statement definitions.

Rewrite lemmas restate them, so proofs can unfold them without unsealing.

The statement stores the precomputed secret key as runs of its own oracle algorithms.

Each run replays the hash from the cache.

The chain walk, the cache views and the cache replays are first-order forms of those replays.

The proof works with these forms.

The cache-replay evaluation file bridges the two.
-/

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

@[simp]
theorem truncateHash_zero : truncateHash 0 = 0 := by decide

namespace Concrete

namespace CacheView

def digestAt (cache : QueryCache HashSpec) (input : HashInput) : Digest :=
  match cache input with
  | some output => truncateHash output
  | none => 0

def tweakableHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) : Digest :=
  digestAt cache (XmssSecurity.tweakableHashInput parameter domain payload)

def encodingInput (parameter : PublicParameter) (leafIndex : LeafIndex)
    (input : Message × Randomness) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.encoding leafIndex)
    (Concrete.encodingPayload input.1 input.2)

def chainInput (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.chain leafIndex chain position)
    (Concrete.digestBytes value)

def leafInput (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.leaf leafIndex)
    (Concrete.leafPayload endpoints)

def merkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.merkle level node)
    (Concrete.nodePayload left right)

def encodingHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (input : Message × Randomness) : Digest :=
  digestAt cache (encodingInput parameter leafIndex input)

def chainStep (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (chain : ChainIndex) (position : Nat) (value : Digest) : Digest :=
  if hposition : position < chainLength - 1 then
    digestAt cache (chainInput parameter leafIndex chain ⟨position, hposition⟩ value)
  else
    0

def leafHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) : Digest :=
  digestAt cache (leafInput parameter leafIndex endpoints)

def merkleHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) : Digest :=
  digestAt cache (merkleInput parameter level node left right)

/-! The top layer's cache view. -/

def topEncodingInput (parameter : PublicParameter) (key : TopIndex)
    (input : Digest × Randomness) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.topEncoding key)
    (Concrete.topEncodingPayload input.1 input.2)

def topChainInput (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.topChain key chain position)
    (Concrete.digestBytes value)

def topLeafInput (parameter : PublicParameter) (key : TopIndex)
    (endpoints : ChainIndex → Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.topLeaf key) (Concrete.leafPayload endpoints)

def topMerkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : TopNode) (left right : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.topMerkle level node)
    (Concrete.nodePayload left right)

def topEncodingHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : TopIndex) (input : Digest × Randomness) : Digest :=
  digestAt cache (topEncodingInput parameter key input)

def topChainStep (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : TopIndex) (chain : ChainIndex) (position : Nat) (value : Digest) : Digest :=
  if hposition : position < chainLength - 1 then
    digestAt cache (topChainInput parameter key chain ⟨position, hposition⟩ value)
  else
    0

def topLeafHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : TopIndex) (endpoints : ChainIndex → Digest) : Digest :=
  digestAt cache (topLeafInput parameter key endpoints)

def topMerkleHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (node : TopNode) (left right : Digest) : Digest :=
  digestAt cache (topMerkleInput parameter level node left right)

/-- The address of node `j` above `level` in a layer's tree, with `j` reduced modulo its nodes. -/
def nodeDomain : EthLib.Cryptography.Xmss.Layer → MerkleLevel → Nat → HashDomain
  | .bottom, level, j => .merkle level (Concrete.merkleNodeOfNat j)
  | .top, level, j => .topMerkle level (Concrete.topNodeOfNat j)

/-- The number of leaves of a layer's tree, which bounds every node index on it. -/
def layerLeaves : EthLib.Cryptography.Xmss.Layer → Nat
  | .bottom => lifetime
  | .top => topLifetime

/-- The oracle input of node `j` above `level` in a layer's tree, from its two children. -/
def nodeInput (parameter : PublicParameter) (layer : EthLib.Cryptography.Xmss.Layer)
    (level : MerkleLevel) (j : Nat) (left right : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (nodeDomain layer level j)
    (Concrete.nodePayload left right)

/-- The node at position `(level, j)` of a layer's tree, from its two children, read from the cache.

The level is the parent's, from 1 to 16, and the address holds the children's level. -/
def nodeAt (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (layer : EthLib.Cryptography.Xmss.Layer) : Nat → Nat → Digest → Digest → Id Digest
  | level + 1, j, left, right =>
      if hlevel : level < treeHeight then
        pure (digestAt cache (nodeInput parameter layer ⟨level, hlevel⟩ j left right))
      else
        pure 0
  | 0, _, _, _ => pure 0

/-- The oracle input of a bottom node is its Merkle input, at its index modulo the node count. -/
theorem nodeInput_bottom (parameter : PublicParameter) (level : MerkleLevel) (j : Nat)
    (left right : Digest) :
    nodeInput parameter .bottom level j left right =
      merkleInput parameter level (Concrete.merkleNodeOfNat j) left right :=
  rfl

/-- The oracle input of a top node is its Merkle input, at its index modulo the node count. -/
theorem nodeInput_top (parameter : PublicParameter) (level : MerkleLevel) (j : Nat)
    (left right : Digest) :
    nodeInput parameter .top level j left right =
      topMerkleInput parameter level (Concrete.topNodeOfNat j) left right :=
  rfl

/-- A node of the bottom forest, read from the cache, is the hash of its address. -/

theorem nodeAt_bottom (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (j : Nat) (left right : Digest) :
    (nodeAt cache parameter .bottom (level.val + 1) j left right).run =
      merkleHash cache parameter level (Concrete.merkleNodeOfNat j) left right := by
  simp [nodeAt, level.isLt]
  rfl

/-- A node of the top tree, read from the cache, is the hash of its address. -/
theorem nodeAt_top (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (j : Nat) (left right : Digest) :
    (nodeAt cache parameter .top (level.val + 1) j left right).run =
      topMerkleHash cache parameter level (Concrete.topNodeOfNat j) left right := by
  simp [nodeAt, level.isLt]
  rfl

end CacheView

namespace CacheReplay

def oneTimePublicKey (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) : ChainIndex → Digest :=
  fun chain => Wots.walk (CacheView.chainStep cache parameter leafIndex chain) 0
    (chainLength - 1) (secret leafIndex chain)

def leafAt (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) : Digest :=
  CacheView.leafHash cache parameter leafIndex
    (oneTimePublicKey cache parameter secret leafIndex)

def treeNode (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) : Nat → MerkleNode → Digest
  | 0, node => leafAt cache parameter secret node
  | levels + 1, node =>
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0

attribute [irreducible] treeNode

def topOneTimePublicKey (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (key : TopIndex) : ChainIndex → Digest :=
  fun chain => Wots.walk (CacheView.topChainStep cache parameter key chain) 0
    (chainLength - 1) (topSecret key chain)

def topLeafAt (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (key : TopIndex) : Digest :=
  CacheView.topLeafHash cache parameter key (topOneTimePublicKey cache parameter topSecret key)

def topTreeNode (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) : Nat → TopNode → Digest
  | 0, node => topLeafAt cache parameter topSecret node
  | levels + 1, node =>
      if hlevel : levels < treeHeight then
        CacheView.topMerkleHash cache parameter ⟨levels, hlevel⟩ node
          (topTreeNode cache parameter topSecret levels (Concrete.topChildNode node false))
          (topTreeNode cache parameter topSecret levels (Concrete.topChildNode node true))
      else
        0

attribute [irreducible] topTreeNode

end CacheReplay

attribute [local semireducible] treeNode CacheReplay.treeNode sampleSecret signingRandomness

noncomputable local instance : SampleableType (LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (LeafIndex → ChainIndex → Digest)

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

@[simp]
theorem treeNode_zero_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (node : MerkleNode) :
    treeNode (m := m) parameter secret 0 node =
      leafAt (m := m) parameter secret node := rfl

theorem treeNode_succ_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    treeNode (m := m) parameter secret (levels + 1) node = (do
      let left ← treeNode (m := m) parameter secret levels (childNode node false)
      let right ← treeNode (m := m) parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash (m := m) parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0) := rfl

theorem sampleSecret_eq : sampleSecret = $ᵗ (LeafIndex → ChainIndex → Digest) := rfl

theorem signingRandomness_eq : signingRandomness = $ᵗ Randomness := rfl

namespace CacheReplay

@[simp]
theorem treeNode_zero_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (node : MerkleNode) :
    treeNode cache parameter secret 0 node = leafAt cache parameter secret node := by
  with_unfolding_all rfl

theorem treeNode_succ_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (levels : Nat) (node : MerkleNode) :
    treeNode cache parameter secret (levels + 1) node =
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0 := by
  with_unfolding_all rfl

theorem topTreeNode_zero_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (node : TopNode) :
    topTreeNode cache parameter topSecret 0 node = topLeafAt cache parameter topSecret node := by
  with_unfolding_all rfl

theorem topTreeNode_succ_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (levels : Nat) (node : TopNode) :
    topTreeNode cache parameter topSecret (levels + 1) node =
      if hlevel : levels < treeHeight then
        CacheView.topMerkleHash cache parameter ⟨levels, hlevel⟩ node
          (topTreeNode cache parameter topSecret levels (Concrete.topChildNode node false))
          (topTreeNode cache parameter topSecret levels (Concrete.topChildNode node true))
      else
        0 := by
  with_unfolding_all rfl

end CacheReplay

end Concrete

end XmssSecurity
