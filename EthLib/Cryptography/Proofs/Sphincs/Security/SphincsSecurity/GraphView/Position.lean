module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Domains

/-!
# Structural positions and their addresses

A position is a hash of the honest key: a chain step, a one-time leaf or a tree node.

The positions cover every tree of every layer, and pruning selects the ones that are computed.

In FORS, the positions are the leaves and the nodes of every tree of every instance.

The FORS public key of an instance is a position too, and it reads the root of each of its trees.

Signing and verification both compute that key, the hash `T_k` of the roots.

Distinct positions give distinct hash inputs, whatever their payloads.
-/

@[expose] public section

namespace SphincsSecurity

variable [Params]

/-- The level and the node index of a tree node each fit in a 32-bit address word. -/
def HashDomain.InRange : HashDomain → Prop
  | .node _ _ level nodeIdx => level < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
  | _ => True

namespace Security

/-- A table of FORS secrets, by instance, tree and leaf. -/
abbrev ForsSecrets := Index → FTree → FLeaf → Digest

omit [Params] in
private theorem fin_of_ofNat_eq {w n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ w)
    (h : BitVec.ofNat w a.val = BitVec.ofNat w b.val) : a = b :=
  Fin.ext (ofNat_inj_of_lt (a.isLt.trans_le hn) (b.isLt.trans_le hn) h)

/-- Two in-range hash domains with the same address fields are equal. -/
theorem hashFields_injective {left right : HashDomain} (hl : HashDomain.InRange left)
    (hr : HashDomain.InRange right) (heq : hashDomainFields left = hashDomainFields right) :
    left = right := by
  have hlayer := congrArg TweakFields.layer heq
  have htree := congrArg TweakFields.tree heq
  have htag := congrArg TweakFields.tag heq
  have hkey := congrArg TweakFields.keyPair heq
  have hheight := congrArg TweakFields.height heq
  have hindex := congrArg TweakFields.index heq
  have h32 : (16 : Nat) < 2 ^ 32 := by norm_num
  cases left <;> cases right
  all_goals try { simp [hashDomainFields, treeFields, forsFields, tweakFields] at htag; done }
  · rename_i lay tree leaf chain step lay' tree' leaf' chain' step'
    have he1 : lay = lay' := layerByte_ofNat_injective hlayer
    have he2 : tree = tree' := Fin.ext (ofNat_inj_of_lt (w := 96) (tree_lt_two_pow_96 _)
        (tree_lt_two_pow_96 _) htree)
    have he3 : leaf = leaf' := Fin.ext (ofNat_inj_of_lt (w := 32) (leaf_lt_two_pow_32 _)
        (leaf_lt_two_pow_32 _) hkey)
    have he4 := fin_of_ofNat_eq (w := 32) (by decide) hheight
    have he5 := fin_of_ofNat_eq (w := 32) (by decide) hindex
    cases he1; cases he2; cases he3; cases he4; cases he5; rfl
  · rename_i lay tree leaf lay' tree' leaf'
    have he1 : lay = lay' := layerByte_ofNat_injective hlayer
    have he2 : tree = tree' := Fin.ext (ofNat_inj_of_lt (w := 96) (tree_lt_two_pow_96 _)
        (tree_lt_two_pow_96 _) htree)
    have he3 : leaf = leaf' := Fin.ext (ofNat_inj_of_lt (w := 32) (leaf_lt_two_pow_32 _)
        (leaf_lt_two_pow_32 _) hkey)
    cases he1; cases he2; cases he3; rfl
  · rename_i lay tree level nodeIdx lay' tree' level' nodeIdx'
    have he1 : lay = lay' := layerByte_ofNat_injective hlayer
    have he2 : tree = tree' := Fin.ext (ofNat_inj_of_lt (w := 96) (tree_lt_two_pow_96 _)
        (tree_lt_two_pow_96 _) htree)
    have he3 := ofNat_inj_of_lt (w := 32) hl.1 hr.1 hheight
    have he4 := ofNat_inj_of_lt (w := 32) hl.2 hr.2 hindex
    cases he1; cases he2; cases he3; cases he4; rfl
  · rename_i lay tree leaf lay' tree' leaf'
    have he1 : lay = lay' := layerByte_ofNat_injective hlayer
    have he2 : tree = tree' := Fin.ext (ofNat_inj_of_lt (w := 96) (tree_lt_two_pow_96 _)
        (tree_lt_two_pow_96 _) htree)
    have he3 : leaf = leaf' := Fin.ext (ofNat_inj_of_lt (w := 32) (leaf_lt_two_pow_32 _)
        (leaf_lt_two_pow_32 _) hkey)
    cases he1; cases he2; cases he3; rfl
  · rename_i index κ leaf index' κ' leaf'
    have hidx : index = index' := forsAddress_index_injective htree hkey
    have hp := ofNat_inj_of_lt (w := 32) (forsTreeIndex_lt κ 0 leaf.isLt)
      (forsTreeIndex_lt κ' 0 leaf'.isLt) hindex
    obtain ⟨hκ, hleaf⟩ := forsTreeIndex_injective leaf.isLt leaf'.isLt hp
    subst hidx hκ
    cases Fin.ext hleaf; rfl
  · rename_i index κ leaf index' κ' level' node'
    have := ofNat_inj_of_lt (w := 32) (a := 0) (by norm_num) ((level_lt_16 level').trans h32)
      hheight
    omega
  · rename_i index κ level node index' κ' leaf'
    have := ofNat_inj_of_lt (w := 32) (b := 0) ((level_lt_16 level).trans h32) (by norm_num) hheight
    omega
  · rename_i index κ level node index' κ' level' node'
    have hidx : index = index' := forsAddress_index_injective htree hkey
    have hlv : level = level' := Fin.ext (by
      have := ofNat_inj_of_lt (w := 32) ((level_lt_16 level).trans h32)
        ((level_lt_16 level').trans h32) hheight
      omega)
    subst hidx hlv
    have hp := ofNat_inj_of_lt (w := 32) (forsTreeIndex_lt κ (level.val + 1) node.isLt)
      (forsTreeIndex_lt κ' (level.val + 1) node'.isLt) hindex
    obtain ⟨hκ, hn⟩ := forsTreeIndex_injective node.isLt node'.isLt hp
    subst hκ
    cases Fin.ext hn; rfl
  · rename_i index index'
    cases forsAddress_index_injective htree hkey; rfl

/--
A structural position of the honest key.

A tree node that stores level `j` is the node at level `j + 1`, and the leaves are at level 0.

The same holds in a FORS tree.

The last kind of position is the FORS public key of an instance, the hash `T_k` of its roots.
-/
inductive Position where
  | chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
  | fleaf (index : Index) (κ : FTree) (leaf : FLeaf)
  | fnode (index : Index) (κ : FTree) (level : FLevel) (node : FLeaf)
  | froots (index : Index)
  deriving DecidableEq

instance positionFintype : Fintype Position where
  elems :=
    (Finset.univ.image fun x : Layer × TreeIndex × LeafIndex × ChainIndex × ChainStep =>
      Position.chain x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∪
    (Finset.univ.image fun x : Layer × TreeIndex × LeafIndex => Position.leaf x.1 x.2.1 x.2.2) ∪
    (Finset.univ.image fun x : Layer × TreeIndex × Fin maxLayerHeight × LeafIndex =>
      Position.node x.1 x.2.1 x.2.2.1 x.2.2.2) ∪
    (Finset.univ.image fun x : Index × FTree × FLeaf => Position.fleaf x.1 x.2.1 x.2.2) ∪
    (Finset.univ.image fun x : Index × FTree × FLevel × FLeaf =>
      Position.fnode x.1 x.2.1 x.2.2.1 x.2.2.2) ∪
    (Finset.univ.image Position.froots)
  complete := by
    intro p
    cases p <;> simp

namespace Position

/-- The hash domain a position is hashed at. -/
def domain : Position → HashDomain
  | .chain lay tree leafIdx chainIdx step => HashDomain.chain lay tree leafIdx chainIdx step
  | .leaf lay tree leafIdx => HashDomain.leaf lay tree leafIdx
  | .node lay tree level nodeIdx => HashDomain.node lay tree (level.val + 1) nodeIdx.val
  | .fleaf index κ lf => HashDomain.forsLeaf index κ lf
  | .fnode index κ level nd => HashDomain.forsNode index κ level nd
  | .froots index => HashDomain.forsRoots index

theorem domain_inRange (p : Position) : HashDomain.InRange p.domain := by
  cases p with
  | node lay tree level nodeIdx =>
      have hlevel := level.isLt
      have hmax := maxLayerHeight_le
      have hh := totalHeight_le_28
      show level.val + 1 < 2 ^ 32 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, leaf_lt_two_pow_32 nodeIdx⟩
  | _ => exact (trivial : True)

theorem domain_injective {p q : Position} (h : p.domain = q.domain) : p = q := by
  cases p <;> cases q <;> simp only [domain] at h <;> simp_all [Fin.ext_iff]

/-- The last chain step, whose answer is the end of the chain. -/
def lastChainStep : ChainStep :=
  ⟨chainLength - 2, by have := (show 2 ≤ chainLength by decide); omega⟩

/-- The stored level `a - 1` of the root of a FORS tree, which is at level `a`. -/
def rootLevel : FLevel := ⟨forsHeight - 1, by have := Params.forsHeight_ge; omega⟩

/-- The positions whose values make up the payload at a position. -/
def children : Position → List Position
  | .chain lay tree leafIdx chainIdx step =>
      if h : 0 < step.val then [.chain lay tree leafIdx chainIdx ⟨step.val - 1, by omega⟩] else []
  | .leaf lay tree leafIdx =>
      List.ofFn fun chainIdx : ChainIndex => .chain lay tree leafIdx chainIdx lastChainStep
  | .node lay tree level nodeIdx =>
      if hidx : 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight then
        if hlevel : 0 < level.val then
          [.node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val, by omega⟩,
            .node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩]
        else
          [.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩,
            .leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩]
      else []
  | .fleaf _ _ _ => []
  | .fnode index κ level nd =>
      if hidx : 2 * nd.val + 1 < 2 ^ forsHeight then
        if hlevel : 0 < level.val then
          [.fnode index κ ⟨level.val - 1, by omega⟩ ⟨2 * nd.val, by omega⟩,
            .fnode index κ ⟨level.val - 1, by omega⟩ ⟨2 * nd.val + 1, by omega⟩]
        else
          [.fleaf index κ ⟨2 * nd.val, by omega⟩, .fleaf index κ ⟨2 * nd.val + 1, by omega⟩]
      else []
  | .froots index => List.ofFn fun κ : FTree => .fnode index κ rootLevel ⟨0, Nat.two_pow_pos _⟩

/-! ### Depth and separated addresses -/

/-- A depth that strictly decreases from a position to each of its children. -/
def depth : Position → Nat
  | .chain _ _ _ _ step => step.val
  | .leaf _ _ _ => chainLength
  | .node _ _ level _ => chainLength + 1 + level.val
  | .fleaf _ _ _ => 0
  | .fnode _ _ level _ => 1 + level.val
  | .froots _ => 1 + forsHeight

theorem depth_lt_of_mem_children {c d : Position} (hmem : c ∈ d.children) :
    c.depth < d.depth := by
  cases d with
  | chain lay tree leafIdx chainIdx step =>
      rw [children] at hmem
      split at hmem
      · rw [List.mem_singleton] at hmem
        subst hmem
        simp only [depth]
        omega
      · simp at hmem
  | leaf =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨chainIdx, hmem⟩ := hmem
      subst hmem
      have := (show 2 ≤ chainLength by decide)
      simp only [depth, lastChainStep]
      omega
  | node lay tree level nodeIdx =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | fleaf => simp [children] at hmem
  | fnode index κ level nd =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | froots index =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨κ, rfl⟩ := hmem
      have := Params.forsHeight_ge
      simp only [depth, rootLevel]
      omega

theorem fields_injective {left right : Position}
    (h : hashDomainFields left.domain = hashDomainFields right.domain) : left = right :=
  domain_injective (hashFields_injective left.domain_inRange right.domain_inRange h)

theorem input_separated (parameter : PublicParameter) {left right : Position}
    (hne : left ≠ right) (leftPayload rightPayload : HashInput) :
    tweakableHashInput parameter left.domain leftPayload ≠
      tweakableHashInput parameter right.domain rightPayload := by
  intro h
  exact hne (fields_injective (tweakableInput_injective h).1)

end Position

end Security
end SphincsSecurity
