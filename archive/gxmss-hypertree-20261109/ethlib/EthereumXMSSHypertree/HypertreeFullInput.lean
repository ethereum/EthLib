/- Authors: Matthias Meijers -/

module
public import EthereumXMSSHypertree.HypertreeFrames

/-!
# Full-input injectivity of the concrete global hash

Legal physical calls retain their complete coordinates. Every other call has the injective
reserved virtual frame, whose type code separates it from all physical calls.
-/

public section

namespace EthereumXMSSHypertree.ConcreteHypertree

open EthLib.Base EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants

private theorem node_coordinate_inj (first second : GXMSS.Hypertree.TreePosition shape)
    (level : Fin 17) (node otherNode : Fin (2 ^ 16))
    (hnode : ReachedNode level node) (hother : ReachedNode level otherNode)
    (hlayer : sourceLayer first = sourceLayer second)
    (hindex : UInt32.ofNat (nodeGlobalIndex first level.val node.val) =
      UInt32.ofNat (nodeGlobalIndex second level.val otherNode.val)) :
    first = second ∧ node = otherNode := by
  have hlevel : level.val ≤ 16 := by have := level.isLt; omega
  have hg := congrArg UInt32.toNat hindex
  rw [nodeGlobalIndex_no_wrap first _ _ hlevel hnode.2,
    nodeGlobalIndex_no_wrap second _ _ hlevel hother.2] at hg
  have hd := congrArg (fun n => n / 2 ^ (16 - level.val)) hg
  have hp := Nat.two_pow_pos (16 - level.val)
  have divide (tree : GXMSS.Hypertree.TreePosition shape) (localNode : Nat)
      (hb : localNode < 2 ^ (16 - level.val)) :
      nodeGlobalIndex tree level.val localNode / 2 ^ (16 - level.val) = tree.2.val := by
    unfold nodeGlobalIndex
    rw [Nat.add_comm, Nat.mul_comm tree.2.val, Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt hb, Nat.zero_add]
  rw [divide first node.val hnode.2, divide second otherNode.val hother.2] at hd
  have hn : node.val = otherNode.val := by
    unfold nodeGlobalIndex at hg
    rw [hd] at hg
    omega
  exact ⟨GXMSS.Hypertree.treePosition_ext (layerEquiv.symm.injective hlayer) hd, Fin.ext hn⟩

private inductive PhysicalCall where
  | chain (position : GXMSS.Hypertree.ChainPosition shape) (value : Digest)
  | leaf (tree : GXMSS.Hypertree.TreePosition shape) (node : Fin (2 ^ 16))
      (values : Fin 58 → Digest)
  | node (tree : GXMSS.Hypertree.TreePosition shape) (level : Fin 17)
      (index : Fin (2 ^ 16)) (reached : ReachedNode level index) (left right : Digest)

private def physicalBytes (pp : PublicParam) : PhysicalCall → ByteArray
  | .chain c value => chainInput pp (sourceLayer c.1.1) (sourceKey c.1) c.2.1 c.2.2 value
  | .leaf tree node values =>
      FullInputs.leafInput pp (sourceLayer tree) (sourceKey (tree, node)) (Vector.ofFn values)
  | .node tree level index _ left right =>
      FullInputs.nodeInput pp (sourceLayer tree) level
        (UInt32.ofNat (nodeGlobalIndex tree level.val index.val)) left right

private theorem physicalBytes_inj {pp pp' : PublicParam} {first second : PhysicalCall}
    (h : physicalBytes pp first = physicalBytes pp' second) : pp = pp' ∧ first = second := by
  cases first <;> cases second
  case chain.chain first value second other =>
    obtain ⟨hpp, hl, hk, hi, hmu, hv⟩ := chainInput_inj h
    have hp := sourceKey_injective hl hk
    have hc : first = second := Prod.ext hp (Prod.ext hi hmu)
    exact ⟨hpp, congrArg₂ PhysicalCall.chain hc hv⟩
  case leaf.leaf tree node values otherTree otherNode otherValues =>
    obtain ⟨hpp, hl, hk, hv⟩ := FullInputs.leafInput_inj h
    have hp := sourceKey_injective hl hk
    have hvalues : values = otherValues := by
      funext i
      simpa using congrArg (fun vs : Vector Digest 58 => vs[i]) hv
    exact ⟨hpp, by cases hp; cases hvalues; rfl⟩
  case node.node tree level node reached left right otherTree otherLevel otherNode otherReached
      otherLeft otherRight =>
    obtain ⟨hpp, hl, hz, hj, hleft, hright⟩ := FullInputs.nodeInput_inj h
    subst otherLevel
    obtain ⟨htree, hnode⟩ := node_coordinate_inj tree otherTree level node otherNode
      reached otherReached hl hj
    exact ⟨hpp, by cases htree; cases hnode; cases hleft; cases hright; rfl⟩
  all_goals
    have ha := (thInput_inj h).2.1
    have hc := (encodeAddress_inj.mp ha).1
    norm_num [AddressType.code] at hc

private theorem virtual_ne_physical (pp pp' : PublicParam) (tweak : Tweak) (input : Input)
    (call : PhysicalCall) : virtualInput pp tweak input ≠ physicalBytes pp' call := by
  cases call with
  | chain c value => exact virtualInput_ne_source pp pp' tweak input .chain _ _ _ _
  | leaf tree node values => exact virtualInput_ne_source pp pp' tweak input .leaf _ _ _ _
  | node tree level node reached left right =>
    exact virtualInput_ne_source pp pp' tweak input .node _ _ _ _

private inductive NormalCall where
  | physical (pp : PublicParam) (call : PhysicalCall)
  | virtual (pp : PublicParam) (tweak : Tweak) (input : Input)

private def normalBytes : NormalCall → ByteArray
  | .physical pp call => physicalBytes pp call
  | .virtual pp tweak input => virtualInput pp tweak input

private theorem normalBytes_injective : Function.Injective normalBytes := by
  intro first second h
  cases first with
  | physical pp first =>
    cases second with
    | physical pp' second =>
      obtain ⟨hpp, hc⟩ := physicalBytes_inj h
      cases hpp; cases hc; rfl
    | virtual pp' tweak input =>
      exact False.elim (virtual_ne_physical pp' pp tweak input first h.symm)
  | virtual pp tweak input =>
    cases second with
    | physical pp' call => exact False.elim (virtual_ne_physical pp pp' tweak input call h)
    | virtual pp' tweak' input' =>
      have he : (pp, tweak, input) = (pp', tweak', input') := virtualInput_injective h
      cases he; rfl

private def normalize (pp : PublicParam) (tweak : Tweak) (input : Input) : NormalCall :=
  match tweak, input with
  | .inl c, .digest value => .physical pp (.chain c value)
  | .inr (tree, level, node), .ends values =>
    if level.val = 0 then .physical pp (.leaf tree node values) else .virtual pp tweak input
  | .inr (tree, level, node), .pair left right =>
    if h : ReachedNode level node then .physical pp (.node tree level node h left right)
    else .virtual pp tweak input
  | _, _ => .virtual pp tweak input

private def restore : NormalCall → PublicParam × Tweak × Input
  | .physical pp (.chain c value) => (pp, .inl c, .digest value)
  | .physical pp (.leaf tree node values) => (pp, .inr (tree, 0, node), .ends values)
  | .physical pp (.node tree level node _ left right) =>
      (pp, .inr (tree, level, node), .pair left right)
  | .virtual pp tweak input => (pp, tweak, input)

private theorem restore_normalize (pp : PublicParam) (tweak : Tweak) (input : Input) :
    restore (normalize pp tweak input) = (pp, tweak, input) := by
  cases tweak with
  | inl c => cases input <;> rfl
  | inr t =>
    obtain ⟨tree, level, node⟩ := t
    cases input with
    | digest value => rfl
    | pair left right =>
      by_cases h : ReachedNode level node <;> simp [normalize, h, restore]
    | ends values =>
      by_cases h : level.val = 0
      · have hz : level = 0 := Fin.ext h
        simp [normalize, restore, hz]
      · simp [normalize, h, restore]

private theorem normalBytes_normalize (pp : PublicParam) (tweak : Tweak) (input : Input) :
    normalBytes (normalize pp tweak input) = hashInput pp tweak input := by
  cases tweak with
  | inl c => cases input <;> rfl
  | inr t =>
    obtain ⟨tree, level, node⟩ := t
    cases input with
    | digest value => rfl
    | pair left right =>
      by_cases h : ReachedNode level node <;>
        simp [normalize, h, normalBytes, physicalBytes, hashInput]
    | ends values =>
      by_cases h : level.val = 0 <;> simp [normalize, h, normalBytes, physicalBytes, hashInput]

/-- Every abstract call is recoverable from its complete concrete hash input bytes. -/
theorem fullInput_injective : FullInputInjective := by
  intro first second h
  have hn : normalBytes (normalize first.1 first.2.1 first.2.2) =
      normalBytes (normalize second.1 second.2.1 second.2.2) := by
    simpa only [normalBytes_normalize] using h
  have he := congrArg restore (normalBytes_injective hn)
  simpa only [restore_normalize] using he

/-- Forest calls are disjoint from all other source purposes, including encoding and PRF calls. -/
theorem hashInput_ne_otherPurpose (pp pp' : PublicParam) (tweak : Tweak) (input : Input)
    (kind : AddressType) (hchain : kind ≠ .chain) (hleaf : kind ≠ .leaf) (hnode : kind ≠ .node)
    (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) (payload : ByteArray) :
    hashInput pp tweak input ≠ thInput pp' (encodeAddress kind.code mu hi lo) payload := by
  rw [← normalBytes_normalize pp tweak input]
  cases normalize pp tweak input with
  | virtual param t data => exact virtualInput_ne_source param pp' t data kind mu hi lo payload
  | physical param call =>
    cases call with
    | chain c value =>
      exact fullInput_ne_of_type_ne _ _ _ _ _ _ _ _ (Ne.symm hchain)
    | leaf tree node values =>
      exact fullInput_ne_of_type_ne _ _ _ _ _ _ _ _ (Ne.symm hleaf)
    | node tree level index reached left right =>
      exact fullInput_ne_of_type_ne _ _ _ _ _ _ _ _ (Ne.symm hnode)

/-- Every complete forest input is at least 64 bytes, including totalized unused calls. -/
theorem hashInput_size_lower (pp : PublicParam) (tweak : Tweak) (input : Input) :
    64 ≤ (hashInput pp tweak input).size := by
  have virtual_size (param : PublicParam) (t : Tweak) (data : Input) :
      64 ≤ (virtualInput param t data).size := by
    cases data <;>
      simp only [virtualInput, thInput, ByteArray.size_append, tweakFrame_size, inputFrame,
        packDigests, size_packBytes] <;>
      norm_num [PUBLIC_PARAM_LEN, ADDRESS_LEN, DIGEST_LEN, ByteArray.size]
  rw [← normalBytes_normalize pp tweak input]
  cases normalize pp tweak input with
  | virtual param t data => exact virtual_size param t data
  | physical param call =>
    cases call <;>
      simp only [normalBytes, physicalBytes, chainInput, FullInputs.leafInput,
        FullInputs.nodeInput, thInput, ByteArray.size_append, packDigests, size_packBytes] <;>
      norm_num [PUBLIC_PARAM_LEN, ADDRESS_LEN, DIGEST_LEN]

/-- The raw-seed tag input is outside the whole forest input image by its exact length. -/
theorem schemeSeedInput_ne_hashInput (raw : Seed) (pp : PublicParam) (tweak : Tweak)
    (input : Input) : FullInputs.schemeSeedInput raw ≠ hashInput pp tweak input := by
  intro h
  have hs := congrArg ByteArray.size h
  have hl := hashInput_size_lower pp tweak input
  rw [FullInputs.schemeSeedInput_size] at hs
  omega

end EthereumXMSSHypertree.ConcreteHypertree
