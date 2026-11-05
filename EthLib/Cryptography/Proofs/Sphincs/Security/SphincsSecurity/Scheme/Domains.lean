module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Bytes
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Encoding
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.RandomOracle

/-!
# Domain separation of the hash inputs

Every hash input except the scheme seed input starts with the parameter and the 16-byte address.

This prefix determines the parameter and the address fields, whatever the payload.

Seed derivations use other address types than the verification hashes, so their inputs differ.

A seed-derivation input determines its parameter, its domain and its seed.
-/

@[expose] public section

namespace SphincsSecurity.Completeness

variable [Params]

omit [Params] in
/-- Two inputs whose addresses have different types differ, whatever their parameters and payloads.

The type is in the byte at offset 23 of every input. -/
theorem fieldInput_ne_of_tag_ne_across (parameter parameter' : PublicParameter)
    {fields1 fields2 : TweakFields} (htag : fields1.tag ≠ fields2.tag)
    (payload1 payload2 : HashInput) :
    bytesLE 16 parameter ++ fieldBytes fields1 ++ payload1 ≠
      bytesLE 16 parameter' ++ fieldBytes fields2 ++ payload2 := by
  intro h
  apply htag
  obtain ⟨hprefix, _⟩ := List.append_inj h (by
    simp only [List.length_append]
    rw [bytesLE_length 16 parameter, bytesLE_length 16 parameter']
    simp [fieldBytes, bytesLE_length])
  obtain ⟨_, hfields⟩ := List.append_inj hprefix
    ((bytesLE_length 16 parameter).trans (bytesLE_length 16 parameter').symm)
  rw [SphincsSecurity.fieldBytes_injective hfields]

end SphincsSecurity.Completeness

namespace SphincsSecurity.Security

variable [Params]

omit [Params] in
/-- The prefix `P || A` determines the parameter and the address fields.

So two equal inputs also have equal payloads. -/
theorem fieldInput_injective {fields fields' : TweakFields}
    {parameter parameter' : PublicParameter} {payload payload' : HashInput}
    (h : bytesLE 16 parameter ++ fieldBytes fields ++ payload =
      bytesLE 16 parameter' ++ fieldBytes fields' ++ payload') :
    fields = fields' ∧ parameter = parameter' ∧ payload = payload' := by
  obtain ⟨hprefix, hpayload⟩ := List.append_inj h (by
    simp only [List.length_append]
    rw [bytesLE_length 16 parameter, bytesLE_length 16 parameter']
    simp [fieldBytes, bytesLE_length])
  obtain ⟨hparameter, hfields⟩ := List.append_inj hprefix
    ((bytesLE_length 16 parameter).trans (bytesLE_length 16 parameter').symm)
  exact ⟨fieldBytes_injective hfields, bytesLE_injective hparameter, hpayload⟩

/-- A verification hash input determines its address fields, its parameter and its payload. -/
theorem tweakableInput_injective {parameter parameter' : PublicParameter}
    {domain domain' : HashDomain} {payload payload' : HashInput}
    (h : tweakableHashInput parameter domain payload =
      tweakableHashInput parameter' domain' payload') :
    hashDomainFields domain = hashDomainFields domain' ∧
      parameter = parameter' ∧ payload = payload' :=
  fieldInput_injective h

/-! ### FORS addresses -/

theorem two_pow_forsHeight_le : 2 ^ forsHeight ≤ 2 ^ 12 :=
  Nat.pow_le_pow_right (by decide) Params.forsHeight_le

theorem forsSlot_lt (κ : FTree) {position : Nat} (h : position < 2 ^ 18) :
    forsSlot κ position < 2 ^ 24 := by
  have := κ.isLt; have := Params.forsTrees_le
  unfold forsSlot
  omega

/-- The slot `κ + 64 p` determines the tree `κ` and the position `p`. -/
theorem forsSlot_injective {κ κ' : FTree} {position position' : Nat}
    (h : forsSlot κ position = forsSlot κ' position') : κ = κ' ∧ position = position' := by
  have := κ.isLt; have := κ'.isLt; have := Params.forsTrees_le
  unfold forsSlot at h
  refine ⟨Fin.ext ?_, ?_⟩ <;> omega

theorem nodePosition_lt (level : Nat) (node : FLeaf) (hlevel : level < 16) :
    nodePosition level node.val < 2 ^ 18 := by
  have := node.isLt; have := two_pow_forsHeight_le
  unfold nodePosition
  omega

omit [Params] in
/-- For levels below 16, the position `level + 16 node` determines the level and the node. -/
theorem nodePosition_injective {level level' node node' : Nat} (hlevel : level < 16)
    (hlevel' : level' < 16)
    (h : nodePosition level node = nodePosition level' node') : level = level' ∧ node = node' := by
  unfold nodePosition at h
  omega

theorem leaf_lt_two_pow_18 (leaf : FLeaf) : leaf.val < 2 ^ 18 :=
  lt_of_lt_of_le leaf.isLt (two_pow_forsHeight_le.trans (by decide))

theorem pair_lt_two_pow_18 (pair : FPair) : pair.val < 2 ^ 18 :=
  lt_of_lt_of_le pair.isLt
    (Nat.pow_le_pow_right (by decide) (by have := Params.forsHeight_le; omega))

theorem level_lt_16 (level : FLevel) : level.val + 1 < 16 := by
  have := level.isLt; have := Params.forsHeight_le
  omega

theorem deriveFields_injective : Function.Injective keygenDomainFields := by
  intro left right h
  cases left <;> cases right <;>
    simp only [keygenDomainFields, tweakFields, treeFields, TweakFields.mk.injEq] at h
  all_goals try { simp at h; done }
  · rfl
  · rename_i lay tree leaf chain lay' tree' leaf' chain'
    obtain ⟨_, _, hlayer, htree, hchain, hleaf⟩ := h
    have hl : lay = lay' := layerByte_ofNat_injective hlayer
    have ht : tree = tree' :=
      Fin.ext (ofNat_inj_of_lt (tree_lt_two_pow_32 tree) (tree_lt_two_pow_32 tree') htree)
    have hc : chain = chain' := by
      apply Fin.ext
      exact ofNat_inj_of_lt (chain.isLt.trans_le (by decide))
        (chain'.isLt.trans_le (by decide)) hchain
    have he : leaf = leaf' :=
      Fin.ext (ofNat_inj_of_lt (leaf_lt_two_pow_32 leaf) (leaf_lt_two_pow_32 leaf') hleaf)
    cases hl; cases ht; cases he; cases hc; rfl
  · rename_i index κ pair index' κ' pair'
    obtain ⟨_, _, _, _, hpos, hindex⟩ := h
    have hidx : index = index' :=
      Fin.ext (ofNat_inj_of_lt (index_lt_two_pow_32 index) (index_lt_two_pow_32 index') hindex)
    have hp := ofNat_inj_of_lt (forsSlot_lt κ (pair_lt_two_pow_18 pair))
      (forsSlot_lt κ' (pair_lt_two_pow_18 pair')) hpos
    obtain ⟨hκ, hpair⟩ := forsSlot_injective hp
    subst hidx hκ
    cases Fin.ext hpair; rfl
  · rename_i level level'
    obtain ⟨_, _, _, _, hlevel, _⟩ := h
    have hl : level = level' := by
      apply Fin.ext
      have := totalHeight_le_28; have := maxLayerHeight_le
      exact ofNat_inj_of_lt (level.isLt.trans_le (by omega))
        (level'.isLt.trans_le (by omega)) hlevel
    cases hl; rfl

/-- A seed-derivation input determines its parameter, its domain and its seed. -/
theorem keygenInput_injective {parameter parameter' : PublicParameter}
    {domain domain' : KeygenDomain} {seed seed' : MasterSeed}
    (h : keygenHashInput parameter domain seed = keygenHashInput parameter' domain' seed') :
    parameter = parameter' ∧ domain = domain' ∧ seed = seed' := by
  obtain ⟨hfields, hp, hs⟩ := fieldInput_injective h
  exact ⟨hp, deriveFields_injective hfields, bytesLE_injective hs⟩

/-- No seed-derivation domain has the address type of a verification domain. -/
theorem derive_tag_ne_hash_tag (derive : KeygenDomain) (hash : HashDomain) :
    (keygenDomainFields derive).tag ≠ (hashDomainFields hash).tag := by
  cases derive <;> cases hash <;>
    simp [keygenDomainFields, hashDomainFields, tweakFields, treeFields]

/-- A seed-derivation input differs from every verification hash input, for any two parameters. -/
theorem keygenInput_ne_hashInput (parameter parameter' : PublicParameter)
    (derive : KeygenDomain) (hash : HashDomain) (seed : MasterSeed) (payload : HashInput) :
    keygenHashInput parameter derive seed ≠ tweakableHashInput parameter' hash payload :=
  Completeness.fieldInput_ne_of_tag_ne_across parameter parameter'
    (derive_tag_ne_hash_tag derive hash) _ _

end SphincsSecurity.Security
