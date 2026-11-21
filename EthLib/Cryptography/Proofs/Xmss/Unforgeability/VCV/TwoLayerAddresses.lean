module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerConflict

/-!
# Hash inputs charged to the two-layer graph

The leanXMSS draft assigns distinct codes to its seven address types in "Address encoding".

Only the chain, leaf and node types can charge the graph potential.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph

open HashSig OracleComp OracleSpec Constants
open ChainGraph (Public Word)
open scoped ENNReal

/-- The cache holds the low row and its full input decodes to a chain, leaf or node. -/
@[expose] def addressedInputs (pp : PublicParam) (c : Public.QueryCache) : Set HashInput :=
  {b | (c (.inl b)).isSome ∧ (decode pp b).isSome}

/-- Only occupied, well-formed chain, leaf and node inputs can charge the graph. -/
theorem potential_le_addressed (pp : PublicParam) (st : RelabelState Public Start Row Word) :
    (keys pp).potential ((subgraph pp).project st) ≤
      2 * ((addressedInputs pp st.1).encard : ℝ≥0∞) / Nat.card Word := by
  have sub : (keys pp).keyEntries st.1 ⊆ Sum.inl '' addressedInputs pp st.1 := by
    rintro (b | b) ⟨present, named⟩
    · exact ⟨b, ⟨present, named⟩, rfl⟩
    · exact False.elim (Bool.false_ne_true named)
  apply ((keys pp).potential_le_two_mul _).trans
  gcongr
  exact (Set.encard_le_encard sub).trans (Set.encard_image_le _ _)

/-- Every input charged by the graph is among the physical inputs of the caller. -/
theorem addressed_subset (pp : PublicParam) (c : Public.QueryCache) :
    addressedInputs pp c ⊆ physicalInputs c := fun _ h => Or.inl h.1

/-- An address of a different type cannot decode to a graph role, for any parameter and payload. -/
theorem decode_otherType (pp other : PublicParam) (tag : AddressType)
    (chain : tag ≠ .chain) (leaf : tag ≠ .leaf) (node : tag ≠ .node)
    (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) (payload : ByteArray) :
    decode pp (thInput other (encodeAddress tag.code mu hi lo) payload).data.toList = none := by
  classical
  unfold decode
  split
  next hit =>
    obtain ⟨⟨l, r⟩, vs, _, same⟩ := hit
    have address := (thInput_inj (ByteArray.ext (Array.toList_inj.mp same))).2.1
    cases r with
    | chain =>
      exact False.elim (chain (AddressType.code_injective (encodeAddress_inj.mp address).1.symm))
    | leaf =>
      exact False.elim (leaf (AddressType.code_injective (encodeAddress_inj.mp address).1.symm))
    | node =>
      exact False.elim (node (AddressType.code_injective (encodeAddress_inj.mp address).1.symm))
  next => rfl

/-- Seed, parameter, randomizer and message inputs are outside the charged graph. -/
theorem other_address_not_charged (pp other : PublicParam) (c : Public.QueryCache)
    (tag : AddressType) (otherType : tag = .prf ∨ tag = .param ∨ tag = .rnd ∨ tag = .msg)
    (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) (payload : ByteArray) :
    (thInput other (encodeAddress tag.code mu hi lo) payload).data.toList ∉
      addressedInputs pp c := by
  intro charged
  have bounds : tag ≠ .chain ∧ tag ≠ .leaf ∧ tag ≠ .node := by
    rcases otherType with rfl | rfl | rfl | rfl <;> decide
  have missing := decode_otherType pp other tag bounds.1 bounds.2.1 bounds.2.2 mu hi lo payload
  have present := charged.2
  rw [missing] at present
  exact Bool.false_ne_true present

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph
