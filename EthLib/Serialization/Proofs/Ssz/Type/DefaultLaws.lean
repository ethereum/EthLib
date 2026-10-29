import EthLib.Serialization.Ssz.Type.Default
import EthLib.Serialization.Proofs.Ssz.Codec.Fits

/-! Defaults belong to their declared value domains. -/

namespace EthLib.Serialization.Ssz

/-- Every successful default is admissible, including defaults of nested fields. -/
theorem default_fits (shape : Desc) :
    ∀ value, shape.default = .ok value → Fits shape value := by
  -- Default construction and field collection are proved together, preserving both counts and domains.
  induction shape using Desc.default.induct
    (motive_2 := fun fields => ∀ values, Desc.defaultFields fields = .ok values →
      fields.length = values.length ∧ ∀ pair ∈ fields.zip values, Fits pair.1 pair.2) with
  -- False is always admitted by the boolean domain.
  | case1 => rintro _ ⟨⟩; exact .bool false
  -- Zero is below every positive power-of-two integer bound.
  | case2 width => rintro _ ⟨⟩; exact .uint (Nat.pow_pos (by decide))
  -- Replicated bytes and bits have exactly the declared fixed length.
  | case3 length => rintro _ ⟨⟩; exact .byteVector (by simp)
  | case4 length => rintro _ ⟨⟩; exact .bitVector (by simp)
  -- Empty variable arrays satisfy every natural-number capacity.
  | case5 limit => rintro _ ⟨⟩; exact .byteList (by simp)
  | case6 limit => rintro _ ⟨⟩; exact .bitList (by simp)
  | case7 limit => rintro _ ⟨⟩; exact .progressiveBitList (by cases limit <;> simp [withinBound])
  -- An empty element sequence has no child-domain obligations.
  | case8 element limit => rintro _ ⟨⟩; exact .list (by simp) (by simp)
  | case9 element limit =>
    rintro _ ⟨⟩
    exact .progressiveList (by cases limit <;> simp [withinBound]) (by simp)
  | case10 element length ih =>
    intro value made
    -- Replication preserves admissibility of the element default at every position.
    cases one : element.default <;>
      simp [Desc.default, one, Bind.bind, Except.bind, pure, Except.pure] at made
    subst value
    exact .vector (by simp) (fun item member => (List.mem_replicate.mp member).2 ▸ ih _ one)
  | case11 names fields ih =>
    intro value made
    -- Each field contributes one default, in declaration order.
    cases parts : Desc.defaultFields fields <;>
      simp [Desc.default, parts, Bind.bind, Except.bind, pure, Except.pure] at made
    subst value
    exact .container (ih _ parts).1 (ih _ parts).2
  | case12 active names fields ih =>
    intro value made
    -- Gaps carry no values, so admissibility uses the same field pairing as a container.
    cases parts : Desc.defaultFields fields <;>
      simp [Desc.default, parts, Bind.bind, Except.bind, pure, Except.pure] at made
    subst value
    exact .progressiveContainer (ih _ parts).1 (ih _ parts).2
  -- A union has no default, so successful construction is impossible in this case.
  | case13 selectors options => rintro _ ⟨⟩
  -- An empty field suffix contributes zero values and no unmatched fields.
  | case14 =>
    rename_i made
    cases made
    simp
  | case15 field rest ihHead ihTail =>
    rename_i values made
    -- Successful collection requires both the first default and all later defaults.
    cases head : field.default <;> cases tail : Desc.defaultFields rest <;>
      simp [Desc.defaultFields, head, tail, Bind.bind, Except.bind, pure, Except.pure] at made
    subst values
    -- The suffix preserves its length and each field-value pairing.
    obtain ⟨sized, each⟩ := ihTail _ tail
    refine ⟨by simp [sized], fun pair member => ?_⟩
    -- Every pair belongs either to the first field or to the already-admissible suffix.
    rcases List.mem_cons.mp member with first | later
    · exact first ▸ ihHead _ head
    · exact each pair later

end EthLib.Serialization.Ssz
