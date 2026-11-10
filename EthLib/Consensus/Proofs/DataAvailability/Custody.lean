module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.DataAvailability.CustodyColumns

/-!
# Proofs: custody groups and their columns

A successful selection returns `count` distinct groups, sorted, each below the number of groups.

A request for every group returns all of them, and a request for more fails.

A node that asks for more groups, with the same fuel, keeps every group it had.

The groups split the columns: a column belongs to the group of its residue.

A custody column bit is set exactly when its column belongs to one of the groups of the node.
-/

@[expose] public section

namespace EthLib.Consensus.DataAvailability

variable {config : Config}

/-- Two errors with one code come from one constructor. -/
theorem CustodyError.code_injective (e₁ e₂ : CustodyError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [CustodyError.code] at h; exact absurd h (by decide))

/-! ## Selection of the groups -/

/-- Asking for more groups than exist fails. -/
theorem getCustodyGroups_tooManyGroups {id : NodeID} {count : UInt64} {fuel : Nat}
    (h : config.NUMBER_OF_CUSTODY_GROUPS < count) :
    getCustodyGroups config id count fuel = .error (.tooManyGroups count) := by
  rw [getCustodyGroups, ite_eq_left h]

/-- A request for every group returns all of them, in order. -/
theorem getCustodyGroups_all (id : NodeID) (fuel : Nat) :
    getCustodyGroups config id config.NUMBER_OF_CUSTODY_GROUPS fuel =
      .ok ((List.range config.NUMBER_OF_CUSTODY_GROUPS.toNat).map UInt64.ofNat) := by
  rw [getCustodyGroups, ite_eq_right (UInt64.lt_irrefl _), ite_eq_left rfl]

/-- The search keeps the groups it starts from, as a prefix. -/
theorem collectGroups_prefix {count fuel : Nat} {id : NodeID} {groups out : List CustodyIndex}
    (h : collectGroups config count fuel id groups = .ok out) : groups <+: out := by
  induction fuel generalizing id groups with
  | zero =>
    rw [collectGroups] at h
    split at h
    · cases h
      exact List.prefix_refl _
    · cases h
  | succ fuel ih =>
    rw [collectGroups] at h
    split at h
    · cases h
      exact List.prefix_refl _
    · dsimp only at h
      split at h
      · exact ih h
      · exact (List.prefix_append _ _).trans (ih h)

/-- From groups that are distinct and in range, the search finds exactly `count` such groups. -/
theorem collectGroups_ok {count fuel : Nat} {id : NodeID} {groups out : List CustodyIndex}
    (h : collectGroups config count fuel id groups = .ok out)
    (hpos : 0 < config.NUMBER_OF_CUSTODY_GROUPS) (hnd : groups.Nodup)
    (hlt : ∀ g ∈ groups, g < config.NUMBER_OF_CUSTODY_GROUPS) (hle : groups.length ≤ count) :
    out.Nodup ∧ (∀ g ∈ out, g < config.NUMBER_OF_CUSTODY_GROUPS) ∧ out.length = count := by
  induction fuel generalizing id groups with
  | zero =>
    rw [collectGroups] at h
    split at h
    · cases h
      exact ⟨hnd, hlt, by omega⟩
    · cases h
  | succ fuel ih =>
    rw [collectGroups] at h
    split at h
    · cases h
      exact ⟨hnd, hlt, by omega⟩
    · rename_i hlen
      dsimp only at h
      split at h
      · exact ih h hnd hlt hle
      · rename_i hnew
        refine ih h (List.nodup_append.mpr ⟨hnd, by simp, ?_⟩) ?_ ?_
        · intro a ha b hb
          rw [List.mem_singleton] at hb
          subst hb
          exact fun he => hnew (he ▸ ha)
        · intro g hg
          rcases List.mem_append.mp hg with hg | hg
          · exact hlt g hg
          · rw [List.mem_singleton.mp hg]
            exact UInt64.mod_lt _ hpos
        · rw [List.length_append, List.length_singleton]
          omega

/-- With the same fuel, a larger `count` finds every group that a smaller one finds. -/
theorem collectGroups_mono {count count' fuel : Nat} {id : NodeID}
    {groups out out' : List CustodyIndex} (hc : count ≤ count')
    (h : collectGroups config count fuel id groups = .ok out)
    (h' : collectGroups config count' fuel id groups = .ok out') : out <+: out' := by
  induction fuel generalizing id groups with
  | zero =>
    rw [collectGroups] at h h'
    split at h
    · cases h
      split at h'
      · cases h'
        exact List.prefix_refl _
      · cases h'
    · cases h
  | succ fuel ih =>
    rw [collectGroups] at h
    split at h
    · cases h
      exact collectGroups_prefix h'
    · rename_i hlen
      rw [collectGroups, ite_eq_right (by omega)] at h'
      exact ih h h'

private theorem pairwise_lt_of_sort {l : List CustodyIndex} (hnd : l.Nodup) :
    (l.mergeSort).Pairwise (· < ·) := by
  have hs := List.pairwise_mergeSort (le := fun a b : UInt64 => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact UInt64.le_trans hab hbc)
    (fun a b => by simp only [decide_eq_true_eq, Bool.or_eq_true]; exact UInt64.le_total a b) l
  have hnd' := (List.mergeSort_perm l (fun a b : UInt64 => decide (a ≤ b))).nodup_iff.mpr hnd
  exact (hs.and hnd').imp fun ⟨h1, h2⟩ =>
    UInt64.lt_of_le_of_ne (by simpa using h1) h2

/-- The groups that a selection returns: `count` of them, strictly increasing, all in range. -/
theorem getCustodyGroups_ok {id : NodeID} {count : UInt64} {fuel : Nat} {gs : List CustodyIndex}
    (h : getCustodyGroups config id count fuel = .ok gs) :
    gs.length = count.toNat ∧ gs.Pairwise (· < ·) ∧
      ∀ g ∈ gs, g < config.NUMBER_OF_CUSTODY_GROUPS := by
  rw [getCustodyGroups] at h
  split at h
  · cases h
  split at h
  · rename_i heq
    cases h
    subst heq
    have hN := UInt64.toNat_lt config.NUMBER_OF_CUSTODY_GROUPS
    refine ⟨by simp, ?_, ?_⟩
    · rw [List.pairwise_map]
      refine List.pairwise_lt_range.imp_of_mem ?_
      intro a b ha hb hab
      rw [List.mem_range] at ha hb
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
      omega
    · intro g hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      rw [List.mem_range] at ha
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
      omega
  · rename_i hgt hne
    have hlt : count < config.NUMBER_OF_CUSTODY_GROUPS :=
      UInt64.lt_of_le_of_ne (UInt64.not_lt.mp hgt) hne
    have hpos : 0 < config.NUMBER_OF_CUSTODY_GROUPS := by
      rw [UInt64.lt_iff_toNat_lt] at hlt ⊢
      simp only [UInt64.toNat_zero]
      omega
    cases hc : collectGroups config count.toNat fuel id [] with
    | error e => rw [hc] at h; cases h
    | ok out =>
      rw [hc] at h
      cases h
      obtain ⟨hnd, hrange, hlen⟩ :=
        collectGroups_ok hc hpos List.nodup_nil (by simp) (by simp)
      have hp := List.mergeSort_perm out (fun a b : UInt64 => decide (a ≤ b))
      exact ⟨hp.length_eq.trans hlen, pairwise_lt_of_sort hnd,
        fun g hg => hrange g (hp.mem_iff.mp hg)⟩

/-- A node that asks for more groups keeps every group it had, with the same fuel. -/
theorem getCustodyGroups_mono {id : NodeID} {count count' : UInt64} {fuel : Nat}
    {gs gs' : List CustodyIndex} (hc : count ≤ count')
    (h : getCustodyGroups config id count fuel = .ok gs)
    (h' : getCustodyGroups config id count' fuel = .ok gs') : ∀ g ∈ gs, g ∈ gs' := by
  intro g hg
  have hrange := (getCustodyGroups_ok h).2.2 g hg
  rw [getCustodyGroups] at h'
  split at h'
  · cases h'
  split at h'
  · rename_i heq
    cases h'
    rw [List.mem_map]
    refine ⟨g.toNat, List.mem_range.mpr ?_, UInt64.ofNat_toNat⟩
    exact UInt64.lt_iff_toNat_lt.mp hrange
  · rename_i hgt' hne'
    have hlt' : count' < config.NUMBER_OF_CUSTODY_GROUPS :=
      UInt64.lt_of_le_of_ne (UInt64.not_lt.mp hgt') hne'
    have hlt : count < config.NUMBER_OF_CUSTODY_GROUPS := UInt64.lt_of_le_of_lt hc hlt'
    rw [getCustodyGroups, ite_eq_right (UInt64.not_lt.mpr (UInt64.le_of_lt hlt)),
      ite_eq_right (UInt64.ne_of_lt hlt)] at h
    cases hc0 : collectGroups config count.toNat fuel id [] with
    | error e => rw [hc0] at h; cases h
    | ok out =>
      cases hc1 : collectGroups config count'.toNat fuel id [] with
      | error e => rw [hc1] at h'; cases h'
      | ok out' =>
        rw [hc0] at h
        rw [hc1] at h'
        cases h
        cases h'
        have hpre := collectGroups_mono (UInt64.le_iff_toNat_le.mp hc) hc0 hc1
        exact (List.mergeSort_perm _ _).mem_iff.mpr
          (hpre.subset ((List.mergeSort_perm _ _).mem_iff.mp hg))

/-! ## Columns of a group -/

/-- A group out of range has no columns. -/
theorem computeColumnsForCustodyGroup_outOfRange {preset : Preset} {group : CustodyIndex}
    (h : ¬group < config.NUMBER_OF_CUSTODY_GROUPS) :
    computeColumnsForCustodyGroup config preset group = .error (.groupOutOfRange group) := by
  rw [computeColumnsForCustodyGroup, ite_eq_right h]

/-- Let `N` be the number of groups.

The columns of a group are those below `N * (NUMBER_OF_COLUMNS / N)` with its residue modulo `N`. -/
theorem mem_computeColumnsForCustodyGroup {preset : Preset} {group : CustodyIndex}
    {cols : List ColumnIndex} (h : computeColumnsForCustodyGroup config preset group = .ok cols)
    (c : ColumnIndex) :
    c ∈ cols ↔ c.toNat < config.NUMBER_OF_CUSTODY_GROUPS.toNat *
        (preset.NUMBER_OF_COLUMNS / config.NUMBER_OF_CUSTODY_GROUPS).toNat ∧
      c.toNat % config.NUMBER_OF_CUSTODY_GROUPS.toNat = group.toNat := by
  rw [computeColumnsForCustodyGroup] at h
  split at h
  · rename_i hg
    cases h
    have hg' := UInt64.lt_iff_toNat_lt.mp hg
    have hC := UInt64.toNat_lt preset.NUMBER_OF_COLUMNS
    have hM : config.NUMBER_OF_CUSTODY_GROUPS.toNat *
        (preset.NUMBER_OF_COLUMNS / config.NUMBER_OF_CUSTODY_GROUPS).toNat ≤
        preset.NUMBER_OF_COLUMNS.toNat := by
      rw [UInt64.toNat_div]
      exact Nat.mul_div_le _ _
    -- Below the bound, the column `N * i + group` does not wrap around `2^64`.
    have hval : ∀ i < (preset.NUMBER_OF_COLUMNS / config.NUMBER_OF_CUSTODY_GROUPS).toNat,
        (config.NUMBER_OF_CUSTODY_GROUPS * UInt64.ofNat i + group).toNat =
          config.NUMBER_OF_CUSTODY_GROUPS.toNat * i + group.toNat ∧
        config.NUMBER_OF_CUSTODY_GROUPS.toNat * i + group.toNat <
          config.NUMBER_OF_CUSTODY_GROUPS.toNat *
            (preset.NUMBER_OF_COLUMNS / config.NUMBER_OF_CUSTODY_GROUPS).toNat := by
      intro i hi
      have hlt : config.NUMBER_OF_CUSTODY_GROUPS.toNat * i + group.toNat <
          config.NUMBER_OF_CUSTODY_GROUPS.toNat *
            (preset.NUMBER_OF_COLUMNS / config.NUMBER_OF_CUSTODY_GROUPS).toNat :=
        calc _ < config.NUMBER_OF_CUSTODY_GROUPS.toNat * (i + 1) := by
              rw [Nat.mul_add, Nat.mul_one]
              omega
          _ ≤ _ := Nat.mul_le_mul_left _ hi
      refine ⟨?_, hlt⟩
      have hi' : config.NUMBER_OF_CUSTODY_GROUPS.toNat * i < 2 ^ 64 := by omega
      have hi'' : i < 2 ^ 64 := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · omega
        · exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left i (by omega)) hi'
      rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi'',
        Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt (by omega)]
    constructor
    · intro hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      rw [List.mem_range] at hi
      obtain ⟨he, hlt⟩ := hval i hi
      rw [he]
      refine ⟨hlt, ?_⟩
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hg']
    · rintro ⟨hlt, hmod⟩
      have hpos : 0 < config.NUMBER_OF_CUSTODY_GROUPS.toNat := by omega
      have hi : c.toNat / config.NUMBER_OF_CUSTODY_GROUPS.toNat <
          (preset.NUMBER_OF_COLUMNS / config.NUMBER_OF_CUSTODY_GROUPS).toNat :=
        (Nat.div_lt_iff_lt_mul hpos).mpr (by rw [Nat.mul_comm]; exact hlt)
      refine List.mem_map.mpr ⟨_, List.mem_range.mpr hi, ?_⟩
      apply UInt64.toNat_inj.mp
      rw [(hval _ hi).1, ← hmod, Nat.div_add_mod]
  · cases h

/-! ## The custody column bits -/

/-- A custody column bit is set exactly when a group of the node has that column. -/
theorem getCustodyColumnBits_get_iff {preset : Preset} {nodeId : NodeID} {count : UInt64}
    {fuel : Nat} {bits : Serialization.Ssz.Bitvector preset.NUMBER_OF_COLUMNS.toNat}
    {groups : List CustodyIndex}
    (computed : getCustodyColumnBits config preset nodeId count fuel = .ok bits)
    (chosen : getCustodyGroups config nodeId count fuel = .ok groups)
    (column : Fin preset.NUMBER_OF_COLUMNS.toNat) :
    bits.bits[column] = true ↔ ∃ group ∈ groups, ∃ columns,
      computeColumnsForCustodyGroup config preset group = .ok columns ∧
        UInt64.ofNat column ∈ columns := by
  simp only [getCustodyColumnBits, chosen, bind, Except.bind] at computed
  split at computed
  · cases computed
  · rename_i all made
    obtain rfl := (Except.ok.inj computed).symm
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, List.any_eq_true, List.contains_iff_mem]
    constructor
    · rintro ⟨columns, held, member⟩
      obtain ⟨group, mem, found⟩ := Base.mapM_ok_mem made columns held
      exact ⟨group, mem, columns, found, member⟩
    · rintro ⟨group, mem, columns, found, member⟩
      obtain ⟨other, held, found'⟩ := Base.exists_mem_of_mapM_ok made mem
      obtain rfl := Except.ok.inj (found.symm.trans found')
      exact ⟨columns, held, member⟩

/-- Let `N` be the number of groups.

A custody column bit is set exactly when the column is below `N * (NUMBER_OF_COLUMNS / N)`.

Its residue modulo `N` must also be one of the groups of the node. -/
theorem getCustodyColumnBits_get_iff_mod {preset : Preset} {nodeId : NodeID} {count : UInt64}
    {fuel : Nat} {bits : Serialization.Ssz.Bitvector preset.NUMBER_OF_COLUMNS.toNat}
    {groups : List CustodyIndex}
    (computed : getCustodyColumnBits config preset nodeId count fuel = .ok bits)
    (chosen : getCustodyGroups config nodeId count fuel = .ok groups)
    (column : Fin preset.NUMBER_OF_COLUMNS.toNat) :
    bits.bits[column] = true ↔ column.val < config.NUMBER_OF_CUSTODY_GROUPS.toNat *
        (preset.NUMBER_OF_COLUMNS / config.NUMBER_OF_CUSTODY_GROUPS).toNat ∧
      ∃ group ∈ groups, column.val % config.NUMBER_OF_CUSTODY_GROUPS.toNat = group.toNat := by
  have noWrap : (UInt64.ofNat column.val).toNat = column.val :=
    Nat.mod_eq_of_lt (Nat.lt_trans column.isLt (UInt64.toNat_lt _))
  rw [getCustodyColumnBits_get_iff computed chosen column]
  have inRange := (getCustodyGroups_ok chosen).2.2
  constructor
  · rintro ⟨group, mem, columns, found, member⟩
    have := (mem_computeColumnsForCustodyGroup found _).mp member
    rw [noWrap] at this
    exact ⟨this.1, group, mem, this.2⟩
  · rintro ⟨below, group, mem, residue⟩
    have found : computeColumnsForCustodyGroup config preset group =
        .ok (((List.range (preset.NUMBER_OF_COLUMNS / config.NUMBER_OF_CUSTODY_GROUPS).toNat).map
          fun i => config.NUMBER_OF_CUSTODY_GROUPS * UInt64.ofNat i + group)) := by
      simp [computeColumnsForCustodyGroup, inRange group mem]
    refine ⟨group, mem, _, found, ?_⟩
    rw [mem_computeColumnsForCustodyGroup found, noWrap]
    exact ⟨below, residue⟩

end EthLib.Consensus.DataAvailability
