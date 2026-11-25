module

public import EthLib.Consensus.Proofs.DataAvailability.Custody
public import EthLib.Cryptography.Proofs.RandomOracleTable

/-!
# Proofs: column sampling with a cached random oracle

From Fulu, a node samples the columns of a few custody groups, picked by hashing its node ID.

A node that asks for `k` of the `G` groups accepts with probability at most `C(a, k) / C(G, k)`.

Here `a` counts the groups whose columns are all served.

The oracle answers in place of the SHA-256 call that gives each ID its group.

The bound holds for the oracle only; no theorem bounds the search when SHA-256 answers.

SHA-256 is public, so an adversary that knows a node ID can compute the groups of that node.

The bound says nothing about such an adversary.
-/

@[expose] public section

namespace EthLib.Consensus.DataAvailability

open Base OracleComp OracleSpec ENNReal

/-- The group of one ID, with its hash call exposed to a shared oracle. -/
def queryGroupOfId (config : Config) (id : NodeID) :
    OracleComp (ByteArray →ₒ Bytes32) CustodyIndex :=
  (fun digest => firstUInt64 digest % config.NUMBER_OF_CUSTODY_GROUPS) <$>
    liftM ((ByteArray →ₒ Bytes32).query ⟨(U256.toBeBytes id).toArray.reverse⟩)

/-- The search for distinct groups, with each hash call exposed to a shared oracle. -/
def queryCollectGroups (config : Config) (count : Nat) :
    Nat → NodeID → List CustodyIndex →
      OracleComp (ByteArray →ₒ Bytes32) (Except CustodyError (List CustodyIndex))
  | fuel, id, groups =>
    if count ≤ groups.length then pure (.ok groups)
    else match fuel with
      | 0 => pure (.error (.outOfFuel groups.length count))
      | fuel + 1 => do
        let group ← queryGroupOfId config id
        queryCollectGroups config count fuel (id + 1)
          (if group ∈ groups then groups else groups ++ [group])

/-- The custody groups of a node, with each hash call exposed to a shared oracle. -/
def queryCustodyGroups (config : Config) (nodeId : NodeID) (count : UInt64) (fuel : Nat) :
    OracleComp (ByteArray →ₒ Bytes32) (Except CustodyError (List CustodyIndex)) :=
  if config.NUMBER_OF_CUSTODY_GROUPS < count then pure (.error (.tooManyGroups count))
  else if count = config.NUMBER_OF_CUSTODY_GROUPS then
    pure (.ok ((List.range config.NUMBER_OF_CUSTODY_GROUPS.toNat).map UInt64.ofNat))
  else (fun found => found.map List.mergeSort) <$>
    queryCollectGroups config count.toNat fuel nodeId []

/-- Answering the exposed hash calls with SHA-256 gives the specified search. -/
private theorem evalWithAnswerFn_queryCollectGroups (config : Config) (count fuel : Nat)
    (id : NodeID) (groups : List CustodyIndex) :
    evalWithAnswerFn (QueryImpl.ofFn Cryptography.Hash.Sha256.hash32)
      (queryCollectGroups config count fuel id groups) =
      collectGroups config count fuel id groups := by
  induction fuel generalizing id groups with
  | zero =>
    rw [queryCollectGroups, collectGroups]
    split_ifs <;> rfl
  | succ fuel ih =>
    rw [queryCollectGroups, collectGroups]
    split_ifs
    · rfl
    · simp only [evalWithAnswerFn_bind, queryGroupOfId]
      rw [ih]
      rfl

/-- Answering the exposed hash calls with SHA-256 gives the specified custody groups. -/
theorem evalWithAnswerFn_queryCustodyGroups (config : Config) (nodeId : NodeID)
    (count : UInt64) (fuel : Nat) :
    evalWithAnswerFn (QueryImpl.ofFn Cryptography.Hash.Sha256.hash32)
      (queryCustodyGroups config nodeId count fuel) =
        getCustodyGroups config nodeId count fuel := by
  rw [queryCustodyGroups, getCustodyGroups]
  split_ifs
  · rfl
  · rfl
  · rw [evalWithAnswerFn_map, evalWithAnswerFn_queryCollectGroups]

/-- Whether the network serves every column of a group. -/
def groupServed (config : Config) (preset : Preset) (served : ColumnIndex → Bool)
    (group : CustodyIndex) : Bool :=
  match computeColumnsForCustodyGroup config preset group with
  | .ok columns => columns.all served
  | .error _ => false

/-- The number of groups whose columns the network all serves. -/
def servedGroupCount (config : Config) (preset : Preset) (served : ColumnIndex → Bool) : Nat :=
  ((List.range config.NUMBER_OF_CUSTODY_GROUPS.toNat).filter
    fun group => groupServed config preset served (UInt64.ofNat group)).length

/-- Bytes folded in from the most significant end give their base-256 integer.

It needs at most eight bytes, so that no shift overflows. -/
private theorem foldr_byte_toNat (l : List UInt8) (short : l.length ≤ 8) :
    (l.foldr (fun b (acc : UInt64) => acc <<< 8 ||| b.toUInt64) 0).toNat =
      Nat.ofDigits 256 (l.map UInt8.toNat) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have length : l.length ≤ 7 := by simp only [List.length_cons] at short; omega
    have digits : Nat.ofDigits 256 (l.map UInt8.toNat) < 256 ^ (l.map UInt8.toNat).length :=
      Nat.ofDigits_lt_base_pow_length (by norm_num)
        (by simpa using fun a _ => a.toNat_lt)
    rw [List.length_map] at digits
    have bound : Nat.ofDigits 256 (l.map UInt8.toNat) < 256 ^ 7 :=
      lt_of_lt_of_le digits (Nat.pow_le_pow_right (by norm_num) length)
    have byte := b.toNat_lt
    have eight : (8 : UInt64).toNat % 64 = 8 := by decide
    rw [List.foldr_cons, List.map_cons, Nat.ofDigits_cons, UInt64.toNat_or,
      UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, ih (by omega), eight, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega), ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt byte,
      Nat.shiftLeft_eq]
    omega

/-- Below `q G`, `q` times as many integers pass a test of their residue modulo `G` as below `G`.

Each integer is its quotient and its residue. -/
private theorem card_filter_range_mod (q G : Nat) (R : Nat → Prop) [DecidablePred R] :
    ((Finset.range (q * G)).filter fun n => R (n % G)).card =
      q * ((Finset.range G).filter R).card := by
  rw [show q * ((Finset.range G).filter R).card =
      (Finset.range q ×ˢ (Finset.range G).filter R).card by
    rw [Finset.card_product, Finset.card_range]]
  refine Finset.card_nbij' (fun n => (n / G, n % G)) (fun pair => pair.1 * G + pair.2)
    ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    have positive : 0 < G := Nat.pos_of_ne_zero fun h => by simp [h] at hn
    simp only [Finset.coe_product, Finset.coe_range, Finset.coe_filter, Finset.mem_range,
      Set.mem_prod, Set.mem_Iio, Set.mem_ofPred_eq]
    exact ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hn.1), Nat.mod_lt _ positive, hn.2⟩
  · rintro ⟨a, r⟩ hp
    simp only [Finset.coe_product, Finset.coe_range, Finset.coe_filter, Finset.mem_range,
      Set.mem_prod, Set.mem_Iio, Set.mem_ofPred_eq] at hp
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    have residue : (a * G + r) % G = r := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.2.1]
    refine ⟨by nlinarith [hp.1, hp.2.1], by rw [residue]; exact hp.2.2⟩
  · intro n _
    exact Nat.div_add_mod' n G
  · rintro ⟨a, r⟩ hp
    simp only [Finset.coe_product, Finset.coe_range, Finset.coe_filter, Finset.mem_range,
      Set.mem_prod, Set.mem_Iio, Set.mem_ofPred_eq] at hp
    have positive : 0 < G := by omega
    have residue : (a * G + r) % G = r := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.2.1]
    have quotient : (a * G + r) / G = a := by
      rw [Nat.mul_comm, Nat.mul_add_div positive, Nat.div_eq_of_lt hp.2.1, Nat.add_zero]
    simp only [quotient, residue]

/-- A byte as a digit of base 256. -/
private def byteDigit : UInt8 ≃ Fin 256 :=
  ⟨UInt8.toFin, UInt8.ofFin, fun _ => rfl, fun _ => rfl⟩

/-- The digit of a byte is its value. -/
private theorem byteDigit_val (b : UInt8) : (byteDigit b).val = b.toNat := rfl

/-- Eight bytes as the digits of base 256 of an integer, least significant first. -/
private def firstBytesCode : (Fin 8 → UInt8) ≃ Fin (2 ^ 64) :=
  (Equiv.arrowCongr (Equiv.refl _) byteDigit).trans
    (finFunctionFinEquiv.trans (finCongr (by norm_num)))

/-- The integer of the first eight bytes is their code in base 256. -/
private theorem firstUInt64_toNat (bytes : Bytes32) :
    (firstUInt64 bytes).toNat = (firstBytesCode fun i => bytes[i.val]).val := by
  rw [firstUInt64, ← List.foldr_map (f := fun i : Fin 8 => bytes[i.val])
    (g := fun b (acc : UInt64) => acc <<< 8 ||| b.toUInt64), foldr_byte_toNat _ (by simp)]
  simp [firstBytesCode, List.finRange_succ, Nat.ofDigits_cons]
  rw [finFunctionFinEquiv_apply]
  simp [Fin.sum_univ_succ, byteDigit_val]
  ring

/-- The group of a uniform digest is uniform among the groups, when their number divides `2^64`.

So a test of the group holds with the share of groups that pass it. -/
private theorem prEvent_group_uniform (N : UInt64) (divides : N.toNat ∣ 2 ^ 64)
    (P : CustodyIndex → Prop) [DecidablePred P] :
    Pr{let v ← $ᵗ Bytes32}[P (firstUInt64 v % N)] =
      (((Finset.range N.toNat).filter fun r => P (UInt64.ofNat r)).card : ℝ≥0∞) / N.toNat := by
  obtain ⟨q, hq⟩ := divides
  have nonzero : (2 : Nat) ^ 64 ≠ 0 := pow_ne_zero 64 two_ne_zero
  have positive : 0 < N.toNat := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.zero_mul] at hq
    exact nonzero hq
  have copies : q ≠ 0 := fun h => by
    rw [h, Nat.mul_zero] at hq
    exact nonzero hq
  let reads : Bytes32 → Fin 8 → UInt8 :=
    fun v i => v[(Fin.castLE (by norm_num : 8 ≤ 32) i).val]
  -- The group is the residue of the base-256 code of the first eight bytes.
  have reduce (v : Bytes32) :
      firstUInt64 v % N = UInt64.ofNat ((firstBytesCode (reads v)).val % N.toNat) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, firstUInt64_toNat, UInt64.toNat_ofNat_of_lt']
    · rfl
    · exact lt_of_lt_of_le (Nat.mod_lt _ positive) (Nat.le_of_dvd (Nat.pos_of_ne_zero nonzero)
        ⟨q, hq⟩)
  simp only [reduce]
  rw [← prEvent_map ($ᵗ Bytes32) reads
      (fun b => P (UInt64.ofNat ((firstBytesCode b).val % N.toNat))),
    (evalDistEq_uniformSample_vector_map_getElem_injective (R := UInt8) (m := 32)
      (e := Fin.castLE (by norm_num : 8 ≤ 32)) (Fin.castLE_injective _)).prEvent_eq,
    SampleableType.prEvent_uniformSample]
  -- Count the codes below `2^64` rather than the byte strings.
  have numerator : (Finset.univ.filter fun b : Fin 8 → UInt8 =>
      P (UInt64.ofNat ((firstBytesCode b).val % N.toNat))).card =
      ((Finset.range (2 ^ 64)).filter fun n => P (UInt64.ofNat (n % N.toNat))).card := by
    -- Subtypes avoid unfolding the finite set of all byte strings.
    let := Nat.CountSet.fintype (fun n => P (UInt64.ofNat (n % N.toNat))) (2 ^ 64)
    rw [← Fintype.card_subtype, ← Fintype.card_of_subtype _
      (p := fun n => n < 2 ^ 64 ∧ P (UInt64.ofNat (n % N.toNat)))
      (fun n => by simp only [Finset.mem_filter, Finset.mem_range])]
    exact Fintype.card_congr
      { toFun := fun b => ⟨(firstBytesCode b.1).val, (firstBytesCode b.1).isLt, b.2⟩
        invFun := fun n => ⟨firstBytesCode.symm ⟨n.1, n.2.1⟩, by
          rw [Equiv.apply_symm_apply]
          exact n.2.2⟩
        left_inv := fun b => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have total : Fintype.card (Fin 8 → UInt8) = 2 ^ 64 := by
    rw [Fintype.card_congr firstBytesCode, Fintype.card_fin]
  rw [numerator, total, hq, Nat.mul_comm,
    card_filter_range_mod q N.toNat (fun r => P (UInt64.ofNat r)), Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_div_mul_left _ _ (by exact_mod_cast copies) (ENNReal.natCast_ne_top q)]

/-- An event after a draw is bounded case by case on the draw.

The bound is `ε₁` where `p₁` holds, `ε₂` where `p₂` holds, and zero elsewhere. -/
private theorem prEvent_bind_le_split {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (p₁ p₂ : α → Prop) (q : β → Prop) (ε₁ ε₂ : ℝ≥0∞)
    (first : ∀ a, p₁ a → Pr{let y ← f a}[q y] ≤ ε₁)
    (second : ∀ a, p₂ a → Pr{let y ← f a}[q y] ≤ ε₂)
    (neither : ∀ a, ¬ p₁ a → ¬ p₂ a → Pr{let y ← f a}[q y] = 0) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p₁ a] * ε₁ + Pr{let a ← mx}[p₂ a] * ε₂ := by
  classical
  rw [prEvent_bind_eq_tsum, prEvent_eq_tsum_ite mx p₁, prEvent_eq_tsum_ite mx p₂,
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← tsum_add]
  refine tsum_le_tsum fun a => ?_
  by_cases one : p₁ a
  · simp only [one, ↓reduceIte]
    refine le_add_right ?_
    gcongr
    exact first a one
  · by_cases two : p₂ a
    · simp only [two, ↓reduceIte]
      refine le_add_left ?_
      gcongr
      exact second a two
    · rw [neither a one two, mul_zero]
      exact zero_le

/-- One step of the search runs the hash call of its ID, then the rest of the search. -/
private theorem run'_queryCollectGroups_succ (config : Config) (count fuel : Nat) (id : NodeID)
    (groups : List CustodyIndex) (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (short : ¬ count ≤ groups.length) :
    (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryCollectGroups config count (fuel + 1) id groups)).run' cache =
      (simulateQ (ByteArray →ₒ Bytes32).randomOracle (queryGroupOfId config id)).run cache >>=
        fun z => (simulateQ (ByteArray →ₒ Bytes32).randomOracle
          (queryCollectGroups config count fuel (id + 1)
            (if z.1 ∈ groups then groups else groups ++ [z.1]))).run' z.2 := by
  rw [queryCollectGroups, ite_eq_right short]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

/-- A cached ID gives the group of its cached digest, and leaves the cache as it was. -/
private theorem run_queryGroupOfId_of_cached (config : Config) (id : NodeID)
    (cache : (ByteArray →ₒ Bytes32).QueryCache) (v : Bytes32)
    (cached : cache ⟨(U256.toBeBytes id).toArray.reverse⟩ = some v) :
    (simulateQ (ByteArray →ₒ Bytes32).randomOracle (queryGroupOfId config id)).run cache =
      pure (firstUInt64 v % config.NUMBER_OF_CUSTODY_GROUPS, cache) := by
  simp only [queryGroupOfId, simulateQ_map, simulateQ_spec_query, StateT.run_map,
    randomOracle.run_eq, cached, map_pure]

/-- A fresh ID gives the group of a uniform digest, which the cache then keeps. -/
private theorem run_queryGroupOfId_of_fresh (config : Config) (id : NodeID)
    (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (fresh : cache ⟨(U256.toBeBytes id).toArray.reverse⟩ = none) :
    (simulateQ (ByteArray →ₒ Bytes32).randomOracle (queryGroupOfId config id)).run cache =
      ($ᵗ Bytes32) >>= fun v => pure (firstUInt64 v % config.NUMBER_OF_CUSTODY_GROUPS,
        cache.cacheQuery ⟨(U256.toBeBytes id).toArray.reverse⟩ v) := by
  simp only [queryGroupOfId, simulateQ_map, simulateQ_spec_query, StateT.run_map,
    randomOracle.run_eq, fresh, map_bind, map_pure]

/-- Removing one element from both sides scales `C(A, m + 1) / C(N, m + 1)` by `N / A`. -/
private theorem choose_step (A N m : Nat) :
    A * (A - 1).choose m * N.choose (m + 1) = N * A.choose (m + 1) * (N - 1).choose m := by
  cases A with
  | zero => simp
  | succ A =>
    cases N with
    | zero => simp
    | succ N =>
      apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m)
      have left := Nat.add_one_mul_choose_eq A m
      have right := Nat.add_one_mul_choose_eq N m
      simp only [Nat.add_sub_cancel]
      calc (A + 1) * A.choose m * (N + 1).choose (m + 1) * (m + 1)
          = (A + 1) * A.choose m * ((N + 1).choose (m + 1) * (m + 1)) := by ring
        _ = (A + 1) * A.choose m * ((N + 1) * N.choose m) := by rw [right]
        _ = (N + 1) * ((A + 1) * A.choose m) * N.choose m := by ring
        _ = (N + 1) * ((A + 1).choose (m + 1) * (m + 1)) * N.choose m := by rw [left]
        _ = (N + 1) * (A + 1).choose (m + 1) * N.choose m * (m + 1) := by ring

/-- The bound on a search that holds `j` served groups: `C(a - j, k - j) / C(G - j, k - j)`. -/
private noncomputable def searchBound (a G k j : Nat) : ℝ≥0∞ :=
  ((a - j).choose (k - j) : ℝ≥0∞) / ((G - j).choose (k - j) : ℝ≥0∞)

/-- One more served group scales the bound by `(G - j) / (a - j)`. -/
private theorem searchBound_succ (a G k j : Nat) (short : j < k) (below : k < G) :
    ((a - j : Nat) : ℝ≥0∞) * searchBound a G k (j + 1) =
      ((G - j : Nat) : ℝ≥0∞) * searchBound a G k j := by
  obtain ⟨m, hm⟩ : ∃ m, k - j = m + 1 := ⟨k - j - 1, by omega⟩
  have next : k - (j + 1) = m := by omega
  have upper : (G - (j + 1)).choose m ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have lower : (G - j).choose (m + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  unfold searchBound
  rw [hm, next, Nat.sub_add_eq, Nat.sub_add_eq, ← mul_div_assoc, ← mul_div_assoc,
    ENNReal.div_eq_div_iff (by exact_mod_cast lower) (ENNReal.natCast_ne_top _)
      (by exact_mod_cast upper) (ENNReal.natCast_ne_top _)]
  exact_mod_cast by
    rw [Nat.mul_comm, choose_step (a - j) (G - j) m]
    ring

/-- Averaging the bounds over the next group gives back the bound.

With `j` of the `G` groups held, the next group is held with chance `j / G`.

It is a new served group with chance `(a - j) / G`. -/
private theorem searchBound_average (a G k j : Nat) (short : j < k) (below : k < G) :
    (j : ℝ≥0∞) / G * searchBound a G k j +
        ((a - j : Nat) : ℝ≥0∞) / G * searchBound a G k (j + 1) =
      searchBound a G k j := by
  have nonzero : (G : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show G ≠ 0 by omega)
  calc (j : ℝ≥0∞) / G * searchBound a G k j +
        ((a - j : Nat) : ℝ≥0∞) / G * searchBound a G k (j + 1)
      = (G : ℝ≥0∞)⁻¹ * ((j : ℝ≥0∞) * searchBound a G k j +
          ((a - j : Nat) : ℝ≥0∞) * searchBound a G k (j + 1)) := by
        simp only [div_eq_mul_inv]
        ring
    _ = (G : ℝ≥0∞)⁻¹ * (((j + (G - j) : Nat) : ℝ≥0∞) * searchBound a G k j) := by
        rw [searchBound_succ a G k j short below, Nat.cast_add, add_mul]
    _ = searchBound a G k j := by
        rw [Nat.add_sub_cancel' (by omega), ← mul_assoc, ENNReal.inv_mul_cancel nonzero
          (ENNReal.natCast_ne_top G), one_mul]

/-- At most as many groups below `G` are held as the list of held groups is long. -/
private theorem card_held_le (G : Nat) (bounded : G ≤ 2 ^ 64) (groups : List CustodyIndex) :
    ((Finset.range G).filter fun r => UInt64.ofNat r ∈ groups).card ≤ groups.length := by
  calc ((Finset.range G).filter fun r => UInt64.ofNat r ∈ groups).card
      ≤ (groups.map UInt64.toNat).toFinset.card := by
        refine Finset.card_le_card fun r held => ?_
        rw [Finset.mem_filter, Finset.mem_range] at held
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨UInt64.ofNat r, held.2, UInt64.toNat_ofNat_of_lt' (by
          simp only [UInt64.size]
          omega)⟩
    _ ≤ (groups.map UInt64.toNat).length := List.toFinset_card_le _
    _ = groups.length := List.length_map _

/-- The served groups below `G` count the held groups, all served, and the new served ones. -/
private theorem card_new_add_le (G : Nat) (good : CustodyIndex → Bool) (groups : List CustodyIndex)
    (distinct : groups.Nodup) (inRange : ∀ g ∈ groups, g.toNat < G)
    (accepted : ∀ g ∈ groups, good g = true) :
    ((Finset.range G).filter fun r =>
        UInt64.ofNat r ∉ groups ∧ good (UInt64.ofNat r) = true).card + groups.length ≤
      ((Finset.range G).filter fun r => good (UInt64.ofNat r) = true).card := by
  have held : (groups.map UInt64.toNat).toFinset.card = groups.length := by
    rw [List.toFinset_card_of_nodup (distinct.map fun _ _ same => UInt64.toNat_inj.mp same),
      List.length_map]
  rw [← held, ← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card fun r member => ?_
    rw [Finset.mem_union, Finset.mem_filter, List.mem_toFinset, List.mem_map] at member
    rw [Finset.mem_filter]
    rcases member with ⟨small, _, served⟩ | ⟨g, mem, rfl⟩
    · exact ⟨small, served⟩
    · rw [UInt64.ofNat_toNat]
      exact ⟨Finset.mem_range.mpr (inRange g mem), accepted g mem⟩
  · rw [Finset.disjoint_left]
    intro r fresh old
    rw [Finset.mem_filter] at fresh
    rw [List.mem_toFinset, List.mem_map] at old
    obtain ⟨g, mem, rfl⟩ := old
    rw [UInt64.ofNat_toNat] at fresh
    exact fresh.2.1 mem

/-- A search that already holds a rejected group never returns only accepted groups.

The search keeps the groups it starts from. -/
private theorem prEvent_queryCollectGroups_eq_zero (config : Config) (good : CustodyIndex → Bool)
    (count fuel : Nat) (id : NodeID) (groups : List CustodyIndex)
    (cache : (ByteArray →ₒ Bytes32).QueryCache) (rejects : ∃ g ∈ groups, good g = false) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryCollectGroups config count fuel id groups)).run' cache}[
        ∃ out, z = .ok out ∧ ∀ g ∈ out, good g = true] = 0 := by
  obtain ⟨g, member, rejected⟩ := rejects
  induction fuel generalizing id groups cache with
  | zero =>
    rw [queryCollectGroups]
    split_ifs
    · -- The returned list is the start list, which fails the test at `g`.
      simp
      exact ⟨g, member, rejected⟩
    · simp
  | succ fuel ih =>
    by_cases short : count ≤ groups.length
    · rw [queryCollectGroups, ite_eq_left short]
      simp
      exact ⟨g, member, rejected⟩
    · rw [run'_queryCollectGroups_succ config count fuel id groups cache short]
      -- Every continuation starts from more groups, `g` among them.
      refine le_antisymm (prEvent_bind_le_of_forall_le _ _ _ fun z => (ih _ _ _ ?_).le) zero_le
      split_ifs
      · exact member
      · exact List.mem_append_left _ member

/-- A search from `j` accepted groups accepts with chance at most `C(a-j, k-j) / C(G-j, k-j)`.

Here `G` counts the groups, `a` the accepted ones and `k < G` the groups that the search wants.
-/
private theorem prEvent_queryCollectGroups_le (config : Config) (good : CustodyIndex → Bool)
    (divides : config.NUMBER_OF_CUSTODY_GROUPS.toNat ∣ 2 ^ 64) (count : Nat)
    (below : count < config.NUMBER_OF_CUSTODY_GROUPS.toNat) (fuel : Nat) (id : NodeID)
    (groups : List CustodyIndex) (cache : (ByteArray →ₒ Bytes32).QueryCache)
    -- The `j` groups are distinct.
    (distinct : groups.Nodup)
    (inRange : ∀ g ∈ groups, g.toNat < config.NUMBER_OF_CUSTODY_GROUPS.toNat)
    (accepted : ∀ g ∈ groups, good g = true)
    -- Every digest in the cache gives a group that the search already holds.
    --
    -- So a repeated ID gives nothing new, and each fresh ID gives a uniform group.
    (known : ∀ x v, cache x = some v → firstUInt64 v % config.NUMBER_OF_CUSTODY_GROUPS ∈ groups) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryCollectGroups config count fuel id groups)).run' cache}[
        -- The search accepts when it returns only accepted groups.
        ∃ out, z = .ok out ∧ ∀ g ∈ out, good g = true] ≤
      searchBound ((Finset.range config.NUMBER_OF_CUSTODY_GROUPS.toNat).filter
        fun r => good (UInt64.ofNat r) = true).card
        config.NUMBER_OF_CUSTODY_GROUPS.toNat count groups.length := by
  set accepts := ((Finset.range config.NUMBER_OF_CUSTODY_GROUPS.toNat).filter
    fun r => good (UInt64.ofNat r) = true).card with accepts_def
  have stop (j : Nat) (done : count ≤ j) :
      searchBound accepts config.NUMBER_OF_CUSTODY_GROUPS.toNat count j = 1 := by
    rw [searchBound, Nat.sub_eq_zero_of_le done, Nat.choose_zero_right, Nat.choose_zero_right,
      Nat.cast_one, div_one]
  induction fuel generalizing id groups cache with
  | zero =>
    rw [queryCollectGroups]
    split_ifs with done
    · exact (prEvent_le_one _).trans (stop _ done).ge
    · simp
  | succ fuel ih =>
    by_cases done : count ≤ groups.length
    · rw [queryCollectGroups, ite_eq_left done]
      exact (prEvent_le_one _).trans (stop _ done).ge
    rw [run'_queryCollectGroups_succ config count fuel id groups cache done]
    cases cached : cache ⟨(U256.toBeBytes id).toArray.reverse⟩ with
    | some v =>
      -- A cached digest gives a held group, so nothing changes.
      rw [run_queryGroupOfId_of_cached config id cache v cached, pure_bind]
      simp only [known _ v cached, ↓reduceIte]
      exact ih _ _ _ distinct inRange accepted known
    | none =>
      rw [run_queryGroupOfId_of_fresh config id cache cached, bind_assoc]
      simp only [pure_bind]
      -- After a fresh answer, every cached digest gives a group of a list with the new one.
      have knownAfter (v : Bytes32) (next : List CustodyIndex)
          (holds : firstUInt64 v % config.NUMBER_OF_CUSTODY_GROUPS ∈ next)
          (grows : groups ⊆ next) (x : ByteArray) (w : Bytes32)
          (hit : (cache.cacheQuery ⟨(U256.toBeBytes id).toArray.reverse⟩ v) x = some w) :
          firstUInt64 w % config.NUMBER_OF_CUSTODY_GROUPS ∈ next := by
        by_cases same : x = ⟨(U256.toBeBytes id).toArray.reverse⟩
        · rw [same, QueryCache.cacheQuery_self, Option.some_inj] at hit
          rw [← hit]
          exact holds
        · rw [QueryCache.cacheQuery_of_ne _ _ same] at hit
          exact grows (known x w hit)
      refine (prEvent_bind_le_split ($ᵗ Bytes32) _
        (fun v => firstUInt64 v % config.NUMBER_OF_CUSTODY_GROUPS ∈ groups)
        (fun v => firstUInt64 v % config.NUMBER_OF_CUSTODY_GROUPS ∉ groups ∧
          good (firstUInt64 v % config.NUMBER_OF_CUSTODY_GROUPS) = true) _
        (searchBound accepts config.NUMBER_OF_CUSTODY_GROUPS.toNat count groups.length)
        (searchBound accepts config.NUMBER_OF_CUSTODY_GROUPS.toNat count (groups.length + 1))
        ?_ ?_ ?_).trans ?_
      · intro v held
        simp only [held, ↓reduceIte]
        exact ih _ _ _ distinct inRange accepted (knownAfter v groups held (fun _ h => h))
      · rintro v ⟨fresh, ok⟩
        simp only [fresh, ↓reduceIte]
        -- A new accepted group joins the held ones.
        have step := ih (id + 1) (groups ++ [firstUInt64 v % config.NUMBER_OF_CUSTODY_GROUPS])
          (cache.cacheQuery ⟨(U256.toBeBytes id).toArray.reverse⟩ v)
          (List.nodup_append.mpr ⟨distinct, List.nodup_singleton _, fun a ha b hb same =>
            fresh (by rw [List.mem_singleton.mp hb] at same; exact same ▸ ha)⟩)
          (fun g member => by
            rcases List.mem_append.mp member with old | new
            · exact inRange g old
            · rw [List.mem_singleton.mp new, UInt64.toNat_mod]
              exact Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) below))
          (fun g member => by
            rcases List.mem_append.mp member with old | new
            · exact accepted g old
            · rw [List.mem_singleton.mp new]
              exact ok)
          (knownAfter v _ (List.mem_append_right _ (List.mem_singleton_self _))
            (List.subset_append_left _ _))
        rwa [List.length_append, List.length_singleton] at step
      · intro v held new
        simp only [held, ↓reduceIte]
        -- A new rejected group stays in every list that the search returns.
        refine prEvent_queryCollectGroups_eq_zero config good count fuel (id + 1) _ _
          ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        simpa [held] using new
      · -- The next group is uniform: held with chance at most `j / G`, new and accepted with
        -- chance at most `(a - j) / G`.
        have bounded : config.NUMBER_OF_CUSTODY_GROUPS.toNat ≤ 2 ^ 64 :=
          Nat.le_of_dvd (by norm_num) divides
        have fresh := card_new_add_le _ good groups distinct inRange accepted
        rw [prEvent_group_uniform _ divides (fun g => g ∈ groups),
          prEvent_group_uniform _ divides (fun g => g ∉ groups ∧ good g = true)]
        calc _ ≤ (groups.length : ℝ≥0∞) / config.NUMBER_OF_CUSTODY_GROUPS.toNat *
                searchBound accepts config.NUMBER_OF_CUSTODY_GROUPS.toNat count groups.length +
              ((accepts - groups.length : Nat) : ℝ≥0∞) / config.NUMBER_OF_CUSTODY_GROUPS.toNat *
                searchBound accepts config.NUMBER_OF_CUSTODY_GROUPS.toNat count
                  (groups.length + 1) := by
              gcongr
              · exact_mod_cast card_held_le _ bounded groups
              · exact_mod_cast Nat.le_sub_of_add_le fresh
          _ = _ := searchBound_average _ _ _ _ (by omega) below

/-- A node accepts its sample with probability at most `C(a, k) / C(G, k)`.

Here `G` counts the groups, `a` the served groups and `k` the groups that the node asks for.

The oracle starts with an empty cache, and the served columns are fixed before it answers. -/
theorem prEvent_queryCustodyGroups_served_le (config : Config) (preset : Preset)
    (nodeId : NodeID) (count : UInt64) (fuel : Nat)
    -- It needs `G` to divide `2^64`, so that a fresh digest gives every group the chance `1 / G`.
    (divides : config.NUMBER_OF_CUSTODY_GROUPS.toNat ∣ 2 ^ 64) (served : ColumnIndex → Bool) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryCustodyGroups config nodeId count fuel)).run' ∅}[
        -- A node accepts when every group that its search returns is served.
        --
        -- An error, such as a search out of fuel or more groups than exist, is a rejection.
        ∃ groups, z = .ok groups ∧ ∀ group ∈ groups, groupServed config preset served group] ≤
      ((servedGroupCount config preset served).choose count.toNat : ℝ≥0∞) /
        (config.NUMBER_OF_CUSTODY_GROUPS.toNat.choose count.toNat : ℝ≥0∞) := by
  -- The served groups, counted as a finite set.
  have counted : servedGroupCount config preset served =
      ((Finset.range config.NUMBER_OF_CUSTODY_GROUPS.toNat).filter fun r =>
        groupServed config preset served (UInt64.ofNat r) = true).card := by
    unfold servedGroupCount
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    congr 1
    ext r
    simp
  rw [queryCustodyGroups]
  by_cases over : config.NUMBER_OF_CUSTODY_GROUPS < count
  · rw [ite_eq_left over]
    simp
  rw [ite_eq_right over]
  by_cases every : count = config.NUMBER_OF_CUSTODY_GROUPS
  · rw [ite_eq_left every]
    simp only [simulateQ_pure, StateT.run'_pure']
    classical
    rw [prEvent_pure]
    split_ifs with accepts
    · -- Accepting every group needs every group served, and then the bound is one.
      obtain ⟨groups, same, all⟩ := accepts
      rw [Except.ok.injEq] at same
      have full :
          servedGroupCount config preset served = config.NUMBER_OF_CUSTODY_GROUPS.toNat := by
        unfold servedGroupCount
        rw [List.filter_eq_self.mpr fun r member => all _ (same ▸ List.mem_map_of_mem member),
          List.length_range]
      rw [full, every, ENNReal.div_self (by exact_mod_cast (Nat.choose_pos le_rfl).ne')
        (ENNReal.natCast_ne_top _)]
    · exact zero_le
  rw [ite_eq_right every]
  have below : count.toNat < config.NUMBER_OF_CUSTODY_GROUPS.toNat := by
    have different : count.toNat ≠ config.NUMBER_OF_CUSTODY_GROUPS.toNat :=
      fun same => every (UInt64.toNat_inj.mp same)
    have := UInt64.lt_iff_toNat_lt.not.mp over
    omega
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  calc _ = Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
        (queryCollectGroups config count.toNat fuel nodeId [])).run' ∅}[
          ∃ out, z = .ok out ∧ ∀ g ∈ out, groupServed config preset served g = true] := by
        rw [StateT.run'_eq, prEvent_map]
        refine prEvent_congr _ _ _ fun z => ?_
        -- Sorting keeps the members of the list.
        rcases z with ⟨_ | out, _⟩
        · simp [Except.map]
        · simp [Except.map, List.mem_mergeSort]
    _ ≤ searchBound ((Finset.range config.NUMBER_OF_CUSTODY_GROUPS.toNat).filter fun r =>
          groupServed config preset served (UInt64.ofNat r) = true).card
          config.NUMBER_OF_CUSTODY_GROUPS.toNat count.toNat ([] : List CustodyIndex).length :=
        prEvent_queryCollectGroups_le config _ divides _ below fuel nodeId [] ∅ List.nodup_nil
          (by simp) (by simp) (by simp)
    _ = _ := by
        rw [searchBound, ← counted]
        simp

/-- On mainnet, take a network that serves at most 63 of the 128 columns.

Fewer than half of the columns cannot rebuild the data, so this is the case of withheld data.

A node that asks for `k` groups accepts with probability at most `C(63, k) / C(128, k)`. -/
theorem prEvent_queryCustodyGroups_served_le_mainnet (nodeId : NodeID) (count : UInt64)
    (fuel : Nat) (served : ColumnIndex → Bool)
    (withheld : ((List.range 128).filter fun column => served (UInt64.ofNat column)).length ≤ 63) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryCustodyGroups Config.mainnet nodeId count fuel)).run' ∅}[
        ∃ groups, z = .ok groups ∧
          ∀ group ∈ groups, groupServed Config.mainnet Preset.mainnet served group] ≤
      ((Nat.choose 63 count.toNat : Nat) : ℝ≥0∞) / (Nat.choose 128 count.toNat : Nat) := by
  have groups : Config.mainnet.NUMBER_OF_CUSTODY_GROUPS.toNat = 128 := rfl
  -- Each mainnet group holds the one column of its own index.
  have same : servedGroupCount Config.mainnet Preset.mainnet served =
      ((List.range 128).filter fun column => served (UInt64.ofNat column)).length := by
    unfold servedGroupCount
    rw [groups]
    congr 1
    refine List.filter_congr fun g hg => ?_
    have small : g < 128 := List.mem_range.mp hg
    have range : UInt64.ofNat g < Config.mainnet.NUMBER_OF_CUSTODY_GROUPS := by
      rw [UInt64.lt_iff_toNat_lt, groups, UInt64.toNat_ofNat_of_lt' (by
        simp only [UInt64.size]; omega)]
      exact small
    have one : (Preset.mainnet.NUMBER_OF_COLUMNS /
        Config.mainnet.NUMBER_OF_CUSTODY_GROUPS).toNat = 1 := rfl
    simp only [groupServed, computeColumnsForCustodyGroup, range, ite_true, one]
    simp
  refine (prEvent_queryCustodyGroups_served_le Config.mainnet Preset.mainnet nodeId count fuel
    (by rw [groups]; decide) served).trans ?_
  rw [groups]
  gcongr
  rw [same]
  exact withheld

/-- One step multiplies `C(63, k) 2^k` by `2 (63 - k)` and `C(128, k)` by `128 - k`, which is more.

So a bound at `k` gives a strict bound at `k + 1`. -/
private theorem choose_sixtyThree_mul_pow_lt_succ (k : Nat) (small : k < 63)
    (le : Nat.choose 63 k * 2 ^ k ≤ Nat.choose 128 k) :
    Nat.choose 63 (k + 1) * 2 ^ (k + 1) < Nat.choose 128 (k + 1) := by
  have pos : 0 < Nat.choose 128 k := Nat.choose_pos (by omega)
  have left := Nat.choose_succ_right_eq 63 k
  have right := Nat.choose_succ_right_eq 128 k
  refine Nat.lt_of_mul_lt_mul_right (a := k + 1) ?_
  calc Nat.choose 63 (k + 1) * 2 ^ (k + 1) * (k + 1)
      = Nat.choose 63 k * 2 ^ k * (2 * (63 - k)) := by
        rw [mul_right_comm, left, pow_succ]
        ring
    _ ≤ Nat.choose 128 k * (2 * (63 - k)) := Nat.mul_le_mul_right _ le
    _ < Nat.choose 128 k * (128 - k) := Nat.mul_lt_mul_of_pos_left (by omega) pos
    _ = Nat.choose 128 (k + 1) * (k + 1) := right.symm

/-- Up to `k = 63`, `C(63, k) 2^k` stays at most `C(128, k)`. -/
private theorem choose_sixtyThree_mul_pow_le (k : Nat) (small : k ≤ 63) :
    Nat.choose 63 k * 2 ^ k ≤ Nat.choose 128 k := by
  induction k with
  | zero => simp
  | succ k ih => exact (choose_sixtyThree_mul_pow_lt_succ k (by omega) (ih (by omega))).le

/-- For `k ≥ 1`, the mainnet bound `C(63, k) / C(128, k)` is below `2^-k`.

Each of its `k` factors `(63 - i) / (128 - i)` is below one half. -/
theorem choose_sixtyThree_div_lt (k : Nat) (positive : 0 < k) :
    ((Nat.choose 63 k : Nat) : ℝ≥0∞) / (Nat.choose 128 k : Nat) < (2 ^ k)⁻¹ := by
  by_cases large : 128 < k
  · -- Both binomials vanish, and `0 / 0 = 0` in the extended reals.
    rw [Nat.choose_eq_zero_of_lt (by omega : 63 < k), Nat.cast_zero, ENNReal.zero_div]
    exact ENNReal.inv_pos.mpr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have pos : 0 < Nat.choose 128 k := Nat.choose_pos (by omega)
  -- Clear the denominators: it is `2^k C(63, k) < C(128, k)`.
  have bound : 2 ^ k * Nat.choose 63 k < Nat.choose 128 k := by
    by_cases few : k ≤ 63
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [mul_comm]
      exact choose_sixtyThree_mul_pow_lt_succ j (by omega)
        (choose_sixtyThree_mul_pow_le j (by omega))
    · rw [Nat.choose_eq_zero_of_lt (by omega : 63 < k), mul_zero]
      exact pos
  rw [ENNReal.lt_inv_iff_lt_inv, ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top _))
    (Or.inl (by exact_mod_cast pos.ne')), ENNReal.lt_div_iff_mul_lt
    (Or.inr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast bound

end EthLib.Consensus.DataAvailability
