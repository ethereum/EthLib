module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.WinValue
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.SchemeSeed

/-!
# Eliminating the seeds from the game with derived randomizers

The SUF-CMA advantage against the signer with derived randomizers has a bound.

It is the seed-free win probability of the internalized memoizing adversary, under the budget cap.

The bound adds `3 q / 2^256` for a hash call that names a hidden seed.

That seed is the key's seed `S0` in the input of the scheme seed.

It can also be the scheme seed in a derivation input or in a randomizer derivation.

The eager table splits off an independent uniform table at the seed's randomizer derivations.

The two runs agree until a query names such an input.

Memoizing and then averaging that table gives the cost game with fresh randomizers.

That table holds one base `R0` per message, and the run reads each base at most once.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.Det

variable [Params]

open Completeness SeedCoupling Internalize Eager Short SeedModel Graph Assembly Stop HiddenCost
  GraphView Reduce DetValue

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-! ### Randomizer-derivation inputs -/

/-- The input derives a randomizer from the given master seed. -/
def RandHit (input : HashInput) (seed : MasterSeed) : Prop :=
  ∃ parameter message, randomizerHashInput parameter seed message = input

omit [Params] in
theorem randomizerHashInput_injective {parameter parameter' : PublicParameter}
    {seed seed' : MasterSeed} {message message' : Message}
    (h : randomizerHashInput parameter seed message =
      randomizerHashInput parameter' seed' message') :
    parameter = parameter' ∧ seed = seed' ∧ message = message' := by
  unfold randomizerHashInput at h
  obtain ⟨h, hm⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hs⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hp, -⟩ := List.append_inj h (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hp, bytesLE_injective hs, bytesLE_injective hm⟩

omit [Params] in
theorem randHit_unique {input : HashInput} {seed seed' : MasterSeed}
    (h : RandHit input seed) (h' : RandHit input seed') : seed = seed' := by
  obtain ⟨parameter, message, heq⟩ := h
  obtain ⟨parameter', message', heq'⟩ := h'
  exact (randomizerHashInput_injective (heq.trans heq'.symm)).2.1

omit [Params] in
theorem randHit_probability_le (input : HashInput) :
    Pr{let x ← sampleMasterSeed}[(RandHit input) x] ≤ 1 / (2 : ℝ≥0∞) ^ 256 := by
  let := SampleableType.ofFintype MasterSeed
  rw [show sampleMasterSeed = ($ᵗ MasterSeed : ProbComp MasterSeed) from rfl,
    SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter (RandHit input)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro seed hseed seed' hseed'
    exact randHit_unique (Finset.mem_filter.mp hseed).2 (Finset.mem_filter.mp hseed').2
  rw [show Fintype.card MasterSeed = 2 ^ 256 by simp, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

/-- The inputs whose answers the seed-free run must not see. -/
def Marked (seed : MasterSeed) (input : HashInput) : Prop :=
  SeedGuess.SeedHit input seed ∨ RandHit input seed

theorem marked_probability_le (input : HashInput) :
    Pr{let seed ← sampleMasterSeed}[Marked seed input] ≤ 2 / (2 : ℝ≥0∞) ^ 256 := by
  calc
    _ ≤ Pr{let x ← sampleMasterSeed}[(SeedGuess.SeedHit input) x] +
        Pr{let x ← sampleMasterSeed}[(RandHit input) x] :=
      prEvent_or_le _ _ _
    _ ≤ 1 / (2 : ℝ≥0∞) ^ 256 + 1 / (2 : ℝ≥0∞) ^ 256 :=
      add_le_add (SeedGuess.seedHit_probability_le input) (randHit_probability_le input)
    _ = _ := by rw [← ENNReal.add_div]; norm_num

/-- The ordinary entries of a trace. -/
def ordinaryCount : List (Entry HashInput) → Nat
  | [] => 0
  | .inl _ :: rest => ordinaryCount rest + 1
  | .inr _ :: rest => ordinaryCount rest

omit [Params] in
theorem ordinaryCount_le_traceCost (entries : List (Entry HashInput)) :
    ordinaryCount entries ≤ traceCost entries := by
  induction entries with
  | nil => simp [ordinaryCount, traceCost]
  | cons entry rest ih =>
      cases entry with
      | inl input => simp only [ordinaryCount, traceCost, List.map_cons, List.sum_cons,
                       entryCost] at ih ⊢; omega
      | inr amount => simp only [ordinaryCount, traceCost, List.map_cons, List.sum_cons,
                        entryCost] at ih ⊢; omega

theorem trace_marked_probability (entries : List (Entry HashInput)) :
    Pr{let seed ← sampleMasterSeed}[Hits (Marked seed) entries] ≤
      ordinaryCount entries * (2 / (2 : ℝ≥0∞) ^ 256) := by
  induction entries with
  | nil => simp [Hits, ordinaryCount]
  | cons entry rest ih =>
      cases entry with
      | inl input =>
          have hevent : (fun seed => Hits (Marked seed) (.inl input :: rest)) =
              fun seed => Marked seed input ∨ Hits (Marked seed) rest := by
            funext seed
            apply propext
            constructor
            · rintro ⟨x, hx, hm⟩
              rcases List.mem_cons.1 hx with heq | hx
              · cases heq
                exact Or.inl hm
              · exact Or.inr ⟨x, hx, hm⟩
            · rintro (hm | ⟨x, hx, hm⟩)
              · exact ⟨input, List.mem_cons_self, hm⟩
              · exact ⟨x, List.mem_cons_of_mem _ hx, hm⟩
          rw [hevent]
          refine (prEvent_or_le _ _ _).trans ?_
          refine (add_le_add (marked_probability_le input) ih).trans (le_of_eq ?_)
          simp only [ordinaryCount, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          rw [add_comm]
      | inr amount =>
          have hevent : (fun seed => Hits (Marked seed) (.inr amount :: rest)) =
              fun seed => Hits (Marked seed) rest := by
            funext seed
            apply propext
            constructor
            · rintro ⟨x, hx, hm⟩
              rcases List.mem_cons.1 hx with heq | hx
              · cases heq
              · exact ⟨x, hx, hm⟩
            · rintro ⟨x, hx, hm⟩
              exact ⟨x, List.mem_cons_of_mem _ hx, hm⟩
          rw [hevent]
          simpa only [ordinaryCount] using ih

/-- A run that does not depend on the seed, with traces of cost at most `q`, names the hidden seed.

The chance of this is at most `2 q / 2^256`. -/
theorem marked_hit_le {Ω : Type} (program : ProbComp Ω) (entries : Ω → List (Entry HashInput))
    (q : ℕ)
    (hcost : ∀ result ∈ support program, traceCost (entries result) ≤ q) :
    Pr{let pair ← sampleMasterSeed >>= fun seed => (fun result => (seed, result)) <$> program}[Hits
        (Marked pair.1) (entries pair.2)] ≤
      2 * (q / (2 : ℝ≥0∞) ^ 256) := by
  calc
    _ = Pr{let pair ← program >>= fun result => (fun seed => (seed, result)) <$>
             sampleMasterSeed}[Hits (Marked pair.1) (entries pair.2)] := by
      have h := (FiniteGraphSampling.bind_bind_swap sampleMasterSeed program
        (fun seed result => (pure (seed, result) : ProbComp (MasterSeed × Ω)))).prEvent_eq
          fun pair => Hits (Marked pair.1) (entries pair.2)
      simpa only [bind_pure_comp] using h
    _ ≤ ∑' result, Pr{let x ← program}[x = result] * (q * (2 / (2 : ℝ≥0∞) ^ 256)) := by
      rw [OracleComp.prEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun result => ?_
      by_cases hr : result ∈ support program
      · refine mul_le_mul' le_rfl ?_
        rw [prEvent_map]
        refine (trace_marked_probability (entries result)).trans ?_
        refine mul_le_mul' ?_ le_rfl
        exact_mod_cast (ordinaryCount_le_traceCost _).trans (hcost result hr)
      · rw [(prEvent_eq_zero_of_not_mem_support _) hr]
        simp
    _ ≤ q * (2 / (2 : ℝ≥0∞) ^ 256) := tsum_prob_mul_le _ _
    _ = 2 * (q / (2 : ℝ≥0∞) ^ 256) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_left_comm]

/-! ### Splitting the eager table at the seed's randomizer-derivation inputs -/

/-- The short input that derives the randomizer base of a message. -/
def randIn (parameter : PublicParameter) (seed : MasterSeed) (message : Message) : ShortIn :=
  ⟨randomizerHashInput parameter seed message, randomizerHashInput_short parameter seed message⟩

omit [Params] in
theorem randIn_injective {parameter : PublicParameter} {seed : MasterSeed}
    {message message' : Message}
    (h : randIn parameter seed message = randIn parameter seed message') :
    message = message' :=
  (randomizerHashInput_injective (congrArg Subtype.val h)).2.2

/-- A table whose randomizer derivations, for a parameter and a seed, come from another table. -/
noncomputable def plant (parameter : PublicParameter) (seed : MasterSeed) (table : Eager.Table)
    (rnd : RTable) : Eager.Table := fun input =>
  if h : ∃ message : Message, input = randIn parameter seed message then
    rnd (Classical.choose h)
  else table input

omit [Params] in
theorem plant_randIn (parameter : PublicParameter) (seed : MasterSeed) (table : Eager.Table)
    (rnd : RTable) (message : Message) :
    plant parameter seed table rnd (randIn parameter seed message) = rnd message := by
  have h : ∃ message' : Message,
      randIn parameter seed message = randIn parameter seed message' := ⟨message, rfl⟩
  rw [plant, dite_eq_left h]
  rw [randIn_injective (Classical.choose_spec h).symm]

omit [Params] in
theorem plant_other (parameter : PublicParameter) (seed : MasterSeed) (table : Eager.Table)
    (rnd : RTable) (input : ShortIn) (hinput : ∀ message, input ≠ randIn parameter seed message) :
    plant parameter seed table rnd input = table input := by
  rw [plant, dite_eq_right]
  rintro ⟨message, hmessage⟩
  exact hinput message hmessage

/-- Swap the randomizer entries of a table with an independent randomizer table. -/
noncomputable def swapPair (parameter : PublicParameter) (seed : MasterSeed)
    (pair : Eager.Table × RTable) : Eager.Table × RTable :=
  (plant parameter seed pair.1 pair.2, fun message => pair.1 (randIn parameter seed message))

omit [Params] in
theorem swapPair_involutive (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Involutive (swapPair parameter seed) := by
  rintro ⟨table, rnd⟩
  simp only [swapPair, plant_randIn, Prod.mk.injEq, and_true]
  funext input
  by_cases h : ∃ message : Message, input = randIn parameter seed message
  · obtain ⟨message, rfl⟩ := h
    rw [plant_randIn]
  · have hother : ∀ message, input ≠ randIn parameter seed message :=
      fun message heq => h ⟨message, heq⟩
    rw [plant_other _ _ _ _ _ hother, plant_other _ _ _ _ _ hother]

noncomputable local instance pairSampleable : SampleableType (Eager.Table × RTable) :=
  SampleableType.ofFintype _

omit [Params] in
/-- A uniform table has the law of a uniform table whose randomizer entries are replaced.

The new entries come from an independent uniform randomizer table. -/
theorem evalDist_table_split {β : Type} (parameter : PublicParameter) (seed : MasterSeed)
    (F : Eager.Table → ProbComp β) :
    ($ᵗ Eager.Table : ProbComp Eager.Table) >>= F =ᵈ
      (do
        let table ← ($ᵗ Eager.Table : ProbComp Eager.Table)
        let rnd ← ($ᵗ RTable : ProbComp RTable)
        F (plant parameter seed table rnd)) := by
  have hpair := evalDist_independent_uniform_pair (α := Eager.Table) (β := RTable)
  have hfst : Prod.fst <$> ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) =ᵈ
      ($ᵗ Eager.Table : ProbComp Eager.Table) := by
    refine (hpair.symm.map Prod.fst).trans ?_
    simp only [map_bind, map_pure]
    calc (($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table =>
          ($ᵗ RTable : ProbComp RTable) >>= fun _ => (pure table : ProbComp Eager.Table))
        =ᵈ (($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table =>
            (pure table : ProbComp Eager.Table)) :=
          EvalDistEq.bind_right _ fun _ => OracleComp.EvalDistEq.bind_const _ _
      _ =ᵈ ($ᵗ Eager.Table : ProbComp Eager.Table) := by rw [bind_pure]
  have hswap : swapPair parameter seed <$>
      ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) =ᵈ
      ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective
        (swapPair_involutive parameter seed).bijective
  calc
    _ =ᵈ (Prod.fst <$> ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable))) >>= F :=
      hfst.symm.bind_left _
    _ =ᵈ ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) >>= fun pair =>
        F pair.1 := by
      rw [bind_map_left]
    _ =ᵈ (swapPair parameter seed <$> ($ᵗ (Eager.Table × RTable) : ProbComp
        (Eager.Table × RTable))) >>=
          fun pair => F pair.1 := hswap.symm.bind_left _
    _ =ᵈ ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) >>=
          fun pair => F (plant parameter seed pair.1 pair.2) := by
      rw [bind_map_left]
      simp only [swapPair, EvalDistEq.refl]
    _ =ᵈ (do
          let table ← ($ᵗ Eager.Table : ProbComp Eager.Table)
          let rnd ← ($ᵗ RTable : ProbComp RTable)
          pure (table, rnd)) >>= fun pair => F (plant parameter seed pair.1 pair.2) :=
      hpair.symm.bind_left _
    _ =ᵈ _ := by simp only [bind_assoc, pure_bind, EvalDistEq.refl]

/-! ### Splitting the randomizer table into base randomizers and step halves -/

/-- The step halves of a randomizer table. -/
def highsOf (rnd : RTable) : LTable := fun message => upperHash (rnd message)

omit [Params] in
theorem highsOf_joinTable (lows highs : LTable) : highsOf (joinTable lows highs) = highs := by
  funext message
  exact upperHash_joinHalves _ _

noncomputable local instance halvesSampleable : SampleableType (LTable × LTable) :=
  SampleableType.ofFintype _

omit [Params] in
/-- A uniform randomizer table splits into a uniform table of step halves.

An independent uniform table of base randomizers completes it. -/
theorem evalDist_rtable_split {β : Type} (F : RTable → ProbComp β) :
    ($ᵗ RTable : ProbComp RTable) >>= F =ᵈ
      (do
        let highs ← ($ᵗ LTable : ProbComp LTable)
        let lows ← ($ᵗ LTable : ProbComp LTable)
        F (joinTable lows highs)) := by
  have hjoin : (fun pair : LTable × LTable => joinTable pair.1 pair.2) <$>
      ($ᵗ (LTable × LTable) : ProbComp (LTable × LTable)) =ᵈ ($ᵗ RTable : ProbComp RTable) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective joinTable_bijective
  have hpair : (do
      let lows ← ($ᵗ LTable : ProbComp LTable)
      let highs ← ($ᵗ LTable : ProbComp LTable)
      pure (lows, highs)) =ᵈ ($ᵗ (LTable × LTable) : ProbComp (LTable × LTable)) :=
    evalDist_independent_uniform_pair
  calc
    _ =ᵈ ((fun pair : LTable × LTable => joinTable pair.1 pair.2) <$>
          ($ᵗ (LTable × LTable) : ProbComp (LTable × LTable))) >>= F := hjoin.symm.bind_left _
    _ =ᵈ ($ᵗ (LTable × LTable) : ProbComp (LTable × LTable)) >>= fun pair => F
        (joinTable pair.1 pair.2) := by
      rw [bind_map_left]
    _ =ᵈ (do
          let lows ← ($ᵗ LTable : ProbComp LTable)
          let highs ← ($ᵗ LTable : ProbComp LTable)
          pure (lows, highs)) >>= fun pair => F (joinTable pair.1 pair.2) := by
      exact hpair.symm.bind_left _
    _ =ᵈ _ := by
      simp only [bind_assoc, pure_bind]
      exact FiniteGraphSampling.bind_bind_swap _ _ _

/-! ### One sample -/

theorem hashDomain_tag_ne_seven (domain : HashDomain) :
    (⟨7#5, 0#3, 0#8, 0#32, 0#24, 0#32⟩ : TweakFields).tag ≠ (hashDomainFields domain).tag := by
  cases domain <;> simp [hashDomainFields, tweakFields, treeFields]


noncomputable local instance detLabelsSampleable' : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable

theorem preparedCache_randomizer (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels)
    (parameter : PublicParameter) (seed' : MasterSeed) (message : Message) :
    preparedCache material seed answers (randomizerHashInput parameter seed' message) = none := by
  rw [preparedCache_other material seed answers _ (fun position h => ?_)]
  · rw [programCache_other ∅ seed material _ (fun h => ?_) (fun position h => ?_)]
    · rfl
    · have := congrArg List.length h
      simp [randomizerHashInput_length, parameterInput, keygenHashInput_length] at this
    · have := congrArg List.length h
      simp [randomizerHashInput_length, secretInput, keygenHashInput_length] at this
  · simp only [canonicalGraphInput, tweakableHashInput, tweakBytes, randomizerHashInput] at h
    rw [List.append_assoc (bytesLE 16 parameter ++ fieldBytes _)] at h
    refine Completeness.fieldInput_ne_of_tag_ne_across parameter (SeedModel.parameter material)
      (fields1 := ⟨7#5, 0#3, 0#8, 0#32, 0#24, 0#32⟩)
          (fields2 := hashDomainFields position.domain) ?_ _ _ h
    exact hashDomain_tag_ne_seven position.domain

theorem sampleFn_randomizer (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels)
    (table : Eager.Table) (rnd : RTable) (message : Message) :
    sampleFn material seed answers (plant (SeedModel.parameter material) seed table rnd)
      (randomizerHashInput (SeedModel.parameter material) seed message) = rnd message := by
  unfold sampleFn extend
  rw [preparedCache_randomizer, Option.getD_none, dite_eq_left (randomizerHashInput_short _ _ _)]
  exact plant_randIn _ seed table rnd message

theorem sampleFn_plant_agree (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels)
    (table : Eager.Table) (rnd : RTable) (input : HashInput) (hnot : ¬Marked seed input) :
    sampleFn material seed answers (plant (SeedModel.parameter material) seed table rnd) input =
      graphFn material answers table input := by
  rw [sampleFn_agree _ _ _ _ _ (fun h => hnot (Or.inl h))]
  unfold graphFn extend
  by_cases hshort : IsShort input
  · rw [dite_eq_left hshort, dite_eq_left hshort, plant_other
      (SeedModel.parameter material) seed table rnd
      ⟨input, hshort⟩ fun message heq => hnot (Or.inr
        ⟨SeedModel.parameter material, message, (congrArg Subtype.val heq).symm⟩)]
  · rw [dite_eq_right hshort, dite_eq_right hshort]

/-- Every sample of the internalized deterministic game equals its graph-view cost game. -/
theorem sample_costGameDet (adversary : Adversary) (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) (rnd : RTable) :
    simulateQ (fixedRom (extend (preparedCache material seed answers)
          (plant (SeedModel.parameter material) seed table rnd)))
        (countHashQueries (gameAfterSeedDet adversary seed)) =
      (simulateQ (GraphView.fixedCostSource
          (sampleFn material seed answers (plant (SeedModel.parameter material) seed table rnd))
          (sampleCoordinates material seed answers
              (plant (SeedModel.parameter material) seed table rnd)))
        (costGameDet (SeedModel.parameter material)
          (GraphView.publicData (labelsOf material answers) (highsOf rnd)) rnd
          adversary)).run := by
  set table' := plant (SeedModel.parameter material) seed table rnd
  rw [show (extend (preparedCache material seed answers) table') =
      sampleFn material seed answers table' from rfl,
    evalDist_fixedRom_eq_fixedHashWorld, fixedHashWorld_countHashQueries,
    costGameDet_correct (sampleFn material seed answers table') (SeedModel.parameter material) seed
      (GraphView.publicData (labelsOf material answers) (highsOf rnd))
      (sampleCoordinates material seed answers table')
      (GraphView.publicData_correct _ _ _ _ (sample_consistent material seed answers table')
        (sample_boundary material seed answers table') _)
      (GraphView.coordinates_correct _ _ _ _ (sample_consistent material seed answers table'))
      (sample_parameter material seed answers table') rnd
      (fun message => sampleFn_randomizer material seed answers table rnd message)]

/-- The seed-free capped deterministic run of one sample. -/
noncomputable def detRun (adversary : Adversary) (q : Nat) (material : Material)
    (answers : CanonicalGraphLabels) (table : Eager.Table) (rnd : RTable) :
    ProbComp (Option Bool × List (Entry HashInput)) :=
  costRun (graphFn material answers table) (graphCoordinates material answers)
    (cap (costGameDet (SeedModel.parameter material)
        (publicData (labelsOf material answers) (highsOf rnd))
      rnd adversary) q)

/-- One sample: the capped win in the deterministic game is at most the seed-free capped win.

The bound adds the chance to name the seed. -/
theorem per_sampleDet (adversary : Adversary) (q : Nat) (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) (rnd : RTable) :
    Pr{let result ← (simulateQ (fixedRom (extend (preparedCache material seed answers)
          (plant (SeedModel.parameter material) seed table rnd)))
          (countHashQueries (gameAfterSeedDet adversary seed)))}[result.1 = true ∧ result.2 ≤ q] ≤
      Pr{let x ← detRun adversary q material answers table rnd}[Win x] +
        Pr{let result ← detRun adversary q material answers table rnd}[Hits
            (Marked seed) result.2] := by
  set table' := plant (SeedModel.parameter material) seed table rnd
  have hrun := (sample_costGameDet adversary material seed answers table rnd).trans
    (evalDist_fixedCostSource _ _ _)
  rw [hrun, prEvent_map]
  refine le_trans (le_of_eq ?_) (le_trans
      (probEvent_costRun_le_cap (sampleFn material seed answers table')
    (sampleCoordinates material seed answers table')
    (costGameDet (SeedModel.parameter material)
        (publicData (labelsOf material answers) (highsOf rnd)) rnd
      adversary)
    q (fun value => value = true)) ?_)
  · rfl
  · rw [sampleCoordinates_eq]
    exact probEvent_costRun_le (sampleFn material seed answers table')
        (graphFn material answers table)
      (graphCoordinates material answers) (Marked seed)
      (sampleFn_plant_agree material seed answers table rnd) _ Win

/-! ### The whole game -/

theorem noRepeat_internalize_memoAdv (adversary : Adversary) :
    (Memo.memoAdv (internalize adversary)).NoRepeat := by
  rw [← Memo.internalize_memoAdv]
  exact ForsPotential.noRepeat_internalize_adversary _ (Memo.memoAdv_noRepeat adversary)

attribute [local irreducible] experiment experimentMaster sampleMasterSeed

/-- Seed elimination from a uniform scheme seed.

Assume a bound `B` on the seed-free capped win of the internalized memoizing adversary.

The bound holds in the graph-view game with fresh randomizers, for every table of walk steps.

Start the internalized game from a uniform scheme seed.

Then its capped win is at most `B` plus `2 q / 2^256`, for naming the hidden seed.

The proof fixes the step halves and averages the base randomizers. -/
theorem budgetedWinMaster_le_seedFree (adversary : Adversary) (q : Nat) (B : ℝ≥0∞)
    (hB : ∀ steps, Pr{let x ← seedFreeExperiment
                        (internalize (Memo.memoAdv adversary)) q steps}[Win x] ≤ B) :
    Pr{let result ← experimentMaster (internalize adversary)}[result.1 = true ∧ result.2 ≤ q] ≤ B +
        2 * (q / (2 : ℝ≥0∞) ^ 256) := by
  calc
    _ = Pr{let result ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          simulateQ (fixedRom (extend (preparedCache material seed answers) table))
            (countHashQueries (gameAfterSeedDet (internalize adversary) seed)))}[result.1 = true ∧
                result.2 ≤ q] :=
      (evalDist_experimentMaster_fixed adversary).prEvent_eq _
    _ = Pr{let result ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          simulateQ (fixedRom (extend (preparedCache material seed answers)
              (plant (SeedModel.parameter material) seed table rnd)))
            (countHashQueries (gameAfterSeedDet (internalize adversary) seed)))}[result.1 = true ∧
                result.2 ≤ q] := by
      refine EvalDistEq.prEvent_eq ?_ _
      refine EvalDistEq.bind_right _ fun material => EvalDistEq.bind_right _ fun seed =>
        EvalDistEq.bind_right _ fun answers => ?_
      exact evalDist_table_split (SeedModel.parameter material) seed _
    _ ≤ Pr{let x ← (do
          let material ← sampleMaterial
          let _seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          detRun (internalize adversary) q material answers table rnd)}[Win x] +
        Pr{let pair ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          (fun result => (seed, result)) <$> detRun
              (internalize adversary) q material answers table rnd)}[Hits
              (Marked pair.1) pair.2.2] := by
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun material => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun seed => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun answers => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun table => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun rnd => ?_
      rw [prEvent_map]
      exact per_sampleDet (internalize adversary) q material seed answers table rnd
    _ ≤ B + 2 * (q / (2 : ℝ≥0∞) ^ 256) := by
      refine add_le_add ?_ ?_
      · have hsteps : ∀ steps : LTable, Pr{let x ← (do
            let material ← sampleMaterial
            let _seed ← sampleMasterSeed
            let answers ← $ᵗ CanonicalGraphLabels
            let table ← $ᵗ Eager.Table
            let lows ← ($ᵗ LTable : ProbComp LTable)
            detRun (internalize adversary) q material answers table
                (joinTable lows steps))}[Win x] ≤ B := by
          intro steps
          refine le_trans ?_ (hB steps)
          unfold seedFreeExperiment
          refine probEvent_bind_mono _ _ _ _ fun material => ?_
          refine probEvent_bind_le_of _ _ _ _ fun _ => ?_
          refine probEvent_bind_mono _ _ _ _ fun answers => ?_
          refine probEvent_bind_mono _ _ _ _ fun table => ?_
          unfold detRun seedFreeRun
          simp only [highsOf_joinTable]
          rw [Memo.internalize_memoAdv]
          exact win_avg_le (graphFn material answers table) (graphCoordinates material answers)
            (SeedModel.parameter material) (publicData (labelsOf material answers) steps)
                (internalize adversary)
            (noRepeat_internalize_memoAdv adversary) q
        have hsplit : Pr{let x ← (do
            let material ← sampleMaterial
            let _seed ← sampleMasterSeed
            let answers ← $ᵗ CanonicalGraphLabels
            let table ← $ᵗ Eager.Table
            let rnd ← $ᵗ RTable
            detRun (internalize adversary) q material answers table rnd)}[Win x] =
          Pr{let x ← (do
            let steps ← ($ᵗ LTable : ProbComp LTable)
            let material ← sampleMaterial
            let _seed ← sampleMasterSeed
            let answers ← $ᵗ CanonicalGraphLabels
            let table ← $ᵗ Eager.Table
            let lows ← ($ᵗ LTable : ProbComp LTable)
            detRun (internalize adversary) q material answers table
                (joinTable lows steps))}[Win x] := by
          refine EvalDistEq.prEvent_eq ?_ _
          refine EvalDistEq.trans ?_
            (FiniteGraphSampling.bind_bind_swap ($ᵗ LTable : ProbComp LTable) sampleMaterial _).symm
          refine EvalDistEq.bind_right _ fun material => ?_
          refine EvalDistEq.trans ?_
            (FiniteGraphSampling.bind_bind_swap
                ($ᵗ LTable : ProbComp LTable) sampleMasterSeed _).symm
          refine EvalDistEq.bind_right _ fun _ => ?_
          refine EvalDistEq.trans ?_ (FiniteGraphSampling.bind_bind_swap
              ($ᵗ LTable : ProbComp LTable)
            ($ᵗ CanonicalGraphLabels) _).symm
          refine EvalDistEq.bind_right _ fun answers => ?_
          refine EvalDistEq.trans ?_
            (FiniteGraphSampling.bind_bind_swap ($ᵗ LTable : ProbComp LTable)
                ($ᵗ Eager.Table) _).symm
          refine EvalDistEq.bind_right _ fun table => ?_
          exact evalDist_rtable_split _
        rw [hsplit]
        exact probEvent_bind_le_of _ _ _ _ fun steps => hsteps steps
      · refine probEvent_bind_le_of _ _ _ _ fun material => ?_
        rw [(FiniteGraphSampling.bind_bind_swap sampleMasterSeed
          ($ᵗ CanonicalGraphLabels) _).prEvent_eq]
        refine probEvent_bind_le_of _ _ _ _ fun answers => ?_
        rw [(FiniteGraphSampling.bind_bind_swap sampleMasterSeed
          ($ᵗ Eager.Table) _).prEvent_eq]
        refine probEvent_bind_le_of _ _ _ _ fun table => ?_
        rw [(FiniteGraphSampling.bind_bind_swap sampleMasterSeed
          ($ᵗ RTable) _).prEvent_eq]
        refine probEvent_bind_le_of _ _ _ _ fun rnd => ?_
        exact marked_hit_le (detRun (internalize adversary) q material answers table rnd)
          (fun result => result.2) q (fun result hresult =>
              costRun_cap_cost_le _ _ _ q result hresult)

/-- Seed elimination for the signer with derived randomizers.

Assume a bound `B` on the seed-free capped win of the internalized memoizing adversary.

The bound holds in the graph-view game with fresh randomizers, for every table of walk steps.

Then the SUF-CMA advantage is at most `B` plus `3 q / 2^256`, for naming the hidden seeds. -/
theorem forgeAdvantage_le_seedFree (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q) (B : ℝ≥0∞)
    (hB : ∀ steps, Pr{let x ← seedFreeExperiment
                        (internalize (Memo.memoAdv adversary)) q steps}[Win x] ≤ B) :
    forgeAdvantage adversary ≤ B + 3 * (q / (2 : ℝ≥0∞) ^ 256) := by
  unfold forgeAdvantage
  calc
    _ = Pr{let result ← experiment adversary}[result.1 = true ∧ result.2 ≤ q] :=
      prEvent_congr_of_support _ _ _ fun result hresult =>
          ⟨fun h => ⟨h, hbound result hresult⟩, And.left⟩
    _ ≤ Pr{let result ← experiment (internalize adversary)}[result.1 = true ∧ result.2 ≤ q] :=
        budgetedWin_le_internalize adversary q
    _ ≤ Pr{let result ← experimentMaster (internalize adversary)}[result.1 = true ∧ result.2 ≤ q] +
        q / (2 : ℝ≥0∞) ^ 256 :=
      budgetedWin_le_master adversary q
    _ ≤ B + 2 * (q / (2 : ℝ≥0∞) ^ 256) + q / (2 : ℝ≥0∞) ^ 256 :=
      add_le_add (budgetedWinMaster_le_seedFree adversary q B hB) le_rfl
    _ = B + 3 * (q / (2 : ℝ≥0∞) ^ 256) := by ring

end SphincsSecurity.Security.Det
