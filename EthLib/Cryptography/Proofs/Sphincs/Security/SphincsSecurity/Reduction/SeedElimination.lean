module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.WinValue

/-!
# Eliminating the seeds from the game with derived randomizers

The SUF-CMA advantage against the signer with derived randomizers has a bound.

It is the seed-free win probability of the internalized memoizing adversary, under the budget cap.

The bound adds `2 q / 2^256` for a hash call that names a hidden key value.

That value is the secret seed in a derivation input or in a key-seed input.

It can also be the PRF key in a randomizer derivation.

The statement keeps `3 q / 2^256`, the slack that its consumers use.

The eager table splits off an independent uniform table at the PRF key's randomizer derivations.

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

/-- The input derives a randomizer from the given PRF key. -/
def RandHit (input : HashInput) (prf : HashOutput) : Prop :=
  ∃ parameter message, randomizerHashInput prf parameter message = input

omit [Params] in
theorem randHit_unique {input : HashInput} {prf prf' : HashOutput}
    (h : RandHit input prf) (h' : RandHit input prf') : prf = prf' := by
  obtain ⟨parameter, message, heq⟩ := h
  obtain ⟨parameter', message', heq'⟩ := h'
  exact (randomizerHashInput_injective (heq.trans heq'.symm)).1

omit [Params] in
theorem randHit_probability_le (input : HashInput) :
    Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[(RandHit input) x] ≤
      1 / (2 : ℝ≥0∞) ^ 256 := by
  rw [SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter (RandHit input)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro prf hprf prf' hprf'
    exact randHit_unique (Finset.mem_filter.mp hprf).2 (Finset.mem_filter.mp hprf').2
  rw [show Fintype.card HashOutput = 2 ^ 256 by simp [hashOutputBits], Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

/-- The inputs whose answers the seed-free run must not see. -/
def Marked (seed : MasterSeed) (prf : HashOutput) (input : HashInput) : Prop :=
  SeedGuess.SeedHit input seed ∨ RandHit input prf

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

omit [Params] in
theorem trace_marked_probability {S : Type} (secret : ProbComp S) (Bad : S → HashInput → Prop)
    (ε : ℝ≥0∞) (hε : ∀ input, Pr{let s ← secret}[Bad s input] ≤ ε)
    (entries : List (Entry HashInput)) :
    Pr{let s ← secret}[Hits (Bad s) entries] ≤ ordinaryCount entries * ε := by
  induction entries with
  | nil => simp [Hits, ordinaryCount]
  | cons entry rest ih =>
      cases entry with
      | inl input =>
          have hevent : (fun s => Hits (Bad s) (.inl input :: rest)) =
              fun s => Bad s input ∨ Hits (Bad s) rest := by
            funext s
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
          refine (add_le_add (hε input) ih).trans (le_of_eq ?_)
          simp only [ordinaryCount, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          rw [add_comm]
      | inr amount =>
          have hevent : (fun s => Hits (Bad s) (.inr amount :: rest)) =
              fun s => Hits (Bad s) rest := by
            funext s
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

omit [Params] in
/-- A run that does not depend on a hidden secret, with traces of cost at most `q`, names it.

If each input names the secret with chance at most `ε`, the chance of this is at most `q ε`. -/
theorem marked_hit_le {S Ω γ : Type} (secret : ProbComp S) (Bad : S → HashInput → Prop)
    (ε : ℝ≥0∞) (hε : ∀ input, Pr{let s ← secret}[Bad s input] ≤ ε) (program : ProbComp Ω)
    (entries : Ω → List (Entry HashInput)) (q : ℕ)
    (hcost : ∀ result ∈ support program, traceCost (entries result) ≤ q) (pack : S → Ω → γ)
    (event : γ → Prop)
    (hevent : ∀ s result, event (pack s result) → Hits (Bad s) (entries result)) :
    Pr{let x ← secret >>= fun s => pack s <$> program}[event x] ≤ q * ε := by
  calc
    _ = Pr{let x ← program >>= fun result => (fun s => pack s result) <$> secret}[event x] := by
      have h := (FiniteGraphSampling.bind_bind_swap secret program
        (fun s result => (pure (pack s result) : ProbComp γ))).prEvent_eq event
      simpa only [bind_pure_comp] using h
    _ ≤ ∑' result, Pr{let x ← program}[x = result] * (q * ε) := by
      rw [OracleComp.prEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun result => ?_
      by_cases hr : result ∈ support program
      · refine mul_le_mul' le_rfl ?_
        rw [prEvent_map]
        refine (prEvent_mono _ _ _ fun s hs => hevent s result hs).trans ?_
        refine (trace_marked_probability secret Bad ε hε (entries result)).trans ?_
        refine mul_le_mul' ?_ le_rfl
        exact_mod_cast (ordinaryCount_le_traceCost _).trans (hcost result hr)
      · rw [(prEvent_eq_zero_of_not_mem_support _) hr]
        simp
    _ ≤ q * ε := tsum_prob_mul_le _ _

/-! ### Splitting the eager table at the randomizer-derivation inputs of the PRF key -/

/-- The short input that derives the randomizer base of a message. -/
def randIn (prf : HashOutput) (parameter : PublicParameter) (message : Message) : ShortIn :=
  ⟨randomizerHashInput prf parameter message, randomizerHashInput_short prf parameter message⟩

omit [Params] in
theorem randIn_injective {prf : HashOutput} {parameter : PublicParameter}
    {message message' : Message}
    (h : randIn prf parameter message = randIn prf parameter message') :
    message = message' :=
  (randomizerHashInput_injective (congrArg Subtype.val h)).2.2

/-- A table whose randomizer derivations, for a PRF key and a parameter, come from another table. -/
noncomputable def plant (prf : HashOutput) (parameter : PublicParameter) (table : Eager.Table)
    (rnd : RTable) : Eager.Table := fun input =>
  if h : ∃ message : Message, input = randIn prf parameter message then
    rnd (Classical.choose h)
  else table input

omit [Params] in
theorem plant_randIn (prf : HashOutput) (parameter : PublicParameter) (table : Eager.Table)
    (rnd : RTable) (message : Message) :
    plant prf parameter table rnd (randIn prf parameter message) = rnd message := by
  have h : ∃ message' : Message,
      randIn prf parameter message = randIn prf parameter message' := ⟨message, rfl⟩
  rw [plant, dite_eq_left h]
  rw [randIn_injective (Classical.choose_spec h).symm]

omit [Params] in
theorem plant_other (prf : HashOutput) (parameter : PublicParameter) (table : Eager.Table)
    (rnd : RTable) (input : ShortIn) (hinput : ∀ message, input ≠ randIn prf parameter message) :
    plant prf parameter table rnd input = table input := by
  rw [plant, dite_eq_right]
  rintro ⟨message, hmessage⟩
  exact hinput message hmessage

/-- Swap the randomizer entries of a table with an independent randomizer table. -/
noncomputable def swapPair (prf : HashOutput) (parameter : PublicParameter)
    (pair : Eager.Table × RTable) : Eager.Table × RTable :=
  (plant prf parameter pair.1 pair.2, fun message => pair.1 (randIn prf parameter message))

omit [Params] in
theorem swapPair_involutive (prf : HashOutput) (parameter : PublicParameter) :
    Function.Involutive (swapPair prf parameter) := by
  rintro ⟨table, rnd⟩
  simp only [swapPair, plant_randIn, Prod.mk.injEq, and_true]
  funext input
  by_cases h : ∃ message : Message, input = randIn prf parameter message
  · obtain ⟨message, rfl⟩ := h
    rw [plant_randIn]
  · have hother : ∀ message, input ≠ randIn prf parameter message :=
      fun message heq => h ⟨message, heq⟩
    rw [plant_other _ _ _ _ _ hother, plant_other _ _ _ _ _ hother]

noncomputable local instance pairSampleable : SampleableType (Eager.Table × RTable) :=
  SampleableType.ofFintype _

omit [Params] in
/-- A uniform table has the law of a uniform table whose randomizer entries are replaced.

The new entries come from an independent uniform randomizer table. -/
theorem evalDist_table_split {β : Type} (prf : HashOutput) (parameter : PublicParameter)
    (F : Eager.Table → ProbComp β) :
    ($ᵗ Eager.Table : ProbComp Eager.Table) >>= F =ᵈ
      (do
        let table ← ($ᵗ Eager.Table : ProbComp Eager.Table)
        let rnd ← ($ᵗ RTable : ProbComp RTable)
        F (plant prf parameter table rnd)) := by
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
  have hswap : swapPair prf parameter <$>
      ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) =ᵈ
      ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective
        (swapPair_involutive prf parameter).bijective
  calc
    _ =ᵈ (Prod.fst <$> ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable))) >>= F :=
      hfst.symm.bind_left _
    _ =ᵈ ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) >>= fun pair =>
        F pair.1 := by
      rw [bind_map_left]
    _ =ᵈ (swapPair prf parameter <$> ($ᵗ (Eager.Table × RTable) : ProbComp
        (Eager.Table × RTable))) >>=
          fun pair => F pair.1 := hswap.symm.bind_left _
    _ =ᵈ ($ᵗ (Eager.Table × RTable) : ProbComp (Eager.Table × RTable)) >>=
          fun pair => F (plant prf parameter pair.1 pair.2) := by
      rw [bind_map_left]
      simp only [swapPair, EvalDistEq.refl]
    _ =ᵈ (do
          let table ← ($ᵗ Eager.Table : ProbComp Eager.Table)
          let rnd ← ($ᵗ RTable : ProbComp RTable)
          pure (table, rnd)) >>= fun pair => F (plant prf parameter pair.1 pair.2) :=
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

noncomputable local instance detLabelsSampleable' : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable

theorem preparedCache_randomizer (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (prf : HashOutput) (parameter : PublicParameter)
    (message : Message) :
    preparedCache material seed answers (randomizerHashInput prf parameter message) = none := by
  rw [preparedCache_other material seed answers _ (fun position => ?_)]
  · rw [programCache_other ∅ seed material _ (fun h => ?_) (fun h => ?_) (fun position h => ?_)]
    · rfl
    · exact keySeedInput_ne_randomizerHashInput _ _ _ _ _ h.symm
    · exact keySeedInput_ne_randomizerHashInput _ _ _ _ _ h.symm
    · exact randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ h
  · refine randomizerHashInput_ne_tweakableHashInput _ _ _ _ _ ?_
    rw [List.length_flatMap]
    simp only [bytesLE_length, List.map_const', List.sum_replicate, smul_eq_mul]
    omega

theorem sampleFn_randomizer (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels)
    (table : Eager.Table) (rnd : RTable) (message : Message) :
    sampleFn material seed answers (plant (prf material) (SeedModel.parameter material) table rnd)
      (randomizerHashInput (prf material) (SeedModel.parameter material) message) =
        rnd message := by
  unfold sampleFn extend
  rw [preparedCache_randomizer, Option.getD_none, dite_eq_left (randomizerHashInput_short _ _ _)]
  exact plant_randIn _ _ table rnd message

theorem sampleFn_plant_agree (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels)
    (table : Eager.Table) (rnd : RTable) (input : HashInput)
    (hnot : ¬Marked seed (prf material) input) :
    sampleFn material seed answers (plant (prf material) (SeedModel.parameter material) table rnd)
        input =
      graphFn material answers table input := by
  rw [sampleFn_agree _ _ _ _ _ (fun h => hnot (Or.inl h))]
  unfold graphFn extend
  by_cases hshort : IsShort input
  · rw [dite_eq_left hshort, dite_eq_left hshort, plant_other
      (prf material) (SeedModel.parameter material) table rnd
      ⟨input, hshort⟩ fun message heq => hnot (Or.inr
        ⟨SeedModel.parameter material, message, (congrArg Subtype.val heq).symm⟩)]
  · rw [dite_eq_right hshort, dite_eq_right hshort]

/-- Every sample of the internalized deterministic game equals its graph-view cost game. -/
theorem sample_costGameDet (adversary : Adversary) (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) (rnd : RTable) :
    simulateQ (fixedRom (extend (preparedCache material seed answers)
          (plant (prf material) (SeedModel.parameter material) table rnd)))
        (countHashQueries (gameAfterSeedDet adversary seed)) =
      (simulateQ (GraphView.fixedCostSource
          (sampleFn material seed answers
            (plant (prf material) (SeedModel.parameter material) table rnd))
          (sampleCoordinates material seed answers
              (plant (prf material) (SeedModel.parameter material) table rnd)))
        (costGameDet (SeedModel.parameter material)
          (GraphView.publicData (labelsOf material answers) (highsOf rnd)) rnd
          adversary)).run := by
  set table' := plant (prf material) (SeedModel.parameter material) table rnd
  rw [show (extend (preparedCache material seed answers) table') =
      sampleFn material seed answers table' from rfl,
    evalDist_fixedRom_eq_fixedHashWorld, fixedHashWorld_countHashQueries,
    costGameDet_correct (sampleFn material seed answers table') (SeedModel.parameter material) seed
      (GraphView.publicData (labelsOf material answers) (highsOf rnd))
      (sampleCoordinates material seed answers table')
      (GraphView.publicData_correct _ _ _ _ (sample_consistent material seed answers table')
        (sample_boundary material seed answers table') _)
      (GraphView.coordinates_correct _ _ _ _ (sample_consistent material seed answers table'))
      (sample_parameter material seed answers table') (prf material)
      (eval_prf_prepared _ seed material (sample_agreement material seed answers table')) rnd
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
          (plant (prf material) (SeedModel.parameter material) table rnd)))
          (countHashQueries (gameAfterSeedDet adversary seed)))}[result.1 = true ∧ result.2 ≤ q] ≤
      Pr{let x ← detRun adversary q material answers table rnd}[Win x] +
        Pr{let result ← detRun adversary q material answers table rnd}[Hits
            (Marked seed (prf material)) result.2] := by
  set table' := plant (prf material) (SeedModel.parameter material) table rnd
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
      (graphCoordinates material answers) (Marked seed (prf material))
      (sampleFn_plant_agree material seed answers table rnd) _ Win

/-! ### The whole game -/

theorem noRepeat_internalize_memoAdv (adversary : Adversary) :
    (Memo.memoAdv (internalize adversary)).NoRepeat := by
  rw [← Memo.internalize_memoAdv]
  exact ForsPotential.noRepeat_internalize_adversary _ (Memo.memoAdv_noRepeat adversary)

attribute [local irreducible] experiment sampleMasterSeed

/-- Seed elimination from a uniform `SK.seed`.

Assume a bound `B` on the seed-free capped win of the internalized memoizing adversary.

The bound holds in the graph-view game with fresh randomizers, for every table of walk steps.

Start the internalized game from a uniform `SK.seed`.

Then its capped win is at most `B` plus `2 q / 2^256`, for naming `SK.seed` or `SK.prf`.

The proof fixes the step halves and averages the base randomizers. -/
theorem budgetedWinMaster_le_seedFree (adversary : Adversary) (q : Nat) (B : ℝ≥0∞)
    (hB : ∀ steps, Pr{let x ← seedFreeExperiment
                        (internalize (Memo.memoAdv adversary)) q steps}[Win x] ≤ B) :
    Pr{let result ← experiment (internalize adversary)}[result.1 = true ∧ result.2 ≤ q] ≤ B +
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
      (evalDist_experiment_fixed adversary).prEvent_eq _
    _ = Pr{let result ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          simulateQ (fixedRom (extend (preparedCache material seed answers)
              (plant (prf material) (SeedModel.parameter material) table rnd)))
            (countHashQueries (gameAfterSeedDet (internalize adversary) seed)))}[result.1 = true ∧
                result.2 ≤ q] := by
      refine EvalDistEq.prEvent_eq ?_ _
      refine EvalDistEq.bind_right _ fun material => EvalDistEq.bind_right _ fun seed =>
        EvalDistEq.bind_right _ fun answers => ?_
      exact evalDist_table_split (prf material) (SeedModel.parameter material) _
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
          (fun result => ((seed, prf material), result)) <$> detRun
              (internalize adversary) q material answers table rnd)}[Hits
              (Marked pair.1.1 pair.1.2) pair.2.2] := by
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun material => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun seed => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun answers => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun table => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun rnd => ?_
      rw [prEvent_map]
      exact per_sampleDet (internalize adversary) q material seed answers table rnd
    _ ≤ B + (q / (2 : ℝ≥0∞) ^ 256 + q / (2 : ℝ≥0∞) ^ 256) := by
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
      · refine le_trans (prEvent_mono_of_support _ _ (fun pair :
            (MasterSeed × HashOutput) × (Option Bool × List (Entry HashInput)) =>
            Hits (fun input => SeedGuess.SeedHit input pair.1.1) pair.2.2 ∨
              Hits (fun input => RandHit input pair.1.2) pair.2.2) fun pair _ hpair => ?_)
          ((prEvent_or_le _ _ _).trans (add_le_add ?_ ?_))
        · obtain ⟨input, hmem, hinput | hinput⟩ := hpair
          · exact Or.inl ⟨input, hmem, hinput⟩
          · exact Or.inr ⟨input, hmem, hinput⟩
        · -- The secret seed is drawn independently of the seed-free run.
          refine probEvent_bind_le_of _ _ _ _ fun material => ?_
          rw [(FiniteGraphSampling.bind_bind_swap sampleMasterSeed
            ($ᵗ CanonicalGraphLabels) _).prEvent_eq]
          refine probEvent_bind_le_of _ _ _ _ fun answers => ?_
          rw [(FiniteGraphSampling.bind_bind_swap sampleMasterSeed
            ($ᵗ Eager.Table) _).prEvent_eq]
          refine probEvent_bind_le_of _ _ _ _ fun table => ?_
          rw [(FiniteGraphSampling.bind_bind_swap sampleMasterSeed
            ($ᵗ RTable) _).prEvent_eq]
          refine probEvent_bind_le_of _ _ _ _ fun rnd => ?_
          refine le_trans (marked_hit_le sampleMasterSeed
            (fun seed input => SeedGuess.SeedHit input seed)
            (1 / (2 : ℝ≥0∞) ^ 256) SeedGuess.seedHit_probability_le
            (detRun (internalize adversary) q material answers table rnd) (fun result => result.2) q
            (fun result hresult => costRun_cap_cost_le _ _ _ q result hresult)
            (fun seed result => ((seed, prf material), result)) _ (fun _ _ h => h)) (le_of_eq ?_)
          rw [mul_one_div]
        · -- The PRF key is drawn last in the material, and the seed-free run never reads it.
          simp only [sampleMaterial, bind_assoc, pure_bind]
          refine probEvent_bind_le_of _ _ _ _ fun parameterOutput => ?_
          refine probEvent_bind_le_of _ _ _ _ fun outputs => ?_
          have hprog : ∀ key : HashOutput, (do
              let seed ← sampleMasterSeed
              let answers ← $ᵗ CanonicalGraphLabels
              let table ← $ᵗ Eager.Table
              let rnd ← $ᵗ RTable
              (fun result => ((seed, prf ((parameterOutput, key), outputs)), result)) <$>
                detRun (internalize adversary) q ((parameterOutput, key), outputs) answers table
                  rnd :
                ProbComp ((MasterSeed × HashOutput) × (Option Bool × List (Entry HashInput)))) =
              (fun pair => ((pair.1, key), pair.2)) <$> (do
                let seed ← sampleMasterSeed
                let answers ← $ᵗ CanonicalGraphLabels
                let table ← $ᵗ Eager.Table
                let rnd ← $ᵗ RTable
                (fun result => (seed, result)) <$>
                  detRun (internalize adversary) q ((parameterOutput, 0), outputs) answers table
                    rnd) := by
            intro key
            simp only [map_bind, Functor.map_map]
            -- The run reads no PRF key from the material, so both sides unfold to the same run.
            rfl
          simp only [hprog]
          have hcost : ∀ pair ∈ support (do
                let seed ← sampleMasterSeed
                let answers ← $ᵗ CanonicalGraphLabels
                let table ← $ᵗ Eager.Table
                let rnd ← $ᵗ RTable
                (fun result => (seed, result)) <$>
                  detRun (internalize adversary) q ((parameterOutput, 0), outputs) answers table
                    rnd :
                ProbComp (MasterSeed × (Option Bool × List (Entry HashInput)))),
              traceCost pair.2.2 ≤ q := by
            intro pair hpair
            simp only [mem_support_bind_iff, support_map, Set.mem_image] at hpair
            obtain ⟨_, _, _, _, _, _, _, _, result, hresult, rfl⟩ := hpair
            exact costRun_cap_cost_le _ _ _ q result hresult
          exact le_trans (marked_hit_le (S := HashOutput)
            (Ω := MasterSeed × (Option Bool × List (Entry HashInput)))
            ($ᵗ HashOutput) (fun key input => RandHit input key)
            (1 / (2 : ℝ≥0∞) ^ 256) randHit_probability_le _ (fun pair => pair.2.2) q hcost
            (fun key pair => ((pair.1, key), pair.2)) _ (fun _ _ h => h))
            (le_of_eq (mul_one_div _ _))
    _ = B + 2 * (q / (2 : ℝ≥0∞) ^ 256) := by rw [two_mul]

/-- Seed elimination for the signer with derived randomizers.

Assume a bound `B` on the seed-free capped win of the internalized memoizing adversary.

The bound holds in the graph-view game with fresh randomizers, for every table of walk steps.

Then the SUF-CMA advantage is at most `B` plus `2 q / 2^256`, for naming the seed or the PRF key.

The statement keeps `3 q / 2^256`, the slack that its consumers use. -/
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
    _ ≤ B + 2 * (q / (2 : ℝ≥0∞) ^ 256) := budgetedWinMaster_le_seedFree adversary q B hB
    _ ≤ B + 3 * (q / (2 : ℝ≥0∞) ^ 256) :=
      add_le_add le_rfl (mul_le_mul' (by norm_num) le_rfl)

end SphincsSecurity.Security.Det
