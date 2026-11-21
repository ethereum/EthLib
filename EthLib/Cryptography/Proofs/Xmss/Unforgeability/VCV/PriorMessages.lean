module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PriorIncidence

/-!
# The finite family of active messages at one signing key

A finder can select an initially occupied row only if its exact input occurs in the physical footprint.
Other messages contribute zero, including when a later fresh trial introduces them into the family.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open Constants HashSig OracleComp OracleSpec CachedCodeword PostSigning randomOracle.Partners
open scoped ENNReal

open Classical in
/-- Recover a message only from a full, validly encoded input at this layer and OTS key. -/
noncomputable def messageOfInput (pp : PublicParam) (l : Layer) (e : UInt32) (a : HashInput) :
    Option ByteArray :=
  if h : ∃ m, ∃ r, trialInput pp l e m r = a then some h.choose else none

/-- The finite footprint determines the finite set of messages whose initial selections can count. -/
noncomputable def activeMessages (pp : PublicParam) (l : Layer) (e : UInt32) (seen : Finset HashInput) :=
  seen.biUnion fun a => (messageOfInput pp l e a).toFinset

private theorem trial_mem (pp : PublicParam) (l : Layer) (e : UInt32) (seen : Finset HashInput)
    (m : ByteArray) (r : Randomizer) (hw : trialInput pp l e m r ∈ seen) :
    m ∈ activeMessages pp l e seen := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨_, hw, ?_⟩
  have has : ∃ n s, trialInput pp l e n s = trialInput pp l e m r := ⟨m, r, rfl⟩
  obtain ⟨s, eq⟩ := has.choose_spec
  simp [messageOfInput, has, (trial_message_randomizer eq).1]

private theorem monotone_messages (pp : PublicParam) (l : Layer) (e : UInt32)
    {s t : Finset HashInput} (le : s ⊆ t) :
    activeMessages pp l e s ⊆ activeMessages pp l e t := by
  intro m hm
  obtain ⟨a, ha, atKey⟩ := Finset.mem_biUnion.mp hm
  exact Finset.mem_biUnion.mpr ⟨a, le ha, atKey⟩

private theorem noStored (pp : PublicParam) (l : Layer) (e : UInt32) (cache : HashSpec.QueryCache)
    (seen : Finset HashInput) (covers : ∀ b w, cache b = some w → b ∈ seen)
    {m : ByteArray} (absent : m ∉ activeMessages pp l e seen) (r : Randomizer) :
    cache (trialInput pp l e m r) = none := by
  cases h : cache (trialInput pp l e m r) with
  | none => rfl
  | some w => exact (absent (trial_mem pp l e seen m r (covers _ w h))).elim

set_option maxRecDepth 4096 in
/-- Adding messages outside the initial footprint preserves both initial selection masses exactly. -/
theorem selections_active (pp : PublicParam) (l : Layer) (e : UInt32) (c fuel : Nat)
    (cache : HashSpec.QueryCache) (seen more : Finset HashInput) (le : seen ⊆ more)
    (covers : ∀ b w, cache b = some w → b ∈ seen) :
    let active := fun s => activeMessages pp l e s ×ˢ (Finset.univ : Finset Randomizer)
    occupiedSelections pp l e (active seen) c fuel cache = occupiedSelections pp l e (active more) c fuel cache ∧
    partneredSelections pp l e (active seen) c fuel cache = partneredSelections pp l e (active more) c fuel cache := by
  classical
  intro active
  have sub : active seen ⊆ active more := by
    apply Finset.product_subset_product (monotone_messages pp l e le) (Finset.Subset.refl _)
  have outside (i : ByteArray × Randomizer) (ne : i ∉ active seen) : i.1 ∉ activeMessages pp l e seen :=
    fun mem => ne (Finset.mem_product.mpr ⟨mem, Finset.mem_univ i.2⟩)
  constructor
  · apply Finset.sum_subset sub
    intro i hi ne
    apply prEvent_eq_zero_of_forall_mem_support
    rintro _ _ ⟨r, hr, _⟩
    have missing := noStored pp l e cache seen covers (outside i ne) r
    simp [validRows, missing] at hr
  · apply Finset.sum_subset sub
    intro i hi ne
    apply prEvent_eq_zero_of_forall_mem_support
    rintro _ _ ⟨r, _, w, hw, _⟩
    rw [noStored pp l e cache seen covers (outside i ne) r] at hw
    contradiction

/-- The one-query compensator applies to the evolving set of all messages with physical cache rows. -/
theorem compensate_active (pp : PublicParam) (l : Layer) (e : UInt32) (c fuel : Nat)
    (within : c + fuel ≤ 2 ^ 32) (cache : HashSpec.QueryCache) (seen : Finset HashInput)
    (covers : ∀ b w, cache b = some w → b ∈ seen) (a : HashInput)
    (addr : messageKey pp a = some (l, e)) (cold : cache a = none) :
    let p : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    let ε : ℝ≥0∞ := 1 / 2 ^ 128
    let H := fun s => occupiedSelections pp l e (activeMessages pp l e s ×ˢ Finset.univ) c fuel
    let Φ := fun s => partneredSelections pp l e (activeMessages pp l e s ×ˢ Finset.univ) c fuel
    let V := fun store hist => ((validInputs pp l e store hist).card : ℝ≥0∞)
    let update := fun v => cache.cacheQuery a v
    let after := insert a seen
    p * freshMean (fun v => Φ after (update v)) + ε * (V cache seen * H seen cache) ≤
      p * Φ seen cache + ε * freshMean (fun v => V (update v) after * H after (update v)) := by
  dsimp only
  have agrees := selections_active pp l e c fuel cache seen (insert a seen) (Finset.subset_insert ..) covers
  rw [agrees.1, agrees.2]
  exact compensate_finders pp l e _ c fuel within cache seen covers a addr cold

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest
