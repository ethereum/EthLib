module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Penalties

/-!
# The reserved replay of a branch

The initial ownership of a window, and the reserved replay of each balance event.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

section

open Cryptography.Bls

/-- The initial ownership: the units of the four initial pots, each owned by its key.

Pots 0 and 1 count over the registry and pots 2 and 3 over the pending consolidations. -/
def initialOwnership (x : ForkedBeaconState preset) (high : Nat) : Ownership :=
  let block := fun p idx => (Finset.range (initialPot x high p idx).2).image
    (TokenOrigin.initial p idx)
  let pot := fun p => (Finset.range (if p < 2 then x.state.validators.data.size
    else (pendingQueue x).length)).biUnion (block p)
  let issued := pot 0 ∪ pot 1 ∪ pot 2 ∪ pot 3
  { issued := issued
    owner := fun token => match token with
      | .initial p idx _ => if token ∈ issued then some (initialPot x high p idx).1 else none
      | _ => none
    endpoint := pot 0 ∪ pot 1
    original := fun i => if (x.state.validators.data[i]?).any (fun v =>
      isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
        v.exitEpoch == FAR_FUTURE_EPOCH) then effectiveAt x i else 0
    retired := ∅ }

/-- A token of the initial ownership is a unit of one pot entry, below its bound. -/
private theorem mem_initialOwnership {x : ForkedBeaconState preset} {high : Nat}
    {token : TokenOrigin} :
    token ∈ (initialOwnership x high).issued ↔ ∃ p idx unit, p < 4 ∧
      idx < (if p < 2 then x.state.validators.data.size else (pendingQueue x).length) ∧
      unit < (initialPot x high p idx).2 ∧ token = .initial p idx unit := by
  simp only [initialOwnership, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image]
  constructor
  · rintro (((⟨idx, inside, unit, below, rfl⟩ | ⟨idx, inside, unit, below, rfl⟩) |
      ⟨idx, inside, unit, below, rfl⟩) | ⟨idx, inside, unit, below, rfl⟩)
    · exact ⟨0, idx, unit, by omega, inside, below, rfl⟩
    · exact ⟨1, idx, unit, by omega, inside, below, rfl⟩
    · exact ⟨2, idx, unit, by omega, inside, below, rfl⟩
    · exact ⟨3, idx, unit, by omega, inside, below, rfl⟩
  · rintro ⟨p, idx, unit, small, inside, below, rfl⟩
    have cases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact .inl (.inl (.inl ⟨idx, inside, unit, below, rfl⟩))
    · exact .inl (.inl (.inr ⟨idx, inside, unit, below, rfl⟩))
    · exact .inl (.inr ⟨idx, inside, unit, below, rfl⟩)
    · exact .inr ⟨idx, inside, unit, below, rfl⟩

/-- An issued token of the initial ownership is owned by its pot entry's key. -/
private theorem initialOwnership_owner {x : ForkedBeaconState preset} {high p idx unit : Nat}
    (issued : TokenOrigin.initial p idx unit ∈ (initialOwnership x high).issued) :
    (initialOwnership x high).owner (.initial p idx unit) = some (initialPot x high p idx).1 := by
  show (if TokenOrigin.initial p idx unit ∈ (initialOwnership x high).issued then
    some (initialPot x high p idx).1 else none) = _
  simp only [issued, ↓reduceIte]

/-- One pot entry's units are held by its owner, and pots 0 and 1 are at the endpoint. -/
private theorem initialOwnership_block {x : ForkedBeaconState preset} {high : Nat}
    {p idx : Nat} (small : p < 4)
    (inside : idx < (if p < 2 then x.state.validators.data.size else (pendingQueue x).length)) :
    (Finset.range (initialPot x high p idx).2).image (TokenOrigin.initial p idx) ⊆
        held (initialOwnership x high) (initialPot x high p idx).1 ∧
      (p < 2 → (Finset.range (initialPot x high p idx).2).image (TokenOrigin.initial p idx) ⊆
        (initialOwnership x high).endpoint) ∧
      ((Finset.range (initialPot x high p idx).2).image (TokenOrigin.initial p idx)).card =
        (initialPot x high p idx).2 := by
  have issued : ∀ unit < (initialPot x high p idx).2,
      TokenOrigin.initial p idx unit ∈ (initialOwnership x high).issued := fun unit below =>
    mem_initialOwnership.mpr ⟨p, idx, unit, small, inside, below, rfl⟩
  refine ⟨fun token member => ?_, fun front token member => ?_, ?_⟩
  · obtain ⟨unit, below, rfl⟩ := Finset.mem_image.mp member
    have inIssued := issued unit (Finset.mem_range.mp below)
    exact Finset.mem_filter.mpr ⟨inIssued, initialOwnership_owner inIssued⟩
  · obtain ⟨unit, below, rfl⟩ := Finset.mem_image.mp member
    have front' : p = 0 ∨ p = 1 := by omega
    simp only [initialOwnership, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_image]
    rcases front' with rfl | rfl
    · exact .inl ⟨idx, inside, unit, Finset.mem_range.mp below, rfl⟩
    · exact .inr ⟨idx, inside, unit, Finset.mem_range.mp below, rfl⟩
  · rw [Finset.card_image_of_injective _ (fun a b (same : TokenOrigin.initial p idx a =
      TokenOrigin.initial p idx b) => by injection same), Finset.card_range]

/-- The initial ownership is valid: owners are issued, and endpoint tokens are issued and owned. -/
private theorem initialOwnership_valid (x : ForkedBeaconState preset) (high : Nat) :
    OwnershipValid (initialOwnership x high) := by
  have endpoint : (initialOwnership x high).endpoint ⊆ (initialOwnership x high).issued := by
    intro token member
    simp only [initialOwnership, Finset.mem_union] at member ⊢
    rcases member with front | front
    · exact .inl (.inl (.inl front))
    · exact .inl (.inl (.inr front))
  refine ⟨fun token owned => ?_, endpoint, fun token member => ?_⟩
  · cases token with
    | initial p idx unit =>
      by_contra absent
      have none : (initialOwnership x high).owner (.initial p idx unit) = none := by
        show (if TokenOrigin.initial p idx unit ∈ (initialOwnership x high).issued then
          some (initialPot x high p idx).1 else none) = none
        simp only [absent, ↓reduceIte]
      simp [none] at owned
    | credit => simp [initialOwnership] at owned
    | released => simp [initialOwnership] at owned
  · obtain ⟨p, idx, unit, _, _, _, rfl⟩ := mem_initialOwnership.mp (endpoint member)
    simp [initialOwnership_owner (endpoint member)]

/-- The initial ownership issues one token per unit of each of its pots.

Its first pot is the capped excess of the keys active at `x`.

For each key it is its balance capped at its largest effective balance, minus its effective balance.

The next two are the pre-active stake `Pre` and the due consolidation credits `Pi_c`.

The last is the excess of the pending sources inactive at `x` and withdrawable in the window.

So it issues at most their sum. -/
private theorem initialOwnership_card {x : ForkedBeaconState preset} (high : Nat)
    (early : x.fork < .glamsterdam) :
    (initialOwnership x high).issued.card ≤ initialCappedExcess x + preActiveStake x +
        dueConsolidationCredits x (driftHorizon x high) + pendingSourceExcess x high := by
  have potCard : ∀ p, ((Finset.range (if p < 2 then x.state.validators.data.size
      else (pendingQueue x).length)).biUnion fun idx =>
        (Finset.range (initialPot x high p idx).2).image (TokenOrigin.initial p idx)).card ≤
      ∑ idx ∈ Finset.range (if p < 2 then x.state.validators.data.size
        else (pendingQueue x).length), (initialPot x high p idx).2 := fun p =>
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun idx _ =>
      Finset.card_image_le.trans (Finset.card_range _).le)
  have total : (initialOwnership x high).issued.card ≤
      (∑ i ∈ Finset.range x.state.validators.data.size, (initialPot x high 0 i).2) +
      (∑ i ∈ Finset.range x.state.validators.data.size, (initialPot x high 1 i).2) +
      (∑ j ∈ Finset.range (pendingQueue x).length, (initialPot x high 2 j).2) +
      (∑ j ∈ Finset.range (pendingQueue x).length, (initialPot x high 3 j).2) := by
    have zero := potCard 0
    have one := potCard 1
    have two := potCard 2
    have three := potCard 3
    simp only [show (0 : Nat) < 2 from by decide, show (1 : Nat) < 2 from by decide,
      show ¬ (2 : Nat) < 2 from by decide, show ¬ (3 : Nat) < 2 from by decide,
      ↓reduceIte] at zero one two three
    simp only [initialOwnership]
    refine (Finset.card_union_le _ _).trans ?_
    refine (Nat.add_le_add_right ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
      (Finset.card_union_le _ _) _)) _).trans ?_
    simp only [show (0 : Nat) < 2 from by decide, show (1 : Nat) < 2 from by decide,
      show ¬ (2 : Nat) < 2 from by decide, show ¬ (3 : Nat) < 2 from by decide, ↓reduceIte]
    omega
  -- Pot 0: the active excess, with each balance capped.
  have excess : (∑ i ∈ Finset.range x.state.validators.data.size, (initialPot x high 0 i).2) ≤
      initialCappedExcess x := by
    have rewrite : (∑ i ∈ Finset.range x.state.validators.data.size, (initialPot x high 0 i).2) =
        ∑ i ∈ (Finset.range x.state.validators.data.size).filter (fun i =>
          (x.state.validators.data[i]?).any fun v =>
            isActiveValidator v (getCurrentEpoch x.state)),
          (potential x i - effectiveAt x i) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => by simp [initialPot]
    rw [rewrite]
    apply initial_active_sum_le _ early _ fun i => potential x i - effectiveAt x i
    intro i member
    obtain ⟨_, active⟩ := Finset.mem_filter.mp member
    cases found : x.state.validators.data[i]? with
    | none => simp [found] at active
    | some v => exact ⟨v, rfl, by simpa [found] using active⟩
  -- Pot 1: the stake of keys neither active nor exited.
  have pre : (∑ i ∈ Finset.range x.state.validators.data.size, (initialPot x high 1 i).2) ≤
      preActiveStake x := by
    unfold preActiveStake
    rw [funding_sum_zipIdx x.state.validators.data.toList fun v i =>
      if !isActiveValidator v (getCurrentEpoch x.state) &&
          decide (getCurrentEpoch x.state < v.exitEpoch) then
        max (effectiveAt x i)
          (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
      else 0, Array.length_toList]
    refine Finset.sum_le_sum fun i _ => ?_
    cases found : x.state.validators.data[i]? with
    | none => simp [initialPot, found]
    | some v => simp [initialPot, found, potential, effectiveAt]
  -- Pots 2 and 3: the due pending principal and the due inactive headroom.
  have pending : (∑ j ∈ Finset.range (pendingQueue x).length, (initialPot x high 2 j).2) ≤
      dueConsolidationCredits x (driftHorizon x high) ∧
      (∑ j ∈ Finset.range (pendingQueue x).length, (initialPot x high 3 j).2) ≤
          pendingSourceExcess x high := by
    by_cases electra : .pectra ≤ x.fork
    · have queue : pendingQueue x = (x.state.pendingConsolidations electra).data.toList := by
        simp [pendingQueue, electra]
      unfold dueConsolidationCredits pendingSourceExcess
      simp only [electra, ↓reduceDIte]
      rw [list_map_sum_range, list_map_sum_range, ← queue]
      constructor
      · refine Finset.sum_le_sum fun j _ => ?_
        cases entry : (pendingQueue x)[j]? with
        | none => simp [initialPot, entry]
        | some c =>
          cases found : x.state.validators.data[c.sourceIndex.toNat]? with
          | none => simp [initialPot, entry, found]
          | some v => simp [initialPot, entry, found, horizonEnd]
      · refine Finset.sum_le_sum fun j _ => ?_
        cases entry : (pendingQueue x)[j]? with
        | none => simp [initialPot, entry]
        | some c =>
          cases found : x.state.validators.data[c.sourceIndex.toNat]? with
          | none => simp [initialPot, entry, found]
          | some v =>
            simp only [initialPot, entry, found, Option.map_some, Option.getD_some]
            split_ifs <;> simp_all
    · have empty : pendingQueue x = [] := by simp [pendingQueue, electra]
      simp [empty]
  omega

/-- Two disjoint parts of a held set count separately. -/
private theorem card_add_le_of_disjoint {A B H : Finset TokenOrigin} (left : A ⊆ H) (right : B ⊆ H)
    (apart : Disjoint A B) : A.card + B.card ≤ H.card := by
  rw [← Finset.card_union_of_disjoint apart]
  exact Finset.card_le_card (Finset.union_subset left right)

/-- Units of different pots are different tokens. -/
private theorem initialPot_blocks_disjoint {x : ForkedBeaconState preset} {high p q a b : Nat}
    (differ : p ≠ q) :
    Disjoint ((Finset.range (initialPot x high p a).2).image (TokenOrigin.initial p a))
      ((Finset.range (initialPot x high q b).2).image (TokenOrigin.initial q b)) := by
  refine Finset.disjoint_left.mpr fun token left right => ?_
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp left
  obtain ⟨_, _, same⟩ := Finset.mem_image.mp right
  injection same with same
  exact differ same.symm

/-- A key supported at the current epoch is active at the current or the previous epoch. -/
private theorem supportedAt_current {x : ForkedBeaconState preset} {v : Validator}
    (supported : SupportedAt (getCurrentEpoch x.state) v) :
    isActiveValidator v (getCurrentEpoch x.state) = true ∨
      isActiveValidator v (getPreviousEpoch x.state) = true := by
  rcases supported.2 with current | previous
  · exact .inl current
  · right
    by_cases zero : (getCurrentEpoch x.state).toNat = 0
    · -- At epoch zero the epoch before wraps to the largest epoch, where no key is active.
      exfalso
      have equal : getCurrentEpoch x.state = 0 := UInt64.toNat_inj.mp zero
      have bound := v.exitEpoch.toNat_lt
      simp only [isActiveValidator, equal, Bool.and_eq_true, decide_eq_true_eq,
        UInt64.lt_iff_toNat_lt] at previous
      have wrapped : ((0 : UInt64) - 1).toNat = 2 ^ 64 - 1 := by decide
      omega
    · have equal : getPreviousEpoch x.state = getCurrentEpoch x.state - 1 := by
        apply UInt64.toNat_inj.mp
        rw [getPreviousEpoch_toNat, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr
          (by simp; omega))]
        simp
      rw [equal]
      exact previous

/-- The capped excess of an active key at the start is held at its endpoint.

It is the key's balance capped at its largest effective balance, minus its effective balance. -/
private theorem initialOwnership_excess {x : ForkedBeaconState preset} {high i : Nat}
    {v : Validator} (found : x.state.validators.data[i]? = some v)
    (active : isActiveValidator v (getCurrentEpoch x.state) = true) :
    potential x i - effectiveAt x i ≤
      (held (initialOwnership x high) i ∩ (initialOwnership x high).endpoint).card := by
    have inside : i < x.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
    obtain ⟨heldIn, front, size⟩ := initialOwnership_block (x := x) (high := high) (p := 0)
      (idx := i) (by omega) (by simpa using inside)
    have value : initialPot x high 0 i =
        (i, potential x i - effectiveAt x i) := by simp [initialPot, found, active]
    have owner : (initialPot x high 0 i).1 = i := by rw [value]
    have units : (initialPot x high 0 i).2 = potential x i - effectiveAt x i := by
      rw [value]
    rw [owner] at heldIn
    have bound := Finset.card_le_card (Finset.subset_inter heldIn (front (by omega)))
    omega

/-- A key still to activate at the start holds its potential at its endpoint. -/
private theorem initialOwnership_potential {x : ForkedBeaconState preset} {high i : Nat}
    {v : Validator} (found : x.state.validators.data[i]? = some v)
    (quiet : isActiveValidator v (getCurrentEpoch x.state) = false)
    (notExited : getCurrentEpoch x.state < v.exitEpoch) :
    max v.effectiveBalance.toNat
        (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat) ≤
      (held (initialOwnership x high) i ∩ (initialOwnership x high).endpoint).card := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨oneHeld, front, oneSize⟩ := initialOwnership_block (x := x) (high := high) (p := 1)
    (idx := i) (by omega) (by simpa using inside)
  have value : initialPot x high 1 i = (i, max v.effectiveBalance.toNat
      (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)) := by
    simp [initialPot, found, quiet, notExited, potential]
  have owner : (initialPot x high 1 i).1 = i := by rw [value]
  have units := congrArg Prod.snd value
  rw [owner] at oneHeld
  have bound := Finset.card_le_card (Finset.subset_inter oneHeld (front (by omega)))
  simp only at units
  omega

/-- An unslashed key active at the start is supported at its effective balance. -/
private theorem initialOwnership_weight {g x : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) {i : Nat} {v : Validator}
    (found : x.state.validators.data[i]? = some v)
    (now : isActiveValidator v (getCurrentEpoch x.state) = true) (clean : v.slashed = false) :
    Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey =
      v.effectiveBalance.toNat := by
  have within := x.state.validators.bound early
  have unique := shared.pubkeysDistinct genesis
  have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have back := toNat_toUInt64_of_lt within inside
  have keyAt : v.pubkey ∈ keysAt x.state (getActiveValidatorIndices x.state
      (getCurrentEpoch x.state)) := by
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
    exact ⟨i.toUInt64, (mem_getActiveValidatorIndices within).mpr
      ⟨v, by rw [back]; exact found, now⟩, by simp [back, found]⟩
  have unslashed : v.pubkey ∈ unslashedKeys x.state :=
    Finset.mem_filter.mpr ⟨keyAt, not_slashedAt unique member clean⟩
  simp [Models.supported, unslashed, effectiveWeight_of_member unique member]

/-- The initial ownership of a window: the four initial pots, each unit owned by its key.

It meets the initial ownership facts and the reserve cut at `x` itself.

The reserve cut reads the actual pending queue.

Each clause reads at most two pot entries of one key.

The entries are its capped excess, its potential, and its due pending principal and headroom. -/
theorem initialOwnership_exists {g x : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) (high : Nat) :
    ∃ owned : Ownership, owned = initialOwnership x high ∧ OwnedInitial x high owned ∧
      ReserveCut x high x (getCurrentEpoch x.state) (pendingQueue x) owned := by
  have valid := initialOwnership_valid x high
  have within := x.state.validators.bound early
  have unique := shared.pubkeysDistinct genesis
  -- The capped excess of an active key is held at its endpoint.
  have excess : ∀ i v, x.state.validators.data[i]? = some v →
      isActiveValidator v (getCurrentEpoch x.state) = true →
      potential x i - effectiveAt x i ≤
        (held (initialOwnership x high) i ∩ (initialOwnership x high).endpoint).card :=
    fun _ _ found active => initialOwnership_excess found active
  -- A due pending source holds at least its balance, up to its cap.
  have pendingHeld : ∀ (j : Nat) (c : PendingConsolidation) (v : Validator),
      (pendingQueue x)[j]? = some c →
      x.state.validators.data[c.sourceIndex.toNat]? = some v →
      v.withdrawableEpoch.toNat ≤ horizonEnd x high →
      min (actualBalanceAt x c.sourceIndex.toNat)
        (withdrawalMaxEffectiveBalance preset x.fork v).toNat ≤
        (held (initialOwnership x high) c.sourceIndex.toNat).card := by
    intro j c v entry found due
    have queued : j < (pendingQueue x).length := (List.getElem?_eq_some_iff.mp entry).1
    have effective : effectiveAt x c.sourceIndex.toNat = v.effectiveBalance.toNat := by
      simp [effectiveAt, found]
    obtain ⟨twoHeld, _, twoSize⟩ := initialOwnership_block (x := x) (high := high) (p := 2)
      (idx := j) (by omega) (by simpa using queued)
    have twoValue : initialPot x high 2 j = (c.sourceIndex.toNat,
        min (actualBalanceAt x c.sourceIndex.toNat) v.effectiveBalance.toNat) := by
      simp [initialPot, entry, found, due]
    have twoOwner : (initialPot x high 2 j).1 = c.sourceIndex.toNat := by rw [twoValue]
    have twoUnits := congrArg Prod.snd twoValue
    rw [twoOwner] at twoHeld
    by_cases active : isActiveValidator v (getCurrentEpoch x.state) = true
    · have inside := (Array.getElem?_eq_some_iff.mp found).1
      obtain ⟨zeroHeld, _, zeroSize⟩ := initialOwnership_block (x := x) (high := high) (p := 0)
        (idx := c.sourceIndex.toNat) (by omega) (by simpa using inside)
      have zeroValue : initialPot x high 0 c.sourceIndex.toNat = (c.sourceIndex.toNat,
          potential x c.sourceIndex.toNat - effectiveAt x c.sourceIndex.toNat) := by
        simp [initialPot, found, active]
      have capped : potential x c.sourceIndex.toNat = max v.effectiveBalance.toNat
          (min (actualBalanceAt x c.sourceIndex.toNat)
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat) := by
        simp only [potential, found, Option.map_some, Option.getD_some]
      have zeroOwner : (initialPot x high 0 c.sourceIndex.toNat).1 =
          c.sourceIndex.toNat := by rw [zeroValue]
      have zeroUnits := congrArg Prod.snd zeroValue
      rw [zeroOwner] at zeroHeld
      have both := card_add_le_of_disjoint twoHeld zeroHeld
        (initialPot_blocks_disjoint (x := x) (high := high) (by decide : (2 : Nat) ≠ 0))
      simp only at twoUnits zeroUnits
      omega
    · obtain ⟨threeHeld, _, threeSize⟩ := initialOwnership_block (x := x) (high := high)
        (p := 3) (idx := j) (by omega) (by simpa using queued)
      have threeValue : initialPot x high 3 j = (c.sourceIndex.toNat,
          min (actualBalanceAt x c.sourceIndex.toNat)
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat - v.effectiveBalance.toNat) := by
        simp [initialPot, entry, found, due, active]
      have threeOwner : (initialPot x high 3 j).1 =
          c.sourceIndex.toNat := by rw [threeValue]
      have threeUnits := congrArg Prod.snd threeValue
      rw [threeOwner] at threeHeld
      have both := card_add_le_of_disjoint twoHeld threeHeld
        (initialPot_blocks_disjoint (x := x) (high := high) (by decide : (2 : Nat) ≠ 3))
      simp only at twoUnits threeUnits
      omega
  -- An active key's capped stake sits below its effective balance plus its endpoint tokens.
  have inter : ∀ i, (held (initialOwnership x high) i ∩ (initialOwnership x high).endpoint).card ≤
      (held (initialOwnership x high) i).card := fun i =>
    Finset.card_le_card Finset.inter_subset_left
  have read : ∀ {i : Nat} {v w : Validator}, x.state.validators.data[i]? = some v →
      x.state.validators.data[i]? = some w → w = v := fun one two =>
    Option.some.inj (two.symm.trans one)
  have effective : ∀ {i : Nat} {v : Validator}, x.state.validators.data[i]? = some v →
      effectiveAt x i = v.effectiveBalance.toNat := fun found => by simp [effectiveAt, found]
  have original : ∀ i, (initialOwnership x high).original i =
      if NewReference x i then effectiveAt x i else 0 := fun i => by
    by_cases ref : NewReference x i
    · simp only [ref, ↓reduceIte]
      simp only [NewReference] at ref
      simp [initialOwnership, ref]
    · simp only [ref, ↓reduceIte]
      simp only [NewReference] at ref
      simp [initialOwnership, ref]
  -- A pending source of the actual queue sits at some position of it.
  have position : ∀ c ∈ pendingQueue x, ∃ j, (pendingQueue x)[j]? = some c := fun c member => by
    obtain ⟨j, inside, atJ⟩ := List.getElem_of_mem member
    exact ⟨j, by rw [List.getElem?_eq_getElem inside, atJ]⟩
  have epochLe : (getCurrentEpoch x.state).toNat ≤ horizonEnd x high := by unfold horizonEnd; omega
  refine ⟨initialOwnership x high, rfl, ⟨valid, rfl, initialOwnership_card high early,
    fun token member => ?_, fun token member => ?_, fun i => rfl⟩,
    valid, by simp [initialOwnership], fun i => ?_, fun i ref _ _ => ?_,
    fun i initial v found active _ _ readU _ => ?_, fun i pending _ _ v found => ?_,
    fun c member v found due notRef => ?_, fun i v found notRef notPending idle supp => ?_,
    fun i pending v initial readU readX active _ _ => ?_, fun i v found supp notPrevious => ?_⟩
  · obtain ⟨p, idx, unit, small, _, below, rfl⟩ := mem_initialOwnership.mp member
    exact ⟨p, idx, unit, rfl, small, below, initialOwnership_owner member⟩
  · simp only [initialOwnership, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_image] at member
    rcases member with ⟨idx, _, unit, _, rfl⟩ | ⟨idx, _, unit, _, rfl⟩
    · exact ⟨0, idx, unit, rfl, by decide⟩
    · exact ⟨1, idx, unit, rfl, by decide⟩
  · rw [original]
    split_ifs with ref
    · exact ⟨le_rfl, fun absent => absurd ref absent⟩
    · exact ⟨Nat.zero_le _, fun _ => rfl⟩
  · -- A new reference key holds its capped excess above its effective balance.
    rw [original]
    simp only [ref, ↓reduceIte]
    cases found : x.state.validators.data[i]? with
    | none => simp [NewReference, found] at ref
    | some v =>
      have active : isActiveValidator v (getCurrentEpoch x.state) = true := by
        simp only [NewReference, found, Option.any_some, Bool.and_eq_true] at ref
        exact ref.1.1
      have kept := excess i v found active
      have held := inter i
      omega
  · obtain rfl := read found readU
    have kept := excess i v found active
    simp only [potential, found, Option.map_some, Option.getD_some] at kept
    omega
  · obtain ⟨c, member, rfl, due⟩ := pending
    obtain ⟨j, entry⟩ := position c member
    exact pendingHeld j c v entry found (by simpa [found] using due)
  · obtain ⟨j, entry⟩ := position c member
    exact pendingHeld j c v entry found ((UInt64.le_iff_toNat_le.mp due).trans epochLe)
  · -- A key idle at `x` is supported only if it is still to activate, by its potential.
    have quiet : isActiveValidator v (getCurrentEpoch x.state) = false ∧
        isActiveValidator v (getPreviousEpoch x.state) = false := by
      simpa [found] using idle
    rcases supp with supported | ⟨later, notExited⟩ | ⟨queued, absent⟩
    · rcases supportedAt_current supported with now | before
      · simp [quiet.1] at now
      · simp [quiet.2] at before
    · have potential := initialOwnership_potential (high := high) found quiet.1 notExited
      have held := inter i
      rw [effective found]
      omega
    · exact absurd queued absent
  · obtain rfl := read readX readU
    have kept := excess i v readX active
    simp only [potential, readX, Option.map_some, Option.getD_some] at kept
    constructor <;> omega
  · -- A supported key outside the previous-only keys is an unslashed key active at `x`.
    have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have back := toNat_toUInt64_of_lt within inside
    have keyAt : ∀ epoch, isActiveValidator v epoch = true →
        v.pubkey ∈ keysAt x.state (getActiveValidatorIndices x.state epoch) := by
      intro epoch active
      simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
      exact ⟨i.toUInt64, (mem_getActiveValidatorIndices within).mpr
        ⟨v, by rw [back]; exact found, active⟩, by simp [back, found]⟩
    by_cases now : isActiveValidator v (getCurrentEpoch x.state) = true
    · have weight := initialOwnership_weight shared genesis early found now supp.1
      rw [weight, effective found]
      omega
    · -- Only previously active, its key would be previous-only.
      exfalso
      have before := (supportedAt_current supp).resolve_left now
      apply notPrevious
      refine Finset.mem_sdiff.mpr ⟨keyAt _ before, fun current => ?_⟩
      simp only [activeKeys, keysAt, List.mem_toFinset, List.mem_filterMap] at current
      obtain ⟨index, listed, key⟩ := current
      obtain ⟨w, located, active⟩ := (mem_getActiveValidatorIndices within).mp listed
      simp only [located, Option.map_some, Option.some.injEq] at key
      have same : w = v := List.inj_on_of_nodup_map unique
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? located)) member key
      subst w
      exact now active

end

/-- A payment funded by its source's original stake and held tokens has an owned transfer.

The baseline is the part the original stake covers, minted fresh to the target.

The rest moves held tokens of the source to the target.

The source retires, keeps no original stake and holds nothing else. -/
private theorem ownedTransfer_exists (before : Ownership) (p : Payment preset)
    (position sourceRound : Nat) (valid : OwnershipValid before)
    (fresh : ∀ unit, TokenOrigin.released position unit ∉ before.issued)
    (unretired : p.source ∉ before.retired)
    (funded : p.amount ≤ before.original p.source + (held before p.source).card) :
    ∃ allocation : OwnedRelease, ∃ after : Ownership,
      allocation.sourceRound = sourceRound ∧
      allocation.baseline = min p.amount (before.original p.source) ∧
      OwnedTransfer position p allocation before after := by
  let baseline := min p.amount (before.original p.source)
  obtain ⟨moved, inside, size⟩ :=
    Finset.exists_subset_card_eq (s := held before p.source) (n := p.amount - baseline)
      (by omega)
  let minted := (Finset.range baseline).image (TokenOrigin.released position)
  let after : Ownership :=
    { issued := before.issued ∪ minted
      owner := fun token =>
        if token ∈ moved ∪ minted then some p.target
        else if token ∈ held before p.source then none else before.owner token
      endpoint := (before.endpoint \ held before p.source) ∪ moved ∪ minted
      original := fun i => if i = p.source then 0 else before.original i
      retired := insert p.source before.retired }
  -- Held tokens are issued, and minted tokens are new.
  have heldIssued : held before p.source ⊆ before.issued := Finset.filter_subset _ _
  have apart : Disjoint before.issued minted := Finset.disjoint_left.mpr fun token old new => by
    obtain ⟨unit, _, rfl⟩ := Finset.mem_image.mp new
    exact fresh unit old
  have notMinted : ∀ token ∈ before.issued, token ∉ minted := fun token old new =>
    Finset.disjoint_left.mp apart old new
  have valid' : OwnershipValid after := by
    refine ⟨fun token owned => ?_, fun token member => ?_, fun token member => ?_⟩
    · simp only [after] at owned ⊢
      split_ifs at owned with transferred kept
      · rcases Finset.mem_union.mp transferred with move | mint
        · exact Finset.mem_union_left _ (heldIssued (inside move))
        · exact Finset.mem_union_right _ mint
      · simp at owned
      · exact Finset.mem_union_left _ (valid.1 token owned)
    · simp only [after, Finset.mem_union, Finset.mem_sdiff] at member ⊢
      rcases member with (⟨front, _⟩ | move) | mint
      · exact .inl (valid.2.1 front)
      · exact .inl (heldIssued (inside move))
      · exact .inr mint
    · simp only [after, Finset.mem_union, Finset.mem_sdiff] at member ⊢
      rcases member with (⟨front, notHeld⟩ | move) | mint
      · have notMoved : token ∉ moved := fun move => notHeld (inside move)
        have absent := notMinted token (valid.2.1 front)
        simp only [notMoved, absent, or_self, ↓reduceIte, notHeld]
        exact valid.2.2 token front
      · simp [move]
      · simp [mint]
  refine ⟨⟨baseline, p.amount - baseline, sourceRound⟩, after, rfl, rfl, valid, valid', moved,
        minted,
    inside, size, rfl, apart, rfl, by dsimp only; omega, Nat.min_le_right _ _, unretired, rfl,
    by simp [after], fun i other => by simp [after, other], fun token member => by
      simp [after, member], fun token kept notMoved => ?_, fun token notHeld notNew => ?_, rfl⟩
  · have absent := notMinted token (heldIssued kept)
    simp [after, notMoved, absent, kept]
  · have notMoved : token ∉ moved := fun move => notHeld (inside move)
    simp [after, notMoved, notNew, notHeld]

/-- An owned transfer between two different keys gives the target the whole payment in tokens.

It does so at its endpoint too.

It leaves every other key's held tokens unchanged.

The target keeps what it held, since those tokens are neither the source's nor new.

It gains the moved tokens and the minted ones.

These are disjoint from each other and from everything it held.

Their number is exactly the payment. -/
theorem ownedTransfer_held {position : Nat} {p : Payment preset}
    {allocation : OwnedRelease} {before after : Ownership}
    (transfer : OwnedTransfer position p allocation before after)
    (apart : p.source ≠ p.target) :
    (held before p.target).card + p.amount ≤ (held after p.target).card ∧
      (held before p.target ∩ before.endpoint).card + p.amount ≤
        (held after p.target ∩ after.endpoint).card ∧
      ∀ i, i ≠ p.source → i ≠ p.target → held after i = held before i := by
  obtain ⟨_, _, moved, minted, inside, size, mintedEq, fresh, issued, amount, _, _, _, _, _,
    gained, lost, kept, endpoint⟩ := transfer
  have heldIssued : ∀ i, held before i ⊆ before.issued := fun _ => Finset.filter_subset _ _
  have notMinted : ∀ token ∈ before.issued, token ∉ minted := fun token old new =>
    Finset.disjoint_left.mp fresh old new
  -- A token held by another key than the source is not the source's.
  have notSource : ∀ {i token}, i ≠ p.source → token ∈ held before i →
      token ∉ held before p.source := fun {i token} other mine theirs => by
    have one := (Finset.mem_filter.mp mine).2
    have two := (Finset.mem_filter.mp theirs).2
    exact other (Option.some.inj (one.symm.trans two))
  -- A token held by another key keeps its owner.
  have stays : ∀ {i token}, i ≠ p.source → token ∈ held before i → token ∈ held after i :=
    fun {i token} other mine => by
      have old := heldIssued i mine
      refine Finset.mem_filter.mpr ⟨by rw [issued]; exact Finset.mem_union_left _ old, ?_⟩
      rw [kept token (notSource other mine) (notMinted token old)]
      exact (Finset.mem_filter.mp mine).2
  have mintedCard : minted.card = allocation.baseline := by
    rw [mintedEq, Finset.card_image_of_injective _ (fun a b (same : TokenOrigin.released
      position a = TokenOrigin.released position b) => by injection same), Finset.card_range]
  have movedIssued : moved ⊆ before.issued := inside.trans (heldIssued _)
  have newHeld : moved ∪ minted ⊆ held after p.target := fun token member =>
    Finset.mem_filter.mpr ⟨by
      rw [issued]
      rcases Finset.mem_union.mp member with move | mint
      · exact Finset.mem_union_left _ (movedIssued move)
      · exact Finset.mem_union_right _ mint, gained token member⟩
  -- The new tokens are disjoint from what the target held, and from each other.
  have newApart : ∀ (S : Finset TokenOrigin), S ⊆ held before p.target →
      Disjoint S (moved ∪ minted) := fun S sub => Finset.disjoint_left.mpr
    fun token mine new => by
      rcases Finset.mem_union.mp new with move | mint
      · exact notSource (Ne.symm apart) (sub mine) (inside move)
      · exact notMinted token (heldIssued _ (sub mine)) mint
  have newCard : (moved ∪ minted).card = p.amount := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun token move mint =>
      notMinted token (movedIssued move) mint), size, mintedCard, amount]
  refine ⟨?_, ?_, fun i notSrc notTgt => ?_⟩
  · rw [← newCard, ← Finset.card_union_of_disjoint (newApart _ le_rfl)]
    exact Finset.card_le_card (Finset.union_subset (fun token mine =>
      stays (Ne.symm apart) mine) newHeld)
  · rw [← newCard, ← Finset.card_union_of_disjoint (newApart _ Finset.inter_subset_left)]
    refine Finset.card_le_card (Finset.union_subset (fun token member => ?_) fun token new => ?_)
    · obtain ⟨mine, front⟩ := Finset.mem_inter.mp member
      refine Finset.mem_inter.mpr ⟨stays (Ne.symm apart) mine, ?_⟩
      rw [endpoint]
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨front, notSource (Ne.symm apart) mine⟩))
    · refine Finset.mem_inter.mpr ⟨newHeld new, ?_⟩
      rw [endpoint]
      rcases Finset.mem_union.mp new with move | mint
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ move)
      · exact Finset.mem_union_right _ mint
  · ext token
    constructor
    · intro mine
      obtain ⟨present, owner⟩ := Finset.mem_filter.mp mine
      by_cases new : token ∈ moved ∪ minted
      · rw [gained token new] at owner
        exact absurd (Option.some.inj owner).symm notTgt
      by_cases source : token ∈ held before p.source
      · have notMoved : token ∉ moved := fun move => new (Finset.mem_union_left _ move)
        rw [lost token source notMoved] at owner
        cases owner
      · have notNew : token ∉ minted := fun mint => new (Finset.mem_union_right _ mint)
        rw [kept token source notNew] at owner
        rw [issued] at present
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_union.mp present).resolve_right notNew, owner⟩
    · exact stays notSrc

section

open Cryptography.Bls

def eventCreditUnits (e : BalanceEvent preset) (i : Nat) : Nat :=
  if e.source = .deposits ∧
      (e.before.state.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
        false then 0
  else actualBalanceAt e.after i - actualBalanceAt e.before i

def eventCreditTokens (position : Nat) (e : BalanceEvent preset) : Finset TokenOrigin :=
  (Finset.range e.after.state.validators.data.size).biUnion fun i =>
    (Finset.range (eventCreditUnits e i)).image (TokenOrigin.credit position i)

private theorem mem_eventCreditTokens :
    token ∈ eventCreditTokens position e ↔
      ∃ i unit, i < e.after.state.validators.data.size ∧
        unit < eventCreditUnits e i ∧ token = TokenOrigin.credit position i unit := by
  simp only [eventCreditTokens, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨i, inside, unit, small, rfl⟩
    exact ⟨i, unit, inside, small, rfl⟩
  · rintro ⟨i, unit, inside, small, rfl⟩
    exact ⟨i, inside, unit, small, rfl⟩

private theorem card_eventCreditTokens :
    (eventCreditTokens position e).card =
      ∑ i ∈ Finset.range e.after.state.validators.data.size, eventCreditUnits e i := by
  rw [eventCreditTokens, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro a b equal
    exact TokenOrigin.credit.inj equal |>.2.2
  · intro i _ j _ apart
    apply Finset.disjoint_left.mpr
    intro token first second
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp first
    obtain ⟨v, _, equal⟩ := Finset.mem_image.mp second
    exact apart (TokenOrigin.credit.inj equal).2.1.symm

def creditOwnership (position : Nat) (e : BalanceEvent preset) (before : Ownership) :
    Ownership where
  issued := before.issued ∪ eventCreditTokens position e
  owner := fun token => match token with
    | .credit event i _ => if event = position ∧ token ∈ eventCreditTokens position e
        then some i else before.owner token
    | _ => before.owner token
  endpoint := before.endpoint ∪ eventCreditTokens position e
  original := before.original
  retired := before.retired

private theorem creditOwnership_owner_kept {e : BalanceEvent preset} {before : Ownership}
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (member : token ∈ before.issued) :
    (creditOwnership position e before).owner token = before.owner token := by
  cases token with
  | initial => rfl
  | released => rfl
  | credit event i unit =>
    by_cases equal : event = position
    · subst event
      exact False.elim (fresh i unit member)
    · simp [creditOwnership, equal]

private theorem ownedCredit_of_fresh {e : BalanceEvent preset} {before : Ownership}
    (valid : OwnershipValid before)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (budget : (∑ i ∈ Finset.range e.after.state.validators.data.size, eventCreditUnits e i) ≤
      if e.source = .deposits then funding_deposit_credit e
      else if e.source = .rewards ∨ e.source = .sync then e.creditLimit else otherCredit e) :
    OwnedCredit position e before (creditOwnership position e before) := by
  have owns : ∀ token ∈ eventCreditTokens position e,
      ∃ i unit, token = .credit position i unit ∧
        unit < eventCreditUnits e i ∧
        (creditOwnership position e before).owner token = some i := by
    intro token member
    obtain ⟨i, unit, _, small, rfl⟩ := mem_eventCreditTokens.mp member
    exact ⟨i, unit, rfl, small, by simp [creditOwnership, member]⟩
  have kept : ∀ token ∈ before.issued,
      (creditOwnership position e before).owner token = before.owner token :=
    fun _ member => creditOwnership_owner_kept fresh member
  have validAfter : OwnershipValid (creditOwnership position e before) := by
    refine ⟨?_, ?_, ?_⟩
    · intro token owned
      by_cases minted : token ∈ eventCreditTokens position e
      · exact Finset.mem_union_right _ minted
      · apply Finset.mem_union_left
        apply valid.1 token
        cases token <;> simpa [creditOwnership, minted] using owned
    · intro token member
      rcases Finset.mem_union.mp member with old | minted
      · exact Finset.mem_union_left _ (valid.2.1 old)
      · exact Finset.mem_union_right _ minted
    · intro token member
      rcases Finset.mem_union.mp member with old | minted
      · rw [kept token (valid.2.1 old)]
        exact valid.2.2 token old
      · obtain ⟨i, unit, _, _, owner⟩ := owns token minted
        simp [owner]
  refine ⟨valid, validAfter, eventCreditTokens position e, ?_, rfl, ?_, ?_, kept,
    rfl, rfl, fun _ => Nat.le_refl _⟩
  · apply Finset.disjoint_left.mpr
    intro token old minted
    obtain ⟨i, unit, _, _, rfl⟩ := mem_eventCreditTokens.mp minted
    exact fresh i unit old
  · intro token member
    obtain ⟨i, unit, same, small, owner⟩ := owns token member
    refine ⟨i, unit, same, ?_, ?_, owner⟩
    · unfold eventCreditUnits at small
      split at small
      · omega
      · exact small
    · intro deposit
      unfold eventCreditUnits at small
      split at small
      · omega
      · rename_i notWithdrawn
        have flag := notWithdrawn ∘ And.intro deposit
        cases found : (e.before.state.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD false
        · rfl
        · exact False.elim (flag found)
  · rw [card_eventCreditTokens]
    exact budget

theorem ownedCredit_of_bounded {e : BalanceEvent preset} {before : Ownership}
    (valid : OwnershipValid before)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (electra : .pectra ≤ e.before.fork) (notTransfer : e.source ≠ .consolidations)
    (matched : e.after.state.validators.data.size = e.after.state.balances.data.size)
    (bounded : e.credits ≤ e.creditLimit) :
    OwnedCredit position e before (creditOwnership position e before) := by
  apply ownedCredit_of_fresh valid fresh
  by_cases deposit : e.source = .deposits
  · simp only [deposit, ↓reduceIte, funding_deposit_credit, electra, and_self]
    apply Finset.sum_le_sum
    intro i _
    simp only [eventCreditUnits, deposit, true_and]
    split <;> simp_all
  · have units : (∑ i ∈ Finset.range e.after.state.validators.data.size,
        eventCreditUnits e i) = e.credits := by
      simp only [eventCreditUnits, deposit, false_and, ↓reduceIte]
      rw [matched]
      rfl
    rw [units]
    cases source : e.source <;>
      simp_all [otherCredit, fundingCredit]

private theorem creditOwnership_held {e : BalanceEvent preset} {before : Ownership}
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (inside : i < e.after.state.validators.data.size) :
    (held (creditOwnership position e before) i).card =
      (held before i).card + eventCreditUnits e i := by
  let block := (Finset.range (eventCreditUnits e i)).image (TokenOrigin.credit position i)
  have same : held (creditOwnership position e before) i = held before i ∪ block := by
    ext token
    simp only [held, Finset.mem_filter, Finset.mem_union]
    change ((token ∈ before.issued ∪ eventCreditTokens position e) ∧
      (creditOwnership position e before).owner token = some i) ↔
        (token ∈ before.issued ∧ before.owner token = some i) ∨ token ∈ block
    rw [Finset.mem_union]
    constructor
    · rintro ⟨old | minted, owner⟩
      · left
        rw [creditOwnership_owner_kept fresh old] at owner
        exact ⟨old, owner⟩
      · right
        obtain ⟨j, unit, _, small, rfl⟩ := mem_eventCreditTokens.mp minted
        have equal : j = i := by simpa [creditOwnership, minted] using owner
        subst j
        exact Finset.mem_image.mpr ⟨unit, Finset.mem_range.mpr small, rfl⟩
    · rintro (⟨old, owner⟩ | minted)
      · refine ⟨Or.inl old, ?_⟩
        rw [creditOwnership_owner_kept fresh old]
        exact owner
      · obtain ⟨unit, small, rfl⟩ := Finset.mem_image.mp minted
        have member : TokenOrigin.credit position i unit ∈ eventCreditTokens position e :=
          mem_eventCreditTokens.mpr
          ⟨i, unit, inside, Finset.mem_range.mp small, rfl⟩
        exact ⟨Or.inr member, by simp [creditOwnership, member]⟩
  have apart : Disjoint (held before i) block := by
    apply Finset.disjoint_left.mpr
    intro token old minted
    obtain ⟨unit, _, rfl⟩ := Finset.mem_image.mp minted
    exact fresh i unit (Finset.mem_filter.mp old).1
  rw [same, Finset.card_union_of_disjoint apart]
  congr 1
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro a b equal
  exact TokenOrigin.credit.inj equal |>.2.2

/-- A balance growth that may append validators keeps the reserve cut.

Indices below the old registry size keep their validators, so their clauses transport.

Such an index may grow without tokens if no clause that reads a balance can see its validator.

That is, the validator is not funding-relevant, never supported again, and not waiting to activate.

Each appended validator meets its clauses through the explicit obligations.

It is new at the reference state, is never supported again if retired, and holds enough tokens. -/
private theorem reserveCut_balance_hidden_append {x u v : ForkedBeaconState preset} {high : Nat}
    {epoch : Epoch} {suffix : List PendingConsolidation} {before after : Ownership}
    {growth : Nat → Nat}
    (fork : v.fork = u.fork)
    (registry : ∃ added : Array Validator,
      v.state.validators.data = u.state.validators.data ++ added)
    (balances : ∀ i, actualBalanceAt v i ≤ actualBalanceAt u i + growth i ∨
      ∀ w, u.state.validators.data[i]? = some w →
        ¬ FundingRelevant u epoch suffix i ∧ (∀ e, epoch ≤ e → ¬ SupportedAt e w) ∧
          ¬ (epoch < w.activationEpoch ∧ epoch < w.exitEpoch))
    (valid : OwnershipValid after) (retired : after.retired = before.retired)
    (original : after.original = before.original)
    (heldGrowth : ∀ i, (held before i).card + growth i ≤ (held after i).card)
    (endpointGrowth : ∀ i, (held before i ∩ before.endpoint).card + growth i ≤
      (held after i ∩ after.endpoint).card)
    (appendedFresh : ∀ j w, u.state.validators.data.size ≤ j →
      v.state.validators.data[j]? = some w → x.state.validators.data[j]? = none)
    (appendedRetired : ∀ j w, u.state.validators.data.size ≤ j →
      v.state.validators.data[j]? = some w → j ∈ after.retired →
      (∀ e, epoch ≤ e → ¬ SupportedAt e w) ∧ ¬ ∃ c ∈ suffix, c.sourceIndex.toNat = j)
    (appendedHeld : ∀ j w, u.state.validators.data.size ≤ j →
      v.state.validators.data[j]? = some w →
      max (effectiveAt v j)
        (min (actualBalanceAt v j) (withdrawalMaxEffectiveBalance preset v.fork w).toNat) ≤
        (held after j).card)
    (appendedEndpoint : ∀ j w, u.state.validators.data.size ≤ j →
      v.state.validators.data[j]? = some w → SupportedAt epoch w → w.pubkey ∉ previousOnly x →
      effectiveAt v j ≤ Models.supported (unslashedKeys x.state) (effectiveWeight x.state)
        w.pubkey + (held after j ∩ after.endpoint).card)
    (reserve : ReserveCut x high u epoch suffix before) :
    ReserveCut x high v epoch suffix after := by
  obtain ⟨added, registry⟩ := registry
  have lookup : ∀ i, i < u.state.validators.data.size →
      v.state.validators.data[i]? = u.state.validators.data[i]? := by
    intro i inside
    rw [registry, Array.getElem?_append_left inside]
  have effective : ∀ i, i < u.state.validators.data.size → effectiveAt v i = effectiveAt u i := by
    intro i inside
    simp only [effectiveAt, lookup i inside]
  have relevant : ∀ i, i < u.state.validators.data.size →
      FundingRelevant v epoch suffix i → FundingRelevant u epoch suffix i := by
    rintro i inside ⟨validator, found, rest⟩
    exact ⟨validator, (lookup i inside).symm ▸ found, rest⟩
  -- An appended index with no initial validator is neither a reference nor initially pending.
  have notReference : ∀ i w, ¬ i < u.state.validators.data.size →
      v.state.validators.data[i]? = some w → ¬ NewReference x i := by
    intro i w outside found reference
    simp [NewReference, appendedFresh i w (Nat.le_of_not_lt outside) found] at reference
  have capped : ∀ i validator, actualBalanceAt v i ≤ actualBalanceAt u i + growth i →
      min (actualBalanceAt v i) (withdrawalMaxEffectiveBalance preset v.fork validator).toNat ≤
      min (actualBalanceAt u i) (withdrawalMaxEffectiveBalance preset u.fork validator).toNat +
        growth i := by
    intro i validator increase
    rw [fork]
    omega
  obtain ⟨_, wasRetired, wasOriginal, reference, scheduled, pending, due, idle,
    activePending, endpoint⟩ := reserve
  refine ⟨valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i member validator found
    by_cases inside : i < u.state.validators.data.size
    · rw [retired] at member
      exact wasRetired i member validator ((lookup i inside).symm ▸ found)
    · exact appendedRetired i validator (Nat.le_of_not_lt inside) found member
  · simpa only [original] using wasOriginal
  · intro i ref notRetired support
    by_cases inside : i < u.state.validators.data.size
    · rw [retired] at notRetired
      have wasRelevant := relevant i inside support
      have old := reference i ref notRetired wasRelevant
      -- A hidden validator is not funding-relevant, so its balance grew within its tokens.
      have ⟨w, found, _⟩ := wasRelevant
      have change := (balances i).resolve_right fun hidden => (hidden w found).1 wasRelevant
      have rise := capped i w change
      have tokens := heldGrowth i
      have foundV := (lookup i inside).trans found
      rw [original]
      simp only [potential, found, foundV, Option.map_some, Option.getD_some] at old ⊢
      omega
    · obtain ⟨w, found, _⟩ := support
      exact absurd ref (notReference i w inside found)
  · intro i initial validator found active clean finite located support
    by_cases inside : i < u.state.validators.data.size
    · have wasLocated := (lookup i inside).symm ▸ located
      have old := scheduled i initial validator found active clean finite wasLocated support
      -- A hidden validator is never supported again.
      have change := capped i validator ((balances i).resolve_right fun hidden =>
        have ⟨e, later, supported⟩ := support
        (hidden validator wasLocated).2.1 e later supported)
      have tokens := endpointGrowth i
      rw [effective i inside]
      omega
    · simp [appendedFresh i validator (Nat.le_of_not_lt inside) located] at found
  · intro i initial notRetired support validator found
    by_cases inside : i < u.state.validators.data.size
    · rw [retired] at notRetired
      have wasLocated := (lookup i inside).symm ▸ found
      have wasRelevant := relevant i inside support
      have old := pending i initial notRetired wasRelevant validator wasLocated
      have change := capped i validator ((balances i).resolve_right fun hidden =>
        (hidden validator wasLocated).1 wasRelevant)
      have tokens := heldGrowth i
      omega
    -- An appended index has no initial validator, so its default withdrawal epoch is too late.
    · obtain ⟨_, _, _, late⟩ := initial
      simp [appendedFresh i validator (Nat.le_of_not_lt inside) found] at late
  · intro entry member validator found ready notRef
    by_cases inside : entry.sourceIndex.toNat < u.state.validators.data.size
    · have wasLocated := (lookup _ inside).symm ▸ found
      have old := due entry member validator wasLocated ready notRef
      -- A queued source is funding-relevant, so it is not hidden.
      have change := capped entry.sourceIndex.toNat validator
        ((balances _).resolve_right fun hidden =>
          (hidden validator wasLocated).1 ⟨validator, wasLocated, .inr (.inr ⟨entry, member, rfl⟩)⟩)
      have tokens := heldGrowth entry.sourceIndex.toNat
      omega
    · have tokens := appendedHeld _ validator (Nat.le_of_not_lt inside) found
      omega
  · intro i validator found notRef notPending quiet support
    by_cases inside : i < u.state.validators.data.size
    · have wasLocated := (lookup i inside).symm ▸ found
      have old := idle i validator wasLocated notRef notPending quiet support
      -- Each way to be idle-eligible contradicts one part of being hidden.
      have change := capped i validator ((balances i).resolve_right fun hidden => by
        obtain ⟨irrelevant, unsupported, waiting⟩ := hidden validator wasLocated
        rcases support with supported | early | ⟨queued, _⟩
        · exact unsupported epoch (Nat.le_refl _) supported
        · exact waiting early
        · exact irrelevant ⟨validator, wasLocated, .inr (.inr queued)⟩)
      have tokens := heldGrowth i
      rw [effective i inside]
      omega
    · exact appendedHeld i validator (Nat.le_of_not_lt inside) found
  · intro i initial validator old located found active notRetired support
    by_cases inside : i < u.state.validators.data.size
    · rw [retired] at notRetired
      have wasLocated := (lookup i inside).symm ▸ located
      have wasRelevant := relevant i inside support
      obtain ⟨balance, eff⟩ := activePending i initial validator old wasLocated found active
        notRetired wasRelevant
      have change := capped i validator ((balances i).resolve_right fun hidden =>
        (hidden validator wasLocated).1 wasRelevant)
      have tokens := endpointGrowth i
      rw [effective i inside]
      constructor <;> omega
    · simp [appendedFresh i validator (Nat.le_of_not_lt inside) located] at found
  · intro i validator found support notPrevious
    by_cases inside : i < u.state.validators.data.size
    · have old := endpoint i validator ((lookup i inside).symm ▸ found) support notPrevious
      have tokens := endpointGrowth i
      rw [effective i inside]
      omega
    · exact appendedEndpoint i validator (Nat.le_of_not_lt inside) found support notPrevious

theorem reserveCut_balance_append {x u v : ForkedBeaconState preset} {high : Nat}
    {epoch : Epoch} {suffix : List PendingConsolidation} {before after : Ownership}
    {growth : Nat → Nat}
    (fork : v.fork = u.fork)
    (registry : ∃ added : Array Validator,
      v.state.validators.data = u.state.validators.data ++ added)
    (balances : ∀ i, actualBalanceAt v i ≤ actualBalanceAt u i + growth i)
    (valid : OwnershipValid after) (retired : after.retired = before.retired)
    (original : after.original = before.original)
    (heldGrowth : ∀ i, (held before i).card + growth i ≤ (held after i).card)
    (endpointGrowth : ∀ i, (held before i ∩ before.endpoint).card + growth i ≤
      (held after i ∩ after.endpoint).card)
    (appendedFresh : ∀ j w, u.state.validators.data.size ≤ j →
      v.state.validators.data[j]? = some w → x.state.validators.data[j]? = none)
    (appendedRetired : ∀ j w, u.state.validators.data.size ≤ j →
      v.state.validators.data[j]? = some w → j ∈ after.retired →
      (∀ e, epoch ≤ e → ¬ SupportedAt e w) ∧ ¬ ∃ c ∈ suffix, c.sourceIndex.toNat = j)
    (appendedHeld : ∀ j w, u.state.validators.data.size ≤ j →
      v.state.validators.data[j]? = some w →
      max (effectiveAt v j)
        (min (actualBalanceAt v j) (withdrawalMaxEffectiveBalance preset v.fork w).toNat) ≤
        (held after j).card)
    (appendedEndpoint : ∀ j w, u.state.validators.data.size ≤ j →
      v.state.validators.data[j]? = some w → SupportedAt epoch w → w.pubkey ∉ previousOnly x →
      effectiveAt v j ≤ Models.supported (unslashedKeys x.state) (effectiveWeight x.state)
        w.pubkey + (held after j ∩ after.endpoint).card)
    (reserve : ReserveCut x high u epoch suffix before) :
    ReserveCut x high v epoch suffix after :=
  reserveCut_balance_hidden_append fork registry (fun i => .inl (balances i)) valid retired
    original heldGrowth endpointGrowth appendedFresh appendedRetired appendedHeld appendedEndpoint
    reserve

private theorem reserveCut_balance_growth {x u v : ForkedBeaconState preset}
    {before after : Ownership} {growth : Nat → Nat}
    (fork : v.fork = u.fork) (registry : v.state.validators.data = u.state.validators.data)
    (balances : ∀ i, actualBalanceAt v i ≤ actualBalanceAt u i + growth i)
    (valid : OwnershipValid after) (retired : after.retired = before.retired)
    (original : after.original = before.original)
    (heldGrowth : ∀ i, (held before i).card + growth i ≤ (held after i).card)
    (endpointGrowth : ∀ i, (held before i ∩ before.endpoint).card + growth i ≤
      (held after i ∩ after.endpoint).card)
    (reserve : ReserveCut x high u epoch suffix before) :
    ReserveCut x high v epoch suffix after := by
  -- With nothing appended, no index at or past the old size has a validator.
  have none : ∀ j w, u.state.validators.data.size ≤ j →
      v.state.validators.data[j]? = some w → False := by
    intro j w outside found
    rw [registry, Array.getElem?_eq_none outside] at found
    cases found
  exact reserveCut_balance_append fork ⟨#[], by rw [registry, Array.append_empty]⟩ balances
    valid retired original heldGrowth endpointGrowth
    (fun j w outside found => (none j w outside found).elim)
    (fun j w outside found => (none j w outside found).elim)
    (fun j w outside found => (none j w outside found).elim)
    (fun j w outside found => (none j w outside found).elim) reserve

theorem reserveCut_balance_decrease {x u v : ForkedBeaconState preset}
    (fork : v.fork = u.fork) (registry : v.state.validators.data = u.state.validators.data)
    (balances : ∀ i, actualBalanceAt v i ≤ actualBalanceAt u i)
    (reserve : ReserveCut x high u epoch suffix owned) :
    ReserveCut x high v epoch suffix owned := by
  apply reserveCut_balance_growth (growth := fun _ => 0) fork registry
    (by simpa only [Nat.add_zero] using balances) reserve.1 rfl rfl
    (fun _ => by omega) (fun _ => by omega) reserve

theorem reservedEvent_zero_credit {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} (notTransfer : e.source ≠ .consolidations)
    (fork : e.after.fork = e.before.fork)
    (registry : e.after.state.validators.data = e.before.state.validators.data)
    (epoch : getCurrentEpoch e.after.state = getCurrentEpoch e.before.state)
    (bounded : e.credits ≤ e.creditLimit) (zero : e.creditLimit = 0)
    (reserve : ReserveCut x high e.before (getCurrentEpoch e.before.state)
      (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned) :
    ReservedEvent x high eventPosition paymentPosition rounding e queue queue [] [] owned
        owned := by
  have decreases : ∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i := by
    intro i
    by_cases inside : i < e.after.state.balances.data.size
    · have single := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.range e.after.state.balances.data.size) =>
          Nat.zero_le (actualBalanceAt e.after j - actualBalanceAt e.before j))
        (Finset.mem_range.mpr inside)
      change actualBalanceAt e.after i - actualBalanceAt e.before i ≤ e.credits at single
      omega
    · simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt inside)]
  have frame : OwnedFrame owned owned :=
    ⟨reserve.1, reserve.1, rfl, fun _ => Or.inl rfl,
      Finset.Subset.refl _, rfl, fun _ => Nat.le_refl _⟩
  refine ⟨?_, assignment, assignment, ?_⟩
  · simp only [OwnedEvent, notTransfer, ↓reduceIte]
    exact ⟨True.intro, True.intro, Or.inr frame⟩
  · simp only [notTransfer, ↓reduceIte]
    refine ⟨reserve, ?_⟩
    rw [epoch]
    exact reserveCut_balance_decrease fork registry decreases reserve

private theorem ownedCredit_endpoint_growth {e : BalanceEvent preset}
    (credit : OwnedCredit position e before after)
    (growth : (held before i).card + amount ≤ (held after i).card) :
    (held before i ∩ before.endpoint).card + amount ≤
      (held after i ∩ after.endpoint).card := by
  obtain ⟨_, _, minted, _, issued, _, _, kept, endpoint, _, _⟩ := credit
  have cover : held after i ⊆ (held before i \ before.endpoint) ∪
      (held after i ∩ after.endpoint) := by
    intro token member
    obtain ⟨present, owner⟩ := Finset.mem_filter.mp member
    rw [issued] at present
    rcases Finset.mem_union.mp present with old | fresh
    · have wasHeld : token ∈ held before i := by
        exact Finset.mem_filter.mpr ⟨old, (kept token old).symm.trans owner⟩
      by_cases wasEndpoint : token ∈ before.endpoint
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
          ⟨member, by rw [endpoint]; exact Finset.mem_union_left _ wasEndpoint⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨wasHeld, wasEndpoint⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨member, by rw [endpoint]; exact Finset.mem_union_right _ fresh⟩)
  have bound := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have partition := Finset.card_sdiff_add_card_inter (held before i) before.endpoint
  omega

/-- A credit keeps the reserve cut when it may append validators and its unminted growth is hidden.

Tokens cover the minted units: one per unit of balance growth.

The exception is a deposit to a validator already withdrawable at the start epoch.

It mints nothing.

Such a validator, where its balance grew, is hidden from every clause that reads a balance. -/
private theorem reserveCut_credit_hidden_append {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {before : Ownership} {position high : Nat} {epoch : Epoch}
    {suffix : List PendingConsolidation}
    (dueHidden : ∀ i, e.source = .deposits →
      (e.before.state.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
        false = true →
      actualBalanceAt e.before i < actualBalanceAt e.after i →
      ∀ w, e.before.state.validators.data[i]? = some w →
        ¬ FundingRelevant e.before epoch suffix i ∧ (∀ t, epoch ≤ t → ¬ SupportedAt t w) ∧
          ¬ (epoch < w.activationEpoch ∧ epoch < w.exitEpoch))
    (fork : e.after.fork = e.before.fork)
    (registry : ∃ added : Array Validator,
      e.after.state.validators.data = e.before.state.validators.data ++ added)
    (matched : e.after.state.validators.data.size = e.after.state.balances.data.size)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (credit : OwnedCredit position e before (creditOwnership position e before))
    (appendedFresh : ∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w → x.state.validators.data[j]? = none)
    (appendedRetired : ∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w →
      j ∈ (creditOwnership position e before).retired →
      (∀ t, epoch ≤ t → ¬ SupportedAt t w) ∧ ¬ ∃ c ∈ suffix, c.sourceIndex.toNat = j)
    (appendedHeld : ∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w →
      max (effectiveAt e.after j)
        (min (actualBalanceAt e.after j)
          (withdrawalMaxEffectiveBalance preset e.after.fork w).toNat) ≤
        (held (creditOwnership position e before) j).card)
    (appendedEndpoint : ∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w →
      SupportedAt epoch w → w.pubkey ∉ previousOnly x →
      effectiveAt e.after j ≤ Models.supported (unslashedKeys x.state) (effectiveWeight x.state)
        w.pubkey + (held (creditOwnership position e before) j ∩
          (creditOwnership position e before).endpoint).card)
    (reserve : ReserveCut x high e.before epoch suffix before) :
    ReserveCut x high e.after epoch suffix (creditOwnership position e before) := by
  have heldGrowth : ∀ i, (held before i).card + eventCreditUnits e i ≤
      (held (creditOwnership position e before) i).card := by
    intro i
    by_cases inside : i < e.after.state.validators.data.size
    · rw [creditOwnership_held fresh inside]
    · have balances : actualBalanceAt e.after i = 0 := by
        have outside : e.after.state.balances.data.size ≤ i := by omega
        simp [actualBalanceAt, Array.getElem?_eq_none outside]
      -- Past the registry no balance remains, so nothing is minted there.
      have zero : eventCreditUnits e i = 0 := by
        simp only [eventCreditUnits, balances, Nat.zero_sub]
        split <;> rfl
      rw [zero, Nat.add_zero]
      apply Finset.card_le_card
      intro token member
      obtain ⟨old, owner⟩ := Finset.mem_filter.mp member
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ old, (creditOwnership_owner_kept fresh old).trans owner⟩
  -- Each balance grows within its minted units, or it is a hidden due deposit target.
  have balances : ∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i +
        eventCreditUnits e i ∨
      ∀ w, e.before.state.validators.data[i]? = some w →
        ¬ FundingRelevant e.before epoch suffix i ∧ (∀ t, epoch ≤ t → ¬ SupportedAt t w) ∧
          ¬ (epoch < w.activationEpoch ∧ epoch < w.exitEpoch) := by
    intro i
    simp only [eventCreditUnits]
    split_ifs with due
    · by_cases grew : actualBalanceAt e.before i < actualBalanceAt e.after i
      · exact Or.inr (dueHidden i due.1 due.2 grew)
      · exact Or.inl (by omega)
    · exact Or.inl (by omega)
  exact reserveCut_balance_hidden_append (before := before) fork registry balances credit.2.1
    rfl rfl heldGrowth
    (fun i => ownedCredit_endpoint_growth credit (heldGrowth i)) appendedFresh appendedRetired
    appendedHeld appendedEndpoint reserve

/-- A same-registry credit keeps the reserve cut when no credited validator is due at a deposit.

The credit mints one token per unit of balance growth.

The exception is a deposit to a validator already withdrawable at the start epoch.

`eligible` rules that exception out wherever the balance grew, so every growth is minted. -/
private theorem reserveCut_credit_eligible {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {before : Ownership} {position high : Nat} {epoch : Epoch}
    {suffix : List PendingConsolidation}
    (eligible : ∀ i, actualBalanceAt e.before i < actualBalanceAt e.after i →
      e.source = .deposits →
      (e.before.state.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
        false = false)
    (fork : e.after.fork = e.before.fork)
    (registry : e.after.state.validators.data = e.before.state.validators.data)
    (matched : e.after.state.validators.data.size = e.after.state.balances.data.size)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (credit : OwnedCredit position e before (creditOwnership position e before))
    (reserve : ReserveCut x high e.before epoch suffix before) :
    ReserveCut x high e.after epoch suffix (creditOwnership position e before) := by
  -- With the same registry, no index past the old size has a validator.
  have none : ∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w → False := by
    intro j w outside found
    rw [registry, Array.getElem?_eq_none outside] at found
    cases found
  exact reserveCut_credit_hidden_append
    (fun i deposit due grew => absurd (eligible i grew deposit) (by simp [due])) fork
    ⟨#[], by rw [registry, Array.append_empty]⟩ matched fresh credit
    (fun j w outside found => (none j w outside found).elim)
    (fun j w outside found => (none j w outside found).elim)
    (fun j w outside found => (none j w outside found).elim)
    (fun j w outside found => (none j w outside found).elim) reserve

theorem reserveCut_credit_non_deposit {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {before : Ownership}
    (notDeposit : e.source ≠ .deposits)
    (fork : e.after.fork = e.before.fork)
    (registry : e.after.state.validators.data = e.before.state.validators.data)
    (matched : e.after.state.validators.data.size = e.after.state.balances.data.size)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (credit : OwnedCredit position e before (creditOwnership position e before))
    (reserve : ReserveCut x high e.before epoch suffix before) :
    ReserveCut x high e.after epoch suffix (creditOwnership position e before) :=
  reserveCut_credit_eligible (fun _ _ deposit => absurd deposit notDeposit) fork registry
    matched fresh credit reserve

end

/-- An owned credit only lowers original stakes.

So the assignment cut carries to a retained suffix. -/
private theorem assignmentCut_credit {rounding : Nat → Nat} {queue suffix : List TaggedEntry}
    {position : Nat} {e : BalanceEvent preset} {before after : Ownership}
    (cut : AssignmentCut rounding queue before) (credit : OwnedCredit position e before after)
    (retained : suffix.Sublist queue) : AssignmentCut rounding suffix after :=
  assignmentCut_transport cut credit.2.2.choose_spec.2.2.2.2.2.2.2 retained

/-- Appending fresh entries that meet the bound keeps the assignment cut. -/
theorem assignmentCut_append_fresh {rounding : Nat → Nat}
    {queue added : List TaggedEntry} {before : Ownership}
    (cut : AssignmentCut rounding queue before)
    (freshBound : ∀ tag ∈ added, ∀ position, tag.tag = .fresh position →
      before.original tag.entry.sourceIndex.toNat ≤
        tag.amount + rounding tag.entry.sourceIndex.toNat) :
    AssignmentCut rounding (queue ++ added) before := by
  intro tag member position fresh
  rcases List.mem_append.mp member with old | new
  · exact cut tag old position fresh
  · exact freshBound tag new position fresh

section

open Cryptography.Bls

/-- A same-registry credit with no due deposit target is a reserved event that keeps the queue.

`eligible` is the condition under which such a credit keeps the reserve cut. -/
private theorem reservedEvent_credit_eligible {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {before : Ownership} {eventPosition paymentPosition high : Nat}
    {rounding : Nat → Nat} {queue : List TaggedEntry}
    (eligible : ∀ i, actualBalanceAt e.before i < actualBalanceAt e.after i →
      e.source = .deposits →
      (e.before.state.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
        false = false)
    (notTransfer : e.source ≠ .consolidations)
    (fork : e.after.fork = e.before.fork)
    (registry : e.after.state.validators.data = e.before.state.validators.data)
    (epoch : getCurrentEpoch e.after.state = getCurrentEpoch e.before.state)
    (matched : e.after.state.validators.data.size = e.after.state.balances.data.size)
    (fresh : ∀ i unit, TokenOrigin.credit eventPosition i unit ∉ before.issued)
    (credit : OwnedCredit eventPosition e before (creditOwnership eventPosition e before))
    (reserve : ReserveCut x high e.before (getCurrentEpoch e.before.state)
      (queue.map (·.entry)) before)
    (assignment : AssignmentCut rounding queue before) :
    ReservedEvent x high eventPosition paymentPosition rounding e queue queue [] [] before
      (creditOwnership eventPosition e before) := by
  refine ⟨?_, assignment, assignmentCut_credit assignment credit (List.Sublist.refl _), ?_⟩
  · simp only [OwnedEvent, notTransfer, ↓reduceIte]
    exact ⟨True.intro, True.intro, Or.inl credit⟩
  · simp only [notTransfer, ↓reduceIte]
    refine ⟨reserve, ?_⟩
    rw [epoch]
    exact reserveCut_credit_eligible eligible fork registry matched fresh credit reserve

private theorem reservedEvent_credit_non_deposit {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {before : Ownership}
    (notDeposit : e.source ≠ .deposits) (notTransfer : e.source ≠ .consolidations)
    (fork : e.after.fork = e.before.fork)
    (registry : e.after.state.validators.data = e.before.state.validators.data)
    (epoch : getCurrentEpoch e.after.state = getCurrentEpoch e.before.state)
    (matched : e.after.state.validators.data.size = e.after.state.balances.data.size)
    (fresh : ∀ i unit, TokenOrigin.credit eventPosition i unit ∉ before.issued)
    (credit : OwnedCredit eventPosition e before (creditOwnership eventPosition e before))
    (reserve : ReserveCut x high e.before (getCurrentEpoch e.before.state)
      (queue.map (·.entry)) before)
    (assignment : AssignmentCut rounding queue before) :
    ReservedEvent x high eventPosition paymentPosition rounding e queue queue [] [] before
      (creditOwnership eventPosition e before) :=
  reservedEvent_credit_eligible (fun _ _ deposit => absurd deposit notDeposit) notTransfer fork
    registry epoch matched fresh credit reserve assignment

end

/-- A paid pending consolidation between distinct keys pays the source's capped balance.

It moves exactly that amount from the source to the target. -/
private theorem pendingTransfer_paying {fork : Fork} {next : Epoch}
    {s d u : BeaconState preset fork} {c : PendingConsolidation} {v : Validator} {b : Gwei}
    (found : getValidator s c.sourceIndex = .ok v) (unslashed : v.slashed = false)
    (due : v.withdrawableEpoch ≤ next) (balance : getBalance s c.sourceIndex = .ok b)
    (debited : decreaseBalance s c.sourceIndex (min b v.effectiveBalance) = .ok d)
    (credited : increaseBalance d c.targetIndex (min b v.effectiveBalance) = .ok u)
    (apart : c.sourceIndex ≠ c.targetIndex) :
    Paying (⟨c.sourceIndex.toNat, c.targetIndex.toNat, (min b v.effectiveBalance).toNat,
      next.toNat, ⟨fork, s⟩, ⟨fork, u⟩⟩ : Payment preset) := by
  have apartNat : c.sourceIndex.toNat ≠ c.targetIndex.toNat :=
    fun same => apart (UInt64.toNat_inj.mp same)
  have read := getValidator_eq_ok_iff.mp found
  have held := getBalance_eq_ok_iff.mp balance
  obtain ⟨insideD, rfl⟩ := decreaseBalance_eq_ok_iff.mp debited
  obtain ⟨insideT, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp credited
  have insideS : c.sourceIndex.toNat < s.balances.data.size := insideD
  have insideU : c.targetIndex.toNat < s.balances.data.size := by
    simpa [BeaconState.putBalance] using insideT
  have bEq : s.balances.data[c.sourceIndex.toNat] = b := by
    rw [Array.getElem?_eq_getElem insideS] at held
    exact Option.some.inj held
  subst bEq
  refine ⟨v, read, unslashed, UInt64.le_iff_toNat_le.mp due, ?_, ?_, ?_⟩
  · simp [actualBalanceAt, Array.getElem?_eq_getElem insideS, Base.Uint64.toNat_min]
  · simp [actualBalanceAt, BeaconState.putBalance, Ne.symm apartNat,
      Array.getElem?_eq_getElem insideS, Base.Uint64.toNat_saturatingSub, Base.Uint64.toNat_min]
  · simp [BeaconState.putBalance] at fits
    simp [actualBalanceAt, BeaconState.putBalance, Array.getElem?_eq_getElem insideU]
    rw [Array.getElem_set_ne _ insideU apartNat] at fits ⊢
    omega

/-- A pending-consolidation pass keeps the registry.

Take the longest front of the queue whose sources are slashed or can withdraw at `next`.

The pass leaves the queue without that front.

A waiting source is unslashed and cannot withdraw, so it stops the front.

A slashed or paid source is in the front, and a payment keeps the registry.

The pass is also the payment pass of its erased queue.

It splits its queue into the consumed front and the suffix.

It pays only from consumed tags, at their own sources and targets and at `next`.

Each payment is from a state with the pass's validators.

Between distinct keys, each payment moves the source's capped balance to the target. -/
theorem TaggedPass.pass_shape {fork : Fork} {next : Epoch}
    {s t : BeaconState preset fork} {queue suffix consumed : List TaggedEntry}
    {payments : List (TaggedEntry × Payment preset)}
    (history : TaggedPass next s queue t suffix consumed payments) :
    (suffix.Sublist queue ∧ t.validators = s.validators ∧
      suffix.map (·.entry) = (queue.map (·.entry)).dropWhile fun c =>
        s.validators.data[c.sourceIndex.toNat]?.any fun v =>
          v.slashed || v.withdrawableEpoch ≤ next) ∧
      PaymentPass next s (queue.map (·.entry)) t consumed.length (payments.map Prod.snd) ∧
      consumed ++ suffix = queue ∧ (payments.map Prod.fst).Sublist consumed ∧
      (∀ pair ∈ payments, pair.1 ∈ queue ∧ pair.2.source = pair.1.entry.sourceIndex.toNat ∧
        pair.2.epoch = next.toNat ∧ pair.2.target = pair.1.entry.targetIndex.toNat ∧
        ∃ w : BeaconState preset fork,
          pair.2.before = ⟨fork, w⟩ ∧ w.validators = s.validators) ∧
      ((∀ tag ∈ queue, tag.entry.sourceIndex ≠ tag.entry.targetIndex) →
        ∀ pair ∈ payments, Paying pair.2) := by
  induction history with
  | nil => exact ⟨⟨List.Sublist.refl _, rfl, rfl⟩, .nil, rfl, .slnil, by simp, by simp⟩
  | waiting found unslashed later =>
    have read := getValidator_eq_ok_iff.mp found
    refine ⟨⟨List.Sublist.refl _, rfl, ?_⟩, .waiting found unslashed later, rfl, .slnil, by simp,
      by simp⟩
    rw [List.map_cons,
      List.dropWhile_cons_of_neg (by simp [read, unslashed, UInt64.not_le.mpr later])]
  | slashed found slashed _ ih =>
    have read := getValidator_eq_ok_iff.mp found
    obtain ⟨⟨sub, same, drop⟩, rest, split, paid, members, paying⟩ := ih
    refine ⟨⟨sub.cons _, same, ?_⟩, .slashed found slashed rest,
      by rw [List.cons_append, split], paid.cons _, fun pair member =>
      ⟨List.mem_cons_of_mem _ (members pair member).1, (members pair member).2⟩,
      fun apart => paying fun tag inside => apart tag (List.mem_cons_of_mem _ inside)⟩
    rw [List.map_cons, List.dropWhile_cons_of_pos (by simp [read, slashed])]
    exact drop
  | paid found unslashed due balance debited credited _ ih =>
    have read := getValidator_eq_ok_iff.mp found
    obtain ⟨⟨sub, same, drop⟩, rest, split, paid, members, paying⟩ := ih
    -- The payment changes only balances.
    have kept := (increaseBalance_validators credited).trans (decreaseBalance_validators debited)
    refine ⟨⟨sub.cons _, same.trans kept, ?_⟩,
      .paid found unslashed due balance debited credited rest, by rw [List.cons_append, split],
      by simpa only [List.map_cons] using paid.cons_cons _, ?_, ?_⟩
    · rw [List.map_cons, List.dropWhile_cons_of_pos (by simp [read, due])]
      rw [kept] at drop
      exact drop
    · intro pair member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨List.mem_cons_self, rfl, rfl, rfl, _, rfl, rfl⟩
      · obtain ⟨inside, source, epoch, target, w, before, validators⟩ := members pair later
        exact ⟨List.mem_cons_of_mem _ inside, source, epoch, target, w, before,
          validators.trans kept⟩
    · intro apart pair member
      rcases List.mem_cons.mp member with rfl | later
      · exact pendingTransfer_paying found unslashed due balance debited credited
          (apart _ List.mem_cons_self)
      · exact paying (fun tag inside => apart tag (List.mem_cons_of_mem _ inside)) pair later

/-- A pending-consolidation pass keeps the registry.

Take the longest front of the queue whose sources are slashed or can withdraw at `next`.

The pass leaves the queue without that front.

A waiting source is unslashed and cannot withdraw, so it stops the front.

A slashed or paid source is in the front, and a payment keeps the registry. -/
theorem TaggedPass.suffix_drop {fork : Fork} {next : Epoch}
    {s t : BeaconState preset fork} {queue suffix consumed : List TaggedEntry}
    {payments : List (TaggedEntry × Payment preset)}
    (history : TaggedPass next s queue t suffix consumed payments) :
    suffix.Sublist queue ∧ t.validators = s.validators ∧
      suffix.map (·.entry) = (queue.map (·.entry)).dropWhile fun c =>
        s.validators.data[c.sourceIndex.toNat]?.any fun v =>
          v.slashed || v.withdrawableEpoch ≤ next :=
  history.pass_shape.1
/-- A pending-consolidation pass leaves a suffix of its queue.

Each step either stops with the whole remaining queue or drops its head and continues. -/
private theorem TaggedPass.suffix_sublist {fork : Fork} {next : Epoch}
    {s t : BeaconState preset fork} {queue suffix consumed : List TaggedEntry}
    {payments : List (TaggedEntry × Payment preset)}
    (history : TaggedPass next s queue t suffix consumed payments) : suffix.Sublist queue :=
  history.suffix_drop.1

/-- One tagged event either keeps a sublist of the tagged queue or appends one fresh tag.

The fresh tag comes only from the recorded case that queues a consolidation.

The other two cases keep the queue unchanged or run a pending-consolidation pass. -/
private theorem TagEvent.queue_shape {e : BalanceEvent preset} {position : Nat}
    {before after consumed : List TaggedEntry} {payments : List (TaggedEntry × Payment preset)}
    {calls : List (IndexedDepartureCall preset config)}
    (one : TagEvent (config := config) e position before after consumed payments calls) :
    after.Sublist before ∨ ∃ tag, after = before ++ [tag] ∧ tag.tag = .fresh position := by
  rcases one.2.2 with ⟨_, same, _⟩ | requested | pending
  · exact Or.inl (same ▸ List.Sublist.refl _)
  -- The request case records the appended tag as its fifteenth conjunct.
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, shape, _⟩ :=
      requested
    exact Or.inr ⟨_, shape, rfl⟩
  -- The pending case keeps the suffix its tagged pass leaves.
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, pass, _⟩ := pending
    exact Or.inl pass.suffix_sublist

section

open Cryptography.Bls

private theorem reservedEvent_bounded_non_deposit {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {before : Ownership}
    (electra : .pectra ≤ e.before.fork)
    (notDeposit : e.source ≠ .deposits) (notTransfer : e.source ≠ .consolidations)
    (fork : e.after.fork = e.before.fork)
    (registry : e.after.state.validators.data = e.before.state.validators.data)
    (epoch : getCurrentEpoch e.after.state = getCurrentEpoch e.before.state)
    (matched : e.after.state.validators.data.size = e.after.state.balances.data.size)
    (fresh : ∀ i unit, TokenOrigin.credit eventPosition i unit ∉ before.issued)
    (bounded : e.credits ≤ e.creditLimit)
    (reserve : ReserveCut x high e.before (getCurrentEpoch e.before.state)
      (queue.map (·.entry)) before)
    (assignment : AssignmentCut rounding queue before) :
    ReservedEvent x high eventPosition paymentPosition rounding e queue queue [] [] before
      (creditOwnership eventPosition e before) :=
  reservedEvent_credit_non_deposit notDeposit notTransfer fork registry epoch matched fresh
    (ownedCredit_of_bounded reserve.1 fresh electra notTransfer matched bounded) reserve assignment

end

/-- Raising one balance whose validator is not yet due is an eligible same-registry credit.

The registry and the slot stay, and only the raised index can grow. -/
private theorem increaseBalance_credit_eligible {fork : Fork} {s t : BeaconState preset fork}
    {index : ValidatorIndex} {amount : Gwei} (ok : increaseBalance s index amount = .ok t)
    (notDue : (s.validators.data[index.toNat]?.map (fun v =>
      decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false = false) :
    t.validators.data = s.validators.data ∧ getCurrentEpoch t = getCurrentEpoch s ∧
      ∀ i, actualBalanceAt (⟨fork, s⟩ : ForkedBeaconState preset) i <
          actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) i →
        (s.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false = false := by
  refine ⟨by rw [increaseBalance_validators ok],
    by simp only [getCurrentEpoch, (frame_increaseBalance ok).slot], fun i grew => ?_⟩
  by_cases same : index.toNat = i
  · exact same ▸ notDue
  -- Every other balance is unchanged, so it cannot have grown.
  · obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
    simp [actualBalanceAt, BeaconState.putBalance, same] at grew

/-- A churned deposit to a known key is an eligible same-registry credit.

The pass applies it only under one condition.

The status of the deposit target must find its validator not yet withdrawable at the next epoch.

So that validator is not due at the current epoch, and the deposit raises only its balance. -/
private theorem applyPendingDeposit_churn_eligible {fork : Fork} {s t : BeaconState preset fork}
    {deposit : PendingDeposit} {nextEpoch : Epoch} {exited : Bool} {position : Nat}
    (status : depositTargetStatus s nextEpoch deposit.pubkey = .ok (exited, false))
    (next : nextEpoch.toNat = (getCurrentEpoch s).toNat + 1)
    (known : s.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some position)
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    t.validators.data = s.validators.data ∧ getCurrentEpoch t = getCurrentEpoch s ∧
      ∀ i, actualBalanceAt (⟨fork, s⟩ : ForkedBeaconState preset) i <
          actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) i →
        (s.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false = false := by
  simp only [applyPendingDeposit, known, liftAccessor_ok, bind_ok_iff] at ok
  obtain ⟨index, converted, raised⟩ := ok
  have indexEq := (Uint64.ofNatChecked_ok_iff.mp (mapError_ok_iff.mp converted)).2
  apply increaseBalance_credit_eligible raised
  -- The status read the same position and found the validator not withdrawable.
  simp only [depositTargetStatus, known, bind_ok_iff] at status
  obtain ⟨read, readConverted, validator, found, status⟩ := status
  have readEq := (Uint64.ofNatChecked_ok_iff.mp (mapError_ok_iff.mp readConverted)).2
  rw [indexEq, ← readEq, getValidator_eq_ok_iff.mp found]
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at status
  have later : ¬ validator.withdrawableEpoch < nextEpoch := by
    simpa using status.2
  rw [UInt64.lt_iff_toNat_lt] at later
  simp only [Option.map_some, Option.getD_some, decide_eq_false_iff_not]
  omega

section

open Cryptography.Bls

/-- A deposit to a key no validator has raises no balance inside the registry.

It changes nothing, or appends one validator with its balance. -/
theorem applyPendingDeposit_absent_balances {fork : Fork}
    {u v : BeaconState preset fork} {deposit : PendingDeposit} (altair : .altair ≤ fork)
    (absent : u.validators.data.findIdx? (·.pubkey == deposit.pubkey) = none)
    (ok : applyPendingDeposit config checks u deposit = .ok v) {i : Nat}
    (inside : i < u.validators.data.size) :
    v.balances.data[i]? = u.balances.data[i]? := by
  simp only [applyPendingDeposit, absent] at ok
  split at ok
  · cases ok
    rfl
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · exact (addValidatorToRegistry_kept altair ok inside).2.1
  · cases ok
    rfl

/-- One deposit pass appends to the registry and keeps the slot.

It raises no balance except at a new index or a validator not due at the current epoch.

The one other exception is the target of a withdrawn deposit.

The fold over the applied deposits reads each deposit's status at the start of the pass.

A deposit keeps every status, so the start status is also the status when it applies.

With matched balances, each appended validator comes from a deposit.

It waits to activate, and its balance covers its effective balance.

Later deposits only raise that balance. -/
private theorem pass_deposit_shape_appended {fork : Fork} {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {available : Gwei} {deposits : List PendingDeposit}
    {s : BeaconState preset fork} {processed : Gwei} {count : Nat}
    {postponed : Array PendingDeposit} {pass : PendingDepositsPass preset fork}
    {read applied moved : List PendingDeposit}
    (electra : .pectra ≤ fork)
    (facts : PassPendingDepositsFacts config checks stop nextEpoch available s processed count
      postponed deposits pass read applied moved)
    (next : nextEpoch.toNat = (getCurrentEpoch s).toNat + 1) :
    (∃ added : Array Validator, pass.state.validators.data = s.validators.data ++ added) ∧
    pass.state.slot = s.slot ∧
    (∀ i, actualBalanceAt (⟨fork, s⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨fork, pass.state⟩ : ForkedBeaconState preset) i →
      s.validators.data.size ≤ i ∨
      (s.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false = false ∨
      ∃ deposit ∈ applied, ∃ exited,
        depositTargetStatus s nextEpoch deposit.pubkey = .ok (exited, true) ∧
        s.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some i) ∧
    -- With matched balances, each appended validator waits to activate and is funded.
    (BalancesMatch s → BalancesMatch pass.state ∧
      ∀ j w, s.validators.data.size ≤ j → pass.state.validators.data[j]? = some w →
        w.activationEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch = FAR_FUTURE_EPOCH ∧
        w.withdrawableEpoch = FAR_FUTURE_EPOCH ∧
        w.effectiveBalance.toNat ≤
          actualBalanceAt (⟨fork, pass.state⟩ : ForkedBeaconState preset) j) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  let Shape := fun u : BeaconState preset fork =>
    (∃ added : Array Validator, u.validators.data = s.validators.data ++ added) ∧
    u.slot = s.slot ∧ depositTargetStatus u = depositTargetStatus s ∧
    (BalancesMatch s → BalancesMatch u ∧
      ∀ j w, s.validators.data.size ≤ j → u.validators.data[j]? = some w →
        w.activationEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch = FAR_FUTURE_EPOCH ∧
        w.withdrawableEpoch = FAR_FUTURE_EPOCH ∧
        w.effectiveBalance.toNat ≤ actualBalanceAt (⟨fork, u⟩ : ForkedBeaconState preset) j) ∧
    ∀ i, actualBalanceAt (⟨fork, s⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨fork, u⟩ : ForkedBeaconState preset) i →
      s.validators.data.size ≤ i ∨
      (s.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false = false ∨
      ∃ deposit ∈ applied, ∃ exited,
        depositTargetStatus s nextEpoch deposit.pubkey = .ok (exited, true) ∧
        s.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some i
  have start : Shape s := ⟨⟨#[], by simp⟩, rfl, rfl,
    fun matched => ⟨matched, fun j _ outside found => by
      rw [Array.getElem?_eq_none outside] at found
      cases found⟩,
    fun _ grew => absurd grew (Nat.lt_irrefl _)⟩
  have stepKeeps : ∀ u deposit v, deposit ∈ applied → Shape u →
      applyPendingDeposit config checks u deposit = .ok v → Shape v := by
    intro u deposit v member prior ok
    obtain ⟨⟨added, grownRegistry⟩, slot, status, classified, grown⟩ := prior
    have epoch : getCurrentEpoch u = getCurrentEpoch s := by
      simp only [getCurrentEpoch, slot]
    -- The registry only grows at its end, and the slot stays.
    have frame : (∃ more : Array Validator, v.validators.data = u.validators.data ++ more) ∧
        v.slot = u.slot := by
      rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, appended⟩
      · exact ⟨⟨#[], by simp⟩, rfl⟩
      · exact ⟨⟨#[], by rw [increaseBalance_validators raised, Array.append_empty]⟩,
          (frame_increaseBalance raised).slot⟩
      · exact ⟨⟨#[_], by rw [addValidatorToRegistry_validators_eq_push appended]; rfl⟩,
          addValidatorToRegistry_slot appended⟩
    obtain ⟨⟨more, extended⟩, slotStep⟩ := frame
    -- Old appended validators stay and only gain balance; a new one comes from the deposit.
    have classifiedV : BalancesMatch s → BalancesMatch v ∧
        ∀ j w, s.validators.data.size ≤ j → v.validators.data[j]? = some w →
          w.activationEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch = FAR_FUTURE_EPOCH ∧
          w.withdrawableEpoch = FAR_FUTURE_EPOCH ∧
          w.effectiveBalance.toNat ≤
            actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) j := by
      intro matchedS
      obtain ⟨matchedU, old⟩ := classified matchedS
      refine ⟨(applyPendingDeposit_kept ok).1 matchedU, fun j w outside found => ?_⟩
      -- A deposit lowers no balance at a position that holds a validator.
      have raisedAt : ∀ w', u.validators.data[j]? = some w' →
          actualBalanceAt (⟨fork, u⟩ : ForkedBeaconState preset) j ≤
            actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) j := by
        intro w' foundU
        have notLowered := (applyPendingDeposit_balanceNotLowered altair ok
          (Array.getElem?_eq_some_iff.mp foundU).1).2.1
        cases atU : u.balances.data[j]? with
        | none => simp [actualBalanceAt, atU]
        | some earlier =>
          obtain ⟨later, atV, grown⟩ := notLowered earlier atU
          simpa [actualBalanceAt, atU, atV] using UInt64.le_iff_toNat_le.mp grown
      rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, appended⟩
      · exact old j w outside found
      · rw [increaseBalance_validators raised] at found
        obtain ⟨a, b, c, d⟩ := old j w outside found
        exact ⟨a, b, c, d.trans (raisedAt w found)⟩
      · obtain ⟨pushedValidators, pushedBalances⟩ := addValidatorToRegistry_push appended matchedU
        rw [pushedValidators, Array.getElem?_push] at found
        split at found
        · rename_i atEnd
          cases found
          have capped := UInt64.le_iff_toNat_le.mp
            (getValidatorFromDeposit_effectiveBalance_le (preset := preset) (fork := fork)
              deposit.pubkey deposit.withdrawalCredentials deposit.amount)
          have balance : actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) j =
              deposit.amount.toNat := by
            have atBalances : j = u.balances.data.size := by rw [matchedU]; exact atEnd
            simp [actualBalanceAt, pushedBalances, atBalances]
          refine ⟨rfl, rfl, rfl, ?_⟩
          rw [balance]
          exact capped
        · obtain ⟨a, b, c, d⟩ := old j w outside found
          exact ⟨a, b, c, d.trans (raisedAt w found)⟩
    refine ⟨⟨added ++ more, by rw [extended, grownRegistry, Array.append_assoc]⟩,
      slotStep.trans slot, (depositTargetStatus_applyPendingDeposit ok).trans status,
      classifiedV, fun i grew => ?_⟩
    by_cases before : actualBalanceAt (⟨fork, s⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨fork, u⟩ : ForkedBeaconState preset) i
    · exact grown i before
    -- Otherwise the deposit itself raised the balance at `i`.
    have step : actualBalanceAt (⟨fork, u⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) i := by omega
    have unchanged : v.balances.data[i]? = u.balances.data[i]? → False := by
      intro same
      simp only [actualBalanceAt, same] at step
      exact Nat.lt_irrefl _ step
    by_cases outside : s.validators.data.size ≤ i
    · exact Or.inl outside
    have inside : i < s.validators.data.size := Nat.lt_of_not_le outside
    have insideU : i < u.validators.data.size := by
      rw [grownRegistry, Array.size_append]
      omega
    have sameValidator : u.validators.data[i]? = s.validators.data[i]? := by
      rw [grownRegistry, Array.getElem?_append_left inside]
    -- The status at the start of the pass exists and is not the postponed one.
    have memberRead : deposit ∈ read := facts.appliedSublist.subset member
    obtain ⟨⟨exited, withdrawn⟩, statusS⟩ := facts.statusOk deposit memberRead
    have statusU : depositTargetStatus u nextEpoch deposit.pubkey = .ok (exited, withdrawn) := by
      rw [status]
      exact statusS
    cases found : u.validators.data.findIdx? (·.pubkey == deposit.pubkey) with
    | none =>
      exact (unchanged (applyPendingDeposit_absent_balances altair found ok insideU)).elim
    | some position =>
      cases withdrawn with
      | false =>
        -- A churned deposit raises only a validator not due at the current epoch.
        have nextU : nextEpoch.toNat = (getCurrentEpoch u).toNat + 1 := by rw [epoch]; exact next
        obtain ⟨_, _, eligible⟩ := applyPendingDeposit_churn_eligible statusU nextU found ok
        have notDue := eligible i step
        rw [sameValidator, epoch] at notDue
        exact Or.inr (Or.inl notDue)
      | true =>
        -- A withdrawn deposit raises only its target, which the start state already holds.
        have atTarget : i = position := by
          by_contra other
          exact unchanged ((applyPendingDeposit_known_balances found ok).2 i other)
        subst atTarget
        cases foundS : s.validators.data.findIdx? (·.pubkey == deposit.pubkey) with
        | none =>
          simp [depositTargetStatus, foundS, pure, Except.pure] at statusS
        | some p =>
          have same : u.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some p := by
            rw [grownRegistry, Array.findIdx?_append, foundS]
            rfl
          rw [found] at same
          cases same
          exact Or.inr (Or.inr ⟨deposit, member, exited, statusS, foundS⟩)
  have kept := foldlM_ok_invariant_of_mem Shape stepKeeps start facts.applies
  exact ⟨kept.1, kept.2.1, kept.2.2.2.2, kept.2.2.2.1⟩

/-- A validator waiting to activate at the far future is never active, so never supported. -/
private theorem far_never_supported {w : Validator}
    (activation : w.activationEpoch = FAR_FUTURE_EPOCH) (exit : w.exitEpoch = FAR_FUTURE_EPOCH)
    (t : Epoch) : ¬ SupportedAt t w := by
  have never : ∀ e : Epoch, isActiveValidator w e = false := by
    intro e
    simp only [isActiveValidator, activation, exit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases late : FAR_FUTURE_EPOCH ≤ e
    · exact Or.inr (UInt64.not_lt.mpr late)
    · exact Or.inl late
  rintro ⟨_, active | active⟩ <;> simp [never] at active

/-- Classified appended validators meet the credit adapter's held and endpoint obligations.

Such a validator had no balance before the event, so all of its balance is minted to it.

That balance covers its effective balance, and it is never supported. -/
private theorem appended_credit_obligations {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {before : Ownership} {position : Nat} {epoch : Epoch}
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (matched : BalancesMatch e.before.state)
    (classified : ∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w →
      w.activationEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch = FAR_FUTURE_EPOCH ∧
      w.withdrawableEpoch = FAR_FUTURE_EPOCH ∧
      w.effectiveBalance.toNat ≤ actualBalanceAt e.after j) :
    (∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w → ∀ t, ¬ SupportedAt t w) ∧
    (∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w →
      max (effectiveAt e.after j)
        (min (actualBalanceAt e.after j)
          (withdrawalMaxEffectiveBalance preset e.after.fork w).toNat) ≤
        (held (creditOwnership position e before) j).card) ∧
    (∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w →
      SupportedAt epoch w → w.pubkey ∉ previousOnly x →
      effectiveAt e.after j ≤ Models.supported (unslashedKeys x.state) (effectiveWeight x.state)
        w.pubkey + (held (creditOwnership position e before) j ∩
          (creditOwnership position e before).endpoint).card) := by
  have unsupported : ∀ j w, e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w → ∀ t, ¬ SupportedAt t w := by
    intro j w outside found t
    obtain ⟨activation, exit, _⟩ := classified j w outside found
    exact far_never_supported activation exit t
  refine ⟨unsupported, fun j w outside found => ?_,
    fun j w outside found support => absurd support (unsupported j w outside found epoch)⟩
  have inside : j < e.after.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  rw [creditOwnership_held fresh inside]
  -- No validator and no balance stood at `j` before, so the whole balance is minted.
  have noBalance : actualBalanceAt e.before j = 0 := by
    have past : e.before.state.balances.data.size ≤ j := by
      unfold BalancesMatch at matched
      omega
    simp [actualBalanceAt, Array.getElem?_eq_none past]
  have units : eventCreditUnits e j = actualBalanceAt e.after j := by
    simp [eventCreditUnits, Array.getElem?_eq_none outside, noBalance]
  have effective : effectiveAt e.after j = w.effectiveBalance.toNat := by
    simp [effectiveAt, found]
  have covered := (classified j w outside found).2.2.2
  rw [units, effective]
  have := Nat.min_le_left (actualBalanceAt e.after j)
    (withdrawalMaxEffectiveBalance preset e.after.fork w).toNat
  omega

private theorem pending_source_not_withdrawn {fork : Fork} {s : BeaconState preset fork}
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (electra : .pectra ≤ fork) (c : PendingConsolidation)
    (member : c ∈ (s.pendingConsolidations electra).data.toList)
    (v : Validator) (found : s.validators.data[c.sourceIndex.toNat]? = some v)
    (next : nextEpoch.toNat = (getCurrentEpoch s).toNat + 1) :
    ¬ v.withdrawableEpoch < nextEpoch := by
  have later := ((ordered.2 electra).2 c member v found).2.2
  rw [UInt64.lt_iff_toNat_lt]
  omega

private theorem pending_source_not_bypass {fork : Fork} {s : BeaconState preset fork}
    {nextEpoch : Epoch} {deposit : PendingDeposit} {exited : Bool} {i : Nat}
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (electra : .pectra ≤ fork) (c : PendingConsolidation)
    (member : c ∈ (s.pendingConsolidations electra).data.toList)
    (source : c.sourceIndex.toNat = i)
    (next : nextEpoch.toNat = (getCurrentEpoch s).toNat + 1)
    (status : depositTargetStatus s nextEpoch deposit.pubkey = .ok (exited, true))
    (known : s.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some i) : False := by
  simp only [depositTargetStatus, known, bind_ok_iff] at status
  obtain ⟨index, converted, v, found, status⟩ := status
  have indexEq := (Uint64.ofNatChecked_ok_iff.mp (mapError_ok_iff.mp converted)).2
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at status
  have withdrawn : v.withdrawableEpoch < nextEpoch := by simpa using status.2
  have queued : s.validators.data[c.sourceIndex.toNat]? = some v := by
    simpa only [source, indexEq] using getValidator_eq_ok_iff.mp found
  exact pending_source_not_withdrawn ordered electra c member v queued next withdrawn

theorem epochTrace_pendingConsolidationsOrdered {fork : Fork}
    {stages : List EpochStage} {s t : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks) stages s t)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s) :
    PendingConsolidationsOrdered config (getCurrentEpoch t).toNat t := by
  exact trace.induction_on
    (fun _ u => PendingConsolidationsOrdered config (getCurrentEpoch u).toNat u) ordered
    (fun _ _ _ _ ok held => (EpochStage.action_cases.mp ok).pendingConsolidationsOrdered held)

private theorem due_not_active {v : Validator} {current epoch : Epoch}
    (finite : current < FAR_FUTURE_EPOCH)
    (ordered : v.exitEpoch ≤ v.withdrawableEpoch)
    (delay : v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (due : v.withdrawableEpoch ≤ current) (later : current ≤ epoch) :
    isActiveValidator v epoch = false ∧ isActiveValidator v (epoch - 1) = false ∧
      ¬ (epoch < v.activationEpoch ∧ epoch < v.exitEpoch) := by
  have exitLe := UInt64.le_iff_toNat_le.mp ordered
  have dueLe := UInt64.le_iff_toNat_le.mp due
  have currentLe := UInt64.le_iff_toNat_le.mp later
  have finiteLt := UInt64.lt_iff_toNat_lt.mp finite
  have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    intro equal
    rw [equal] at exitLe
    omega
  have delayed := delay assigned
  have oneLe : (1 : Epoch) ≤ epoch := by
    rw [UInt64.le_iff_toNat_le]
    change 1 ≤ epoch.toNat
    omega
  have previous : (epoch - 1).toNat = epoch.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ oneLe
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    UInt64.lt_iff_toNat_lt, previous]
  exact ⟨Or.inr (by omega), Or.inr (by omega), fun impossible => by omega⟩

private theorem due_reserve_hidden {u : ForkedBeaconState preset} {i : Nat} {v : Validator}
    {epoch : Epoch} {suffix : List PendingConsolidation}
    (found : u.state.validators.data[i]? = some v)
    (finite : epoch < FAR_FUTURE_EPOCH)
    (ordered : v.exitEpoch ≤ v.withdrawableEpoch)
    (delay : v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (due : v.withdrawableEpoch ≤ epoch)
    (notQueued : ¬ ∃ c ∈ suffix, c.sourceIndex.toNat = i) :
    ¬ FundingRelevant u epoch suffix i ∧ (∀ e, epoch ≤ e → ¬ SupportedAt e v) ∧
      ¬ (epoch < v.activationEpoch ∧ epoch < v.exitEpoch) := by
  have unsupported (e : Epoch) (later : epoch ≤ e) : ¬ SupportedAt e v := by
    have inactive := due_not_active finite ordered delay due later
    simp only [SupportedAt, inactive.1, inactive.2.1, Bool.false_eq_true, or_self,
      and_false, not_false_eq_true]
  refine ⟨?_, unsupported, (due_not_active finite ordered delay due (UInt64.le_refl _)).2.2⟩
  rintro ⟨w, lookup, supported | notDue | queued⟩
  · obtain rfl := Option.some.inj (found.symm.trans lookup)
    exact unsupported epoch (UInt64.le_refl _) supported
  · obtain rfl := Option.some.inj (found.symm.trans lookup)
    exact (UInt64.not_lt.mpr due) notDue
  · exact notQueued queued

private theorem bypass_reserve_hidden {fork : Fork} {s : BeaconState preset fork}
    {nextEpoch : Epoch} {deposit : PendingDeposit} {exited : Bool} {i : Nat}
    {suffix : List PendingConsolidation}
    (electra : .pectra ≤ fork)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delay : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (suffixIn : ∀ c ∈ suffix, c ∈ (s.pendingConsolidations electra).data.toList)
    (next : nextEpoch.toNat = (getCurrentEpoch s).toNat + 1)
    (status : depositTargetStatus s nextEpoch deposit.pubkey = .ok (exited, true))
    (known : s.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some i) :
    ∀ w, s.validators.data[i]? = some w →
      ¬ FundingRelevant (⟨fork, s⟩ : ForkedBeaconState preset) (getCurrentEpoch s) suffix i ∧
        (∀ e, getCurrentEpoch s ≤ e → ¬ SupportedAt e w) ∧
          ¬ (getCurrentEpoch s < w.activationEpoch ∧ getCurrentEpoch s < w.exitEpoch) := by
  have noQueue : ¬ ∃ c ∈ suffix, c.sourceIndex.toNat = i := by
    rintro ⟨c, member, source⟩
    exact pending_source_not_bypass ordered electra c (suffixIn c member) source next status known
  simp only [depositTargetStatus, known, bind_ok_iff] at status
  obtain ⟨index, converted, v, read, status⟩ := status
  have indexEq := (Uint64.ofNatChecked_ok_iff.mp (mapError_ok_iff.mp converted)).2
  intro w found
  have lookup : s.validators.data[index.toNat]? = some w := by simpa only [indexEq] using found
  have same : w = v := Option.some.inj (lookup.symm.trans (getValidator_eq_ok_iff.mp read))
  subst same
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at status
  have withdrawn : w.withdrawableEpoch < nextEpoch := by simpa using status.2
  have due : w.withdrawableEpoch ≤ getCurrentEpoch s := by
    rw [UInt64.lt_iff_toNat_lt] at withdrawn
    rw [UInt64.le_iff_toNat_le]
    omega
  exact due_reserve_hidden found finite (exits w (Array.mem_of_getElem? found))
    (delay i w found) due noQueue

private theorem pass_deposit_due_hidden_of_shape {fork : Fork}
    {nextEpoch : Epoch} {s : BeaconState preset fork} {pass : PendingDepositsPass preset fork}
    {applied : List PendingDeposit} {suffix : List PendingConsolidation}
    (electra : .pectra ≤ fork)
    (shape : ∀ i, actualBalanceAt (⟨fork, s⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨fork, pass.state⟩ : ForkedBeaconState preset) i →
      s.validators.data.size ≤ i ∨
      (s.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false = false ∨
      ∃ deposit ∈ applied, ∃ exited,
        depositTargetStatus s nextEpoch deposit.pubkey = .ok (exited, true) ∧
        s.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some i)
    (next : nextEpoch.toNat = (getCurrentEpoch s).toNat + 1)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delay : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (suffixIn : ∀ c ∈ suffix, c ∈ (s.pendingConsolidations electra).data.toList) :
    ∀ i, (s.validators.data[i]?.map (fun v =>
      decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch s).toNat))).getD false = true →
      actualBalanceAt (⟨fork, s⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨fork, pass.state⟩ : ForkedBeaconState preset) i →
      ∀ w, s.validators.data[i]? = some w →
        ¬ FundingRelevant (⟨fork, s⟩ : ForkedBeaconState preset) (getCurrentEpoch s) suffix i ∧
          (∀ e, getCurrentEpoch s ≤ e → ¬ SupportedAt e w) ∧
            ¬ (getCurrentEpoch s < w.activationEpoch ∧ getCurrentEpoch s < w.exitEpoch) := by
  intro i due grew w found
  rcases shape i grew with added | eligible | bypass
  · have inside := (Array.getElem?_eq_some_iff.mp found).1
    omega
  · rw [eligible] at due
    cases due
  · obtain ⟨deposit, _, exited, status, known⟩ := bypass
    exact bypass_reserve_hidden electra ordered exits finite delay suffixIn next status known w
        found

private theorem ownedCredit_deposit {e : BalanceEvent preset} {before : Ownership}
    (deposit : e.source = .deposits) (electra : .pectra ≤ e.before.fork)
    (valid : OwnershipValid before)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued) :
    OwnedCredit position e before (creditOwnership position e before) := by
  apply ownedCredit_of_fresh valid fresh
  simp only [deposit, electra, eventCreditUnits, funding_deposit_credit, true_and, ↓reduceIte]
  exact Nat.le_refl _

/-- Take an unslashed validator that had not exited at the window start and has not exited yet.

The endpoint covers its capped balance.

It reads no demand epoch, so a validator that activates later is already covered. -/
def EndpointCoverAll (x u : ForkedBeaconState preset) (o : Ownership) : Prop :=
  ∀ (i : Nat) (v : Validator), u.state.validators.data[i]? = some v → v.slashed = false →
    getCurrentEpoch x.state < v.exitEpoch → getCurrentEpoch u.state ≤ v.exitEpoch →
    min (actualBalanceAt u i) (withdrawalMaxEffectiveBalance preset u.fork v).toNat ≤
      Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey +
        (held o i ∩ o.endpoint).card

/-- The initial ownership covers every unslashed validator that has not exited.

An active key is supported at its effective balance and holds its capped excess at the endpoint.

A key still to activate holds its potential at the endpoint. -/
theorem initialOwnership_endpointCover {g x : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) (high : Nat) :
    EndpointCoverAll x x (initialOwnership x high) := by
  intro i v found clean notExited _
  by_cases now : isActiveValidator v (getCurrentEpoch x.state) = true
  · have weight := initialOwnership_weight shared genesis early found now clean
    have kept := initialOwnership_excess (high := high) found now
    simp only [potential, found, Option.map_some, Option.getD_some] at kept
    have effective : effectiveAt x i = v.effectiveBalance.toNat := by simp [effectiveAt, found]
    rw [weight]
    omega
  · have potential := initialOwnership_potential (high := high) found
      (Bool.eq_false_iff.mpr now) notExited
    have := Nat.le_max_right v.effectiveBalance.toNat
      (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    omega

/-- Take an unslashed validator that is not yet active and whose exit is after the window start.

The endpoint covers its effective balance.

A validator still to activate may hold an effective balance above its balance.

So the capped balance that the endpoint covers for every such validator does not bound it.

The guard has no condition on an assigned activation.

The registry updates only assign an activation from the far future.

So they keep every guarded validator guarded. -/
def FutureEffectiveCover (x u : ForkedBeaconState preset) (o : Ownership) : Prop :=
  ∀ (i : Nat) (v : Validator), u.state.validators.data[i]? = some v →
    getCurrentEpoch u.state < v.activationEpoch → v.slashed = false →
    getCurrentEpoch x.state < v.exitEpoch →
    effectiveAt u i ≤ Models.supported (unslashedKeys x.state) (effectiveWeight x.state) v.pubkey +
      (held o i ∩ o.endpoint).card

/-- The initial ownership covers every validator still to activate at its potential.

That potential is at least its effective balance. -/
theorem initialOwnership_futureCover (x : ForkedBeaconState preset) (high : Nat) :
    FutureEffectiveCover x x (initialOwnership x high) := by
  intro i v found later _ notExited
  -- An activation after the current epoch is not yet active.
  have quiet : isActiveValidator v (getCurrentEpoch x.state) = false := by
    simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt64.not_le]
    exact Or.inl later
  have potential := initialOwnership_potential (high := high) found quiet notExited
  have effective : effectiveAt x i = v.effectiveBalance.toNat := by simp [effectiveAt, found]
  have := Nat.le_max_left v.effectiveBalance.toNat
    (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
  omega

/-- A step keeps the future cover when two conditions hold.

Every guarded validator after it was guarded before it, with no higher effective balance.

No key loses endpoint tokens. -/
theorem futureCover_mono {x u v : ForkedBeaconState preset} {before after : Ownership}
    (lookup : ∀ (i : Nat) (w : Validator), v.state.validators.data[i]? = some w →
      getCurrentEpoch v.state < w.activationEpoch → w.slashed = false →
      getCurrentEpoch x.state < w.exitEpoch → ∃ w₀,
        u.state.validators.data[i]? = some w₀ ∧ getCurrentEpoch u.state < w₀.activationEpoch ∧
        w₀.slashed = false ∧ getCurrentEpoch x.state < w₀.exitEpoch ∧ w₀.pubkey = w.pubkey ∧
        effectiveAt v i ≤ effectiveAt u i)
    (endpointKept : ∀ i, (held before i ∩ before.endpoint).card ≤
      (held after i ∩ after.endpoint).card)
    (cover : FutureEffectiveCover x u before) :
    FutureEffectiveCover x v after := by
  intro i w found later clean notExited
  obtain ⟨w₀, foundU, later₀, clean₀, notExited₀, key, effective⟩ :=
    lookup i w found later clean notExited
  have was := cover i w₀ foundU later₀ clean₀ notExited₀
  rw [key] at was
  have kept := endpointKept i
  omega

/-- Take a step that keeps the validators and does not move the current epoch back.

It keeps the future cover. -/
theorem futureCover_records {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {o : Ownership}
    (validators : v.validators = u.validators) (later : getCurrentEpoch u ≤ getCurrentEpoch v)
    (cover : FutureEffectiveCover x ⟨fork, u⟩ o) : FutureEffectiveCover x ⟨fork, v⟩ o := by
  apply futureCover_mono (u := ⟨fork, u⟩) ?_ (fun _ => Nat.le_refl _) cover
  intro i w found after clean notExited
  have foundU : u.validators.data[i]? = some w := by
    change v.validators.data[i]? = some w at found
    rwa [validators] at found
  refine ⟨w, foundU, UInt64.lt_of_le_of_lt later after, clean, notExited, rfl, ?_⟩
  simp only [effectiveAt, validators, le_refl]

/-- The credit ownership mints each validator's credit units at the endpoint.

It keeps every endpoint token the validator held. -/
private theorem creditOwnership_endpoint {e : BalanceEvent preset} {before : Ownership}
    {position i : Nat}
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (credit : OwnedCredit position e before (creditOwnership position e before))
    (inside : i < e.after.state.validators.data.size) :
    (held before i ∩ before.endpoint).card + eventCreditUnits e i ≤
      (held (creditOwnership position e before) i ∩
        (creditOwnership position e before).endpoint).card := by
  have heldGrowth : (held before i).card + eventCreditUnits e i ≤
      (held (creditOwnership position e before) i).card := by
    rw [creditOwnership_held fresh inside]
  exact ownedCredit_endpoint_growth credit heldGrowth

/-- An index past the registry before an event had no balance.

So all its balance after the event is credit units. -/
private theorem eventCreditUnits_appended {e : BalanceEvent preset} {i : Nat}
    (matchedBefore : BalancesMatch e.before.state)
    (old : ¬ i < e.before.state.validators.data.size) :
    eventCreditUnits e i = actualBalanceAt e.after i := by
  have past : e.before.state.balances.data.size ≤ i := by
    unfold BalancesMatch at matchedBefore
    omega
  have noBalance : actualBalanceAt e.before i = 0 := by
    simp [actualBalanceAt, Array.getElem?_eq_none past]
  simp [eventCreditUnits, Array.getElem?_eq_none (Nat.le_of_not_lt old), noBalance]

/-- A credit keeps the cover.

Every grown validator mints its growth at the endpoint.

The exception is a deposit to a validator already withdrawable.

`dueExited` shows that this validator has exited, so it is not covered.

Only a deposit needs `dueExited`.

An appended validator had no balance before, so its whole balance is minted. -/
private theorem endpointCover_credit {x : ForkedBeaconState preset} {e : BalanceEvent preset}
    {before : Ownership} {position : Nat}
    (fork : e.after.fork = e.before.fork)
    (registry : ∃ added : Array Validator,
      e.after.state.validators.data = e.before.state.validators.data ++ added)
    (epochs : getCurrentEpoch e.after.state = getCurrentEpoch e.before.state)
    (matchedBefore : BalancesMatch e.before.state)
    (dueExited : e.source = .deposits →
      ∀ (i : Nat) (v : Validator), e.before.state.validators.data[i]? = some v →
      v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat →
      v.exitEpoch < getCurrentEpoch e.before.state)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (credit : OwnedCredit position e before (creditOwnership position e before))
    (cover : EndpointCoverAll x e.before before) :
    EndpointCoverAll x e.after (creditOwnership position e before) := by
  obtain ⟨added, registry⟩ := registry
  intro i w found clean notExited current
  have inside : i < e.after.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have tokens := creditOwnership_endpoint fresh credit inside
  have capped := Nat.min_le_left (actualBalanceAt e.after i)
    (withdrawalMaxEffectiveBalance preset e.after.fork w).toNat
  by_cases old : i < e.before.state.validators.data.size
  · have foundBefore : e.before.state.validators.data[i]? = some w := by
      rw [← Array.getElem?_append_left (ys := added) old, ← registry]
      exact found
    have currentBefore : getCurrentEpoch e.before.state ≤ w.exitEpoch := epochs ▸ current
    have was := cover i w foundBefore clean notExited currentBefore
    -- A covered validator has not exited, so it is not a withdrawable deposit target.
    have units : actualBalanceAt e.after i ≤ actualBalanceAt e.before i + eventCreditUnits e i := by
      simp only [eventCreditUnits]
      split_ifs with due
      · have flag := due.2
        simp only [foundBefore, Option.map_some, Option.getD_some, decide_eq_true_eq] at flag
        have exited := dueExited due.1 i w foundBefore flag
        exact absurd currentBefore (UInt64.not_le.mpr exited)
      · omega
    have capBefore := Nat.min_le_left (actualBalanceAt e.before i)
      (withdrawalMaxEffectiveBalance preset e.before.fork w).toNat
    rw [fork]
    rw [fork] at capped
    omega
  · -- An appended validator had no balance before, so its whole balance is minted.
    have units := eventCreditUnits_appended matchedBefore old
    omega

/-- A credit keeps the future cover.

An old validator keeps its effective balance and every endpoint token it held.

An appended validator had no balance before, so its whole balance is minted at the endpoint.

`appendedEffective` bounds its effective balance by that balance. -/
theorem futureCover_credit {x : ForkedBeaconState preset} {e : BalanceEvent preset}
    {before : Ownership} {position : Nat}
    (registry : ∃ added : Array Validator,
      e.after.state.validators.data = e.before.state.validators.data ++ added)
    (epochs : getCurrentEpoch e.after.state = getCurrentEpoch e.before.state)
    (matchedBefore : BalancesMatch e.before.state)
    (appendedEffective : ∀ (j : Nat) (w : Validator), e.before.state.validators.data.size ≤ j →
      e.after.state.validators.data[j]? = some w →
      w.effectiveBalance.toNat ≤ actualBalanceAt e.after j)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (credit : OwnedCredit position e before (creditOwnership position e before))
    (cover : FutureEffectiveCover x e.before before) :
    FutureEffectiveCover x e.after (creditOwnership position e before) := by
  obtain ⟨added, registry⟩ := registry
  intro i w found later clean notExited
  have inside : i < e.after.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have tokens := creditOwnership_endpoint fresh credit inside
  have effective : effectiveAt e.after i = w.effectiveBalance.toNat := by
    simp [effectiveAt, found]
  by_cases old : i < e.before.state.validators.data.size
  · have foundBefore : e.before.state.validators.data[i]? = some w := by
      rw [← Array.getElem?_append_left (ys := added) old, ← registry]
      exact found
    have was := cover i w foundBefore (epochs ▸ later) clean notExited
    have same : effectiveAt e.before i = w.effectiveBalance.toNat := by
      simp [effectiveAt, foundBefore]
    omega
  · have units := eventCreditUnits_appended matchedBefore old
    have bound := appendedEffective i w (Nat.le_of_not_lt old) found
    omega

/-- A credit that is not a deposit, on the same registry, keeps the cover. -/
theorem endpointCover_nonDeposit {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {before : Ownership} {position : Nat}
    (notDeposit : e.source ≠ .deposits)
    (fork : e.after.fork = e.before.fork)
    (registry : e.after.state.validators.data = e.before.state.validators.data)
    (epochs : getCurrentEpoch e.after.state = getCurrentEpoch e.before.state)
    (matchedBefore : BalancesMatch e.before.state)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (credit : OwnedCredit position e before (creditOwnership position e before))
    (cover : EndpointCoverAll x e.before before) :
    EndpointCoverAll x e.after (creditOwnership position e before) :=
  endpointCover_credit fork ⟨#[], by rw [registry, Array.append_empty]⟩ epochs matchedBefore
    (fun deposit => absurd deposit notDeposit) fresh credit cover

/-- An owned transfer leaves every other key's endpoint tokens exactly as they were.

That key's tokens were neither the source's nor new, and the endpoint changes only at those. -/
theorem ownedTransfer_endpoint_other {position : Nat} {p : Payment preset}
    {allocation : OwnedRelease} {before after : Ownership}
    (transfer : OwnedTransfer position p allocation before after)
    (apart : p.source ≠ p.target) {i : Nat} (source : i ≠ p.source) (target : i ≠ p.target) :
    held after i ∩ after.endpoint = held before i ∩ before.endpoint := by
  rw [(ownedTransfer_held transfer apart).2.2 i source target]
  obtain ⟨_, _, moved, minted, inside, _, _, fresh, _, _, _, _, _, _, _, _, _, _,
    endpoint⟩ := transfer
  have notSource : ∀ token ∈ held before i, token ∉ held before p.source := by
    intro token mine theirs
    have one := (Finset.mem_filter.mp mine).2
    have two := (Finset.mem_filter.mp theirs).2
    rw [one] at two
    exact source (Option.some.inj two)
  ext token
  simp only [Finset.mem_inter, endpoint, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨mine, (⟨atEndpoint, _⟩ | wasMoved) | wasMinted⟩
    · exact ⟨mine, atEndpoint⟩
    · exact absurd (inside wasMoved) (notSource token mine)
    · exact absurd wasMinted
        (Finset.disjoint_left.mp fresh (Finset.mem_filter.mp mine).1)
  · rintro ⟨mine, atEndpoint⟩
    exact ⟨mine, Or.inl (Or.inl ⟨atEndpoint, notSource token mine⟩)⟩

/-- An owned transfer keeps the cover when its source is no longer covered.

The target gains the whole payment at its endpoint, and its balance gains at most the payment.

Every other key keeps its held tokens, and so its endpoint tokens.

The reason is that none of them was the source's or is new. -/
private theorem endpointCover_transfer {x u v : ForkedBeaconState preset} {position : Nat}
    {p : Payment preset} {allocation : OwnedRelease} {before after : Ownership}
    (transfer : OwnedTransfer position p allocation before after)
    (apart : p.source ≠ p.target)
    (fork : v.fork = u.fork) (registry : v.state.validators.data = u.state.validators.data)
    (epochs : getCurrentEpoch v.state = getCurrentEpoch u.state)
    (targetBalance : actualBalanceAt v p.target ≤ actualBalanceAt u p.target + p.amount)
    (others : ∀ i, i ≠ p.source → i ≠ p.target → actualBalanceAt v i ≤ actualBalanceAt u i)
    (sourceGone : ∀ w, u.state.validators.data[p.source]? = some w → w.slashed = false →
      getCurrentEpoch x.state < w.exitEpoch → getCurrentEpoch u.state ≤ w.exitEpoch → False)
    (cover : EndpointCoverAll x u before) :
    EndpointCoverAll x v after := by
  have targetEndpoint := (ownedTransfer_held transfer apart).2.1
  intro i w found clean notExited current
  have foundU : u.state.validators.data[i]? = some w := registry ▸ found
  have currentU : getCurrentEpoch u.state ≤ w.exitEpoch := epochs ▸ current
  have was := cover i w foundU clean notExited currentU
  rw [fork]
  have capU := Nat.min_le_left (actualBalanceAt u i)
    (withdrawalMaxEffectiveBalance preset u.fork w).toNat
  by_cases source : i = p.source
  · subst source
    exact (sourceGone w foundU clean notExited currentU).elim
  by_cases target : i = p.target
  · subst target
    omega
  -- Another key keeps exactly its endpoint tokens.
  rw [ownedTransfer_endpoint_other transfer apart source target]
  have balance := others i source target
  have capV := Nat.min_le_left (actualBalanceAt v i)
    (withdrawalMaxEffectiveBalance preset u.fork w).toNat
  omega

/-- A step keeps the cover when two conditions hold.

Every covered validator after it was covered before it, with no more capped balance.

No key loses endpoint tokens.

An ownership frame alone does not give `endpointKept`.

It may erase an owner or drop an endpoint token.

So each frame of the history must supply it. -/
theorem endpointCover_mono {x u v : ForkedBeaconState preset} {before after : Ownership}
    (lookup : ∀ (i : Nat) (w : Validator), v.state.validators.data[i]? = some w →
      w.slashed = false → getCurrentEpoch x.state < w.exitEpoch →
      getCurrentEpoch v.state ≤ w.exitEpoch → ∃ w₀,
        u.state.validators.data[i]? = some w₀ ∧ w₀.slashed = false ∧
        getCurrentEpoch x.state < w₀.exitEpoch ∧ getCurrentEpoch u.state ≤ w₀.exitEpoch ∧
        w₀.pubkey = w.pubkey ∧
        min (actualBalanceAt v i) (withdrawalMaxEffectiveBalance preset v.fork w).toNat ≤
          min (actualBalanceAt u i) (withdrawalMaxEffectiveBalance preset u.fork w₀).toNat)
    (endpointKept : ∀ i, (held before i ∩ before.endpoint).card ≤
      (held after i ∩ after.endpoint).card)
    (cover : EndpointCoverAll x u before) :
    EndpointCoverAll x v after := by
  intro i w found clean notExited current
  obtain ⟨w₀, foundU, clean₀, notExited₀, current₀, key, capped⟩ :=
    lookup i w found clean notExited current
  have was := cover i w₀ foundU clean₀ notExited₀ current₀
  rw [key] at was
  have kept := endpointKept i
  omega

theorem due_exit_before {v : Validator} {current next : Epoch}
    (finite : next < FAR_FUTURE_EPOCH)
    (ordered : v.exitEpoch ≤ v.withdrawableEpoch)
    (delay : v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (due : v.withdrawableEpoch ≤ next)
    (nextBound : next.toNat ≤ current.toNat + 1) : v.exitEpoch < current := by
  have orderedNat := UInt64.le_iff_toNat_le.mp ordered
  have dueNat := UInt64.le_iff_toNat_le.mp due
  have finiteNat := UInt64.lt_iff_toNat_lt.mp finite
  have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    intro same
    rw [same] at orderedNat
    omega
  have delayed := delay assigned
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

private theorem endpoint_dueExited {v : Validator} {current : Epoch}
    (finite : current < FAR_FUTURE_EPOCH)
    (ordered : v.exitEpoch ≤ v.withdrawableEpoch)
    (delay : v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (due : v.withdrawableEpoch.toNat ≤ current.toNat) : v.exitEpoch < current :=
  due_exit_before finite ordered delay (UInt64.le_iff_toNat_le.mpr due) (by omega)

private theorem endpoint_sourceGone {v : Validator} {current next : Epoch}
    (finite : next < FAR_FUTURE_EPOCH)
    (ordered : v.exitEpoch ≤ v.withdrawableEpoch)
    (delay : v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (due : v.withdrawableEpoch ≤ next)
    (checked : Uint64.addChecked current 1 = .ok next)
    (covered : current ≤ v.exitEpoch) : False := by
  have nextEq := (Uint64.addChecked_ok_iff.mp checked).2
  have exited := due_exit_before (current := current) (next := next)
    finite ordered delay due (by simpa only [UInt64.reduceToNat] using nextEq.le)
  exact (UInt64.not_le.mpr exited) covered

/-- The pending deposits keep the reserve cut, the endpoint cover and the future cover.

They do so after one credit event.

Both read the same pass shape and the same owned credit of the event.

The cover needs no balance bound on new validators.

An appended index has no unit before, and the event mints its whole balance.

An appended validator's effective balance is at most its balance.

So the future cover holds for it too.

A covered validator is not due.

A due one has exited before the current epoch.

The reason is that its exit is assigned and at least two epochs before its withdrawal. -/
private theorem processPendingDeposits_reserve_covers {fork : Fork}
    {s t : BeaconState preset fork}
    {x : ForkedBeaconState preset} {high position : Nat} {before : Ownership}
    {suffix : List PendingConsolidation}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delay : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (suffixIn : ∀ c ∈ suffix, c ∈ (s.pendingConsolidations electra).data.toList)
    (referenceSize : x.state.validators.data.size ≤ s.validators.data.size)
    (ok : processPendingDeposits config checks s electra = .ok t)
    (fresh : ∀ i unit, TokenOrigin.credit position i unit ∉ before.issued)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) suffix before) :
    let event : BalanceEvent preset :=
      ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩
    ReserveCut x high ⟨fork, t⟩ (getCurrentEpoch s) suffix
        (creditOwnership position event before) ∧
      (EndpointCoverAll x ⟨fork, s⟩ before →
        EndpointCoverAll x ⟨fork, t⟩ (creditOwnership position event before)) ∧
      (FutureEffectiveCover x ⟨fork, s⟩ before →
        FutureEffectiveCover x ⟨fork, t⟩ (creditOwnership position event before)) := by
  dsimp only
  let event : BalanceEvent preset :=
    ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩
  obtain ⟨nextEpoch, _, _, _, pass, nextOk, _, _, _, passOk, validators, balances, _, _⟩ :=
    processPendingDeposits_pass ok
  have next := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp nextOk)).2
  obtain ⟨_, _, _, facts⟩ := passPendingDeposits_applied passOk
  have shape := pass_deposit_shape_appended electra facts (by simpa using next)
  obtain ⟨matchedPass, classifiedPass⟩ := shape.2.2.2 matched
  have registry : ∃ added : Array Validator, t.validators.data = s.validators.data ++ added := by
    simpa only [validators] using shape.1
  have matchedAfter : BalancesMatch t := by
    simpa only [BalancesMatch, validators, balances] using matchedPass
  have classified : ∀ j w, s.validators.data.size ≤ j → t.validators.data[j]? = some w →
      w.activationEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch = FAR_FUTURE_EPOCH ∧
        w.withdrawableEpoch = FAR_FUTURE_EPOCH ∧
          w.effectiveBalance.toNat ≤ actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) j := by
    simpa only [validators, actualBalanceAt, balances] using classifiedPass
  have hiddenPass := pass_deposit_due_hidden_of_shape electra shape.2.2.1
    (by simpa using next) ordered exits finite delay suffixIn
  have hidden := hiddenPass
  simp only [actualBalanceAt, ← balances] at hidden
  have credit := ownedCredit_deposit (e := event) rfl electra reserve.1 fresh
  have appended := appended_credit_obligations (e := event) (x := x)
    (epoch := getCurrentEpoch s) fresh matched classified
  -- The pass keeps the slot, so the event's two states share the current epoch.
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, (frame_processPendingDeposits ok).slot]
  refine ⟨?_, fun cover => endpointCover_credit (e := event) rfl registry epoch matched
    (fun _ i v found due => endpoint_dueExited finite (exits v (Array.mem_of_getElem? found))
      (delay i v found) due) fresh credit cover,
    fun cover => futureCover_credit (e := event) registry epoch matched
      (fun j w outside found => (classified j w outside found).2.2.2) fresh credit cover⟩
  apply reserveCut_credit_hidden_append (e := event)
    (fun i _ due grew => hidden i due grew) rfl registry matchedAfter.symm fresh credit
  · intro j w outside _
    change s.validators.data.size ≤ j at outside
    exact Array.getElem?_eq_none (by omega)
  · intro j w outside found _
    change s.validators.data.size ≤ j at outside
    refine ⟨fun e _ => appended.1 j w outside found e, ?_⟩
    rintro ⟨c, member, source⟩
    obtain ⟨v, lookup, _⟩ := (ordered.1 electra).2 c (suffixIn c member)
    have inside := (Array.getElem?_eq_some_iff.mp lookup).1
    omega
  · exact appended.2.1
  · exact appended.2.2
  · exact reserve

private theorem reservedEvent_processPendingDeposits_cover {fork : Fork}
    {s t : BeaconState preset fork} {x : ForkedBeaconState preset}
    {high eventPosition paymentPosition : Nat} {before : Ownership}
    {rounding : Nat → Nat} {queue : List TaggedEntry}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delay : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (queueIn : ∀ c ∈ queue.map (·.entry), c ∈ (s.pendingConsolidations electra).data.toList)
    (referenceSize : x.state.validators.data.size ≤ s.validators.data.size)
    (ok : processPendingDeposits config checks s electra = .ok t)
    (fresh : ∀ i unit, TokenOrigin.credit eventPosition i unit ∉ before.issued)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) before)
    (assignment : AssignmentCut rounding queue before) :
    let event : BalanceEvent preset :=
      ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩
    ReservedEvent x high eventPosition paymentPosition rounding event queue queue [] [] before
      (creditOwnership eventPosition event before) ∧
      (EndpointCoverAll x ⟨fork, s⟩ before →
        EndpointCoverAll x ⟨fork, t⟩ (creditOwnership eventPosition event before)) ∧
      (FutureEffectiveCover x ⟨fork, s⟩ before →
        FutureEffectiveCover x ⟨fork, t⟩ (creditOwnership eventPosition event before)) := by
  dsimp only
  let event : BalanceEvent preset :=
    ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩
  have credit := ownedCredit_deposit (e := event) rfl electra reserve.1 fresh
  have transported := processPendingDeposits_reserve_covers electra matched ordered exits finite
    delay queueIn referenceSize ok fresh reserve
  refine ⟨?_, transported.2.1, transported.2.2⟩
  refine ⟨?_, assignment, assignmentCut_credit assignment credit (List.Sublist.refl _), ?_⟩
  · simp only [OwnedEvent, reduceCtorEq, ↓reduceIte]
    exact ⟨True.intro, True.intro, Or.inl credit⟩
  · change ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) before ∧
      ReserveCut x high ⟨fork, t⟩ (getCurrentEpoch t) (queue.map (·.entry))
        (creditOwnership eventPosition event before)
    refine ⟨reserve, ?_⟩
    have epoch : getCurrentEpoch t = getCurrentEpoch s := by
      simp only [getCurrentEpoch, (frame_processPendingDeposits ok).slot]
    rw [epoch]
    exact transported.1

theorem deposit_prefix_facts {fork : Fork} {s t : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks)
      [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset] s t)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s)
    (delay : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
        v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
          v.withdrawableEpoch.toNat) :
    t.slot = s.slot ∧
      PendingConsolidationsOrdered config (getCurrentEpoch t).toNat t ∧ ExitsOrdered t ∧
        ∀ (i : Nat) (v : Validator), t.validators.data[i]? = some v →
          v.exitEpoch ≠ FAR_FUTURE_EPOCH →
            v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
              v.withdrawableEpoch.toNat := by
  let schedule : List EpochStage :=
    [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset]
  let Q (rest : List EpochStage) (u : BeaconState preset fork) :=
    (∀ k ∈ rest, k ∈ schedule) ∧ u.slot = s.slot ∧
      PendingConsolidationsOrdered config (getCurrentEpoch u).toNat u ∧ ExitsOrdered u ∧
        ∀ (i : Nat) (v : Validator), u.validators.data[i]? = some v →
          v.exitEpoch ≠ FAR_FUTURE_EPOCH →
            v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
              v.withdrawableEpoch.toNat
  have start : Q schedule s := ⟨fun _ member => member, rfl, ordered, exits, delay⟩
  have finish := trace.induction_on Q start (fun k rest a b ok prior => by
    have edge := EpochStage.action_cases.mp ok
    have member := prior.1 k List.mem_cons_self
    refine ⟨fun j inside => prior.1 j (List.mem_cons_of_mem k inside),
      edge.slot_eq.trans prior.2.1, edge.pendingConsolidationsOrdered prior.2.2.1,
      ?_, edge.exit_withdrawable_delay prior.2.2.2.2⟩
    by_cases justification : k = .justification
    · subst k
      have registry := (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).1
      simpa only [ExitsOrdered, registry] using prior.2.2.2.1
    · have ordinary : k ≠ .justification ∧ k ≠ .payments ∧ k ≠ .participation ∧
          k ≠ .pendingDeposits := by
        simp only [schedule, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      exact (mutatorEpochFrameLaws.toEpochStepLaws.epochEdge ordinary ok).toFrame.exitsOrdered
        prior.2.2.2.1)
  exact finish.2

private theorem tagEvent_processPendingDeposits {fork : Fork} {s t : BeaconState preset fork}
    {queue : List TaggedEntry} (electra : .pectra ≤ fork)
    (ok : processPendingDeposits config checks s electra = .ok t)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    TagEvent (config := config)
      ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩
      position queue queue [] [] [] := by
  have same : pendingQueue (⟨fork, t⟩ : ForkedBeaconState preset) = pendingQueue ⟨fork, s⟩ := by
    simp only [pendingQueue, electra, ↓reduceDIte,
      processPendingDeposits_pendingConsolidations ok]
  exact ⟨erasure, same ▸ erasure,
    Or.inl ⟨by change BalanceSource.deposits ≠ .consolidations; decide, rfl, rfl, rfl, rfl⟩⟩

def OwnershipBefore (eventPosition paymentPosition : Nat) (owned : Ownership) : Prop :=
  ∀ token ∈ owned.issued, match token with
    | .initial _ _ _ => True
    | .credit position _ _ => position < eventPosition
    | .released position _ => position < paymentPosition

theorem OwnedInitial.counters (initial : OwnedInitial x high owned) :
    OwnershipBefore 0 0 owned := by
  intro token member
  obtain ⟨pot, index, unit, rfl, _⟩ := initial.2.2.2.1 token member
  trivial

theorem OwnershipBefore.credit_fresh
    (prior : OwnershipBefore eventPosition paymentPosition owned)
    (later : eventPosition ≤ position) :
    ∀ i unit, TokenOrigin.credit position i unit ∉ owned.issued := by
  intro i unit member
  have earlier := prior _ member
  change position < eventPosition at earlier
  omega

theorem OwnershipBefore.release_fresh
    (prior : OwnershipBefore eventPosition paymentPosition owned)
    (later : paymentPosition ≤ position) :
    ∀ unit, TokenOrigin.released position unit ∉ owned.issued := by
  intro unit member
  have earlier := prior _ member
  change position < paymentPosition at earlier
  omega

theorem OwnershipBefore.credit {e : BalanceEvent preset}
    (prior : OwnershipBefore eventPosition paymentPosition before)
    (credit : OwnedCredit eventPosition e before after) :
    OwnershipBefore (eventPosition + 1) paymentPosition after := by
  obtain ⟨_, _, minted, _, issued, origins, _⟩ := credit
  intro token member
  rw [issued] at member
  rcases Finset.mem_union.mp member with old | new
  · have earlier := prior token old
    cases token <;> dsimp only at earlier ⊢ <;> omega
  · obtain ⟨i, unit, rfl, _⟩ := origins token new
    exact Nat.lt_succ_self _

theorem OwnershipBefore.frame
    (prior : OwnershipBefore eventPosition paymentPosition before)
    (frame : OwnedFrame before after) :
    OwnershipBefore eventPosition paymentPosition after := by
  intro token member
  rw [frame.2.2.1] at member
  exact prior token member

theorem OwnershipBefore.mono
    (prior : OwnershipBefore eventPosition paymentPosition owned)
    (events : eventPosition ≤ nextEvent) (payments : paymentPosition ≤ nextPayment) :
    OwnershipBefore nextEvent nextPayment owned := by
  intro token member
  have earlier := prior token member
  cases token <;> dsimp only at earlier ⊢ <;> omega

theorem OwnershipBefore.transfer {p : Payment preset} {allocation : OwnedRelease}
    (prior : OwnershipBefore eventPosition paymentPosition before)
    (transfer : OwnedTransfer paymentPosition p allocation before after) :
    OwnershipBefore eventPosition (paymentPosition + 1) after := by
  obtain ⟨_, _, _, minted, _, _, mintedEq, _, issued, _⟩ := transfer
  intro token member
  rw [issued] at member
  rcases Finset.mem_union.mp member with old | new
  · have earlier := prior token old
    cases token <;> dsimp only at earlier ⊢ <;> omega
  · rw [mintedEq] at new
    obtain ⟨unit, _, rfl⟩ := Finset.mem_image.mp new
    exact Nat.lt_succ_self _

/-- The credit bound that an owned credit puts on the tokens one event mints. -/
def ownedCreditBound (e : BalanceEvent preset) : Nat :=
  if e.source = .deposits then funding_deposit_credit e
  else if e.source = .rewards ∨ e.source = .sync then e.creditLimit else otherCredit e

/-- Adding disjoint tokens adds their filtered count. -/
private theorem filter_union_card (p : TokenOrigin → Prop) [DecidablePred p]
    {issued minted : Finset TokenOrigin}
    (apart : Disjoint issued minted) :
    ((issued ∪ minted).filter p).card = (issued.filter p).card + (minted.filter p).card := by
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter apart)]

/-- Adding tokens that all fail a test keeps the tokens that pass it. -/
private theorem filter_union_none (p : TokenOrigin → Prop) [DecidablePred p]
    (issued : Finset TokenOrigin) {minted : Finset TokenOrigin} (none : ∀ t ∈ minted, ¬ p t) :
    (issued ∪ minted).filter p = issued.filter p := by
  rw [Finset.filter_union, Finset.filter_eq_empty_iff.mpr none, Finset.union_empty]

/-- Owned payments, with the tokens they issue.

They issue no initial or credit token, and one released token per unit of baseline. -/
private theorem OwnedPayments.counters_ledger {paid : List (Payment preset)}
    (payments : OwnedPayments paymentPosition paid allocations before after)
    (prior : OwnershipBefore eventPosition paymentPosition before) :
    OwnershipBefore eventPosition (paymentPosition + paid.length) after ∧
    after.issued.filter ((·.isInitial)) =
      before.issued.filter ((·.isInitial)) ∧
    after.issued.filter ((·.isCredit)) =
      before.issued.filter ((·.isCredit)) ∧
    (after.issued.filter ((·.isReleased))).card =
      (before.issued.filter ((·.isReleased))).card +
        (allocations.map (·.baseline)).sum := by
  induction payments generalizing eventPosition with
  | nil => exact ⟨by simpa only [List.length_nil, Nat.add_zero] using prior, rfl, rfl, by simp⟩
  | @cons position p allocation before middle payments allocations after one _ ih =>
    obtain ⟨counted, initialEq, creditEq, releasedEq⟩ := ih (prior.transfer one)
    obtain ⟨_, _, _, minted, _, _, mintedEq, apart, issued, _⟩ := one
    have released : ∀ t ∈ minted, ∃ unit, t = .released position unit := by
      intro t member
      rw [mintedEq] at member
      obtain ⟨unit, _, rfl⟩ := Finset.mem_image.mp member
      exact ⟨unit, rfl⟩
    have allReleased : minted.filter
        ((·.isReleased)) = minted :=
      Finset.filter_true_of_mem fun t member => by
        obtain ⟨unit, rfl⟩ := released t member
        simp
    have count : minted.card = allocation.baseline := by
      rw [mintedEq, Finset.card_image_of_injective _ (fun a b same => by cases same; rfl),
        Finset.card_range]
    refine ⟨by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using counted, ?_, ?_, ?_⟩
    · rw [initialEq, issued]
      exact filter_union_none _ _ fun t member => by
        obtain ⟨unit, rfl⟩ := released t member
        simp
    · rw [creditEq, issued]
      exact filter_union_none _ _ fun t member => by
        obtain ⟨unit, rfl⟩ := released t member
        simp
    · rw [releasedEq, issued, filter_union_card _ apart, allReleased, count]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- An owned event, with the tokens it issues.

A credit issues at most its credit bound of credit tokens.

A consolidation issues its released tokens, and a frame issues none. -/
private theorem OwnedEvent.counters_ledger {e : BalanceEvent preset}
    (event : OwnedEvent eventPosition paymentPosition e tagged allocations before after)
    (prior : OwnershipBefore eventPosition paymentPosition before) :
    OwnershipBefore (eventPosition + 1) (paymentPosition + tagged.length) after ∧
    after.issued.filter ((·.isInitial)) =
      before.issued.filter ((·.isInitial)) ∧
    (after.issued.filter ((·.isCredit))).card ≤
      (before.issued.filter ((·.isCredit))).card +
        ownedCreditBound e ∧
    (after.issued.filter ((·.isReleased))).card =
      (before.issued.filter ((·.isReleased))).card +
        (allocations.map (·.baseline)).sum := by
  unfold OwnedEvent at event
  split at event
  · obtain ⟨counted, initialEq, creditEq, releasedEq⟩ := event.1.counters_ledger prior
    simp only [List.length_map] at counted
    exact ⟨counted.mono (Nat.le_succ _) (Nat.le_refl _), initialEq, by rw [creditEq]; omega,
      releasedEq⟩
  · obtain ⟨rfl, rfl, credit | frame⟩ := event
    · have counted := prior.credit credit
      obtain ⟨_, _, minted, apart, issued, origins, bound, _⟩ := credit
      have credited : ∀ t ∈ minted, ∃ i unit, t = .credit eventPosition i unit := by
        intro t member
        obtain ⟨i, unit, same, _⟩ := origins t member
        exact ⟨i, unit, same⟩
      refine ⟨by simpa only [List.length_nil, Nat.add_zero] using counted, ?_, ?_, ?_⟩
      · rw [issued]
        exact filter_union_none _ _ fun t member => by
          obtain ⟨i, unit, rfl⟩ := credited t member
          simp
      · rw [issued, filter_union_card _ apart]
        have small := Finset.card_filter_le minted
          ((·.isCredit))
        unfold ownedCreditBound
        omega
      · rw [issued, filter_union_none _ _ fun t member => by
          obtain ⟨i, unit, rfl⟩ := credited t member
          simp]
        simp
    · have same := frame.2.2.1
      refine ⟨by simpa only [List.length_nil, Nat.add_zero] using
        (prior.frame frame).mono (Nat.le_succ _) (Nat.le_refl _), by rw [same], ?_, ?_⟩
      · rw [same]
        omega
      · rw [same]
        simp

/-- Queueing a consolidation appends its entry to the pending consolidations. -/
theorem queueConsolidation_pendingConsolidations {fork : Fork}
    {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    (t.pendingConsolidations electra).data.toList =
      (s.pendingConsolidations electra).data.toList ++ [⟨sourceIndex, targetIndex⟩] := by
  obtain ⟨_, _, _, _, _, _, _, set, appended, rfl⟩ := queueConsolidation_steps ok
  -- The churn update and the registry write keep the queue.
  obtain ⟨_, rfl⟩ := setValidator_ok set
  simp [appendWithinLimit_data appended, BeaconState.putValidator]

/-- Switching to compounding credentials keeps the pending consolidations.

It also keeps the consolidation churn state. -/
theorem switchToCompoundingValidator_consolidationQueues {fork : Fork}
    {s t : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) :
    t.pendingConsolidations electra = s.pendingConsolidations electra ∧
      t.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra ∧
      t.consolidationBalanceToConsume electra = s.consolidationBalanceToConsume electra := by
  simp only [switchToCompoundingValidator, queueExcessActiveBalance, bind_ok_iff, pure,
    Except.pure] at ok
  obtain ⟨_, _, written, set, _, _, queued⟩ := ok
  obtain ⟨_, rfl⟩ := setValidator_ok set
  -- The excess balance moves to the pending deposits only.
  split at queued
  · simp only [bind_ok_iff, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, balanced, setBalance, rfl⟩ := queued
    obtain ⟨_, rfl⟩ := setBalance_ok setBalance
    exact ⟨rfl, rfl, rfl⟩
  · cases queued
    exact ⟨rfl, rfl, rfl⟩

/-- Let each queued entry be initially queued, or have a source whose exit is unset at `x`.

One recorded event keeps this.

A request queues only an accepted source, and an accepted source has no exit at the event's state.

The registry lifecycle from `x` to that state then leaves the exit unset at `x`.

The pending pass keeps a sublist of the queue, and every other event keeps the queue.

It also returns, for every tag the event appends, the unset exit at `x` of the tag's source. -/
private theorem TagEvent.queueProvenance_appended {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {position : Nat} {before after consumed : List TaggedEntry}
    {payments : List (TaggedEntry × Payment preset)}
    {calls : List (IndexedDepartureCall preset config)}
    (one : TagEvent (config := config) e position before after consumed payments calls)
    (life : RegistryLifecycle x.state e.before.state)
    (held : ∀ c ∈ before.map (·.entry), c ∈ pendingQueue x ∨
          (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH)) :
    (∀ c ∈ after.map (·.entry), c ∈ pendingQueue x ∨
          (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH)) ∧
      ∀ tag ∈ after, tag ∉ before →
        (x.state.validators.data[tag.entry.sourceIndex.toNat]?).all
          (·.exitEpoch == FAR_FUTURE_EPOCH) := by
  obtain ⟨erasedBefore, erasedAfter, rest⟩ := one
  rcases rest with ⟨_, rfl, _⟩ | requested | pending
  · exact ⟨held, fun _ member fresh => absurd member fresh⟩
  · obtain ⟨fork, s, t, electra, request, sourceIndex, source, targetIndex, called, _, beforeEq,
      afterEq, processed, found, _, _, _, _, _, _, _, _, _, shape, _⟩ := requested
    subst shape
    -- The queue at the event's end is the queue at its start with the new entry.
    have grown : (t.pendingConsolidations electra).data.toList =
        (s.pendingConsolidations electra).data.toList ++ [⟨sourceIndex, targetIndex⟩] := by
      have endQueue := erasedAfter
      have startQueue := erasedBefore
      unfold QueueErasure at endQueue startQueue
      rw [afterEq] at endQueue
      rw [beforeEq] at startQueue
      simp only [pendingQueue, electra, ↓reduceDIte] at endQueue startQueue
      rw [← endQueue, ← startQueue, List.map_append]
      rfl
    have sourceAt := getValidator_eq_ok_iff.mp found
    -- The request queued an accepted source, which is this source, with an unset exit.
    have unset : source.exitEpoch = FAR_FUTURE_EPOCH := by
      rcases consolidationRequest_cases processed with rfl | ⟨_, _, _, switched⟩ |
        ⟨index, accepted, _, _, valid, again⟩
      · have sizes := congrArg List.length grown
        simp at sizes
      · rw [(switchToCompoundingValidator_consolidationQueues switched).1] at grown
        have sizes := congrArg List.length grown
        simp at sizes
      · rw [queueConsolidation_pendingConsolidations again, List.append_cancel_left_eq] at grown
        simp only [List.cons.injEq, PendingConsolidation.mk.injEq, and_true] at grown
        obtain ⟨rfl, -⟩ := grown
        obtain rfl := Option.some.inj (valid.sourceAt.symm.trans sourceAt)
        exact valid.sourceStays
    -- The lifecycle from `x` leaves the appended source's exit unset at `x`.
    have unsetX : (x.state.validators.data[sourceIndex.toNat]?).all
        (·.exitEpoch == FAR_FUTURE_EPOCH) := by
      cases initial : x.state.validators.data[sourceIndex.toNat]? with
      | none => rfl
      | some v =>
        obtain ⟨later, read, epochs⟩ := life.validators _ v initial
        rw [beforeEq] at read
        obtain rfl := Option.some.inj (read.symm.trans sourceAt)
        simp only [Option.all_some, beq_iff_eq]
        by_contra assigned
        exact assigned ((epochs.exitEpoch assigned).symm.trans unset)
    refine ⟨fun c member => ?_, fun tag member fresh => ?_⟩
    · rw [List.map_append] at member
      rcases List.mem_append.mp member with old | added
      · exact held c old
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at added
        subst added
        exact Or.inr unsetX
    · rcases List.mem_append.mp member with old | added
      · exact absurd old fresh
      · rw [List.mem_singleton] at added
        subst added
        exact unsetX
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, pass, _⟩ := pending
    exact ⟨fun c member => held c ((pass.suffix_sublist.map _).subset member),
      fun _ member fresh => absurd (pass.suffix_sublist.subset member) fresh⟩

/-- The entry provenance of the queue after one tagged event. -/
private theorem TagEvent.queueProvenance {x : ForkedBeaconState preset}
    {e : BalanceEvent preset} {position : Nat} {before after consumed : List TaggedEntry}
    {payments : List (TaggedEntry × Payment preset)}
    {calls : List (IndexedDepartureCall preset config)}
    (one : TagEvent (config := config) e position before after consumed payments calls)
    (life : RegistryLifecycle x.state e.before.state)
    (held : ∀ c ∈ before.map (·.entry), c ∈ pendingQueue x ∨
          (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH)) :
    ∀ c ∈ after.map (·.entry), c ∈ pendingQueue x ∨
          (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH) :=
  (one.queueProvenance_appended life held).1

/-- The tags whose origin is known at `x`.

An initial tag carries an entry of the queue at `x`.

A fresh tag's source had no exit at `x`. -/
def TagsKnown (x : ForkedBeaconState preset) (queue : List TaggedEntry) : Prop :=
  ∀ tag ∈ queue, (∀ p, tag.tag = .initial p → tag.entry ∈ pendingQueue x) ∧
    ∀ n, tag.tag = .fresh n →
      (x.state.validators.data[tag.entry.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH)

/-- The payments a tagged event records are the payments of the actual event. -/
private theorem TagEvent.event_payments {e : BalanceEvent preset} {position : Nat}
    {before after consumed : List TaggedEntry} {payments : List (TaggedEntry × Payment preset)}
    {calls : List (IndexedDepartureCall preset config)}
    (one : TagEvent (config := config) e position before after consumed payments calls) :
    EventPayments e (payments.map Prod.snd) := by
  obtain ⟨erasedBefore, erasedAfter, rest⟩ := one
  unfold EventPayments
  rcases rest with ⟨other, _, _, rfl, _⟩ | requested | pending
  · simp [other]
  · obtain ⟨_, _, _, _, _, _, _, _, _, excess, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
      _⟩ := requested
    simp [excess]
  · obtain ⟨fork, s, t, u, electra, next, consolidations, beforeEq, afterEq, nextOk, processed,
      pass, validators, balances, _⟩ := pending
    simp only [consolidations, ↓reduceIte]
    obtain ⟨-, paying, split, -, -, -⟩ := pass.pass_shape
    have startQueue : before.map (·.entry) = (s.pendingConsolidations electra).data.toList := by
      unfold QueueErasure at erasedBefore
      rw [beforeEq] at erasedBefore
      simpa only [pendingQueue, electra, ↓reduceDIte] using erasedBefore
    have endQueue : after.map (·.entry) = (t.pendingConsolidations electra).data.toList := by
      unfold QueueErasure at erasedAfter
      rw [afterEq] at erasedAfter
      simpa only [pendingQueue, electra, ↓reduceDIte] using erasedAfter
    rw [startQueue] at paying
    refine ⟨fork, s, t, u, electra, next, consumed.length, beforeEq, afterEq, nextOk, processed,
      paying, validators, balances, ?_⟩
    rw [← endQueue, ← startQueue, ← split, List.map_append,
      List.drop_left' (List.length_map _)]

/-- One tagged event keeps tag origins known, and pays only from known tags of its input. -/
private theorem TagEvent.tags_known {x : ForkedBeaconState preset} {e : BalanceEvent preset}
    {position : Nat} {before after consumed : List TaggedEntry}
    {payments : List (TaggedEntry × Payment preset)}
    {calls : List (IndexedDepartureCall preset config)}
    (one : TagEvent (config := config) e position before after consumed payments calls)
    (life : RegistryLifecycle x.state e.before.state) (known : TagsKnown x before) :
    TagsKnown x after ∧ ∀ pair ∈ payments,
      TagsKnown x [pair.1] ∧ pair.2.source = pair.1.entry.sourceIndex.toNat := by
  have held : ∀ c ∈ before.map (·.entry), c ∈ pendingQueue x ∨
      (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH) := by
    intro c member
    obtain ⟨tag, inside, rfl⟩ := List.mem_map.mp member
    cases kind : tag.tag with
    | initial p => exact Or.inl ((known tag inside).1 p kind)
    | fresh n => exact Or.inr ((known tag inside).2 n kind)
  have appended := (one.queueProvenance_appended life held).2
  have shape := one.queue_shape
  have members : ∀ pair ∈ payments,
      pair.1 ∈ before ∧ pair.2.source = pair.1.entry.sourceIndex.toNat := by
    obtain ⟨_, _, rest⟩ := one
    rcases rest with ⟨_, _, _, rfl, _⟩ | requested | pending
    · simp
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
        _⟩ := requested
      simp
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, pass, _⟩ := pending
      exact fun pair member => ⟨(pass.pass_shape.2.2.2.2.1 pair member).1,
        (pass.pass_shape.2.2.2.2.1 pair member).2.1⟩
  refine ⟨fun tag member => ?_, fun pair member => ?_⟩
  · by_cases old : tag ∈ before
    · exact known tag old
    · have far := appended tag member old
      rcases shape with sub | ⟨added, grown, fresh⟩
      · exact absurd (sub.subset member) old
      · rw [grown] at member
        rcases List.mem_append.mp member with inside | single
        · exact absurd inside old
        · rw [List.mem_singleton] at single
          subst single
          refine ⟨fun p kind => ?_, fun _ _ => far⟩
          rw [fresh] at kind
          cases kind
  · obtain ⟨inside, source⟩ := members pair member
    refine ⟨fun tag single => ?_, source⟩
    rw [List.mem_singleton] at single
    subst single
    exact known _ inside

/-- One tagged event pays from its consumed tags, at their own sources and targets.

Its consumed tags and output queue are its input queue followed by its fresh tags.

It appends one fresh tag per call, at consecutive positions. -/
private theorem TagEvent.consumed_shape {e : BalanceEvent preset} {position : Nat}
    {before after consumed : List TaggedEntry} {payments : List (TaggedEntry × Payment preset)}
    {calls : List (IndexedDepartureCall preset config)}
    (one : TagEvent (config := config) e position before after consumed payments calls) :
    (payments.map Prod.fst).Sublist consumed ∧
    (∀ pair ∈ payments, pair.2.source = pair.1.entry.sourceIndex.toNat ∧
      pair.2.target = pair.1.entry.targetIndex.toNat) ∧ ∃ appended : List TaggedEntry,
      consumed ++ after = before ++ appended ∧ appended.length = calls.length ∧
      ∀ k (h : k < appended.length), (appended[k]).tag = .fresh (position + k) ∧
        ∃ called, calls[k]? = some called ∧
          called.index = some (appended[k]).entry.sourceIndex.toNat ∧
          called.call.amount.toNat = (appended[k]).amount ∧
          called.call.epoch.toNat = (appended[k]).epoch := by
  obtain ⟨_, _, rest⟩ := one
  rcases rest with ⟨_, rfl, rfl, rfl, rfl⟩ | requested | pending
  · exact ⟨.slnil, by simp, [], by simp, rfl, by simp⟩
  · obtain ⟨_, _, _, _, _, _, _, _, called, _, _, _, _, _, _, index, _, _, _, _, _, _, _, rfl,
      rfl, rfl, rfl⟩ := requested
    refine ⟨.slnil, by simp, [_], rfl, rfl, fun k inside => ?_⟩
    simp only [List.length_singleton, Nat.lt_one_iff] at inside
    subst inside
    exact ⟨by simp, called, rfl, index, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, pass, _, _, rfl⟩ := pending
    obtain ⟨-, -, split, paid, members, -⟩ := pass.pass_shape
    exact ⟨paid, fun pair member => ⟨(members pair member).2.1, (members pair member).2.2.2.1⟩, [],
      by simpa using split, rfl, by simp⟩

/-- An event keeps every initial tag of its output from its input.

Only a consolidation request appends a tag, and that tag is fresh. -/
private theorem TagEvent.initial_from {e : BalanceEvent preset}
    {before after consumed : List TaggedEntry} {payments : List (TaggedEntry × Payment preset)}
    {calls : List (IndexedDepartureCall preset config)}
    (tagged : TagEvent (config := config) e position before after consumed payments calls) :
    ∀ tag ∈ after, ∀ n, tag.tag = .initial n → tag ∈ before := by
  intro tag member n initial
  rcases tagged.2.2 with ⟨_, same, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, appended, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, pass, _, _, _⟩
  · exact same ▸ member
  · rw [appended] at member
    rcases List.mem_append.mp member with inside | fresh
    · exact inside
    · rw [List.mem_singleton.mp fresh] at initial
      cases initial
  · exact pass.suffix_sublist.subset member

/-- An owned event never raises an original.

A consolidation pays through transfers, a credit keeps the originals, and a frame lowers them. -/
theorem OwnedEvent.original_le {e : BalanceEvent preset}
    {tagged : List (TaggedEntry × Payment preset)}
    (event : OwnedEvent eventPosition paymentPosition e tagged allocations before after) :
    ∀ i, after.original i ≤ before.original i := by
  unfold OwnedEvent at event
  split at event
  · exact event.1.original_le
  · rcases event.2.2 with credit | frame
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, original⟩ := credit
      exact original
    · exact frame.2.2.2.2.2.2

/-- The counters of a replay, the queue provenance it keeps, and its nonincreasing originals.

Given the registry lifecycle from `x` to each event, every queued entry stays provenanced.

It was initially queued, or its source was unexited at `x`.

Originals never increase, and every initial tag of the output was in the input queue. -/
theorem ReservedReplay.counters_original
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final payments allocations calls before after) :
    (OwnershipBefore eventPosition paymentPosition before →
      OwnershipBefore (eventPosition + events.length) (paymentPosition + payments.length) after ∧
      after.issued.filter ((·.isInitial)) =
        before.issued.filter ((·.isInitial)) ∧
      (after.issued.filter ((·.isCredit))).card ≤
        (before.issued.filter ((·.isCredit))).card +
          (events.map ownedCreditBound).sum ∧
      (after.issued.filter ((·.isReleased))).card =
        (before.issued.filter ((·.isReleased))).card +
          (allocations.map (·.baseline)).sum) ∧
      ((∀ e ∈ events, RegistryLifecycle x.state e.before.state) →
        (∀ c ∈ queue.map (·.entry), c ∈ pendingQueue x ∨
          (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH)) →
        ∀ c ∈ final.map (·.entry), c ∈ pendingQueue x ∨
          (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH)) ∧
      (∀ i, after.original i ≤ before.original i) ∧
      (∀ tag ∈ final, ∀ n, tag.tag = .initial n → tag ∈ queue) ∧
      ReserveCut x high finish finishEpoch (final.map (·.entry)) after ∧
      (∃ per : List (List (TaggedEntry × Payment preset)),
        List.Forall₂ (fun e pairs => EventPayments e (pairs.map Prod.snd)) events per ∧
          payments = per.flatten) ∧
      ((∀ e ∈ events, RegistryLifecycle x.state e.before.state) → TagsKnown x queue →
        TagsKnown x final ∧ ∀ pair ∈ payments,
          TagsKnown x [pair.1] ∧ pair.2.source = pair.1.entry.sourceIndex.toNat) ∧
      ∃ consumed appended, TagReplay (config := config) callPosition events queue final consumed
        payments calls ∧ (payments.map Prod.fst).Sublist consumed ∧
        (∀ pair ∈ payments, pair.2.source = pair.1.entry.sourceIndex.toNat ∧
          pair.2.target = pair.1.entry.targetIndex.toNat) ∧
        (consumed ++ final).Perm (queue ++ appended) ∧ appended.length = calls.length ∧
        ∀ k (h : k < appended.length), (appended[k]).tag = .fresh (callPosition + k) ∧
          ∃ called, calls[k]? = some called ∧
            called.index = some (appended[k]).entry.sourceIndex.toNat ∧
            called.call.amount.toNat = (appended[k]).amount ∧
            called.call.epoch.toNat = (appended[k]).epoch := by
  induction history with
  | nil frame =>
    have same := frame.2.2.1.2.2.1
    exact ⟨fun prior => ⟨
        (by simpa only [List.length_nil, Nat.add_zero] using prior.frame frame.2.2.1),
        by rw [same], by simp [same], by simp [same]⟩,
      fun _ held => held, frame.2.2.1.2.2.2.2.2.2, fun _ member _ _ => member,
      frame.2.2.2.2.2.2.2.2, ⟨[], .nil, rfl⟩, fun _ known => ⟨known, by simp⟩, [], [], .nil,
      .slnil, by simp, by simp, rfl, by simp⟩
  | cons frame tagged event _ ih =>
    have same := frame.2.2.1.2.2.1
    obtain ⟨counted, carried, lowered, initialFrom, endpoint, ⟨per, related, flat⟩,
      tagKnown, consumed, appended, replay, paidSub, pairs, perm, sizes, facts⟩ := ih
    refine ⟨fun prior => ?_, fun lives held => ?_, fun i =>
        (lowered i).trans ((event.1.original_le i).trans (frame.2.2.1.2.2.2.2.2.2 i)),
      fun tag member n initial => tagged.initial_from tag (initialFrom tag member n initial) n
        initial, endpoint,
      ⟨_ :: per, .cons tagged.event_payments related, by rw [flat, List.flatten_cons]⟩,
      fun lives known => ?_, ?_⟩
    · obtain ⟨next, eventInitial, eventCredit, eventReleased⟩ :=
        event.1.counters_ledger (prior.frame frame.2.2.1)
      obtain ⟨rest, restInitial, restCredit, restReleased⟩ := counted next
      refine ⟨by simpa only [List.length_cons, List.length_append, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using rest, by rw [restInitial, eventInitial, same],
        ?_, ?_⟩
      · rw [← same, List.map_cons, List.sum_cons]
        omega
      · rw [← same, List.map_append, List.sum_append]
        omega
    · exact carried (fun e member => lives e (List.mem_cons_of_mem _ member))
        (tagged.queueProvenance (lives _ List.mem_cons_self) held)
    · obtain ⟨middle, members⟩ := tagged.tags_known (lives _ List.mem_cons_self) known
      obtain ⟨ending, rest⟩ :=
        tagKnown (fun e member => lives e (List.mem_cons_of_mem _ member)) middle
      exact ⟨ending, fun pair member =>
        (List.mem_append.mp member).elim (members pair) (rest pair)⟩
    · obtain ⟨eventPaid, eventPairs, eventAppended, split, eventSizes, eventFacts⟩ :=
        tagged.consumed_shape
      refine ⟨_, eventAppended ++ appended, .cons tagged replay, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.map_append]
        exact eventPaid.append paidSub
      · intro pair member
        rcases List.mem_append.mp member with head | later
        · exact eventPairs pair head
        · exact pairs pair later
      · calc _ = _ ++ (consumed ++ _) := List.append_assoc _ _ _
          List.Perm _ (_ ++ (_ ++ appended)) := perm.append_left _
          _ = (_ ++ _) ++ appended := (List.append_assoc _ _ _).symm
          _ = _ := by rw [split, List.append_assoc]
      · simp [eventSizes, sizes]
      · intro k inside
        rw [List.length_append] at inside
        by_cases first : k < eventAppended.length
        · obtain ⟨tagEq, called, found, rest⟩ := eventFacts k first
          refine ⟨by rw [List.getElem_append_left first]; exact tagEq, called, ?_, ?_⟩
          · rw [List.getElem?_append_left (by omega)]
            exact found
          · rw [List.getElem_append_left first]
            exact rest
        · have later : k - eventAppended.length < appended.length := by omega
          obtain ⟨tagEq, called, found, rest⟩ := facts _ later
          refine ⟨?_, called, ?_, ?_⟩
          · rw [List.getElem_append_right (by omega), tagEq]
            congr 1
            omega
          · rw [List.getElem?_append_right (by omega), ← eventSizes]
            exact found
          · rw [List.getElem_append_right (by omega)]
            exact rest

/-- The counters of a replay, and the queue provenance it keeps.

Let every queued entry be initially queued or have a source unexited at `x`.

Given the registry lifecycle from `x` to the event's state, each event keeps this. -/
theorem ReservedReplay.counters_provenance
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final payments allocations calls before after)
    (prior : OwnershipBefore eventPosition paymentPosition before) :
    OwnershipBefore (eventPosition + events.length) (paymentPosition + payments.length) after ∧
      ((∀ e ∈ events, RegistryLifecycle x.state e.before.state) →
        (∀ c ∈ queue.map (·.entry), c ∈ pendingQueue x ∨
          (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH)) →
        ∀ c ∈ final.map (·.entry), c ∈ pendingQueue x ∨
          (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH)) :=
  ⟨(history.counters_original.1 prior).1, history.counters_original.2.1⟩

theorem ReservedReplay.counters
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final payments allocations calls before after)
    (prior : OwnershipBefore eventPosition paymentPosition before) :
    OwnershipBefore (eventPosition + events.length) (paymentPosition + payments.length) after :=
  (history.counters_provenance prior).1

theorem ReservedReplay.append
    (first : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch middle middleEpoch eventPosition paymentPosition callPosition
      events queue intermediate payments allocations calls before owned)
    (suffix : ReservedReplay (config := config) (checks := checks) x high rounding
      middle middleEpoch finish finishEpoch (eventPosition + events.length)
      (paymentPosition + payments.length) (callPosition + calls.length)
      rest intermediate final restPayments restAllocations restCalls owned after) :
    ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      (events ++ rest) queue final (payments ++ restPayments)
      (allocations ++ restAllocations) (calls ++ restCalls) before after := by
  induction first with
  | nil frame =>
    simp only [List.length_nil, Nat.add_zero] at suffix
    cases suffix with
    | nil last => exact .nil (frame.trans last)
    | cons first tagged event tail =>
      simpa only [List.nil_append] using
        ReservedReplay.cons (frame.trans first) tagged event tail
  | cons frame tagged event tail ih =>
    have joined := ih (by
      simpa only [List.length_cons, List.length_append, Nat.add_assoc,
        Nat.add_right_comm _ 1] using suffix)
    simpa only [List.cons_append, List.append_assoc] using
      ReservedReplay.cons frame tagged event joined

theorem reservedFrame_refl
    (reserve : ReserveCut x high u epoch (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue u)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      u u epoch epoch queue owned owned :=
  ⟨.nil, UInt64.le_refl _,
    ⟨reserve.1, reserve.1, rfl, fun _ => Or.inl rfl, Finset.Subset.refl _, rfl,
      fun _ => Nat.le_refl _⟩,
    assignment, assignment, erasure, erasure, reserve, reserve⟩

theorem ReservedReplay.singleton_nonconsolidation {e : BalanceEvent preset}
    (notTransfer : e.source ≠ .consolidations)
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      start e.before startEpoch (getCurrentEpoch e.before.state) queue before eventOwned)
    (tagged : TagEvent (config := config) e callPosition queue queue [] [] [])
    (event : ReservedEvent x high eventPosition paymentPosition rounding e queue queue [] []
      eventOwned after) :
    ReservedReplay (config := config) (checks := checks) x high rounding start startEpoch
      e.after (getCurrentEpoch e.after.state) eventPosition paymentPosition callPosition
      [e] queue queue [] [] [] before after := by
  have reserve := event.2.2.2
  simp only [notTransfer, ↓reduceIte] at reserve
  have last := reservedFrame_refl (config := config) (checks := checks)
    reserve.2 event.2.2.1 tagged.2.1
  have same : eventDemandEpoch e = getCurrentEpoch e.after.state := by
    simp only [eventDemandEpoch, notTransfer, ↓reduceIte]
  have aligned : ReservedFrame (config := config) (checks := checks) x high rounding
      e.after e.after (eventDemandEpoch e) (getCurrentEpoch e.after.state) queue after after := by
    simpa only [same] using last
  exact ReservedReplay.cons frame tagged event (.nil aligned)

theorem reservedCredit_facts {e : BalanceEvent preset}
    (electra : .pectra ≤ e.before.fork)
    (notDeposit : e.source ≠ .deposits) (notTransfer : e.source ≠ .consolidations)
    (fork : e.after.fork = e.before.fork)
    (registry : e.after.state.validators.data = e.before.state.validators.data)
    (epoch : getCurrentEpoch e.after.state = getCurrentEpoch e.before.state)
    (matched : e.after.state.validators.data.size = e.after.state.balances.data.size)
    (queueSame : pendingQueue e.after = pendingQueue e.before)
    (bounded : e.credits ≤ e.creditLimit)
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      start e.before startEpoch (getCurrentEpoch e.before.state) queue before eventOwned)
    (prior : OwnershipBefore eventPosition paymentPosition before) :
    TagEvent (config := config) e callPosition queue queue [] [] [] ∧
      ReservedEvent x high eventPosition paymentPosition rounding e queue queue [] [] eventOwned
        (creditOwnership eventPosition e eventOwned) := by
  have fresh := (prior.frame frame.2.2.1).credit_fresh (Nat.le_refl eventPosition)
  obtain ⟨_, _, _, _, assignment, _, erasure, _, reserve⟩ := id frame
  have tagged : TagEvent (config := config) e callPosition queue queue [] [] [] :=
    ⟨erasure, queueSame ▸ erasure, Or.inl ⟨notTransfer, rfl, rfl, rfl, rfl⟩⟩
  have owned := reservedEvent_bounded_non_deposit (paymentPosition := paymentPosition)
    electra notDeposit notTransfer fork registry epoch matched fresh bounded reserve assignment
  exact ⟨tagged, owned⟩

theorem reservedReplay_processPendingDeposits_frame {fork : Fork}
    {s t : BeaconState preset fork} {x start : ForkedBeaconState preset}
    {high eventPosition paymentPosition callPosition : Nat} {startEpoch : Epoch}
    {rounding : Nat → Nat} {queue : List TaggedEntry} {before eventOwned : Ownership}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    (ordered : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (exits : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (delay : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (referenceSize : x.state.validators.data.size ≤ s.validators.data.size)
    (ok : processPendingDeposits config checks s electra = .ok t)
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      start ⟨fork, s⟩ startEpoch (getCurrentEpoch s) queue before eventOwned)
    (prior : OwnershipBefore eventPosition paymentPosition before) :
    ReservedReplay (config := config) (checks := checks) x high rounding start startEpoch
      ⟨fork, t⟩ (getCurrentEpoch t) eventPosition paymentPosition callPosition
      [⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩]
      queue queue [] [] [] before (creditOwnership eventPosition
        ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩ eventOwned) ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, t⟩ ⟨fork, t⟩ (getCurrentEpoch t) (getCurrentEpoch t) queue
        (creditOwnership eventPosition
          ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩ eventOwned)
        (creditOwnership eventPosition
          ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩ eventOwned) ∧
      (EndpointCoverAll x ⟨fork, s⟩ eventOwned →
        EndpointCoverAll x ⟨fork, t⟩ (creditOwnership eventPosition
          ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩ eventOwned)) ∧
      (FutureEffectiveCover x ⟨fork, s⟩ eventOwned →
        FutureEffectiveCover x ⟨fork, t⟩ (creditOwnership eventPosition
          ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, consumedDeposits s t electra, 0⟩ eventOwned)) := by
  have fresh := (prior.frame frame.2.2.1).credit_fresh (Nat.le_refl eventPosition)
  obtain ⟨_, _, _, _, assignment, _, erasure, _, reserve⟩ := id frame
  have queueIn : ∀ c ∈ queue.map (·.entry),
      c ∈ (s.pendingConsolidations electra).data.toList := by
    intro c member
    have same : queue.map (·.entry) = (s.pendingConsolidations electra).data.toList := by
      simpa only [QueueErasure, pendingQueue, electra, ↓reduceDIte] using erasure
    exact same ▸ member
  have tagged := tagEvent_processPendingDeposits (position := callPosition) electra ok erasure
  obtain ⟨owned, cover, future⟩ := reservedEvent_processPendingDeposits_cover
    (paymentPosition := paymentPosition)
    electra matched ordered exits finite delay queueIn referenceSize ok fresh reserve assignment
  have notTransfer : BalanceSource.deposits ≠ .consolidations := by decide
  -- The event's own reserve, assignment and outgoing erasure form the frame at its output.
  have reserveT := owned.2.2.2
  simp only [notTransfer, ↓reduceIte] at reserveT
  exact ⟨ReservedReplay.singleton_nonconsolidation notTransfer frame tagged owned,
    reservedFrame_refl reserveT.2 owned.2.2.1 tagged.2.1, cover, future⟩

private theorem reservedReplay_rewards_owned {fork : Fork} {s t : BeaconState preset fork}
    {recorded : List (BalanceEvent preset)}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    (initial : ReservedFrame (config := config) (checks := checks) x high rounding
      start ⟨fork, s⟩ startEpoch (getCurrentEpoch s) queue before owned)
    (prior : OwnershipBefore eventPosition paymentPosition before)
    (ok : replayRewards (config := config) (s, []) = .ok (t, recorded)) :
    ∃ after, ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch ⟨fork, t⟩ (getCurrentEpoch t)
      eventPosition paymentPosition callPosition recorded queue queue [] [] [] before after ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, t⟩ ⟨fork, t⟩ (getCurrentEpoch t) (getCurrentEpoch t) queue after after ∧
      OwnershipBefore (eventPosition + recorded.length) paymentPosition after ∧ BalancesMatch t ∧
      (EndpointCoverAll x ⟨fork, s⟩ owned → EndpointCoverAll x ⟨fork, t⟩ after) ∧
      (FutureEffectiveCover x ⟨fork, s⟩ owned → FutureEffectiveCover x ⟨fork, t⟩ after) ∧
      after.retired = owned.retired ∧ t.validators.data = s.validators.data ∧
      after.original = owned.original := by
  let P : BalanceReplay preset fork → Prop := fun pre => ∃ after,
    ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch ⟨fork, pre.1⟩ (getCurrentEpoch pre.1)
      eventPosition paymentPosition callPosition pre.2 queue queue [] [] [] before after ∧
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, pre.1⟩ ⟨fork, pre.1⟩ (getCurrentEpoch pre.1) (getCurrentEpoch pre.1) queue after after
          ∧
    OwnershipBefore (eventPosition + pre.2.length) paymentPosition after ∧ BalancesMatch pre.1 ∧
    (EndpointCoverAll x ⟨fork, s⟩ owned → EndpointCoverAll x ⟨fork, pre.1⟩ after) ∧
    (FutureEffectiveCover x ⟨fork, s⟩ owned → FutureEffectiveCover x ⟨fork, pre.1⟩ after) ∧
    after.retired = owned.retired ∧ pre.1.validators.data = s.validators.data ∧
    after.original = owned.original
  have extend {pre : BalanceReplay preset fork} {post : BeaconState preset fork}
      {source : BalanceSource} {credit debit : Nat}
      (held : P pre) (notDeposit : source ≠ .deposits)
      (notTransfer : source ≠ .consolidations)
      (registry : post.validators.data = pre.1.validators.data)
      (epoch : getCurrentEpoch post = getCurrentEpoch pre.1)
      (sizes : BalancesMatch post)
      (queueSame : pendingQueue (⟨fork, post⟩ : ForkedBeaconState preset) =
            pendingQueue ⟨fork, pre.1⟩)
      (bounded : (BalanceEvent.mk source ⟨fork, pre.1⟩ ⟨fork, post⟩ credit debit).credits ≤ credit)
          :
      P (post, pre.2 ++ [⟨source, ⟨fork, pre.1⟩, ⟨fork, post⟩, credit, debit⟩]) := by
    obtain ⟨current, history, frame, counters, matchedPre, covered, futureCovered, retiredSame,
      registrySame, originalSame⟩ := held
    let e : BalanceEvent preset := ⟨source, ⟨fork, pre.1⟩, ⟨fork, post⟩, credit, debit⟩
    obtain ⟨tagged, event⟩ := reservedCredit_facts
      (e := e) (callPosition := callPosition) electra notDeposit notTransfer rfl registry
      epoch sizes.symm queueSame bounded frame counters
    have single := ReservedReplay.singleton_nonconsolidation notTransfer frame tagged event
    have joined := history.append (by simpa only [List.length_nil, Nat.add_zero] using single)
    have reserve := event.2.2.2
    simp only [e, notTransfer, ↓reduceIte] at reserve
    -- The event mints its growth at the endpoint, so it keeps the cover.
    have fresh := counters.credit_fresh (Nat.le_refl _)
    have credit := ownedCredit_of_bounded reserve.1.1 fresh electra notTransfer sizes.symm bounded
    refine ⟨_, joined, reservedFrame_refl reserve.2 event.2.2.1 tagged.2.1, ?_, sizes,
      fun start => endpointCover_nonDeposit (e := e) notDeposit rfl registry epoch matchedPre fresh
        credit (covered start),
      fun start => futureCover_credit (e := e) ⟨#[], by rw [registry, Array.append_empty]⟩ epoch
        matchedPre (fun j w outside found => by
          change post.validators.data[j]? = some w at found
          rw [registry, Array.getElem?_eq_none outside] at found
          cases found) fresh credit (futureCovered start),
      -- A credit keeps the retired set, and the event keeps the registry.
      retiredSame, registry.trans registrySame, originalSame⟩
    have next := single.counters counters
    simpa only [List.length_append, List.length_singleton, List.length_nil, Nat.add_zero,
      Nat.add_assoc] using next
  apply replayRewards_induction P _ _ _ ok
  · intro pre post index reward held step
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
      exists_eq_left', liftAccessor_ok] at step
    obtain ⟨after, action, rfl⟩ := step
    have queueSame : pendingQueue (⟨fork, after⟩ : ForkedBeaconState preset) =
        pendingQueue ⟨fork, pre.1⟩ := by
      obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp action
      rfl
    exact extend held (by decide) (by decide)
      (congrArg (·.data) (increaseBalance_validators action))
      (by simp only [getCurrentEpoch, (frame_increaseBalance action).slot])
      (balancesMatch_of_sameSizes (sameSizes_increaseBalance action) held.choose_spec.2.2.2.1)
      queueSame (credits_increase action).1.le
  · intro source pre post index penalty sourceOk held step
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
      exists_eq_left', liftAccessor_ok] at step
    obtain ⟨after, action, rfl⟩ := step
    have queueSame : pendingQueue (⟨fork, after⟩ : ForkedBeaconState preset) =
        pendingQueue ⟨fork, pre.1⟩ := by
      obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp action
      rfl
    exact extend held (by rcases sourceOk with rfl | rfl <;> decide)
      (by rcases sourceOk with rfl | rfl <;> decide)
      (congrArg (·.data) (decreaseBalance_validators action))
      (by simp only [getCurrentEpoch, (frame_decreaseBalance action).slot])
      (balancesMatch_of_sameSizes (sameSizes_decreaseBalance action) held.choose_spec.2.2.2.1)
      queueSame (debits_decrease action).1.le
  · exact ⟨owned, .nil initial,
      reservedFrame_refl initial.2.2.2.2.2.2.2.2 initial.2.2.2.2.1 initial.2.2.2.2.2.2.1,
      by simpa only [List.length_nil, Nat.add_zero] using prior.frame initial.2.2.1, matched,
      id, id, rfl, rfl, rfl⟩

/-- Each validator after a switch to compounding credentials is the one before at its index.

Its credentials may be new.

Its effective balance and current epoch are unchanged, and its balance does not rise.

Its balance up to its cap does not rise either.

The switch may raise the cap.

But in the same step, its balance above the activation balance leaves for the pending deposits.

The cap before is at least the activation balance. -/
theorem switchToCompoundingValidator_lookup {fork : Fork}
    {u v : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : switchToCompoundingValidator u electra index = .ok v) :
    getCurrentEpoch v = getCurrentEpoch u ∧
      (∀ i, effectiveAt (⟨fork, v⟩ : ForkedBeaconState preset) i = effectiveAt ⟨fork, u⟩ i) ∧
      ∀ i w, v.validators.data[i]? = some w → ∃ w₀ credentials,
        u.validators.data[i]? = some w₀ ∧ w = { w₀ with withdrawalCredentials := credentials } ∧
        actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) i ≤ actualBalanceAt ⟨fork, u⟩ i ∧
        min (actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) i)
            (withdrawalMaxEffectiveBalance preset fork w).toNat ≤
          min (actualBalanceAt ⟨fork, u⟩ i)
            (withdrawalMaxEffectiveBalance preset fork w₀).toNat := by
  have slot := (frame_switchToCompoundingValidator ok).slot
  have epoch : getCurrentEpoch v = getCurrentEpoch u := by simp only [getCurrentEpoch, slot]
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨validator, found, mid, set, queued⟩ := ok
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have foundU := getValidator_eq_ok_iff.mp found
  have validators := queueExcessActiveBalance_validators queued
  -- The queued step reads the balance, then keeps it or lowers it to the activation balance.
  have read := queued
  simp only [queueExcessActiveBalance, bind_ok_iff] at read
  obtain ⟨balance, foundBalance, _⟩ := read
  have balanceU : u.balances.data[index.toNat]? = some balance :=
    getBalance_eq_ok_iff.mp foundBalance
  have lowered := getBalance_eq_ok_iff.mp (queueExcessActiveBalance_balance foundBalance queued).1
  have others : ∀ i, i ≠ index.toNat → v.balances.data[i]? = u.balances.data[i]? := by
    intro i apart
    have step := queued
    simp only [queueExcessActiveBalance, bind_ok_iff] at step
    obtain ⟨_, _, step⟩ := step
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨_, _, _, _, _, setOk, rfl⟩ := step
      obtain ⟨_, rfl⟩ := setBalance_ok setOk
      simp [BeaconState.putBalance, BeaconState.putValidator, Ne.symm apart]
    · simp only [pure, Except.pure, Except.ok.injEq] at step
      subst step
      rfl
  -- The cap before is at least the activation balance.
  have floor : preset.MIN_ACTIVATION_BALANCE.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork validator).toNat := by
    simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte, getMaxEffectiveBalance]
    split
    · exact UInt64.le_iff_toNat_le.mp compounding
    · exact Nat.le_refl _
  refine ⟨epoch, fun i => ?_, fun i w foundV => ?_⟩
  · simp only [effectiveAt, validators, BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set]
    by_cases same : index.toNat = i
    · subst same
      rw [Array.getElem?_set_self, foundU]
      rfl
    · rw [Array.getElem?_set_ne _ same]
  rw [validators] at foundV
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at foundV
  by_cases same : index.toNat = i
  · subst same
    rw [Array.getElem?_set_self] at foundV
    cases foundV
    have below : actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) index.toNat =
        (min balance preset.MIN_ACTIVATION_BALANCE).toNat := by
      simp [actualBalanceAt, lowered]
    have was : actualBalanceAt (⟨fork, u⟩ : ForkedBeaconState preset) index.toNat =
        balance.toNat := by
      simp [actualBalanceAt, balanceU]
    have minimum := Uint64.toNat_min balance preset.MIN_ACTIVATION_BALANCE
    refine ⟨validator, _, foundU, rfl, ?_, ?_⟩
    · rw [below, was]
      omega
    · show min _ _ ≤ min _ (withdrawalMaxEffectiveBalance preset fork validator).toNat
      rw [below, was]
      omega
  · rw [Array.getElem?_set_ne _ same] at foundV
    have balanceEq : actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) i =
        actualBalanceAt ⟨fork, u⟩ i := by
      simp [actualBalanceAt, others i (Ne.symm same)]
    refine ⟨w, w.withdrawalCredentials, foundV, rfl, ?_, ?_⟩
    · rw [balanceEq]
    · rw [balanceEq]

/-- A switch to compounding credentials keeps the endpoint cover.

The switch may raise the validator's cap.

But in the same step, its balance above the activation balance leaves for the pending deposits.

So its capped balance after is at most the activation balance, which is at most its cap before.

No other validator and no other balance changes. -/
theorem endpointCover_switch {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {o : Ownership}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : switchToCompoundingValidator u electra index = .ok v)
    (cover : EndpointCoverAll x ⟨fork, u⟩ o) :
    EndpointCoverAll x ⟨fork, v⟩ o := by
  obtain ⟨epoch, _, lookup⟩ := switchToCompoundingValidator_lookup compounding ok
  apply endpointCover_mono (u := ⟨fork, u⟩) ?_ (fun _ => Nat.le_refl _) cover
  intro i w foundV clean notExited current
  obtain ⟨w₀, _, foundU, rfl, _, capped⟩ := lookup i w foundV
  refine ⟨w₀, foundU, clean, notExited, ?_, rfl, capped⟩
  rw [← epoch]
  exact current

/-- After the registry updates, each validator is the one before at its index.

It has the same key, effective balance, credentials and slashed flag.

Any assigned epoch is unchanged. -/
private theorem processRegistryUpdates_lookup {fork : Fork} {u v : BeaconState preset fork}
    (ok : processRegistryUpdates config u = .ok v) :
    ∀ (i : Nat) (w : Validator), v.validators.data[i]? = some w → ∃ w₀,
      u.validators.data[i]? = some w₀ ∧ ValidatorSame w₀ w ∧ ValidatorLifecycle w₀ w := by
  have sizes := (sameSizes_processRegistryUpdates ok).1
  have lifecycle := registryLifecycle_processRegistryUpdates ok
  have kept := (processRegistryUpdates_kept ok).1
  intro i w found
  have insideV := (Array.getElem?_eq_some_iff.mp found).1
  have inside : i < u.validators.data.size := by omega
  have foundU := Array.getElem?_eq_getElem inside
  obtain ⟨w', found', same⟩ := kept i _ foundU
  obtain ⟨w'', found'', life⟩ := lifecycle.validators i _ foundU
  rw [found] at found' found''
  cases found'
  cases found''
  exact ⟨_, foundU, same, life⟩

/-- Every epoch is at most the far future. -/
theorem le_far (e : Epoch) : e ≤ FAR_FUTURE_EPOCH := by
  rw [UInt64.le_iff_toNat_le]
  have := e.toNat_lt
  have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  omega

/-- Let a step keep every validator's key, effective balance, credentials and slashed flag.

Then it keeps each entry of the registry. -/
private theorem registryKept_of_lookup {fork : Fork} {u v : BeaconState preset fork}
    (lookup : ∀ (i : Nat) (w : Validator), v.validators.data[i]? = some w → ∃ w₀,
      u.validators.data[i]? = some w₀ ∧ ValidatorSame w₀ w ∧ ValidatorLifecycle w₀ w) :
    RegistryEntriesKept u v := by
  intro i w found
  obtain ⟨w₀, foundU, ⟨key, effective, credentials, slashed⟩, life⟩ := lookup i w found
  refine ⟨w₀, foundU, key, effective, ?_, fun clean => slashed.symm.trans clean, life⟩
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance hasCompoundingWithdrawalCredential
  rw [credentials]

/-- A step that keeps the registry, the balances and the current epoch keeps the endpoint cover.

It only assigns an exit that was at the far future.

So a validator covered after it was covered before it. -/
theorem endpointCover_of_kept {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {o : Ownership}
    (kept : RegistryEntriesKept u v) (balances : v.balances = u.balances)
    (epoch : getCurrentEpoch v = getCurrentEpoch u)
    (cover : EndpointCoverAll x ⟨fork, u⟩ o) :
    EndpointCoverAll x ⟨fork, v⟩ o := by
  apply endpointCover_mono (u := ⟨fork, u⟩) ?_ (fun _ => Nat.le_refl _) cover
  intro i w found clean notExited current
  obtain ⟨w₀, foundU, key, _, credentials, slashed, life⟩ := kept i w found
  -- The exit before is the same one, or the far future, which bounds every epoch.
  have exits : getCurrentEpoch x.state < w₀.exitEpoch ∧ getCurrentEpoch u ≤ w₀.exitEpoch := by
    by_cases unset : w₀.exitEpoch = FAR_FUTURE_EPOCH
    · rw [unset]
      exact ⟨UInt64.lt_of_lt_of_le notExited (le_far _), le_far _⟩
    · rw [← life.exitEpoch unset]
      exact ⟨notExited, epoch ▸ current⟩
  refine ⟨w₀, foundU, slashed clean, exits.1, exits.2, key.symm, ?_⟩
  have balanceEq : actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) i =
      actualBalanceAt ⟨fork, u⟩ i := by
    simp only [actualBalanceAt, balances]
  exact le_of_eq (by rw [balanceEq]; exact congrArg (fun c => min _ (UInt64.toNat c)) credentials)

/-- A step that keeps the registry and the current epoch keeps the future cover.

It only assigns an activation or an exit that was at the far future.

So a guarded validator after it was guarded before it. -/
theorem futureCover_of_kept {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {o : Ownership}
    (kept : RegistryEntriesKept u v) (epoch : getCurrentEpoch v = getCurrentEpoch u)
    (cover : FutureEffectiveCover x ⟨fork, u⟩ o) :
    FutureEffectiveCover x ⟨fork, v⟩ o := by
  apply futureCover_mono (u := ⟨fork, u⟩) ?_ (fun _ => Nat.le_refl _) cover
  intro i w found later clean notExited
  obtain ⟨w₀, foundU, key, effective, _, slashed, life⟩ := kept i w found
  have laterU : getCurrentEpoch u < w.activationEpoch := epoch ▸ later
  refine ⟨w₀, foundU, ?_, slashed clean, ?_, key.symm, ?_⟩
  · by_cases unset : w₀.activationEpoch = FAR_FUTURE_EPOCH
    · rw [unset]
      exact UInt64.lt_of_lt_of_le laterU (le_far _)
    · rw [← life.activationEpoch unset]
      exact laterU
  · by_cases unset : w₀.exitEpoch = FAR_FUTURE_EPOCH
    · rw [unset]
      exact UInt64.lt_of_lt_of_le notExited (le_far _)
    · rw [← life.exitEpoch unset]
      exact notExited
  · simp only [effectiveAt, found, foundU, effective, Option.map_some, Option.getD_some, le_refl]

/-- The registry updates keep the endpoint cover.

They keep the balances, the slot, and each validator's key, credentials and slashed flag.

They only assign an exit that was at the far future.

So a validator covered after them was covered before them. -/
private theorem endpointCover_registry {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {o : Ownership}
    (ok : processRegistryUpdates config u = .ok v)
    (cover : EndpointCoverAll x ⟨fork, u⟩ o) :
    EndpointCoverAll x ⟨fork, v⟩ o := by
  have epoch : getCurrentEpoch v = getCurrentEpoch u := by
    simp only [getCurrentEpoch, (frame_processRegistryUpdates ok).slot]
  exact endpointCover_of_kept (registryKept_of_lookup (processRegistryUpdates_lookup ok))
    (processRegistryUpdates_balances ok) epoch cover

/-- The registry updates keep the future cover.

They keep each validator's key, effective balance and slashed flag.

They only assign an activation or an exit that was at the far future.

So a guarded validator after them was guarded before them. -/
private theorem futureCover_registry {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {o : Ownership}
    (ok : processRegistryUpdates config u = .ok v)
    (cover : FutureEffectiveCover x ⟨fork, u⟩ o) :
    FutureEffectiveCover x ⟨fork, v⟩ o := by
  have epoch : getCurrentEpoch v = getCurrentEpoch u := by
    simp only [getCurrentEpoch, (frame_processRegistryUpdates ok).slot]
  exact futureCover_of_kept (registryKept_of_lookup (processRegistryUpdates_lookup ok)) epoch
    cover

/-- Let a step keep the balances and each validator's key, effective balance and credentials.

Let it also unslash nobody.

Then it keeps the reserve cut at the current epoch.

It may assign an activation, an exit and a withdrawable epoch, or set a slashed flag.

Besides `kept`, it reads the facts that the registry updates need to keep the reserve cut.

Retired and initially active keys were already activated.

Activity up to the current epoch is unchanged.

A withdrawable epoch is unchanged, or after the current epoch both before and after the step. -/
theorem reserveCut_of_kept {x : ForkedBeaconState preset} {high : Nat} {fork : Fork}
    {u v : BeaconState preset fork} {suffix : List PendingConsolidation} {o : Ownership}
    (retiredActivated : ∀ i ∈ o.retired, ∀ w₀ : Validator, u.validators.data[i]? = some w₀ →
      w₀.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (startActivated : ∀ (i : Nat) (initial w₀ : Validator),
      x.state.validators.data[i]? = some initial →
      isActiveValidator initial (getCurrentEpoch x.state) = true →
      u.validators.data[i]? = some w₀ → w₀.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (activity : ∀ (i : Nat) (w₀ w : Validator), u.validators.data[i]? = some w₀ →
      v.validators.data[i]? = some w → ∀ e ≤ getCurrentEpoch u,
        isActiveValidator w e = isActiveValidator w₀ e)
    (kept : RegistryEntriesKept u v)
    (withdrawable : ∀ (i : Nat) (w₀ w : Validator), u.validators.data[i]? = some w₀ →
      v.validators.data[i]? = some w →
      w.withdrawableEpoch = w₀.withdrawableEpoch ∨
        (getCurrentEpoch u < w₀.withdrawableEpoch ∧ getCurrentEpoch u < w.withdrawableEpoch))
    (balances : v.balances = u.balances)
    (reserve : ReserveCut x high ⟨fork, u⟩ (getCurrentEpoch u) suffix o) :
    ReserveCut x high ⟨fork, v⟩ (getCurrentEpoch u) suffix o := by
  have far : ∀ e : Epoch, e ≤ FAR_FUTURE_EPOCH := fun e => by
    rw [UInt64.le_iff_toNat_le]
    have := e.toNat_lt
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  -- Each validator after the step is one before it, with the same fields that matter.
  have lookup : ∀ (i : Nat) (w : Validator), v.validators.data[i]? = some w →
      ∃ w₀, u.validators.data[i]? = some w₀ ∧ w.pubkey = w₀.pubkey ∧
        w.effectiveBalance = w₀.effectiveBalance ∧
        withdrawalMaxEffectiveBalance preset fork w =
          withdrawalMaxEffectiveBalance preset fork w₀ ∧
        (w.slashed = false → w₀.slashed = false) ∧ ValidatorLifecycle w₀ w ∧
        (w.withdrawableEpoch = w₀.withdrawableEpoch ∨
          (getCurrentEpoch u < w₀.withdrawableEpoch ∧
            getCurrentEpoch u < w.withdrawableEpoch)) := by
    intro i w found
    obtain ⟨w₀, foundU, key, effective, credentials, slashed, life⟩ := kept i w found
    exact ⟨w₀, foundU, key, effective, credentials, slashed, life,
      withdrawable i w₀ w foundU found⟩
  have effectiveEq : ∀ (i : Nat) (w w₀ : Validator), v.validators.data[i]? = some w →
      u.validators.data[i]? = some w₀ → w.effectiveBalance = w₀.effectiveBalance →
      effectiveAt (⟨fork, v⟩ : ForkedBeaconState preset) i = effectiveAt ⟨fork, u⟩ i := by
    intro i w w₀ found foundU same
    simp [effectiveAt, found, foundU, same]
  have balanceEq : ∀ i, actualBalanceAt (⟨fork, v⟩ : ForkedBeaconState preset) i =
      actualBalanceAt ⟨fork, u⟩ i := fun i => by simp only [actualBalanceAt, balances]
  -- Support at the demand epoch and the one before is unchanged.
  have supportNow : ∀ (i : Nat) (w₀ w : Validator), u.validators.data[i]? = some w₀ →
      v.validators.data[i]? = some w → (w.slashed = false → w₀.slashed = false) →
      SupportedAt (getCurrentEpoch u) w → SupportedAt (getCurrentEpoch u) w₀ := by
    intro i w₀ w foundU found slashed ⟨clean, active⟩
    refine ⟨slashed clean, ?_⟩
    rcases active with now | before
    · exact .inl ((activity i w₀ w foundU found _ (UInt64.le_refl _)) ▸ now)
    · by_cases zero : (getCurrentEpoch u).toNat = 0
      · -- The epoch before epoch zero wraps to the largest epoch, where no key is active.
        exfalso
        have equal : getCurrentEpoch u = 0 := UInt64.toNat_inj.mp zero
        have wrapped : ((0 : UInt64) - 1).toNat = 2 ^ 64 - 1 := by decide
        have bound := w.exitEpoch.toNat_lt
        simp only [isActiveValidator, equal, Bool.and_eq_true, decide_eq_true_eq,
          UInt64.lt_iff_toNat_lt, wrapped] at before
        omega
      · have earlier : getCurrentEpoch u - 1 ≤ getCurrentEpoch u := by
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _
            (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
          simp
        exact .inr ((activity i w₀ w foundU found _ earlier) ▸ before)
  -- An already activated key is supported later only if it was before the updates.
  have supportLater : ∀ (w₀ w : Validator), w₀.activationEpoch ≠ FAR_FUTURE_EPOCH →
      ValidatorLifecycle w₀ w → (w.slashed = false → w₀.slashed = false) → ∀ e,
        SupportedAt e w → SupportedAt e w₀ := by
    intro w₀ w activated life slashed e ⟨clean, active⟩
    have activation := life.activationEpoch activated
    have exitLe : w.exitEpoch ≤ w₀.exitEpoch := by
      by_cases unset : w₀.exitEpoch = FAR_FUTURE_EPOCH
      · rw [unset]
        exact far _
      · rw [life.exitEpoch unset]
        exact UInt64.le_refl _
    have keep : ∀ e', isActiveValidator w e' = true → isActiveValidator w₀ e' = true := by
      intro e' now
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at now ⊢
      rw [activation] at now
      exact ⟨now.1, UInt64.lt_of_lt_of_le now.2 exitLe⟩
    exact ⟨slashed clean, active.imp (keep _) (keep _)⟩
  have relevant : ∀ i, FundingRelevant ⟨fork, v⟩ (getCurrentEpoch u) suffix i →
      FundingRelevant ⟨fork, u⟩ (getCurrentEpoch u) suffix i := by
    rintro i ⟨w, found, rest⟩
    obtain ⟨w₀, foundU, _, _, _, slashed, _, withdrawable⟩ := lookup i w found
    refine ⟨w₀, foundU, ?_⟩
    rcases rest with supported | later | queued
    · exact .inl (supportNow i w₀ w foundU found slashed supported)
    · rcases withdrawable with same | ⟨old, _⟩
      · exact .inr (.inl (same ▸ later))
      · exact .inr (.inl old)
    · exact .inr (.inr queued)
  obtain ⟨valid, wasRetired, wasOriginal, reference, scheduled, pending, due, idle,
    activePending, endpoint⟩ := reserve
  refine ⟨valid, ?_, wasOriginal, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i member w found
    obtain ⟨w₀, foundU, _, _, _, slashed, life, _⟩ := lookup i w found
    obtain ⟨never, unqueued⟩ := wasRetired i member w₀ foundU
    exact ⟨fun e later supported => never e later (supportLater w₀ w
      (retiredActivated i member w₀ foundU) life slashed e supported), unqueued⟩
  · intro i ref notRetired support
    have old := reference i ref notRetired (relevant i support)
    obtain ⟨w, found, _⟩ := support
    obtain ⟨w₀, foundU, _, effective, cap, _, _, _⟩ := lookup i w found
    simp only [potential, found, foundU, Option.map_some, Option.getD_some] at old ⊢
    rw [effective, cap, balanceEq]
    exact old
  · intro i initial w found active clean finite located support
    obtain ⟨w₀, foundU, _, effective, credentials, slashed, life, _⟩ := lookup i w located
    have activated := startActivated i initial w₀ found active foundU
    obtain ⟨e, later, supported⟩ := support
    have old := scheduled i initial w₀ found active clean finite foundU
      ⟨e, later, supportLater w₀ w activated life slashed e supported⟩
    rw [effectiveEq i w w₀ located foundU effective, balanceEq]
    show max _ (min _ (withdrawalMaxEffectiveBalance preset fork w).toNat) ≤ _
    rw [credentials]
    exact old
  · intro i initial notRetired support w found
    obtain ⟨w₀, foundU, _, _, credentials, _, _, _⟩ := lookup i w found
    have old := pending i initial notRetired (relevant i support) w₀ foundU
    rw [balanceEq]
    show min _ (withdrawalMaxEffectiveBalance preset fork w).toNat ≤ _
    rw [credentials]
    exact old
  · intro entry member w found ready notRef
    obtain ⟨w₀, foundU, _, _, credentials, _, _, withdrawable⟩ := lookup _ w found
    have ready₀ : w₀.withdrawableEpoch ≤ getCurrentEpoch u := by
      rcases withdrawable with same | ⟨_, late⟩
      · exact same ▸ ready
      · exact absurd ready (UInt64.not_le.mpr late)
    have old := due entry member w₀ foundU ready₀ notRef
    rw [balanceEq]
    show min _ (withdrawalMaxEffectiveBalance preset fork w).toNat ≤ _
    rw [credentials]
    exact old
  · intro i w found notRef notPending quiet support
    obtain ⟨w₀, foundU, _, effective, credentials, slashed, life, _⟩ := lookup i w found
    -- An assigned activation or exit was at the far future, after every epoch before it.
    have before : ∀ (a b : Epoch), (b ≠ FAR_FUTURE_EPOCH → a = b) →
        getCurrentEpoch u < a → getCurrentEpoch u < b := by
      intro a b same late
      by_cases unset : b = FAR_FUTURE_EPOCH
      · rw [unset]
        exact UInt64.lt_of_lt_of_le late (far _)
      · rw [← same unset]
        exact late
    have support₀ : SupportedAt (getCurrentEpoch u) w₀ ∨
        getCurrentEpoch u < w₀.activationEpoch ∧ getCurrentEpoch u < w₀.exitEpoch ∨
        (∃ c ∈ suffix, c.sourceIndex.toNat = i) ∧
          (¬ ∃ c ∈ pendingQueue x, c.sourceIndex.toNat = i) := by
      rcases support with supported | ⟨early, open'⟩ | queued
      · exact .inl (supportNow i w₀ w foundU found slashed supported)
      · exact .inr (.inl ⟨before _ _ life.activationEpoch early, before _ _ life.exitEpoch open'⟩)
      · exact .inr (.inr queued)
    have old := idle i w₀ foundU notRef notPending quiet support₀
    rw [effectiveEq i w w₀ found foundU effective, balanceEq]
    show max _ (min _ (withdrawalMaxEffectiveBalance preset fork w).toNat) ≤ _
    rw [credentials]
    exact old
  · intro i initial w old located found active notRetired support
    obtain ⟨w₀, foundU, _, effective, credentials, _, _, _⟩ := lookup i w located
    obtain ⟨capped, bounded⟩ := activePending i initial w₀ old foundU found active notRetired
      (relevant i support)
    rw [effectiveEq i w w₀ located foundU effective, balanceEq]
    show min _ (withdrawalMaxEffectiveBalance preset fork w).toNat ≤ _ ∧ _
    rw [credentials]
    exact ⟨capped, bounded⟩
  · intro i w found support notPrevious
    obtain ⟨w₀, foundU, key, effective, _, slashed, _, _⟩ := lookup i w found
    have old := endpoint i w₀ foundU (supportNow i w₀ w foundU found slashed support)
      (key ▸ notPrevious)
    rw [effectiveEq i w w₀ found foundU effective, key]
    exact old

/-- The registry updates keep the reserve cut at the current epoch, under four explicit facts.

The updates keep the balances.

They keep each validator's key, effective balance, credentials and slashed flag.

So every clause transports once its guard does.

They may assign an activation, an exit and a withdrawable epoch:

- Two premises cover the retired keys and the keys active at the start.
  They say that such a key was already activated.
  So an assigned activation cannot make it supported later.
- `activity` says that activity up to the current epoch is unchanged.
  So support at the demand epoch and the one before it is unchanged.
- `ejected` says that a key without an assigned exit keeps its withdrawable epoch.
  Otherwise, both its old and new withdrawable epochs are after the current epoch.

An assigned exit keeps its withdrawable epoch.

This holds from Electra, for the registry updates. -/
private theorem reserveCut_registry {x : ForkedBeaconState preset} {high : Nat} {fork : Fork}
    {u v : BeaconState preset fork} {suffix : List PendingConsolidation} {o : Ownership}
    (electra : .pectra ≤ fork)
    (ok : processRegistryUpdates config u = .ok v)
    (retiredActivated : ∀ i ∈ o.retired, ∀ w₀ : Validator, u.validators.data[i]? = some w₀ →
      w₀.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (startActivated : ∀ (i : Nat) (initial w₀ : Validator),
      x.state.validators.data[i]? = some initial →
      isActiveValidator initial (getCurrentEpoch x.state) = true →
      u.validators.data[i]? = some w₀ → w₀.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (activity : ∀ (i : Nat) (w₀ w : Validator), u.validators.data[i]? = some w₀ →
      v.validators.data[i]? = some w → ∀ e ≤ getCurrentEpoch u,
        isActiveValidator w e = isActiveValidator w₀ e)
    (ejected : ∀ (i : Nat) (w₀ w : Validator), u.validators.data[i]? = some w₀ →
      w₀.exitEpoch = FAR_FUTURE_EPOCH → v.validators.data[i]? = some w →
      w.withdrawableEpoch = w₀.withdrawableEpoch ∨
        (getCurrentEpoch u < w₀.withdrawableEpoch ∧ getCurrentEpoch u < w.withdrawableEpoch))
    (reserve : ReserveCut x high ⟨fork, u⟩ (getCurrentEpoch u) suffix o) :
    ReserveCut x high ⟨fork, v⟩ (getCurrentEpoch u) suffix o := by
  apply reserveCut_of_kept retiredActivated startActivated activity
    (registryKept_of_lookup (processRegistryUpdates_lookup ok)) ?_
    (processRegistryUpdates_balances ok) reserve
  intro i w₀ w foundU found
  by_cases assigned : w₀.exitEpoch = FAR_FUTURE_EPOCH
  · exact ejected i w₀ w foundU assigned found
  · obtain ⟨w', found', exact⟩ :=
      processRegistryUpdates_withdrawableEpoch_of_assigned electra ok i w₀ foundU assigned
    rw [found] at found'
    cases found'
    exact .inl exact

/-- Registry updates keep activity up to the current epoch, as a step that keeps the registry. -/
private theorem registry_activity {fork : Fork} {u v : BeaconState preset fork}
    (ok : processRegistryUpdates config u = .ok v) :
    ∀ (i : Nat) (w₀ w : Validator), u.validators.data[i]? = some w₀ →
      v.validators.data[i]? = some w → ∀ e ≤ getCurrentEpoch u,
        isActiveValidator w e = isActiveValidator w₀ e := by
  intro i w₀ w foundU found e early
  have kept := (stepKeeps_processRegistryUpdates ok).2.2 e
    (UInt64.le_trans early (getCurrentEpoch_le_activityFixedEpoch u)) i
  simpa [isActiveAt, found, foundU] using kept

/-- The registry updates keep the reserve cut at the current epoch, given two facts.

Retired and initially active keys were already activated.

The ejection fact `ejected` holds. -/
private theorem reserveCut_registry_of_ejected {x : ForkedBeaconState preset} {high : Nat}
    {fork : Fork} {u v : BeaconState preset fork} {suffix : List PendingConsolidation}
    {o : Ownership}
    (electra : .pectra ≤ fork)
    (ok : processRegistryUpdates config u = .ok v)
    (retiredActivated : ∀ i ∈ o.retired, ∀ w₀ : Validator, u.validators.data[i]? = some w₀ →
      w₀.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (startActivated : ∀ (i : Nat) (initial w₀ : Validator),
      x.state.validators.data[i]? = some initial →
      isActiveValidator initial (getCurrentEpoch x.state) = true →
      u.validators.data[i]? = some w₀ → w₀.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ejected : ∀ (i : Nat) (w₀ w : Validator), u.validators.data[i]? = some w₀ →
      w₀.exitEpoch = FAR_FUTURE_EPOCH → v.validators.data[i]? = some w →
      w.withdrawableEpoch = w₀.withdrawableEpoch ∨
        (getCurrentEpoch u < w₀.withdrawableEpoch ∧ getCurrentEpoch u < w.withdrawableEpoch))
    (reserve : ReserveCut x high ⟨fork, u⟩ (getCurrentEpoch u) suffix o) :
    ReserveCut x high ⟨fork, v⟩ (getCurrentEpoch u) suffix o :=
  reserveCut_registry electra ok retiredActivated startActivated (registry_activity ok) ejected
    reserve

/-- The registry updates keep the reserve cut at the current epoch.

Besides the update, it reads four facts of the history.

Retired and initially active keys were already activated, and exits come no later than withdrawals.

The current epoch is finite.

A key without an assigned exit then has its withdrawable epoch at the far future.

That epoch is after the current epoch.

The update keeps it there or sets it after the current epoch. -/
private theorem reserveCut_registry_final {x : ForkedBeaconState preset} {high : Nat}
    {fork : Fork} {u v : BeaconState preset fork} {suffix : List PendingConsolidation}
    {o : Ownership}
    (electra : .pectra ≤ fork)
    (ok : processRegistryUpdates config u = .ok v)
    (retiredActivated : ∀ i ∈ o.retired, ∀ w₀ : Validator, u.validators.data[i]? = some w₀ →
      w₀.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (startActivated : ∀ (i : Nat) (initial w₀ : Validator),
      x.state.validators.data[i]? = some initial →
      isActiveValidator initial (getCurrentEpoch x.state) = true →
      u.validators.data[i]? = some w₀ → w₀.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ordered : ExitsOrdered u) (finite : getCurrentEpoch u < FAR_FUTURE_EPOCH)
    (reserve : ReserveCut x high ⟨fork, u⟩ (getCurrentEpoch u) suffix o) :
    ReserveCut x high ⟨fork, v⟩ (getCurrentEpoch u) suffix o := by
  apply reserveCut_registry_of_ejected electra ok retiredActivated startActivated ?_ reserve
  intro i w₀ w foundU unassigned found
  obtain ⟨z, located, withdrawable⟩ :=
    processRegistryUpdates_withdrawableEpoch_of_unassigned electra ok i w₀ foundU unassigned
  rw [found] at located
  cases located
  -- An unassigned exit's withdrawable epoch is at the far future.
  have atFar : w₀.withdrawableEpoch = FAR_FUTURE_EPOCH := by
    have below := ordered w₀ (Array.mem_of_getElem? foundU)
    rw [unassigned] at below
    apply UInt64.toNat_inj.mp
    have := w₀.withdrawableEpoch.toNat_lt
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have := UInt64.le_iff_toNat_le.mp below
    omega
  refine .inr ⟨atFar ▸ finite, ?_⟩
  rcases withdrawable with same | late
  · rw [same, atFar]
    exact finite
  · exact late

def RetiredActivated {f : Fork} (u : BeaconState preset f)
    (retired : Finset Nat) : Prop :=
  ∀ i ∈ retired, ∃ v : Validator, u.validators.data[i]? = some v ∧
    v.activationEpoch ≠ FAR_FUTURE_EPOCH

theorem RetiredActivated.lifecycle {f g : Fork}
    {u : BeaconState preset f} {v : BeaconState preset g}
    (life : RegistryLifecycle u v) (prior : RetiredActivated u retired) :
    RetiredActivated v retired := by
  intro i member
  obtain ⟨old, found, assigned⟩ := prior i member
  obtain ⟨later, located, kept⟩ := life.validators i old found
  refine ⟨later, located, ?_⟩
  rw [kept.activationEpoch assigned]
  exact assigned

theorem RetiredActivated.insert {f : Fork} {u : BeaconState preset f}
    (prior : RetiredActivated u retired) (source : Nat) (v : Validator)
    (found : u.validators.data[source]? = some v)
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    RetiredActivated u (insert source retired) := by
  intro i member
  rcases Finset.mem_insert.mp member with rfl | member
  · exact ⟨v, found, assigned⟩
  · exact prior i member

theorem RetiredActivated.assigned {f : Fork} {u : BeaconState preset f}
    (prior : RetiredActivated u retired) (i : Nat) (member : i ∈ retired)
    (v : Validator) (found : u.validators.data[i]? = some v) :
    v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨old, read, assigned⟩ := prior i member
  obtain rfl : old = v := Option.some.inj (read.symm.trans found)
  exact assigned

/-- A key active at the reference state keeps its assigned activation epoch. -/
theorem lifecycle_start_active_assigned {x u : ForkedBeaconState preset}
    (life : RegistryLifecycle x.state u.state)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (i : Nat) (initial later : Validator)
    (found : x.state.validators.data[i]? = some initial)
    (active : isActiveValidator initial (getCurrentEpoch x.state) = true)
    (read : u.state.validators.data[i]? = some later) :
    later.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  have assigned : initial.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
    intro same
    have bound := UInt64.lt_of_le_of_lt active.1 finite
    rw [same] at bound
    exact (UInt64.lt_irrefl _) bound
  obtain ⟨w, located, kept⟩ := life.validators i initial found
  obtain rfl : w = later := Option.some.inj (located.symm.trans read)
  rw [kept.activationEpoch assigned]
  exact assigned

private theorem reservedFrame_registry {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processRegistryUpdates config s = .ok t)
    (retired : RetiredActivated s owned.retired)
    (start : RegistryLifecycle x.state s)
    (startFinite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (ordered : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩)) :
    ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, t⟩ (getCurrentEpoch s) (getCurrentEpoch s) queue owned owned := by
  have edge : EpochStage.Edge config checks .registry s t := ok
  have sameQueue : pendingQueue ⟨fork, t⟩ = pendingQueue ⟨fork, s⟩ := by
    have same : t.pendingConsolidations = s.pendingConsolidations :=
      edge.samePendingQueue (by simp)
    simp only [pendingQueue, electra, ↓reduceDIte, same]
  have after := reserveCut_registry_final electra ok retired.assigned
    (lifecycle_start_active_assigned (u := ⟨fork, s⟩) start startFinite) ordered finite reserve
  exact ⟨.cons (.epoch .registry (EpochStage.action_cases.mpr edge)) .nil,
    UInt64.le_refl _,
    (reservedFrame_refl (config := config) (checks := checks) reserve assignment erasure).2.2.1,
    assignment, assignment,
    erasure, sameQueue ▸ erasure, reserve, after⟩

private theorem reservedReplay_slashings_frame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch s)
    (ok : processSlashings s = .ok t) (limitOk : delayedSlashingLimit s = .ok limit)
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      start ⟨fork, s⟩ startEpoch (getCurrentEpoch s) queue before eventOwned)
    (prior : OwnershipBefore eventPosition paymentPosition before) :
    ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch ⟨fork, t⟩ (getCurrentEpoch t) eventPosition paymentPosition callPosition
      [⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, 0, limit⟩] queue queue [] [] []
      before (creditOwnership eventPosition
        ⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, 0, limit⟩ eventOwned) ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, t⟩ ⟨fork, t⟩ (getCurrentEpoch t) (getCurrentEpoch t) queue
        (creditOwnership eventPosition ⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, 0, limit⟩ eventOwned)
        (creditOwnership eventPosition ⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, 0, limit⟩ eventOwned) ∧
      (EndpointCoverAll x ⟨fork, s⟩ eventOwned →
        EndpointCoverAll x ⟨fork, t⟩ (creditOwnership eventPosition
          ⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, 0, limit⟩ eventOwned)) ∧
      (FutureEffectiveCover x ⟨fork, s⟩ eventOwned →
        FutureEffectiveCover x ⟨fork, t⟩ (creditOwnership eventPosition
          ⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, 0, limit⟩ eventOwned)) := by
  have records := processSlashings_frame ok
  obtain ⟨limit', computed, credits, _⟩ :=
    delayed_slashing_bounds s t (s.validators.bound early) ok
  have sameLimit : limit' = limit := Except.ok.inj (computed.symm.trans limitOk)
  subst limit'
  have sameSlot : t.slot = s.slot := by
    simpa only using congrArg (fun u : BeaconState preset fork => u.slot) records
  have sameQueue : pendingQueue (⟨fork, t⟩ : ForkedBeaconState preset) =
      pendingQueue ⟨fork, s⟩ := by
    rw [records]
    rfl
  have registry : t.validators.data = s.validators.data := by
    simpa only using congrArg (fun u : BeaconState preset fork => u.validators.data) records
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp only [getCurrentEpoch, sameSlot]
  have sizes := (balancesMatch_of_sameSizes (sameSizes_processSlashings ok) matched).symm
  let e : BalanceEvent preset := ⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, 0, limit⟩
  have notDeposit : e.source ≠ .deposits := by
    change BalanceSource.slashings ≠ .deposits
    decide
  have notTransfer : e.source ≠ .consolidations := by
    change BalanceSource.slashings ≠ .consolidations
    decide
  have fresh := (prior.frame frame.2.2.1).credit_fresh (Nat.le_refl eventPosition)
  have credit := ownedCredit_of_bounded (e := e) frame.2.2.2.2.2.2.2.2.1 fresh
    electra notTransfer sizes credits.le
  have appended : ∀ j w, s.validators.data.size ≤ j → t.validators.data[j]? = some w →
      w.effectiveBalance.toNat ≤ actualBalanceAt ⟨fork, t⟩ j := by
    intro j w outside read
    have inside := (Array.getElem?_eq_some_iff.mp read).1
    rw [registry] at inside
    omega
  obtain ⟨tagged, owned⟩ := reservedCredit_facts (callPosition := callPosition)
    electra notDeposit notTransfer rfl registry epoch sizes sameQueue credits.le frame prior
  -- The event's own reserve, assignment and outgoing erasure form the frame at its output.
  have reserve := owned.2.2.2
  simp only [notTransfer, ↓reduceIte] at reserve
  refine ⟨ReservedReplay.singleton_nonconsolidation notTransfer frame tagged owned,
    reservedFrame_refl reserve.2 owned.2.2.1 tagged.2.1,
    endpointCover_nonDeposit notDeposit rfl registry epoch matched fresh credit,
    futureCover_credit ⟨#[], by simp only [Array.append_empty]; exact registry⟩ epoch matched
      appended fresh credit⟩

theorem reservedReplay_registrySlashings_frame {fork : Fork}
    {s registered slashed : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (matched : BalancesMatch s)
    (registry : processRegistryUpdates config s = .ok registered)
    (slashings : processSlashings registered = .ok slashed)
    (limitOk : delayedSlashingLimit registered = .ok limit)
    (retired : RetiredActivated s eventOwned.retired)
    (startLife : RegistryLifecycle x.state s)
    (startFinite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (ordered : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      start ⟨fork, s⟩ startEpoch (getCurrentEpoch s) queue before eventOwned)
    (prior : OwnershipBefore eventPosition paymentPosition before) :
    ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch ⟨fork, slashed⟩ (getCurrentEpoch slashed)
      eventPosition paymentPosition callPosition
      [⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩]
      queue queue [] [] [] before
      (creditOwnership eventPosition
        ⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩ eventOwned) ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, slashed⟩ ⟨fork, slashed⟩ (getCurrentEpoch slashed) (getCurrentEpoch slashed) queue
        (creditOwnership eventPosition
          ⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩ eventOwned)
        (creditOwnership eventPosition
          ⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩ eventOwned) ∧
      (EndpointCoverAll x ⟨fork, s⟩ eventOwned →
        EndpointCoverAll x ⟨fork, slashed⟩ (creditOwnership eventPosition
          ⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩ eventOwned)) ∧
      (FutureEffectiveCover x ⟨fork, s⟩ eventOwned →
        FutureEffectiveCover x ⟨fork, slashed⟩ (creditOwnership eventPosition
          ⟨.slashings, ⟨fork, registered⟩, ⟨fork, slashed⟩, 0, limit⟩ eventOwned)) := by
  have registryFrame := reservedFrame_registry (checks := checks) electra registry retired startLife
    startFinite ordered finite frame.2.2.2.2.2.2.2.2 frame.2.2.2.2.1 frame.2.2.2.2.2.2.1
  have epoch : getCurrentEpoch registered = getCurrentEpoch s := by
    simp only [getCurrentEpoch, (frame_processRegistryUpdates registry).slot]
  have registeredFrame : ReservedFrame (config := config) (checks := checks) x high rounding
      start ⟨fork, registered⟩ startEpoch (getCurrentEpoch registered) queue before eventOwned := by
    rw [epoch]
    exact frame.trans registryFrame
  have registeredMatch : BalancesMatch registered :=
    (show EpochStage.Edge config checks .registry s registered from
          registry).balancesMatch_of_not_justification
      (by simp) matched
  obtain ⟨replay, last, cover, future⟩ := reservedReplay_slashings_frame electra early
    registeredMatch slashings limitOk registeredFrame prior
  exact ⟨replay, last, fun initial => cover (endpointCover_registry registry initial),
    fun initial => future (futureCover_registry registry initial)⟩

/-- A source the pending consolidations pay at `next` is not covered at the current epoch.

The finite next epoch lets the endpoint bound for a due source exclude an unassigned exit. -/
theorem consolidation_sourceGone {fork : Fork} {s : BeaconState preset fork}
    {next : Epoch} {w : Validator} (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (nextOk : Uint64.addChecked (getCurrentEpoch s) 1 = .ok next)
    (ordered : w.exitEpoch ≤ w.withdrawableEpoch)
    (delay : w.exitEpoch ≠ FAR_FUTURE_EPOCH →
      w.exitEpoch.toNat + 2 ≤ w.withdrawableEpoch.toNat)
    (due : w.withdrawableEpoch ≤ next) (covered : getCurrentEpoch s ≤ w.exitEpoch) : False :=
  endpoint_sourceGone (nextEpoch_lt_farFuture twoSlots nextOk) ordered delay due nextOk covered

theorem endpointCoverAll_records {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {o : Ownership}
    (validators : v.validators = u.validators) (balances : v.balances = u.balances)
    (slot : v.slot = u.slot) (cover : EndpointCoverAll x ⟨fork, u⟩ o) :
    EndpointCoverAll x ⟨fork, v⟩ o := by
  simpa only [EndpointCoverAll, validators, actualBalanceAt, balances, getCurrentEpoch, slot]
    using cover

theorem reservedReplay_epochRewardStart_owned {fork : Fork}
    {s justified scored rewarded : BeaconState preset fork}
    {recorded : List (BalanceEvent preset)}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    (justifiedOk : EpochStage.Edge config checks .justification s justified)
    (scoredOk : EpochStage.Edge config checks .inactivity justified scored)
    (replay : replayRewards (config := config) (scored, []) = .ok (rewarded, recorded))
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned)
    (assignment : AssignmentCut rounding queue owned)
    (erasure : QueueErasure queue (pendingQueue ⟨fork, s⟩))
    (prior : OwnershipBefore eventPosition paymentPosition owned) :
    ∃ after, ReservedReplay (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, rewarded⟩ (getCurrentEpoch rewarded)
      eventPosition paymentPosition callPosition recorded queue queue [] [] [] owned after ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        ⟨fork, rewarded⟩ ⟨fork, rewarded⟩ (getCurrentEpoch rewarded) (getCurrentEpoch rewarded)
        queue after after ∧
      OwnershipBefore (eventPosition + recorded.length) paymentPosition after ∧
      BalancesMatch rewarded ∧
      (EndpointCoverAll x ⟨fork, s⟩ owned → EndpointCoverAll x ⟨fork, rewarded⟩ after) ∧
      (FutureEffectiveCover x ⟨fork, s⟩ owned → FutureEffectiveCover x ⟨fork, rewarded⟩ after) ∧
      after.retired = owned.retired ∧ rewarded.validators.data = s.validators.data ∧
      after.original = owned.original := by
  have first := reservedFrame_justification (config := config) (checks := checks)
    justifiedOk reserve assignment erasure
  have second := reservedFrame_inactivity (config := config) (checks := checks)
    (EpochStage.action_cases.mpr scoredOk) first.2.2.2.2.2.2.2.2 assignment first.2.2.2.2.2.2.1
  have epoch : getCurrentEpoch scored = getCurrentEpoch s := by
    simp only [getCurrentEpoch, scoredOk.slot_eq, justifiedOk.slot_eq]
  have combined : ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, scored⟩ (getCurrentEpoch s) (getCurrentEpoch scored) queue owned owned := by
    rw [epoch]
    exact first.trans second
  obtain ⟨sameValidators, sameBalances, _⟩ := justifiedOk.records (by simp)
  obtain ⟨scoredValidators, scoredBalances, _⟩ := scoredOk.records (by simp)
  have scoredMatched : BalancesMatch scored := by
    simpa only [BalancesMatch, scoredValidators, scoredBalances, sameValidators, sameBalances]
      using matched
  obtain ⟨after, history, frame, counters, sizes, cover, future, retiredSame, registrySame,
      originalSame⟩ :=
    reservedReplay_rewards_owned (callPosition := callPosition) electra scoredMatched combined
      prior replay
  refine ⟨after, history, frame, counters, sizes, fun initial => cover ?_,
    fun initial => future ?_, retiredSame, ?_, originalSame⟩
  rotate_left 2
  · -- Justification and inactivity keep the registry.
    rw [registrySame, scoredValidators, sameValidators]
  · have justifiedCover :=
      endpointCoverAll_records sameValidators sameBalances justifiedOk.slot_eq initial
    exact endpointCoverAll_records scoredValidators scoredBalances scoredOk.slot_eq justifiedCover
  · have justifiedFuture := futureCover_records sameValidators (by
      simp only [getCurrentEpoch, justifiedOk.slot_eq]
      exact UInt64.le_refl _) initial
    exact futureCover_records scoredValidators (by
      simp only [getCurrentEpoch, scoredOk.slot_eq]
      exact UInt64.le_refl _) justifiedFuture

/-- Queueing a consolidation keeps the endpoint cover.

Only the source changes: the step sets its exit epoch, which was the far future.

Its key, credentials, slashed flag and balance stay.

A source covered after the step was covered before it, since every epoch is at most the far future.

No balance changes. -/
private theorem endpointCover_queueConsolidation {x : ForkedBeaconState preset} {fork : Fork}
    {u v : BeaconState preset fork} {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator} {o : Ownership}
    (found : u.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (ok : queueConsolidation config u electra sourceIndex source targetIndex = .ok v)
    (cover : EndpointCoverAll x ⟨fork, u⟩ o) :
    EndpointCoverAll x ⟨fork, v⟩ o := by
  have slot := (frame_queueConsolidation found ok).slot
  have epoch : getCurrentEpoch v = getCurrentEpoch u := by simp only [getCurrentEpoch, slot]
  obtain ⟨exitEpoch, _, _, _, _, churned, _, set, _, rfl⟩ := queueConsolidation_steps ok
  obtain ⟨-, -, balances⟩ := computeConsolidationEpochAndUpdateChurn_earliest churned
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  apply endpointCover_mono (u := ⟨fork, u⟩) ?_ (fun _ => Nat.le_refl _) cover
  intro i w foundV clean notExited current
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at foundV
  have currentU : getCurrentEpoch u ≤ w.exitEpoch := epoch ▸ current
  by_cases same : sourceIndex.toNat = i
  · subst same
    rw [Array.getElem?_set_self] at foundV
    cases foundV
    -- Before the step the source had not started to exit, so it was covered.
    have lt := UInt64.lt_iff_toNat_lt.mp notExited
    have bound := exitEpoch.toNat_lt
    refine ⟨source, found, clean, ?_, ?_, rfl, ?_⟩
    · rw [far]
      exact UInt64.lt_iff_toNat_lt.mpr (by simp only at lt; omega)
    · show getCurrentEpoch u ≤ source.exitEpoch
      rw [far]
      exact UInt64.le_iff_toNat_le.mpr (by have := (getCurrentEpoch u).toNat_lt; omega)
    · -- The step keeps every balance, and the source keeps its credentials.
      simp only [actualBalanceAt, BeaconState.putValidator, balances]
      exact Nat.le_refl _
  · rw [Array.getElem?_set_ne _ same] at foundV
    refine ⟨w, foundV, clean, notExited, currentU, rfl, ?_⟩
    simp only [actualBalanceAt, BeaconState.putValidator, balances]
    exact Nat.le_refl _

/-- A consolidation request keeps the endpoint cover.

It returns its state or switches one validator to compounding credentials.

Otherwise, it queues a consolidation.

Each of these keeps the cover. -/
theorem endpointCover_processConsolidationRequest {x : ForkedBeaconState preset}
    {fork : Fork} {u v : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : ConsolidationRequest} {o : Ownership}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processConsolidationRequest config u electra request = .ok v)
    (cover : EndpointCoverAll x ⟨fork, u⟩ o) :
    EndpointCoverAll x ⟨fork, v⟩ o := by
  have cases := consolidationRequest_cases ok
  rcases cases with rfl | ⟨_, _, _, switched⟩ | ⟨_, _, _, _, accepted, queued⟩
  · exact cover
  · exact endpointCover_switch compounding switched cover
  -- The source had not started to exit.
  · exact endpointCover_queueConsolidation accepted.sourceAt accepted.sourceStays queued cover

/-- The paid step of a pending consolidation keeps the registry and the slot.

It credits the target by at most the moved amount, and raises no other balance. -/
theorem pendingTransfer_balances {fork : Fork} {u d t : BeaconState preset fork}
    {c : PendingConsolidation} {amount : Gwei}
    (debited : decreaseBalance u c.sourceIndex amount = .ok d)
    (credited : increaseBalance d c.targetIndex amount = .ok t)
    (apart : c.sourceIndex.toNat ≠ c.targetIndex.toNat) :
    t.validators = u.validators ∧ t.slot = u.slot ∧
      actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) c.targetIndex.toNat ≤
        actualBalanceAt ⟨fork, u⟩ c.targetIndex.toNat + amount.toNat ∧
      ∀ i, i ≠ c.sourceIndex.toNat → i ≠ c.targetIndex.toNat →
        actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) i ≤ actualBalanceAt ⟨fork, u⟩ i := by
  obtain ⟨insideD, rfl⟩ := decreaseBalance_eq_ok_iff.mp debited
  obtain ⟨insideT, _, rfl⟩ := increaseBalance_eq_ok_iff.mp credited
  refine ⟨rfl, rfl, ?_, fun i source target => ?_⟩
  · -- The target gains the amount; the debit is at another index.
    have insideU : c.targetIndex.toNat < u.balances.data.size := by
      simpa [BeaconState.putBalance] using insideT
    simp [actualBalanceAt, BeaconState.putBalance]
    refine Nat.le_trans (Nat.mod_le _ _) ?_
    simp [Array.getElem_set, apart, Array.getElem?_eq_getElem insideU]
  · simp [actualBalanceAt, BeaconState.putBalance, Ne.symm source, Ne.symm target]

/-- A paid pending consolidation keeps the endpoint cover.

The paid step keeps the registry and the slot.

It gives the target at most the amount, and raises no other balance.

The source can withdraw at the next epoch.

So it has exited before the current epoch and is not covered. -/
theorem endpointCover_pendingTransfer {x : ForkedBeaconState preset} {fork : Fork}
    {u d t : BeaconState preset fork} {c : PendingConsolidation} {w : Validator}
    {b : Gwei} {next : Epoch} {position : Nat} {allocation : OwnedRelease}
    {before after : Ownership}
    (found : getValidator u c.sourceIndex = .ok w)
    (debited : decreaseBalance u c.sourceIndex (min b w.effectiveBalance) = .ok d)
    (credited : increaseBalance d c.targetIndex (min b w.effectiveBalance) = .ok t)
    (transfer : OwnedTransfer position
      ⟨c.sourceIndex.toNat, c.targetIndex.toNat, (min b w.effectiveBalance).toNat, next.toNat,
        ⟨fork, u⟩, ⟨fork, t⟩⟩ allocation before after)
    (apart : c.sourceIndex ≠ c.targetIndex)
    (nextOk : Uint64.addChecked (getCurrentEpoch u) 1 = .ok next)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (exits : ExitsOrdered u)
    (delay : ∀ (i : Nat) (v : Validator), u.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (due : w.withdrawableEpoch ≤ next)
    (cover : EndpointCoverAll x ⟨fork, u⟩ before) :
    EndpointCoverAll x ⟨fork, t⟩ after := by
  have foundU := getValidator_eq_ok_iff.mp found
  have apartNat : c.sourceIndex.toNat ≠ c.targetIndex.toNat :=
    fun same => apart (UInt64.toNat_inj.mp same)
  obtain ⟨validators, slot, target, others⟩ := pendingTransfer_balances debited credited apartNat
  refine endpointCover_transfer (u := ⟨fork, u⟩) transfer apartNat rfl
    (congrArg (·.data) validators) (by simp only [getCurrentEpoch, slot]) target others ?_ cover
  intro v foundV _ _ covered
  change u.validators.data[c.sourceIndex.toNat]? = some v at foundV
  rw [foundU] at foundV
  cases foundV
  exact consolidation_sourceGone twoSlots nextOk (exits w (Array.mem_of_getElem? foundU))
    (delay _ w foundU) due covered

/-- An owned transfer keeps the reserve cut and drops its consolidation from the suffix.

The source retires: it is never supported again, waits for no activation, and leaves the suffix.

The target gains the whole payment in held and endpoint tokens.

Its balance gains at most the payment.

Every other key keeps its tokens, its original and its balance bound. -/
private theorem reserveCut_transfer {x u v : ForkedBeaconState preset} {high position : Nat}
    {p : Payment preset} {allocation : OwnedRelease} {before after : Ownership}
    {epoch : Epoch} {c : PendingConsolidation} {suffix : List PendingConsolidation}
    {w : Validator}
    (transfer : OwnedTransfer position p allocation before after)
    (apart : p.source ≠ p.target)
    (fork : v.fork = u.fork) (registry : v.state.validators.data = u.state.validators.data)
    (targetBalance : actualBalanceAt v p.target ≤ actualBalanceAt u p.target + p.amount)
    (others : ∀ i, i ≠ p.source → i ≠ p.target → actualBalanceAt v i ≤ actualBalanceAt u i)
    (found : u.state.validators.data[p.source]? = some w)
    (sourceGone : ∀ e, epoch ≤ e → ¬ SupportedAt e w)
    (sourceWaiting : ¬ (epoch < w.activationEpoch ∧ epoch < w.exitEpoch))
    (sourceAbsent : ¬ ∃ q ∈ suffix, q.sourceIndex.toNat = p.source)
    (reserve : ReserveCut x high u epoch (c :: suffix) before) :
    ReserveCut x high v epoch suffix after := by
  -- Only the target grows, by the payment.
  let growth : Nat → Nat := fun i => if i = p.target then p.amount else 0
  have tokens := ownedTransfer_held transfer apart
  have balances : ∀ i, i ≠ p.source → actualBalanceAt v i ≤ actualBalanceAt u i + growth i := by
    intro i source
    by_cases target : i = p.target
    · subst target
      simpa [growth] using targetBalance
    · simpa [growth, target] using others i source target
  have heldGrowth : ∀ i, i ≠ p.source → (held before i).card + growth i ≤ (held after i).card := by
    intro i source
    by_cases target : i = p.target
    · subst target
      simpa [growth] using tokens.1
    · simp [growth, target, tokens.2.2 i source target]
  have endpointGrowth : ∀ i, i ≠ p.source → (held before i ∩ before.endpoint).card + growth i ≤
      (held after i ∩ after.endpoint).card := by
    intro i source
    by_cases target : i = p.target
    · subst target
      simpa [growth] using tokens.2.1
    · simp [growth, target, ownedTransfer_endpoint_other transfer apart source target]
  obtain ⟨_, valid, _, _, _, _, _, _, _, _, _, _, retired, originalSource, originalOther,
    _, _, _, _⟩ := transfer
  have lookup : ∀ i : Nat, v.state.validators.data[i]? = u.state.validators.data[i]? := by
    intro i
    rw [registry]
  have effective : ∀ i : Nat, effectiveAt v i = effectiveAt u i := by
    intro i
    simp only [effectiveAt, lookup i]
  have relevant : ∀ i, FundingRelevant v epoch suffix i →
      FundingRelevant u epoch (c :: suffix) i := by
    rintro i ⟨validator, located, rest⟩
    refine ⟨validator, lookup i ▸ located, rest.imp_right (Or.imp_right ?_)⟩
    rintro ⟨q, member, same⟩
    exact ⟨q, List.mem_cons_of_mem _ member, same⟩
  have remains : ∀ i, i ∉ after.retired → i ≠ p.source ∧ i ∉ before.retired := by
    intro i notRetired
    rw [retired, Finset.mem_insert, not_or] at notRetired
    exact notRetired
  have sourceIs : ∀ validator, v.state.validators.data[p.source]? = some validator →
      validator = w := by
    intro validator located
    rw [lookup, found] at located
    exact (Option.some.inj located).symm
  have capped : ∀ i validator, i ≠ p.source →
      min (actualBalanceAt v i) (withdrawalMaxEffectiveBalance preset v.fork validator).toNat ≤
      min (actualBalanceAt u i) (withdrawalMaxEffectiveBalance preset u.fork validator).toNat +
        growth i := by
    intro i validator source
    have increase := balances i source
    rw [fork]
    omega
  obtain ⟨_, wasRetired, wasOriginal, reference, scheduled, pending, queued, idle,
    activePending, endpoint⟩ := reserve
  refine ⟨valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i member validator located
    rw [retired, Finset.mem_insert] at member
    rcases member with rfl | old
    · rw [sourceIs validator located]
      exact ⟨sourceGone, sourceAbsent⟩
    · obtain ⟨unsupported, absent⟩ := wasRetired i old validator (lookup i ▸ located)
      exact ⟨unsupported, fun ⟨q, member, same⟩ =>
        absent ⟨q, List.mem_cons_of_mem _ member, same⟩⟩
  · intro i
    by_cases source : i = p.source
    · subst source
      exact ⟨by rw [originalSource]; exact Nat.zero_le _, fun _ => originalSource⟩
    · rw [originalOther i source]
      exact wasOriginal i
  · intro i ref notRetired support
    obtain ⟨source, old⟩ := remains i notRetired
    have bound := reference i ref old (relevant i support)
    have gain := heldGrowth i source
    obtain ⟨w', located, _⟩ := support
    have rise := capped i w' source
    rw [originalOther i source]
    simp only [potential, located, (lookup i).symm.trans located, Option.map_some,
      Option.getD_some] at bound ⊢
    omega
  · intro i initial validator located active clean finite current support
    by_cases source : i = p.source
    · subst source
      obtain ⟨e, later, supported⟩ := support
      exact (sourceGone e later (sourceIs validator current ▸ supported)).elim
    · have bound := scheduled i initial validator located active clean finite
        (lookup i ▸ current) support
      have change := capped i validator source
      have gain := endpointGrowth i source
      rw [effective i]
      omega
  · intro i initial notRetired support validator located
    obtain ⟨source, old⟩ := remains i notRetired
    have bound := pending i initial old (relevant i support) validator (lookup i ▸ located)
    have change := capped i validator source
    have gain := heldGrowth i source
    omega
  · intro entry member validator located ready notRef
    -- The paid consolidation was the source's only entry, so a later entry has another source.
    have source : entry.sourceIndex.toNat ≠ p.source := fun same =>
      sourceAbsent ⟨entry, member, same⟩
    have bound := queued entry (List.mem_cons_of_mem _ member) validator (lookup _ ▸ located)
      ready notRef
    have change := capped _ validator source
    have gain := heldGrowth _ source
    omega
  · intro i validator located notRef notPending quiet support
    by_cases source : i = p.source
    · subst source
      rw [sourceIs validator located] at support
      rcases support with supported | waiting | ⟨⟨q, member, same⟩, _⟩
      · exact (sourceGone epoch (UInt64.le_refl _) supported).elim
      · exact (sourceWaiting waiting).elim
      · exact (sourceAbsent ⟨q, member, same⟩).elim
    · have bound := idle i validator (lookup i ▸ located) notRef notPending quiet
        (support.imp_right (Or.imp_right fun ⟨⟨q, member, same⟩, outside⟩ =>
          ⟨⟨q, List.mem_cons_of_mem _ member, same⟩, outside⟩))
      have change := capped i validator source
      have gain := heldGrowth i source
      rw [effective i]
      omega
  · intro i initial validator old located current active notRetired support
    obtain ⟨source, wasNotRetired⟩ := remains i notRetired
    obtain ⟨balance, eff⟩ := activePending i initial validator old (lookup i ▸ located) current
      active wasNotRetired (relevant i support)
    have change := capped i validator source
    have gain := endpointGrowth i source
    rw [effective i]
    constructor <;> omega
  · intro i validator located supported notPrevious
    by_cases source : i = p.source
    · subst source
      exact (sourceGone epoch (UInt64.le_refl _) (sourceIs validator located ▸ supported)).elim
    · have bound := endpoint i validator (lookup i ▸ located) supported notPrevious
      have gain := endpointGrowth i source
      rw [effective i]
      omega

/-- A paid pending consolidation keeps the reserve cut and drops its entry from the suffix.

The source is due at `next`, so its exit is no later than `next` and it waits for no activation. -/
theorem reserveCut_pendingTransfer {x : ForkedBeaconState preset} {fork : Fork}
    {u d t : BeaconState preset fork} {c : PendingConsolidation} {w : Validator}
    {b : Gwei} {high : Nat} {next : Epoch} {suffix : List PendingConsolidation} {position : Nat}
    {allocation : OwnedRelease} {before after : Ownership}
    (found : getValidator u c.sourceIndex = .ok w)
    (debited : decreaseBalance u c.sourceIndex (min b w.effectiveBalance) = .ok d)
    (credited : increaseBalance d c.targetIndex (min b w.effectiveBalance) = .ok t)
    (transfer : OwnedTransfer position
      ⟨c.sourceIndex.toNat, c.targetIndex.toNat, (min b w.effectiveBalance).toNat, next.toNat,
        ⟨fork, u⟩, ⟨fork, t⟩⟩ allocation before after)
    (apart : c.sourceIndex ≠ c.targetIndex)
    (exits : ExitsOrdered u)
    (due : w.withdrawableEpoch ≤ next)
    (sourceGone : ∀ epoch, next ≤ epoch → ¬ SupportedAt epoch w)
    (sourceAbsent : ¬ ∃ q ∈ suffix, q.sourceIndex = c.sourceIndex)
    (reserve : ReserveCut x high ⟨fork, u⟩ next (c :: suffix) before) :
    ReserveCut x high ⟨fork, t⟩ next suffix after := by
  have foundU := getValidator_eq_ok_iff.mp found
  have apartNat : c.sourceIndex.toNat ≠ c.targetIndex.toNat :=
    fun same => apart (UInt64.toNat_inj.mp same)
  obtain ⟨validators, _, target, others⟩ := pendingTransfer_balances debited credited apartNat
  refine reserveCut_transfer (u := ⟨fork, u⟩) transfer apartNat rfl
    (congrArg (·.data) validators) target others foundU sourceGone ?_ ?_ reserve
  · -- Its exit is at most its withdrawal epoch, which is at most `next`.
    rintro ⟨_, late⟩
    exact UInt64.not_le.mpr late (UInt64.le_trans (exits w (Array.mem_of_getElem? foundU)) due)
  · rintro ⟨q, member, same⟩
    exact sourceAbsent ⟨q, member, UInt64.toNat_inj.mp same⟩

private theorem reserveCut_payment_funded {x : ForkedBeaconState preset} {fork : Fork}
    {s : BeaconState preset fork} {c : PendingConsolidation} {suffix : List PendingConsolidation}
    {w : Validator} {b : Gwei} {next : Epoch} {before : Ownership}
    (reserve : ReserveCut x high ⟨fork, s⟩ next (c :: suffix) before)
    (found : getValidator s c.sourceIndex = .ok w)
    (balance : getBalance s c.sourceIndex = .ok b)
    (due : w.withdrawableEpoch ≤ next)
    (cap : w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork w) :
    c.sourceIndex.toNat ∉ before.retired ∧
      (min b w.effectiveBalance).toNat ≤
        before.original c.sourceIndex.toNat + (held before c.sourceIndex.toNat).card := by
  have read := getValidator_eq_ok_iff.mp found
  have actual : actualBalanceAt (⟨fork, s⟩ : ForkedBeaconState preset) c.sourceIndex.toNat =
      b.toNat := by
    simp only [actualBalanceAt, getBalance_eq_ok_iff.mp balance]
    rfl
  have unretired : c.sourceIndex.toNat ∉ before.retired := by
    intro retired
    exact (reserve.2.1 _ retired w read).2 ⟨c, List.mem_cons_self, rfl⟩
  refine ⟨unretired, ?_⟩
  have amount : (min b w.effectiveBalance).toNat = min b.toNat w.effectiveBalance.toNat :=
    Uint64.toNat_min _ _
  by_cases fresh : NewReference x c.sourceIndex.toNat
  · have relevant : FundingRelevant ⟨fork, s⟩ next (c :: suffix) c.sourceIndex.toNat :=
      ⟨w, read, Or.inr (Or.inr ⟨c, List.mem_cons_self, rfl⟩)⟩
    have funded := reserve.2.2.2.1 _ fresh unretired relevant
    simp only [potential, read, Option.map_some, Option.getD_some] at funded
    rw [amount]
    exact (Nat.min_le_right _ _).trans ((Nat.le_max_left _ _).trans funded)
  · have funded := reserve.2.2.2.2.2.2.1 c List.mem_cons_self w read due fresh
    rw [actual] at funded
    change min b.toNat (withdrawalMaxEffectiveBalance preset fork w).toNat ≤
      (held before c.sourceIndex.toNat).card at funded
    have bounded := UInt64.le_iff_toNat_le.mp cap
    rw [amount]
    have limited : min b.toNat w.effectiveBalance.toNat ≤
        min b.toNat (withdrawalMaxEffectiveBalance preset fork w).toNat :=
      le_min (Nat.min_le_left _ _) ((Nat.min_le_right _ _).trans bounded)
    exact limited.trans (funded.trans (Nat.le_add_left _ _))

theorem payment_ownedTransfer_exists {x : ForkedBeaconState preset} {fork : Fork}
    {s t : BeaconState preset fork} {c : PendingConsolidation}
    {suffix : List PendingConsolidation} {w : Validator} {b : Gwei} {next : Epoch}
    {before : Ownership} {high position sourceRound : Nat}
    (reserve : ReserveCut x high ⟨fork, s⟩ next (c :: suffix) before)
    (found : getValidator s c.sourceIndex = .ok w)
    (balance : getBalance s c.sourceIndex = .ok b)
    (due : w.withdrawableEpoch ≤ next)
    (cap : w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork w)
    (fresh : ∀ unit, TokenOrigin.released position unit ∉ before.issued) :
    ∃ allocation : OwnedRelease, ∃ after : Ownership,
      allocation.sourceRound = sourceRound ∧
      allocation.baseline = min (min b w.effectiveBalance).toNat
        (before.original c.sourceIndex.toNat) ∧
      OwnedTransfer position
        ⟨c.sourceIndex.toNat, c.targetIndex.toNat, (min b w.effectiveBalance).toNat,
          next.toNat, ⟨fork, s⟩, ⟨fork, t⟩⟩ allocation before after := by
  obtain ⟨unretired, funded⟩ := reserveCut_payment_funded reserve found balance due cap
  exact ownedTransfer_exists before
    ⟨c.sourceIndex.toNat, c.targetIndex.toNat, (min b w.effectiveBalance).toNat,
      next.toNat, ⟨fork, s⟩, ⟨fork, t⟩⟩ position sourceRound reserve.1 fresh unretired funded

end

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
