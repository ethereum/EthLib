module

public import EthLib.Consensus.Proofs.DirectSafety.Drift

/-!
# Direct accountable safety of two executions

Two executions of the state transition start at one genesis and share a prefix up to a state `x`.

Each then runs a tail of its own, and the two end in conflicting finalized checkpoints.

Then the accountable keys hold at least a third of the unslashed active stake at `x`.

Two thirds of the larger drift of the two tails are subtracted from that third.

Otherwise the hashes of the two runs show a collision or a zero root.

A key is accountable when the runs accepted two of its votes that a slashing would punish.

It is also accountable when a block of either tail applied a slashing that names it.

That slashing may be a proposer slashing.

The votes are the attestations that the blocks of the runs applied, read by public key.

The weights are the effective balances at the states of the runs.

A slashing in the shared prefix does not make a key accountable by itself.

A key that it slashed leaves the reference set and the accountable set.

`Accountable` can still hold for such a key, but `accountableKeys` keeps only `unslashedKeys x`.

A key that a prefix attester slashing named without slashing it stays in the reference set.

`slashIfSlashable` skips such a key.

It can still count, through double votes or through evidence in a tail.

The stake of a prefix-slashed key is absent from the later drift and support.

That holds only because of forward persistence: a slashed flag stays set.

The proofs here do not need that fact, because the drift is observed, not bounded.

The drift charges twice the stake that leaves or loses balance after `x`.

It charges once the stake that joins or gains balance.

It also charges twice the stake active only at the previous epoch.

It is zero when the active validators and their effective balances stay the same.

They must stay so from the epoch before `x` to one epoch past the later finalized epoch.

It is the largest drift that the tails observe, not a bound in closed form.

[Casper FFG] §2.1, Theorem 1, proves accountable safety for one set of validators.

[Gasper] §8.6, Theorem 8.3, proves it for changing sets.

These proofs do not go through those models.

For each accountable key, a second theorem gives the checks that the runs executed.

It assumes nothing about the signature checks.

[Casper FFG]: https://arxiv.org/abs/1710.09437
[Gasper]: https://arxiv.org/abs/2003.03052v3
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The unslashed keys active at `x` that are accountable on the two tails. -/
noncomputable def accountableKeys {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b) : Finset BLSPubkey := by
  classical
  exact (unslashedKeys x.state).filter (Accountable shared left right)

/-- Both calls are in the tails, because they target epoch `low` or later.

A key slashed at a call and unslashed at `x` has slashing evidence in the tail of the call. -/
private theorem accountable_pair_bound {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    {low high : Nat} (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (enoughA : EnoughStake (shared.append left) high)
    (enoughB : EnoughStake (shared.append right) high)
    (one two : EitherCall (shared.append left) (shared.append right))
    (lowerOne : low ≤ one.targetEpoch) (lowerTwo : low ≤ two.targetEpoch)
    (withinOne : one.targetEpoch ≤ high) (withinTwo : two.targetEpoch ≤ high)
    (overlap : ∀ key ∈ one.voters ∩ two.voters,
      Slashable (shared.append left) (shared.append right) key) :
      Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) +
        stateDrift x one.state + stateDrift x two.state := by
    classical
    let bad := (unslashedKeys x.state).filter (Accountable shared left right)
    have facts (call : EitherCall (shared.append left) (shared.append right))
        (lower : low ≤ call.targetEpoch) (within : call.targetEpoch ≤ high) :
        call.voters ⊆ recentKeys call.state.state ∧
        2 * Models.stake (effectiveWeight call.state.state) (unslashedKeys call.state.state) ≤
          3 * Models.stake (effectiveWeight call.state.state) call.voters ∧
        (∑ k ∈ unslashedKeys x.state \ bad,
          (effectiveWeight x.state k - Models.supported (recentKeys call.state.state)
            (effectiveWeight call.state.state) k)) ≤ referenceLoss x call.state := by
      have branch {z : ForkedBeaconState preset} (tail : Run config checks x z)
          (enough : EnoughStake (shared.append tail) high)
          (included : ∀ k, tail.SlashingEvidence k → Accountable shared left right k)
          (c : QuorumCall (shared.append tail)) (lower : low ≤ c.target.epoch.toNat)
          (within : c.target.epoch.toNat ≤ high) :
          c.voters ⊆ recentKeys c.cached ∧
          2 * Models.stake (effectiveWeight c.cached) (unslashedKeys c.cached) ≤
            3 * Models.stake (effectiveWeight c.cached) c.voters ∧
          (∑ k ∈ unslashedKeys x.state \ bad,
            (effectiveWeight x.state k - Models.supported (recentKeys c.cached)
              (effectiveWeight c.cached) k)) ≤ referenceLoss x ⟨c.before.fork, c.cached⟩ := by
        -- Removing slashed keys from the denominator keeps a quorum.
        refine ⟨quorum_voters_recent _ parameters genesis c,
          (Nat.mul_le_mul_left 2 (Models.stake_mono (Finset.filter_subset _ _))).trans
            (quorum_count _ genesis enough c within), ?_⟩
        -- The call is in the tail, so the run up to it starts at `x`.
        obtain ⟨pre, post, split⟩ := tail.contains_split (.slot c.advanced)
          (call_after_reference shared tail parameters low starts c lower)
        obtain ⟨_, _, _, _, validators, _⟩ := c.toEpochCall.selected_prefix
        unfold referenceLoss
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          obtain ⟨fresh, absent⟩ := Finset.mem_sdiff.mp hk
          refine Finset.mem_filter.mpr ⟨fresh, ?_⟩
          rintro ⟨v, found, key, slashed⟩
          rcases pre.slashed_evidence v (by simpa only [validators] using found) slashed with
            early | evidence
          · exact (Finset.mem_filter.mp fresh).2 (key ▸ early)
          · have all : tail.SlashingEvidence v.pubkey := by
              obtain ⟨u, w, step, inside, evidence⟩ := evidence
              refine ⟨u, w, step, ?_, evidence⟩
              rw [split]
              exact (Run.contains_append _ post step).mpr (.inl (.earlier inside _))
            exact absent (Finset.mem_filter.mpr ⟨fresh, key ▸ included _ all⟩)
        · intros; exact Nat.zero_le _
      cases call with
      | inl c => exact branch left enoughA (fun _ h => .inr (.inl h)) c lower within
      | inr c => exact branch right enoughB (fun _ h => .inr (.inr h)) c lower within
    obtain ⟨recentOne, quorumOne, lossOne⟩ := facts one lowerOne withinOne
    obtain ⟨recentTwo, quorumTwo, lossTwo⟩ := facts two lowerTwo withinTwo
    -- Include overlap outside the reference set; it contributes no reference weight.
    let accountable := bad ∪ (one.voters ∩ two.voters)
    have outsideLoss (c : EitherCall (shared.append left) (shared.append right))
        (bound : (∑ k ∈ unslashedKeys x.state \ bad,
          (effectiveWeight x.state k - Models.supported (recentKeys c.state.state)
            (effectiveWeight c.state.state) k)) ≤ referenceLoss x c.state) :
        (∑ k ∈ unslashedKeys x.state \ accountable,
          (effectiveWeight x.state k - Models.supported (recentKeys c.state.state)
            (effectiveWeight c.state.state) k)) ≤ referenceLoss x c.state := by
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (by intros; omega)) bound
      exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_left
    have same : unslashedKeys x.state ∩ accountable = bad := by
      ext k
      simp only [accountable, bad, Finset.mem_inter, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨fresh, h | h⟩
        · exact h
        · exact ⟨fresh, .inl (overlap k (Finset.mem_inter.mpr h))⟩
      · intro h; exact ⟨h.1, .inl h⟩
    -- Recent keys are unslashed, so the unslashed active keys are recent.
    have inside (y : ForkedBeaconState preset) : unslashedKeys y.state ⊆ recentKeys y.state := by
      intro k member
      obtain ⟨active, fresh⟩ := Finset.mem_filter.mp member
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ active, fresh⟩
    -- A recent key outside the unslashed active keys is outside the active keys.
    have outside (y : ForkedBeaconState preset) :
        Models.stake (effectiveWeight y.state) (recentKeys y.state \ unslashedKeys y.state) ≤
          boundaryStake y := by
      apply Models.stake_mono
      intro k member
      obtain ⟨recent, notUnslashed⟩ := Finset.mem_sdiff.mp member
      exact Finset.mem_sdiff.mpr ⟨recent, fun active =>
        notUnslashed (Finset.mem_filter.mpr ⟨active, (Finset.mem_filter.mp recent).2⟩)⟩
    have bound := Models.stake_le_accountable_add_change (unslashedKeys x.state)
      (unslashedKeys one.state.state) (unslashedKeys two.state.state)
      (recentKeys one.state.state) (recentKeys two.state.state) one.voters two.voters
      accountable (effectiveWeight x.state) (effectiveWeight one.state.state)
      (effectiveWeight two.state.state) (referenceLoss x one.state) (referenceLoss x two.state)
      (referenceGain x one.state) (referenceGain x two.state)
      (boundaryStake one.state) (boundaryStake two.state)
      (inside one.state) (inside two.state) recentOne recentTwo quorumOne quorumTwo
      Finset.subset_union_right (outsideLoss one lossOne) (outsideLoss two lossTwo)
      (Nat.le_refl _) (Nat.le_refl _) (outside one.state) (outside two.state)
    rw [same] at bound
    change _ ≤ 3 * Models.stake (effectiveWeight x.state) bad +
      stateDrift x one.state + stateDrift x two.state
    dsimp only [stateDrift]
    omega

/-- A conflict at a finalized epoch puts `x` no later than the first slot of that epoch.

The other checkpoint has that epoch or a later one. -/
private theorem conflict_starts {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (f j : Checkpoint) (ordered : f.epoch ≤ j.epoch)
    (conflict : Conflict (shared.append left) (shared.append right) f j) :
    x.state.slot.toNat ≤ f.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
  apply shared.slot_le_of_checkpointPath_ne left right
  simpa only [Conflict, UInt64.min_def, ite_eq_left ordered] using conflict

/-- A finalized field of the left run conflicts with a field of the right run at its epoch or later.

The field of the right run is justified or finalized.

Then two quorum calls of the runs have target epochs between the two epochs.

The unslashed active stake at `x` is at most three times the accountable stake at `x`.

The drift at the state of each call is added.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

The runs start at one genesis built from deposits, and the preset meets the parameters.

Each run's active stake exceeds 1.5 increments at epoch calls after epoch 1 through `j.epoch + 1`.
-/
theorem accountable_safety_at_calls {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    (j : Checkpoint)
    (enoughA : EnoughStake (shared.append left) j.epoch.toNat)
    (enoughB : EnoughStake (shared.append right) j.epoch.toNat)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint ∨
      j = b.state.finalizedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict (shared.append left) (shared.append right) a.state.finalizedCheckpoint j) :
    (∃ one two : EitherCall (shared.append left) (shared.append right),
      a.state.finalizedCheckpoint.epoch.toNat ≤ one.targetEpoch ∧ one.targetEpoch ≤ j.epoch.toNat ∧
      a.state.finalizedCheckpoint.epoch.toNat ≤ two.targetEpoch ∧ two.targetEpoch ≤ j.epoch.toNat ∧
      Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) +
        stateDrift x one.state + stateDrift x two.state) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  rcases conflicting_fields_quorums (shared.append left) (shared.append right)
    parameters genesis j field ordered conflict with witnesses | hashes
  · obtain ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, overlap⟩ := witnesses
    exact .inl ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo,
      accountable_pair_bound shared left right parameters genesis
        (conflict_starts shared left right _ j ordered conflict)
        enoughA enoughB one two lowerOne lowerTwo upperOne upperTwo overlap⟩
  · exact .inr hashes

private theorem selected_call_drift_le {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (parameters : Parameters preset) (low high : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail))
    (lower : low ≤ call.target.epoch.toNat) (upper : call.target.epoch.toNat ≤ high) :
    stateDrift x ⟨call.before.fork, call.cached⟩ ≤ derivedDrift high tail := by
  have member := call_after_reference shared tail parameters low starts call lower
  obtain ⟨pre, post, split⟩ := tail.contains_split (.slot call.advanced) member
  let before := call.before
  -- The budget observes the state before caching, whose slot and registry caching preserves.
  obtain ⟨_, _, _, frame, validators, _⟩ := call.toEpochCall.selected_prefix
  have sameEpoch : getCurrentEpoch call.cached = getCurrentEpoch before.state := by
    simp only [getCurrentEpoch, frame.slot, before]
  have epoch : (getCurrentEpoch before.state).toNat ≤ high + 1 := by
    have target := call.currentEpoch_le
    rw [sameEpoch] at target
    omega
  have observed {z : ForkedBeaconState preset} (run : Run config checks x z)
      (bounded : (getCurrentEpoch z.state).toNat ≤ high + 1) :
      stateDrift x z ≤ derivedDrift high run := by
    cases run with
    | nil => exact Nat.le_refl _
    | snoc pre step =>
      simp only [derivedDrift, ite_eq_left bounded]; exact Nat.le_max_right _ _
  have mono {u v : ForkedBeaconState preset} (pre : Run config checks x u)
      (post : Run config checks u v) :
      derivedDrift high pre ≤ derivedDrift high (pre.append post) := by
    induction post with
    | nil => exact Nat.le_refl _
    | snoc post step ih =>
      simp only [Run.append, derivedDrift]
      split
      · exact ih.trans (Nat.le_max_left _ _)
      · exact ih
  have next : derivedDrift high pre ≤ derivedDrift high (pre.snoc (.slot call.advanced)) := by
    simp only [derivedDrift]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _
  have same : stateDrift x ⟨call.before.fork, call.cached⟩ = stateDrift x before := by
    have weight : effectiveWeight call.cached = effectiveWeight before.state := by
      funext k
      simp only [effectiveWeight, validators, before]
    have slashed : SlashedAt call.cached = SlashedAt before.state := by
      funext k
      simp only [SlashedAt, validators, before]
    have keys : keysAt call.cached = keysAt before.state := by
      funext indices
      unfold keysAt
      rw [validators]
    have indices : getActiveValidatorIndices call.cached =
        getActiveValidatorIndices before.state := by
      funext epoch
      unfold getActiveValidatorIndices
      rw [validators]
    have active : activeKeys call.cached = activeKeys before.state := by
      unfold activeKeys
      rw [keys, indices, sameEpoch]
    have recent : recentKeys call.cached = recentKeys before.state := by
      unfold recentKeys getPreviousEpoch
      rw [slashed, active, keys, indices, sameEpoch]
    simp only [stateDrift, referenceLoss, referenceGain, boundaryStake]
    rw [weight, slashed, recent, active]
  rw [same]
  have result := (observed pre epoch).trans (next.trans (mono _ post))
  simpa only [← split] using result

/-- The drift at the state of a call of either run is at most the larger drift of the tails.

The call targets an epoch from `low` to `high`, and `x` is no later than the first slot of `low`. -/
private theorem either_call_drift_le {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (low high : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (c : EitherCall (shared.append left) (shared.append right))
    (lower : low ≤ c.targetEpoch) (upper : c.targetEpoch ≤ high) :
    stateDrift x c.state ≤ max (derivedDrift high left) (derivedDrift high right) := by
  cases c with
  | inl c => exact (selected_call_drift_le shared left parameters low high starts c lower
      upper).trans (Nat.le_max_left _ _)
  | inr c => exact (selected_call_drift_le shared right parameters low high starts c lower
      upper).trans (Nat.le_max_right _ _)

/-- The finalized fields of the two runs conflict.

The left finalized epoch is at most the right one.

The conflict puts `x` no later than the first slot of the earlier finalized epoch.

Then the unslashed active stake at `x` is at most three times the accountable stake at `x`.

Twice the larger drift of the two tails is added.

The drift of a tail is the largest over its states up to one epoch past the right finalized epoch.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

The runs start at one genesis built from deposits, and the preset meets the parameters.

The floor covers epoch calls after epoch 1 through one epoch past the right finalized epoch.

Each run has active stake above 1.5 increments at each covered call. -/
theorem accountable_safety {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    (enoughA : EnoughStake (shared.append left) b.state.finalizedCheckpoint.epoch.toNat)
    (enoughB : EnoughStake (shared.append right) b.state.finalizedCheckpoint.epoch.toNat)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch)
    (conflict : Conflict (shared.append left) (shared.append right)
      a.state.finalizedCheckpoint b.state.finalizedCheckpoint) :
    (Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
      3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) +
        2 * max (derivedDrift b.state.finalizedCheckpoint.epoch.toNat left)
          (derivedDrift b.state.finalizedCheckpoint.epoch.toNat right)) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  rcases accountable_safety_at_calls shared left right parameters genesis
    b.state.finalizedCheckpoint enoughA enoughB (.inr (.inr rfl)) ordered conflict with
    witnesses | hashes
  · obtain ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, bound⟩ := witnesses
    have start := conflict_starts shared left right _ _ ordered conflict
    have first := either_call_drift_le shared left right parameters _ _ start one lowerOne upperOne
    have second := either_call_drift_le shared left right parameters _ _ start two lowerTwo upperTwo
    exact .inl (by omega)
  · exact .inr hashes

/-- A finalized field of the left run conflicts with a justified field of the right run.

The justified field is at the finalized epoch or later.

With that order, the conflict puts `x` no later than the first slot of the finalized epoch.

Then the unslashed active stake at `x` is at most three times the accountable stake at `x`.

Twice the larger drift of the two tails is added.

The drift of a tail is the largest over its states up to one epoch past the justified epoch.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

The runs start at one genesis built from deposits, and the preset meets the parameters.

Each run's active stake exceeds 1.5 increments at epoch calls after epoch 1 through `j.epoch + 1`.
-/
theorem accountable_safety_justified {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    (j : Checkpoint)
    (enoughA : EnoughStake (shared.append left) j.epoch.toNat)
    (enoughB : EnoughStake (shared.append right) j.epoch.toNat)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict (shared.append left) (shared.append right) a.state.finalizedCheckpoint j) :
    (Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
      3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) +
        2 * max (derivedDrift j.epoch.toNat left) (derivedDrift j.epoch.toNat right)) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  rcases accountable_safety_at_calls shared left right parameters genesis
    j enoughA enoughB (field.imp_right Or.inl) ordered conflict with witnesses | hashes
  · obtain ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, bound⟩ := witnesses
    have starts := conflict_starts shared left right _ _ ordered conflict
    have first := either_call_drift_le shared left right parameters _ _ starts one lowerOne
      upperOne
    have second := either_call_drift_le shared left right parameters _ _ starts two lowerTwo
      upperTwo
    exact .inl (by omega)
  · exact .inr hashes

/-- Two justified fields of the runs at one epoch are equal, or they bound the accountable stake.

`x` is no later than the first slot of that epoch.

The unslashed active stake at `x` is then at most three times the accountable stake at `x`.

Twice the larger drift of the two tails is added.

The drift of a tail is the largest over its states up to one epoch past that epoch.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

The runs start at one genesis built from deposits, and the preset meets the parameters.

Each run's active stake exceeds 1.5 increments at epoch calls after epoch 1 through `j.epoch + 1`.
-/
theorem accountable_justified_unique {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b) (parameters : Parameters preset)
    (genesis : Genesis config checks g)
    (j k : Checkpoint)
    (enoughA : EnoughStake (shared.append left) j.epoch.toNat)
    (enoughB : EnoughStake (shared.append right) j.epoch.toNat)
    (fieldA : j = a.state.previousJustifiedCheckpoint ∨ j = a.state.currentJustifiedCheckpoint)
    (fieldB : k = b.state.previousJustifiedCheckpoint ∨ k = b.state.currentJustifiedCheckpoint)
    (epoch : j.epoch = k.epoch)
    (starts : x.state.slot.toNat ≤ j.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    j = k ∨
      Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right) +
        2 * max (derivedDrift j.epoch.toNat left) (derivedDrift j.epoch.toNat right) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  classical
  by_cases same : j = k
  · exact .inl same
  -- A quorum call cannot target genesis, because its current epoch is at least two.
  have positive {z : ForkedBeaconState preset} {run : Run config checks g z}
      (c : Checkpoint) (history : JustificationHistory run c) : 0 < c.epoch.toNat := by
    let call := history.calls.getLast history.nonempty
    have target := history.finish call (List.getLast?_eq_some_getLast history.nonempty)
    have later := UInt64.lt_iff_toNat_lt.mp call.later
    have one := toNat_genesisEpoch_add_one
    rw [one] at later
    rw [← target, call.targetEpoch]
    cases call.current <;> simp only [Bool.false_eq_true, ↓reduceIte,
      getPreviousEpoch_toNat] <;> omega
  rcases justified_fields (shared.append left) genesis j fieldA with initialA | ha
  · rcases justified_fields (shared.append right) genesis k fieldB with initialB | hb
    · exact .inl (initialA.trans initialB.symm)
    · obtain ⟨hb⟩ := hb
      have pos := positive k hb
      have zero : j.epoch.toNat = 0 := by rw [initialA]; rfl
      rw [epoch] at zero
      omega
  · obtain ⟨ha⟩ := ha
    rcases justified_fields (shared.append right) genesis k fieldB with initialB | hb
    · have pos := positive j ha
      have zero : k.epoch.toNat = 0 := by rw [initialB]; rfl
      rw [← epoch] at zero
      omega
    · obtain ⟨hb⟩ := hb
      let one := ha.calls.getLast ha.nonempty
      let two := hb.calls.getLast hb.nonempty
      have targetA := ha.finish one (List.getLast?_eq_some_getLast ha.nonempty)
      have targetB := hb.finish two (List.getLast?_eq_some_getLast hb.nonempty)
      have overlap := same_epoch_histories (shared.append left) (shared.append right)
        parameters genesis one two
        (by rw [targetA, targetB]; exact epoch)
        (by rw [targetA, targetB]; exact same)
      have withinA : one.target.epoch.toNat = j.epoch.toNat := by rw [targetA]
      have withinB : two.target.epoch.toNat = j.epoch.toNat := by rw [targetB, epoch]
      have bound := accountable_pair_bound shared left right parameters genesis starts
        enoughA enoughB (.inl one) (.inr two) withinA.ge withinB.ge withinA.le withinB.le overlap
      have first := either_call_drift_le shared left right parameters j.epoch.toNat
        j.epoch.toNat starts (.inl one) withinA.ge withinA.le
      have second := either_call_drift_le shared left right parameters j.epoch.toNat
        j.epoch.toNat starts (.inr two) withinB.ge withinB.le
      exact .inr (.inl (by omega))

/-- Data that one of the two runs checked in an aggregate that names `key`. -/
def VerifiedEither {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (key : BLSPubkey) (data : AttestationData) : Prop :=
  (∃ c : AttestationCheck left key, c.indexed.data = data) ∨
    ∃ c : AttestationCheck right key, c.indexed.data = data

/-- Two conflicting messages that name `key`, each with a check that one of the runs executed. -/
def VerifiedConflict {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (key : BLSPubkey) : Prop :=
  (∃ d₁ d₂, VerifiedEither left right key d₁ ∧ VerifiedEither left right key d₂ ∧
      isSlashableAttestationData d₁ d₂ = true) ∨
    (∃ c : HeaderCheck left key, ProposerConflict c.slashing) ∨
    ∃ c : HeaderCheck right key, ProposerConflict c.slashing

/-- A slashing that a block of one run applied gives two checks of its own.

They are two checks of attestations that conflict, or two checks of conflicting headers. -/
private theorem checked_of_slashingEvidence {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {key : BLSPubkey} (evidence : run.SlashingEvidence key) :
    (∃ one two : AttestationCheck run key,
      isSlashableAttestationData one.indexed.data two.indexed.data = true) ∨
    ∃ c : HeaderCheck run key, ProposerConflict c.slashing := by
  obtain ⟨x, y, step, member, evidence⟩ := evidence
  cases step with
  | slot _ => exact evidence.elim
  | block engine signed due applied =>
    rcases evidence with ⟨slashing, included, v, found, rfl⟩ |
      ⟨slashing, included, i, named, v, found, rfl⟩
    · obtain ⟨c, same, conflict⟩ := Run.headerCheck_of_proposerSlashing member included found
      exact .inr ⟨c, same ▸ conflict⟩
    · obtain ⟨one, two, first, second, conflict⟩ :=
        Run.attestationChecks_of_attesterSlashing member included named found
      exact .inl ⟨one, two, by rw [first, second]; exact conflict⟩

/-- Every accountable key has two conflicting messages, each checked by one of the runs.

Each check is that of an indexed attestation or of a header, and it accepted.

It holds for any signature checks, so it says which checks accepted, not who signed.

It needs more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem verifiedConflict_of_accountable {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) (key : BLSPubkey)
    (accountable : Accountable shared left right key) :
    VerifiedConflict (shared.append left) (shared.append right) key := by
  -- Evidence in a tail is evidence in the run that the tail ends.
  have lift {z : ForkedBeaconState preset} (tail : Run config checks x z)
      (evidence : tail.SlashingEvidence key) : (shared.append tail).SlashingEvidence key := by
    obtain ⟨u, w, step, member, evidence⟩ := evidence
    exact ⟨u, w, step, (shared.contains_append tail step).mpr (.inr member), evidence⟩
  rcases accountable with ⟨d₁, d₂, first, second, conflict⟩ | evidence | evidence
  · have verified {data : AttestationData}
        (accepted : AcceptedEither (shared.append left) (shared.append right) key data) :
        VerifiedEither (shared.append left) (shared.append right) key data :=
      accepted.imp (Run.attestationCheck_of_accepted lookahead)
        (Run.attestationCheck_of_accepted lookahead)
    exact .inl ⟨d₁, d₂, verified first, verified second, conflict⟩
  · rcases checked_of_slashingEvidence (lift left evidence) with
      ⟨one, two, conflict⟩ | ⟨c, conflict⟩
    · exact .inl ⟨_, _, .inl ⟨one, rfl⟩, .inl ⟨two, rfl⟩, conflict⟩
    · exact .inr (.inl ⟨c, conflict⟩)
  · rcases checked_of_slashingEvidence (lift right evidence) with
      ⟨one, two, conflict⟩ | ⟨c, conflict⟩
    · exact .inl ⟨_, _, .inr ⟨one, rfl⟩, .inr ⟨two, rfl⟩, conflict⟩
    · exact .inr (.inr ⟨c, conflict⟩)

end EthLib.Consensus.DirectSafety
