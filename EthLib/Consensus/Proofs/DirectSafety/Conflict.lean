module

public import EthLib.Consensus.Proofs.DirectSafety.Evidence

/-!
# Conflicting concrete checkpoint fields expose slashable quorum pairs

The induction follows actual calls of the state transition and their checkpoint epochs.

No abstract voting protocol, justification relation or finality relation is an input.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- One of the two runs accepted a vote for `data` by `key`. -/
def AcceptedEither {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (key : BLSPubkey) (data : AttestationData) : Prop :=
  left.Accepted key data ∨ right.Accepted key data

/-- The two runs together accepted two votes by `key` whose data a slashing would punish.

Each vote may come from either run. -/
def Slashable {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (key : BLSPubkey) : Prop :=
  ∃ d₁ d₂, AcceptedEither left right key d₁ ∧ AcceptedEither left right key d₂ ∧
    isSlashableAttestationData d₁ d₂ = true

/-- A key is accountable when the runs accepted two of its votes that a slashing would punish.

It is also accountable when a block of either run applied a slashing that names it.

That slashing may be a proposer slashing, and it may be in a shared prefix of the runs. -/
def Accountable {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (key : BLSPubkey) : Prop :=
  Slashable left right key ∨ left.SlashingEvidence key ∨ right.SlashingEvidence key

/-- A quorum call of either run.

Two such calls may be on the same run. -/
abbrev EitherCall {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) := QuorumCall left ⊕ QuorumCall right

/-- The epoch of the target of the call. -/
def EitherCall.targetEpoch {g a b : ForkedBeaconState preset} {left : Run config checks g a}
    {right : Run config checks g b} (call : EitherCall left right) : Nat :=
  match call with
  | .inl c => c.target.epoch.toNat
  | .inr c => c.target.epoch.toNat

/-- The keys counted by the call. -/
noncomputable def EitherCall.voters {g a b : ForkedBeaconState preset}
    {left : Run config checks g a} {right : Run config checks g b}
    (call : EitherCall left right) : Finset BLSPubkey :=
  match call with
  | .inl c => c.voters
  | .inr c => c.voters

/-- The state at which the call ran its test, after caching the slot. -/
def EitherCall.state {g a b : ForkedBeaconState preset} {left : Run config checks g a}
    {right : Run config checks g b} (call : EitherCall left right) : ForkedBeaconState preset :=
  match call with
  | .inl c => ⟨c.before.fork, c.cached⟩
  | .inr c => ⟨c.before.fork, c.cached⟩

/-- Two quorums with different targets at one epoch make their common voters slashable.

Each common voter has a vote of the runs for each target, so it voted twice in that epoch. -/
private theorem view_same_epoch {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    {va : TerminalView a} {vb : TerminalView b}
    (one : ViewQuorum left va) (two : ViewQuorum right vb)
    (epoch : one.target.epoch = two.target.epoch) (different : one.target ≠ two.target) :
    ∀ key ∈ one.voters ∩ two.voters, Slashable left right key := by
  intro key member
  obtain ⟨inOne, inTwo⟩ := Finset.mem_inter.mp member
  obtain ⟨d₁, accepted₁, _, target₁⟩ :=
    view_quorum_attestations left parameters genesis one key inOne
  obtain ⟨d₂, accepted₂, _, target₂⟩ :=
    view_quorum_attestations right parameters genesis two key inTwo
  refine ⟨d₁, d₂, Or.inl accepted₁, Or.inr accepted₂, ?_⟩
  apply isSlashableAttestationData_of_double
  · intro same
    exact different (target₁.symm.trans ((congrArg AttestationData.target same).trans target₂))
  · rw [target₁, target₂]
    exact epoch

/-- Two quorum calls with different targets at one epoch make their common voters slashable.

Each common voter has a vote of the runs for each target, so it voted twice in that epoch.

The runs start at one genesis built from deposits, and the preset meets the parameters. -/
theorem same_epoch_histories {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (one : QuorumCall left) (two : QuorumCall right)
    (epoch : one.target.epoch = two.target.epoch) (different : one.target ≠ two.target) :
    ∀ key ∈ one.voters ∩ two.voters, Slashable left right key :=
  view_same_epoch left right parameters genesis (va := .realized) (vb := .realized)
    (.inl one) (.inl two) epoch different

private theorem view_surround {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    {va : TerminalView a} {vb : TerminalView b}
    (outer : ViewQuorum left va) (inner : ViewQuorum right vb)
    (source : outer.source.epoch < inner.source.epoch)
    (target : inner.target.epoch < outer.target.epoch) :
    ∀ key ∈ outer.voters ∩ inner.voters, Slashable left right key := by
  intro key member
  obtain ⟨inOuter, inInner⟩ := Finset.mem_inter.mp member
  obtain ⟨d₁, accepted₁, source₁, target₁⟩ :=
    view_quorum_attestations left parameters genesis outer key inOuter
  obtain ⟨d₂, accepted₂, source₂, target₂⟩ :=
    view_quorum_attestations right parameters genesis inner key inInner
  refine ⟨d₁, d₂, Or.inl accepted₁, Or.inr accepted₂, ?_⟩
  apply isSlashableAttestationData_of_surround
  · simpa only [source₁, source₂] using source
  · simpa only [target₁, target₂] using target

private theorem checkpointPath_zero {g a : ForkedBeaconState preset}
    (run : Run config checks g a) : run.checkpointPath 0 = [] := by
  induction run with
  | nil => rfl
  | snoc pre step ih =>
    unfold Run.checkpointPath Run.headers
    rw [List.filter_append, show pre.headers.filter
      (fun h => decide (h.slot.toNat ≤ (0 : Epoch).toNat * preset.SLOTS_PER_EPOCH.toNat)) = []
        from ih]
    cases step with
    | slot ok => rfl
    | block engine signed due ok =>
      -- A block comes after the slot of the latest header, so its slot is not zero.
      have positive : 0 < signed.message.slot.toNat := by
        have later := UInt64.lt_iff_toNat_lt.mp
          (processBlock_parentRoot (applySignedBlock_ok ok).2.1).2.1
        omega
      simp only [Step.headers, blockHeader]
      cases root : (Serialization.Ssz.SszType.hashTreeRoot signed.message.body).toOption <;>
        (simp [Option.toList]; try omega)

/-- A finalized field of the left view conflicts with a right field at its epoch or later.

A view is the last state of a run, or one justification step on it.

The field of the right view is justified or finalized.

Then two quorums, one of each run, have target epochs between the two epochs.

Each quorum is a quorum call of its run, or the test of the step of its view.

The common voters of the two quorums are slashable.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

The runs start at one genesis built from deposits, and the preset meets the parameters. -/
theorem view_conflicting_fields_quorums {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (va : TerminalView a) (vb : TerminalView b) (j : Checkpoint)
    (field : j = vb.state.previousJustifiedCheckpoint ∨ j = vb.state.currentJustifiedCheckpoint ∨
      j = vb.state.finalizedCheckpoint)
    (ordered : va.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict left right va.state.finalizedCheckpoint j) :
    (∃ (one : ViewQuorum left va) (two : ViewQuorum right vb),
      va.state.finalizedCheckpoint.epoch.toNat ≤ one.target.epoch.toNat ∧
      one.target.epoch.toNat ≤ j.epoch.toNat ∧
      va.state.finalizedCheckpoint.epoch.toNat ≤ two.target.epoch.toNat ∧
      two.target.epoch.toNat ≤ j.epoch.toNat ∧
      ∀ key ∈ one.voters ∩ two.voters, Slashable left right key) ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  classical
  let f := va.state.finalizedCheckpoint
  have orderedNat := UInt64.le_iff_toNat_le.mp ordered
  have paths : left.checkpointPath f.epoch ≠ right.checkpointPath f.epoch := by
    simpa only [Conflict, UInt64.min_def, ite_eq_left ordered] using conflict
  have positive : 0 < f.epoch.toNat := by
    by_contra zero
    have epochZero : f.epoch = 0 := UInt64.toNat_inj.mp (by change f.epoch.toNat = 0; omega)
    exact paths (by rw [epochZero, checkpointPath_zero left, checkpointPath_zero right])
  have notGenesis : f ≠ ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ := by
    intro equal
    have zero : f.epoch.toNat = 0 := by rw [equal]; rfl
    omega
  obtain ⟨crossing, below, above, upper⟩ :=
    view_field_crossing right genesis vb j field f.epoch.toNat positive orderedNat
  -- Equal targets bind the selected paths at every earlier checkpoint boundary.
  have pair (one : ViewQuorum left va)
      (epoch : one.target.epoch = crossing.target.epoch)
      (lower : f.epoch.toNat ≤ one.target.epoch.toNat) :
      (∃ (one : ViewQuorum left va) (two : ViewQuorum right vb),
        f.epoch.toNat ≤ one.target.epoch.toNat ∧ one.target.epoch.toNat ≤ j.epoch.toNat ∧
        f.epoch.toNat ≤ two.target.epoch.toNat ∧ two.target.epoch.toNat ≤ j.epoch.toNat ∧
        ∀ key ∈ one.voters ∩ two.voters, Slashable left right key) ∨
        HashEvidence (left.hashObjects ++ right.hashObjects) := by
    by_cases same : one.target = crossing.target
    · rcases view_quorum_target_binding left right parameters genesis one crossing same with
        bound | hash
      · have earlier : f.epoch ≤ one.target.epoch := UInt64.le_iff_toNat_le.mpr lower
        apply False.elim
        apply paths
        rw [left.checkpointPath_restrict f.epoch one.target.epoch earlier,
          right.checkpointPath_restrict f.epoch crossing.target.epoch (epoch ▸ earlier), bound]
      · exact .inr hash
    · exact .inl ⟨one, crossing, lower, by rw [epoch]; exact upper, above, upper,
        view_same_epoch left right parameters genesis one crossing epoch same⟩
  obtain initial | ⟨outgoing, source, distance, ⟨incoming, incomingTarget⟩, middle⟩ :=
    view_finalized_quorums left genesis va
  · exact False.elim (notGenesis initial)
  change outgoing.target.epoch.toNat = f.epoch.toNat + 1 ∨
    outgoing.target.epoch.toNat = f.epoch.toNat + 2 at distance
  change outgoing.target.epoch.toNat = f.epoch.toNat + 2 →
    ∃ incoming : ViewQuorum left va, incoming.target.epoch.toNat = f.epoch.toNat + 1 at middle
  by_cases atFinal : crossing.target.epoch = f.epoch
  · exact pair incoming (by rw [incomingTarget, atFinal]) (by rw [incomingTarget])
  have aboveStrict : f.epoch.toNat < crossing.target.epoch.toNat := by
    have different : crossing.target.epoch.toNat ≠ f.epoch.toNat :=
      fun equal => atFinal (UInt64.toNat_inj.mp equal)
    omega
  by_cases beyond : outgoing.target.epoch.toNat < crossing.target.epoch.toNat
  · have surround := view_surround right left parameters genesis
      crossing outgoing (by rw [source]; exact UInt64.lt_iff_toNat_lt.mpr below)
      (UInt64.lt_iff_toNat_lt.mpr beyond)
    refine .inl ⟨outgoing, crossing, ?_, ?_, above, upper, ?_⟩
    · change f.epoch.toNat ≤ outgoing.target.epoch.toNat
      rcases distance with one | two <;> omega
    · omega
    · intro key member
      obtain ⟨d₁, d₂, accepted₁, accepted₂, slashable⟩ :=
        surround key (by rwa [Finset.inter_comm] at member)
      exact ⟨d₁, d₂, accepted₁.symm, accepted₂.symm, slashable⟩
  by_cases sameEpoch : outgoing.target.epoch = crossing.target.epoch
  · exact pair outgoing sameEpoch (by rw [sameEpoch]; exact above)
  have middleEpoch : crossing.target.epoch.toNat = f.epoch.toNat + 1 := by
    have different : outgoing.target.epoch.toNat ≠ crossing.target.epoch.toNat :=
      fun equal => sameEpoch (UInt64.toNat_inj.mp equal)
    rcases distance with one | two <;> omega
  have gap : outgoing.target.epoch.toNat = f.epoch.toNat + 2 := by
    rcases distance with one | two
    · have same : outgoing.target.epoch = crossing.target.epoch := UInt64.toNat_inj.mp (by omega)
      exact False.elim (sameEpoch same)
    · exact two
  -- A two-epoch outgoing link needs the middle quorum when the crossing stops before its target.
  obtain ⟨between, betweenEpoch⟩ := middle gap
  exact pair between (UInt64.toNat_inj.mp (by rw [betweenEpoch]; omega))
    (by rw [betweenEpoch]; omega)

/-- A finalized field of the left run conflicts with a field of the right run at its epoch or later.

The field of the right run is justified or finalized.

Then two quorum calls of the runs have target epochs between the two epochs.

The common voters of the two calls are slashable.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

The runs start at one genesis built from deposits, and the preset meets the parameters. -/
theorem conflicting_fields_quorums {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (j : Checkpoint)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint ∨
      j = b.state.finalizedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict left right a.state.finalizedCheckpoint j) :
    (∃ one two : EitherCall left right,
      a.state.finalizedCheckpoint.epoch.toNat ≤ one.targetEpoch ∧ one.targetEpoch ≤ j.epoch.toNat ∧
      a.state.finalizedCheckpoint.epoch.toNat ≤ two.targetEpoch ∧ two.targetEpoch ≤ j.epoch.toNat ∧
      ∀ key ∈ one.voters ∩ two.voters, Slashable left right key) ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  rcases view_conflicting_fields_quorums left right parameters genesis .realized .realized j field
      ordered conflict with ⟨one, two, lowerOne, upperOne, lowerTwo, upperTwo, overlap⟩ | hashes
  · obtain ⟨one, rfl⟩ := one.eq_inl_of_realized
    obtain ⟨two, rfl⟩ := two.eq_inl_of_realized
    exact .inl ⟨.inl one, .inr two, lowerOne, upperOne, lowerTwo, upperTwo, overlap⟩
  · exact .inr hashes

end EthLib.Consensus.DirectSafety
