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

It is also accountable when a block of either run applied a slashing that names it. -/
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

/-- The justified checkpoint that a link names as its source is older than its target. -/
private theorem link_source_lt {fork : Fork} {state : BeaconState preset fork}
    (settled : JustifiedSettled state) (separated : JustifiedSeparated state)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch state) (current : Bool) (target : Checkpoint)
    (targetEpoch : target.epoch =
      if current then getCurrentEpoch state else getPreviousEpoch state) :
    (if current then state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint).epoch < target.epoch := by
  have previous := separated later
  rw [targetEpoch]
  cases current
  · exact previous
  · have settledNat := UInt64.le_iff_toNat_le.mp settled
    have laterNat := UInt64.lt_iff_toNat_lt.mp later
    apply UInt64.lt_iff_toNat_lt.mpr
    simp only [getPreviousEpoch_toNat] at settledNat
    have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by decide
    rw [one] at laterNat
    simp only [↓reduceIte]
    omega

private theorem call_epochs {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    (call : QuorumCall run) : call.source.epoch < call.target.epoch := by
  obtain ⟨pre, _, _, frame, _⟩ := call.toEpochCall.selected_prefix
  obtain ⟨holds, _, separated⟩ := run_justified_separated pre genesis
  exact link_source_lt (frame.invariant holds).settled (separated.of_frame frame) call.later
    call.current call.target call.targetEpoch

/-- Two quorum calls with different targets at one epoch make their common voters slashable.

Each common voter has a vote of the runs for each target, so it voted twice in that epoch.

The runs start at one genesis built from deposits, and the preset meets the parameters. -/
theorem same_epoch_histories {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (one : QuorumCall left) (two : QuorumCall right)
    (epoch : one.target.epoch = two.target.epoch) (different : one.target ≠ two.target) :
    ∀ key ∈ one.voters ∩ two.voters, Slashable left right key := by
  intro key member
  obtain ⟨inOne, inTwo⟩ := Finset.mem_inter.mp member
  obtain ⟨d₁, accepted₁, _, target₁⟩ :=
    quorum_attestations left parameters genesis one key inOne
  obtain ⟨d₂, accepted₂, _, target₂⟩ :=
    quorum_attestations right parameters genesis two key inTwo
  refine ⟨d₁, d₂, Or.inl accepted₁, Or.inr accepted₂, ?_⟩
  apply isSlashableAttestationData_of_double
  · intro same
    exact different (target₁.symm.trans ((congrArg AttestationData.target same).trans target₂))
  · rw [target₁, target₂]
    exact epoch

/-- The first call crossing an epoch is chosen from the actual justification history. -/
private theorem history_crossing {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {c : Checkpoint} (history : JustificationHistory run c) (epoch : Nat)
    (positive : 0 < epoch) (reached : epoch ≤ c.epoch.toNat) :
    ∃ call ∈ history.calls,
      call.source.epoch.toNat < epoch ∧ epoch ≤ call.target.epoch.toNat := by
  have crossing (calls : List (QuorumCall run))
      (start : ∀ call, calls.head? = some call → call.source.epoch.toNat < epoch)
      (finish : ∀ call, calls.getLast? = some call → epoch ≤ call.target.epoch.toNat)
      (consecutive : ∀ i one two, calls[i]? = some one → calls[i + 1]? = some two →
        one.target = two.source) (nonempty : calls ≠ []) :
      ∃ call ∈ calls, call.source.epoch.toNat < epoch ∧
        epoch ≤ call.target.epoch.toNat := by
    induction calls with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest ih =>
      by_cases crossed : epoch ≤ first.target.epoch.toNat
      · exact ⟨first, by simp, start first rfl, crossed⟩
      · cases rest with
        | nil => exact False.elim (crossed (finish first rfl))
        | cons second tail =>
          have joined := consecutive 0 first second rfl rfl
          obtain ⟨call, member, bounds⟩ := ih
            (by
              intro call head
              simp only [List.head?_cons, Option.some.injEq] at head
              subst call
              rw [← joined]
              omega)
            (by
              intro call last
              apply finish call
              simpa using last)
            (by
              intro i one two hOne hTwo
              exact consecutive (i + 1) one two hOne hTwo)
            (by simp)
          exact ⟨call, List.mem_cons_of_mem first member, bounds⟩
  refine crossing history.calls ?_ ?_ history.consecutive history.nonempty
  · intro call head
    rw [history.start call head]
    exact positive
  · intro call last
    rw [history.finish call last]
    exact reached

private theorem surround_quorums {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (outer : QuorumCall left) (inner : QuorumCall right)
    (source : outer.source.epoch < inner.source.epoch)
    (target : inner.target.epoch < outer.target.epoch) :
    ∀ key ∈ outer.voters ∩ inner.voters, Slashable left right key := by
  intro key member
  obtain ⟨inOuter, inInner⟩ := Finset.mem_inter.mp member
  obtain ⟨d₁, accepted₁, source₁, target₁⟩ :=
    quorum_attestations left parameters genesis outer key inOuter
  obtain ⟨d₂, accepted₂, source₂, target₂⟩ :=
    quorum_attestations right parameters genesis inner key inInner
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

private theorem history_target_bound {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    {c : Checkpoint} (history : JustificationHistory run c)
    (call : QuorumCall run) (member : call ∈ history.calls) :
    call.target.epoch.toNat ≤ c.epoch.toNat := by
  have bound (calls : List (QuorumCall run))
      (finish : ∀ last, calls.getLast? = some last → last.target = c)
      (consecutive : ∀ i one two, calls[i]? = some one → calls[i + 1]? = some two →
        one.target = two.source) :
      ∀ call ∈ calls, call.target.epoch.toNat ≤ c.epoch.toNat := by
    induction calls with
    | nil => simp
    | cons first rest ih =>
      intro call member
      cases rest with
      | nil =>
        have equal := finish first rfl
        have same := List.mem_singleton.mp member
        subst call
        rw [equal]
      | cons second tail =>
        have tailBound := ih (by intro last found; apply finish last; simpa using found)
          (by intro i one two hOne hTwo; exact consecutive (i + 1) one two hOne hTwo)
        rcases List.mem_cons.mp member with same | member
        · subst call
          have joined := consecutive 0 first second rfl rfl
          have secondBound := tailBound second (by simp)
          have forward := UInt64.lt_iff_toNat_lt.mp (call_epochs run genesis second)
          rw [joined]
          omega
        · exact tailBound call member
  exact bound history.calls history.finish history.consecutive call member

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
  classical
  let f := a.state.finalizedCheckpoint
  have orderedNat := UInt64.le_iff_toNat_le.mp ordered
  have paths : left.checkpointPath f.epoch ≠ right.checkpointPath f.epoch := by
    simpa only [Conflict, UInt64.min_def, ite_eq_left ordered] using conflict
  have positive : 0 < f.epoch.toNat := by
    by_contra zero
    have epochZero : f.epoch = 0 := UInt64.toNat_inj.mp (by change f.epoch.toNat = 0; omega)
    exact paths (by rw [epochZero, checkpointPath_zero left,
      checkpointPath_zero right])
  have notGenesis : f ≠ ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ := by
    intro equal
    have zero : f.epoch.toNat = 0 := by rw [equal]; rfl
    omega
  have jHistory : Nonempty (JustificationHistory right j) := by
    have alternatives : j = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        Nonempty (JustificationHistory right j) := by
      rcases field with previous | current | finalized
      · exact justified_fields right genesis j (.inl previous)
      · exact justified_fields right genesis j (.inr current)
      · subst j
        rcases finalized_field right genesis with initial | ⟨call, _, rule⟩
        · exact .inl initial
        · obtain ⟨_, _, _, history, _⟩ := finalization_rule_quorums right genesis call _ rule
          exact history
    rcases alternatives with equal | history
    · have zero : j.epoch.toNat = 0 := by rw [equal]; rfl
      exact False.elim (by dsimp [f] at positive; omega)
    · exact history
  obtain ⟨history⟩ := jHistory
  obtain ⟨crossing, member, below, above⟩ :=
    history_crossing history f.epoch.toNat positive orderedNat
  have upper := history_target_bound right genesis history crossing member
  -- Equal targets bind the selected paths at every earlier checkpoint boundary.
  have pair (one : QuorumCall left)
      (epoch : one.target.epoch = crossing.target.epoch)
      (lower : f.epoch.toNat ≤ one.target.epoch.toNat) :
      (∃ one two : EitherCall left right,
        f.epoch.toNat ≤ one.targetEpoch ∧ one.targetEpoch ≤ j.epoch.toNat ∧
        f.epoch.toNat ≤ two.targetEpoch ∧ two.targetEpoch ≤ j.epoch.toNat ∧
        ∀ key ∈ one.voters ∩ two.voters, Slashable left right key) ∨
        HashEvidence (left.hashObjects ++ right.hashObjects) := by
    by_cases same : one.target = crossing.target
    · rcases call_target_binding left right parameters genesis one crossing same with bound | hash
      · have earlier : f.epoch ≤ one.target.epoch := UInt64.le_iff_toNat_le.mpr lower
        apply False.elim
        apply paths
        rw [left.checkpointPath_restrict f.epoch one.target.epoch earlier,
          right.checkpointPath_restrict f.epoch crossing.target.epoch (epoch ▸ earlier), bound]
      · exact .inr hash
    · exact .inl ⟨.inl one, .inr crossing, lower,
        by simpa only [EitherCall.targetEpoch, epoch] using upper,
        above, upper, same_epoch_histories left right parameters genesis
          one crossing epoch same⟩
  obtain equal | ⟨finalCall, _, rule⟩ := finalized_field left genesis
  · exact False.elim (notGenesis equal)
  obtain ⟨outgoing, source, distance, fHistory, middle⟩ :=
    finalization_rule_quorums left genesis finalCall f rule
  by_cases atFinal : crossing.target.epoch = f.epoch
  · have existsHistory := fHistory.resolve_left notGenesis
    obtain ⟨fHistory⟩ := existsHistory
    let incoming := fHistory.calls.getLast fHistory.nonempty
    have incomingTarget : incoming.target = f :=
      fHistory.finish incoming (List.getLast?_eq_some_getLast fHistory.nonempty)
    exact pair incoming (by rw [incomingTarget, atFinal]) (by rw [incomingTarget])
  have aboveStrict : f.epoch.toNat < crossing.target.epoch.toNat := by
    have different : crossing.target.epoch.toNat ≠ f.epoch.toNat :=
      fun equal => atFinal (UInt64.toNat_inj.mp equal)
    omega
  by_cases beyond : outgoing.target.epoch.toNat < crossing.target.epoch.toNat
  · have surround := surround_quorums right left parameters genesis
      crossing outgoing (by rw [source]; exact UInt64.lt_iff_toNat_lt.mpr below)
      (UInt64.lt_iff_toNat_lt.mpr beyond)
    refine .inl ⟨.inr crossing, .inl outgoing, above, upper, ?_, ?_, ?_⟩
    · change f.epoch.toNat ≤ outgoing.target.epoch.toNat
      rcases distance with one | two <;> omega
    · change outgoing.target.epoch.toNat ≤ j.epoch.toNat
      omega
    · intro key member
      obtain ⟨d₁, d₂, accepted₁, accepted₂, slashable⟩ := surround key member
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
  -- A two-epoch outgoing link needs the middle history when the crossing stops before its target.
  obtain ⟨mid, midEpoch, ⟨midHistory⟩⟩ := middle gap
  let incoming := midHistory.calls.getLast midHistory.nonempty
  have incomingTarget : incoming.target = mid :=
    midHistory.finish incoming (List.getLast?_eq_some_getLast midHistory.nonempty)
  exact pair incoming (UInt64.toNat_inj.mp (by rw [incomingTarget]; omega))
    (by rw [incomingTarget]; omega)

end EthLib.Consensus.DirectSafety
