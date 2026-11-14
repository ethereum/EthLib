module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
import EthLib.Consensus.Proofs.ForkChoice.Checkpoints

/-!
# Agreement of held block states

Honest stores run the same checks and execution engine from one anchor.

When their held blocks agree at shared roots, the corresponding states agree too.

Agreement is an explicit collision-exclusion hypothesis, not injectivity of hashing.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

section ForkChoice

variable {ν κ : Type*} [DecidableEq ν] {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
  {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
  {J : Set ν}

/-- A held block is initial or has a signed transition witness in the holder's view. -/
theorem Execution.exists_signed_of_blocks
    (e : Execution (forkChoice config checks sources signed sends) J) {u : ν} (_honest : u ∈ J)
    {n : ℕ} {root : Root} {block : BeaconBlock preset fork}
    (found : ((e.world n).state u).blocks[root]? = some block) :
    ((e.start u).blocks[root]? = some block ∧
        ((e.world n).state u).blockStates[root]? = (e.start u).blockStates[root]?) ∨
      ∃ signedBlock : SignedBeaconBlock preset fork, ∃ pre state,
        .block signedBlock ∈ (e.world n).view u ∧ signedBlock.message = block ∧
        SszType.hashTreeRoot signedBlock.message = .ok root ∧
        ((e.world n).state u).blockStates[block.parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre signedBlock true = .ok state ∧
        ((e.world n).state u).blockStates[root]? = some state := by
  let P (view : Set (Message preset fork)) (s : Store preset fork) : Prop :=
    ∀ r b, s.blocks[r]? = some b →
      ((e.start u).blocks[r]? = some b ∧ s.blockStates[r]? = (e.start u).blockStates[r]?) ∨
      ∃ sb pre post parent, .block sb ∈ view ∧ sb.message = b ∧
        SszType.hashTreeRoot sb.message = .ok r ∧
        s.blocks[b.parentRoot]? = some parent ∧ s.blockStates[b.parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre sb true = .ok post ∧
        s.blockStates[r]? = some post
  have maps {v v' : Set (Message preset fork)} {s t : Store preset fork}
      (h : P v s) (incl : v ⊆ v') (blocks : t.blocks = s.blocks)
      (states : t.blockStates = s.blockStates) : P v' t := by
    intro r b found
    rw [blocks] at found
    rcases h r b found with old | ⟨sb, pre, post, parent, mem, rest⟩
    · exact .inl ⟨old.1, states ▸ old.2⟩
    · exact .inr ⟨sb, pre, post, parent, incl mem, rest.1, rest.2.1,
        blocks ▸ rest.2.2.1, states ▸ rest.2.2.2.1, rest.2.2.2.2.1,
        states ▸ rest.2.2.2.2.2⟩
  have step {v : Set (Message preset fork)} {s t : Store preset fork}
      {sb : SignedBeaconBlock preset fork} (h : P v s) (mem : .block sb ∈ v)
      (added : s.onBlock config checks sources sb = .ok t) : P v t := by
    rcases Store.onBlock_same_or_insert added with
      same | ⟨r, hashed, fresh, blocks, pre, post, preFound, transition, states⟩
    · exact same ▸ h
    have parentKnown : ∃ parent, s.blocks[sb.message.parentRoot]? = some parent := by
      have checked := (Store.onBlock_checks hashed (by
        simp [Std.TreeMap.contains_eq_isSome_getElem?, fresh]) added).2.2
      unfold Store.getCheckpointBlock at checked
      simp only [bind_ok_iff] at checked
      obtain ⟨slot, _, ancestor, walked, _⟩ := checked
      cases known : s.blocks[sb.message.parentRoot]? with
      | none =>
        rw [Store.getAncestor] at walked
        dsimp only at walked
        rw [known] at walked
        simp [throw, throwThe, MonadExceptOf.throw] at walked
      | some parent => exact ⟨parent, rfl⟩
    obtain ⟨parent, parentFound⟩ := parentKnown
    have different : r ≠ sb.message.parentRoot := by
      intro same
      rw [← same, fresh] at parentFound
      cases parentFound
    intro q b found
    rw [blocks, getElem?_insert_root] at found
    by_cases same : r = q
    · subst q
      simp only [↓reduceIte, Option.some.injEq] at found
      subst b
      refine .inr ⟨sb, pre, post, parent, mem, rfl, hashed, ?_, ?_, transition, ?_⟩
      · simpa [blocks, getElem?_insert_root, different] using parentFound
      · simpa [states, getElem?_insert_root, different] using preFound
      · simp [states]
    · simp only [same, ↓reduceIte] at found
      rcases h q b found with old | ⟨sb', pre', post', parent', mem', msg, hash,
        parentFound', preFound', transition', postFound'⟩
      · exact .inl ⟨old.1, by simpa [states, getElem?_insert_root, same] using old.2⟩
      · have different' : r ≠ b.parentRoot := by
          intro eq
          rw [← eq, fresh] at parentFound'
          cases parentFound'
        refine .inr ⟨sb', pre', post', parent', mem', msg, hash, ?_, ?_, transition', ?_⟩
        · simpa [blocks, getElem?_insert_root, different'] using parentFound'
        · simpa [states, getElem?_insert_root, different'] using preFound'
        · simpa [states, getElem?_insert_root, same] using postFound'
  have holds : ∀ i, P ((e.world i).view u) ((e.world i).state u) := by
    intro i
    induction i with
    | zero => exact fun _ _ known => .inl ⟨known, rfl⟩
    | succ i ih =>
      have incl := e.monotone_view u (Nat.le_succ i)
      rcases e.state_succ i u with same | ⟨_, moved⟩
      · exact maps ih incl (congrArg Store.blocks same) (congrArg Store.blockStates same)
      have ih' := maps ih incl rfl rfl
      cases moved with
      | tick _ _ ticked =>
        exact maps ih' (fun _ h => h) (Store.onTick_frame ticked).2.2.1
          (Store.onTick_frame ticked).2.2.2
      | block mem added =>
        exact Store.onBlockWithVotes_preserves (fun h added => step h (incl mem) added)
          (fun _ h a => maps h (fun _ h => h) (Store.onAttestation_frame a).2.1
            (Store.onAttestation_frame a).2.2.1)
          (fun _ h a => maps h (fun _ h => h) (Store.onAttesterSlashing_frame a).2.1
            (Store.onAttesterSlashing_frame a).2.2.1) ih' added
      | attestation _ a =>
        exact maps ih' (fun _ h => h) (Store.onAttestation_frame a).2.1
          (Store.onAttestation_frame a).2.2.1
      | attesterSlashing _ a =>
        exact maps ih' (fun _ h => h) (Store.onAttesterSlashing_frame a).2.1
          (Store.onAttesterSlashing_frame a).2.2.1
      | payloadAttestation _ a =>
        exact maps ih' (fun _ h => h) (Store.onPayloadAttestationMessage_onlyPtcVotes a).frame.2.1
          (Store.onPayloadAttestationMessage_onlyPtcVotes a).frame.2.2
      | envelope _ a =>
        exact maps ih' (fun _ h => h) (Store.onExecutionPayloadEnvelope_frame a).2.1
          (Store.onExecutionPayloadEnvelope_frame a).2.2
      | inclusionList _ a =>
        exact maps ih' (fun _ h => h) (Store.onInclusionList_frame a).2.1
          (Store.onInclusionList_frame a).2.2
  rcases holds n root block found with old | ⟨sb, pre, post, _, mem, msg, hash, _, rest⟩
  · exact .inl old
  · exact .inr ⟨sb, pre, post, mem, msg, hash, rest⟩

/-- Stores from one anchor agree on states wherever their blocks agree. -/
theorem Execution.blockStates_eq (e : Execution (forkChoice config checks sources signed sends) J)
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {u w : ν} (first : u ∈ J) (second : w ∈ J) (startFirst : e.start u = anchor)
    (startSecond : e.start w = anchor) {n k : ℕ}
    (sameBlocks : ∀ (root : Root) left right, ((e.world n).state u).blocks[root]? = some left →
      ((e.world k).state w).blocks[root]? = some right → left = right)
    {root : Root} {left right : BeaconState preset fork}
    (leftFound : ((e.world n).state u).blockStates[root]? = some left)
    (rightFound : ((e.world k).state w).blockStates[root]? = some right) :
    left = right := by
  have reachable {v : ν} (start : e.start v = anchor) (i : ℕ) :
      Store.Reachable config anchorState anchorBlock ((e.world i).state v) := by
    induction i with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start v)
      rw [start]
      exact .anchor anchored
    | succ i ih =>
      rcases e.state_succ i v with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.reachable ih
  have keep {v : ν} {r : Root} {b : BeaconBlock preset fork}
      (known : (e.start v).blocks[r]? = some b) (i : ℕ) :
      ((e.world i).state v).blockStates[r]? = (e.start v).blockStates[r]? := by
    have blockStep {s t : Store preset fork} {sb : SignedBeaconBlock preset fork}
        (h : s.blocks[r]? = some b ∧ s.blockStates[r]? = (e.start v).blockStates[r]?)
        (added : s.onBlock config checks sources sb = .ok t) :
        t.blocks[r]? = some b ∧ t.blockStates[r]? = (e.start v).blockStates[r]? := by
      refine ⟨Store.onBlock_blocks_of_found added h.1, ?_⟩
      rcases Store.onBlock_same_or_insert added with
        same | ⟨q, _, fresh, _, _, _, _, _, states⟩
      · exact same ▸ h.2
      have different : q ≠ r := by
        intro eq
        rw [eq, h.1] at fresh
        cases fresh
      simpa [states, getElem?_insert_root, different] using h.2
    have maps {s t : Store preset fork}
        (h : s.blocks[r]? = some b ∧ s.blockStates[r]? = (e.start v).blockStates[r]?)
        (blocks : t.blocks = s.blocks) (states : t.blockStates = s.blockStates) :
        t.blocks[r]? = some b ∧ t.blockStates[r]? = (e.start v).blockStates[r]? :=
      ⟨blocks ▸ h.1, states ▸ h.2⟩
    suffices h : ((e.world i).state v).blocks[r]? = some b ∧
        ((e.world i).state v).blockStates[r]? = (e.start v).blockStates[r]? from h.2
    induction i with
    | zero => exact ⟨known, rfl⟩
    | succ i ih =>
      rcases e.state_succ i v with same | ⟨_, moved⟩
      · exact same ▸ ih
      cases moved with
      | tick _ _ a => exact maps ih (Store.onTick_frame a).2.2.1 (Store.onTick_frame a).2.2.2
      | block _ a =>
        exact Store.onBlockWithVotes_preserves blockStep
          (fun _ h a => maps h (Store.onAttestation_frame a).2.1
            (Store.onAttestation_frame a).2.2.1)
          (fun _ h a => maps h (Store.onAttesterSlashing_frame a).2.1
            (Store.onAttesterSlashing_frame a).2.2.1) ih a
      | attestation _ a =>
        exact maps ih (Store.onAttestation_frame a).2.1 (Store.onAttestation_frame a).2.2.1
      | attesterSlashing _ a =>
        exact maps ih (Store.onAttesterSlashing_frame a).2.1
          (Store.onAttesterSlashing_frame a).2.2.1
      | payloadAttestation _ a =>
        exact maps ih (Store.onPayloadAttestationMessage_onlyPtcVotes a).frame.2.1
          (Store.onPayloadAttestationMessage_onlyPtcVotes a).frame.2.2
      | envelope _ a =>
        exact maps ih (Store.onExecutionPayloadEnvelope_frame a).2.1
          (Store.onExecutionPayloadEnvelope_frame a).2.2
      | inclusionList _ a =>
        exact maps ih (Store.onInclusionList_frame a).2.1 (Store.onInclusionList_frame a).2.2
  generalize bound : left.slot.toNat = height
  induction height using Nat.strong_induction_on generalizing root left right with
  | h height ih =>
    obtain ⟨lb, lbFound⟩ := (reachable startFirst n).known_of_blockState leftFound
    obtain ⟨rb, rbFound⟩ := (reachable startSecond k).known_of_blockState rightFound
    have message := sameBlocks root lb rb lbFound rbFound
    subst rb
    cases initial : anchor.blocks[root]? with
    | some b =>
      have leftKept := keep (v := u) (startFirst.symm ▸ initial) n
      have rightKept := keep (v := w) (startSecond.symm ▸ initial) k
      rw [startFirst] at leftKept
      rw [startSecond] at rightKept
      exact Option.some.inj (leftFound.symm.trans (leftKept.trans
        (rightKept.symm.trans rightFound)))
    | none =>
      rcases e.exists_signed_of_blocks first lbFound with old | lnew
      · rw [startFirst, initial] at old
        cases old.1
      rcases e.exists_signed_of_blocks second rbFound with old | rnew
      · rw [startSecond, initial] at old
        cases old.1
      obtain ⟨lsb, lp, ls, _, lmsg, _, lpFound, lt, lsFound⟩ := lnew
      obtain ⟨rsb, rp, rs, _, rmsg, _, rpFound, rt, rsFound⟩ := rnew
      have leq := Option.some.inj (lsFound.symm.trans leftFound)
      have req := Option.some.inj (rsFound.symm.trans rightFound)
      subst ls
      subst rs
      obtain ⟨earlier, atSlot⟩ := stateTransition_slot lt
      have lower : lp.slot.toNat < height := by
        rw [← bound, atSlot]
        exact UInt64.lt_iff_toNat_lt.mp earlier
      have parents := ih lp.slot.toNat lower lpFound rpFound rfl
      obtain ⟨la, lslots, _, _, lprocess, _⟩ := stateTransition_ok lt
      obtain ⟨ra, rslots, _, _, rprocess, _⟩ := stateTransition_ok rt
      rw [parents, lmsg] at lslots
      rw [rmsg] at rslots
      have advanced := Except.ok.inj (lslots.symm.trans rslots)
      rw [advanced, lmsg] at lprocess
      rw [rmsg] at rprocess
      exact Except.ok.inj (lprocess.symm.trans rprocess)

end ForkChoice

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Honest stores agree on blocks at shared roots up to the given time.

This excludes collisions among held blocks without assuming hash injectivity. -/
def OneBlockPerRoot
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (last : ℕ) : Prop :=
  ∀ v ∈ J, ∀ u ∈ J, ∀ n k, (e.world n).time ≤ last → (e.world k).time ≤ last →
    ∀ (root : Root) left right,
    ((e.world n).state v).blocks[root]? = some left →
    ((e.world k).state u).blocks[root]? = some right → left = right

/-- Validated delayed blocks pass the receiver's remaining handler checks.

Synchrony supplies view membership, not success of carried votes inside onBlockWithVotes. -/
def BlocksAdmitted
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (GST Δ last : ℕ) : Prop :=
  ∀ v ∈ J, ∀ u ∈ J, ∀ n k, (e.world k).time ≤ last → ∀ signedBlock blockRoot state,
    .block signedBlock ∈ (e.world n).view v →
    ((e.world n).state v).blocks[blockRoot]? = some signedBlock.message →
    max (e.world n).time GST + Δ ≤ (e.world k).time →
    UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u) →
    SszType.hashTreeRoot signedBlock.message = .ok blockRoot →
    ((e.world k).state u).validateOnBlock config checks sources signedBlock blockRoot =
      .ok state →
    ∃ after, ((e.world k).state u).onBlockWithVotes config checks sources signedBlock = .ok after

/-- A cached target state has a lookahead origin with the execution's fixed checks. -/
theorem Execution.checkpointStates_fixedChecks {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {u : ValidatorIndex} (honest : u ∈ J) {n : ℕ}
    {target : Checkpoint} {state : BeaconState preset fork}
    (found : ((e.world n).state u).checkpointStates[target]? = some state) :
    ∃ base slot, ((e.world n).state u).blockStates[target.root]? = some base ∧
      computeStartSlotAtEpoch preset target.epoch = .ok slot ∧
      lookaheadState config checks base slot = .ok state := by
  have forward := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) n u honest
  obtain ⟨base, slot, stored, boundary, cases⟩ := forward.checkpointStatesFromBlocks found
  refine ⟨base, slot, stored, boundary, ?_⟩
  rcases cases with ⟨le, rfl⟩ | ⟨lt, used, rfl, computed⟩
  · simp [lookaheadState, UInt64.not_lt.mpr le, pure, Except.pure]
  · simp only [lookaheadState, lt, ↓reduceIte]
    exact mapError_ok_iff.mpr computed

/-- Newly cached target states have the same fixed-check origin as existing entries. -/
theorem Execution.targetState_fixedChecks {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
    {target : Checkpoint} {withTarget : Store preset fork} {state : BeaconState preset fork}
    (stored : ((e.world k).state w).storeTargetCheckpointState config checks target =
      .ok withTarget)
    (read : withTarget.checkpointState target = .ok state) :
    ∃ base slot, ((e.world k).state w).blockStates[target.root]? = some base ∧
      computeStartSlotAtEpoch preset target.epoch = .ok slot ∧
      lookaheadState config checks base slot = .ok state := by
  unfold Store.storeTargetCheckpointState at stored
  split at stored
  · simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst withTarget
    exact e.checkpointStates_fixedChecks anchored start honest
      (Store.checkpointState_ok_iff.mp read)
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at stored
    obtain ⟨computed, computedOk, rfl⟩ := stored
    have eq : computed = state := by simpa using Store.checkpointState_ok_iff.mp read
    subst computed
    unfold Store.computeCheckpointState at computedOk
    simp only [bind_ok_iff] at computedOk
    obtain ⟨base, held, slot, boundary, computedOk⟩ := computedOk
    exact ⟨base, slot, Store.blockState_ok_iff.mp held, mapError_ok_iff.mp boundary,
      by simpa only [lookaheadState] using computedOk⟩

/-- Two honest stores agree on a target state they read after caching. -/
theorem Execution.targetStates_eq_of_oneBlock {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ} (oneBlock : OneBlockPerRoot e last)
    {u w : ValidatorIndex} (first : u ∈ J) (second : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {target : Checkpoint} {leftStore rightStore : Store preset fork}
    {left right : BeaconState preset fork}
    (leftStored : ((e.world n).state u).storeTargetCheckpointState config checks target =
      .ok leftStore)
    (leftRead : leftStore.checkpointState target = .ok left)
    (rightStored : ((e.world k).state w).storeTargetCheckpointState config checks target =
      .ok rightStore)
    (rightRead : rightStore.checkpointState target = .ok right) : left = right := by
  obtain ⟨leftBase, leftSlot, leftFound, leftSlotOk, leftRun⟩ :=
    e.targetState_fixedChecks anchored start first leftStored leftRead
  obtain ⟨rightBase, rightSlot, rightFound, rightSlotOk, rightRun⟩ :=
    e.targetState_fixedChecks anchored start second rightStored rightRead
  have baseEq := e.blockStates_eq anchored first second (start u first) (start w second)
    (oneBlock u first w second n k nBound kBound) leftFound rightFound
  have slotEq := Except.ok.inj (leftSlotOk.symm.trans rightSlotOk)
  subst rightBase
  subst rightSlot
  exact Except.ok.inj (leftRun.symm.trans rightRun)

/-- Before Gloas, synchrony and compatible finality deliver a held block to an honest receiver.

Admission uses the separate handler-success hypothesis, not synchrony alone. -/
theorem Execution.blocks_of_partiallySynchronous {GST Δ last : ℕ}
    (sync : e.PartiallySynchronous GST Δ) (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e last) (admitted : BlocksAdmitted e GST Δ last)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {v u : ValidatorIndex} (honest : v ∈ J)
    (receiver : u ∈ J) {n k : ℕ}
    (late : max (e.world n).time GST + Δ ≤ (e.world k).time) (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    (finalizedKnown : ∃ finalizedBlock,
      ((e.world k).state u).blocks[((e.world k).state u).finalizedCheckpoint.root]? =
        some finalizedBlock)
    {root : Root} {block : BeaconBlock preset fork}
    (found : ((e.world n).state v).blocks[root]? = some block)
    (final : ((e.world n).state v).getCheckpointBlock root
      ((e.world k).state u).finalizedCheckpoint.epoch =
        .ok ((e.world k).state u).finalizedCheckpoint.root) :
    ((e.world k).state u).blocks[root]? = some block ∧
      ∀ epoch checkpointRoot,
        ((e.world k).state u).finalizedCheckpoint.epoch ≤ epoch →
        ((e.world n).state v).getCheckpointBlock root epoch = .ok checkpointRoot →
        ((e.world k).state u).getCheckpointBlock root epoch = .ok checkpointRoot := by
  have reached (w : ValidatorIndex) (h : w ∈ J) (i : ℕ) :=
    e.reachable (fun w hw => (start w hw).symm ▸ Store.Reachable.anchor anchored) i w h
  have ordered : n ≤ k := by
    by_contra! before
    have time := e.monotone_time (Nat.le_of_lt before)
    change (e.world k).time ≤ (e.world n).time at time
    have positive := sync.1
    omega
  have nBound : (e.world n).time ≤ last := by omega
  unfold Store.getCheckpointBlock at final
  simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at final
  obtain ⟨finalSlot, finalStart, ancestor, walk, ancestorRoot⟩ := final
  have base : ∃ b, ((e.world k).state u).blocks[ancestor.root]? = some b := by
    rw [ancestorRoot]
    exact finalizedKnown
  have admission (r : Root) (b p : BeaconBlock preset fork)
      (bf : ((e.world n).state v).blocks[r]? = some b)
      (pf : ((e.world n).state v).blocks[b.parentRoot]? = some p)
      (above : finalSlot < b.slot) (_lower : p.slot < b.slot)
      (pk : ((e.world k).state u).blocks[b.parentRoot]? = some p)
      (parentWalk : ((e.world k).state u).getAncestor
        ⟨b.parentRoot, Store.parentPayloadStatus b p⟩ finalSlot = .ok ancestor) :
      ((e.world k).state u).blocks[r]? = some b := by
    rcases e.exists_validated_of_blocks bf with old | ⟨i, before, sb, post, mem, msg, hash, valid⟩
    · have initial : ((e.world 0).state u).blocks[r]? = some b := by
        change (e.start u).blocks[r]? = some b
        rw [start u receiver, ← start v honest]
        exact old
      exact e.blocks_of_le (Nat.zero_le k) initial
    have memN := e.monotone_view v (Nat.le_of_lt before) mem
    have iBound : (e.world i).time ≤ last := by
      have := e.monotone_time (Nat.le_of_lt before)
      dsimp at this
      omega
    have memK := sync.2.2 n k ordered v honest u receiver (.block sb) memN late
    obtain ⟨pre, preFound, _, _, _⟩ := Store.validateOnBlock_ok valid
    obtain ⟨other, otherFound, _⟩ := (reached u receiver k).blockStatesFromParents pk
    have states : pre = other := e.blockStates_eq anchored honest receiver
      (start v honest) (start u receiver)
      (oneBlock v honest u receiver i k iBound bounded)
      preFound (msg ▸ otherFound)
    have otherPre : ((e.world k).state u).blockStates[sb.message.parentRoot]? = some pre := by
      rw [states, msg]
      exact otherFound
    have parentCheck : ((e.world k).state u).validateParentPayload sb.message = .ok () :=
      Store.validateParentPayload_of_lt preGloas
    have ci := e.clock_bounds v i
    have ck := e.clock_bounds u k
    rw [start v honest] at ci
    rw [start u receiver] at ck
    have time := e.monotone_time (Nat.le_of_lt before)
    change (e.world i).time ≤ (e.world n).time at time
    have tick := upToDate.1
    have initialLe := UInt64.le_iff_toNat_le.mp ck.2.1
    have clockLe : ((e.world i).state v).timeMs ≤ ((e.world k).state u).timeMs :=
      UInt64.le_iff_toNat_le.mpr (by omega)
    obtain ⟨current, currentOk, notFuture⟩ := (Store.validateOnBlock_checks valid).1
    have atTime := mapError_ok_iff.mp currentOk
    rw [ci.1] at atTime
    obtain ⟨next, nextOk, increasing⟩ := exists_computeSlotAtTimeMs_of_le clockLe atTime
    have nextSlot : ((e.world k).state u).getCurrentSlot config = .ok next := by
      unfold Store.getCurrentSlot
      rw [ck.1, nextOk]
      rfl
    have parentCheckpoint : ((e.world k).state u).getCheckpointBlock sb.message.parentRoot
        ((e.world k).state u).finalizedCheckpoint.epoch =
          .ok ((e.world k).state u).finalizedCheckpoint.root := by
      have rootWalk := Store.getAncestor_root (store := (e.world k).state u)
        ⟨b.parentRoot, Store.parentPayloadStatus b p⟩ .pending finalSlot
      rw [parentWalk] at rootWalk
      unfold Store.getCheckpointBlock
      rw [msg, finalStart]
      simpa [bind, Except.bind, pure, Except.pure, Except.mapError, Functor.map, Except.map,
        ancestorRoot] using rootWalk.symm
    have validated := Store.validateOnBlock_of_parent_state valid preFound otherPre parentCheck
      nextSlot (UInt64.le_trans notFuture increasing) finalStart (msg ▸ above) parentCheckpoint
    obtain ⟨after, added⟩ := admitted v honest u receiver n k bounded sb r post memN
      (msg ▸ bf) late upToDate hash validated
    have fixed := upToDate.2 after (.block memK added)
    have inserted : after.blocks[r]? = some sb.message := by
      unfold Store.onBlockWithVotes at added
      simp only [bind_ok_iff, ← Array.foldlM_toList] at added
      obtain ⟨blocked, blockedOk, voted, attested, slashed⟩ := added
      have bKnown : blocked.blocks[r]? = some sb.message := by
        by_cases known : ((e.world k).state u).blocks.contains r
        · have same := Store.onBlock_known (config := config) (checks := checks)
            (sources := sources) hash known
          rw [same] at blockedOk
          cases blockedOk
          obtain ⟨existing, existingFound⟩ := Option.isSome_iff_exists.mp
            (by rwa [Std.TreeMap.contains_eq_isSome_getElem?] at known)
          have eq := oneBlock v honest u receiver n k nBound bounded r b existing bf existingFound
          simpa [msg, eq] using existingFound
        · exact (Store.onBlock_new hash known blockedOk).2.1
      have votes := foldlM_ok_invariant (fun s => s.blocks[r]? = some sb.message)
        (fun _ _ _ h ok => (Store.onAttestation_frame ok).2.1 ▸ h) bKnown attested
      exact foldlM_ok_invariant (fun s => s.blocks[r]? = some sb.message)
        (fun _ _ _ h ok => (Store.onAttesterSlashing_frame ok).2.1 ▸ h) votes slashed
    simpa [fixed, msg] using inserted
  obtain ⟨⟨b, bf, bk⟩, agree⟩ := Store.getAncestor_of_admission
    (oneBlock v honest u receiver n k nBound bounded) base admission walk
  have eq := Option.some.inj (found.symm.trans bf)
  subst b
  refine ⟨bk, ?_⟩
  intro epoch checkpointRoot higher success
  unfold Store.getCheckpointBlock at success ⊢
  simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at success ⊢
  obtain ⟨target, targetOk, node, nodeOk, rootOk⟩ := success
  have slotLe : finalSlot ≤ target := by
    have f := (Uint64.mulChecked_ok_iff.mp finalStart).2
    have t := (Uint64.mulChecked_ok_iff.mp targetOk).2
    apply UInt64.le_iff_toNat_le.mpr
    rw [f, t]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp higher)
  exact ⟨target, targetOk, node, (agree target slotLe).trans nodeOk, rootOk⟩

end EthLib.Consensus.Models.Network
