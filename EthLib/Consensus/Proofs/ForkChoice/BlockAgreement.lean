module

public import EthLib.Consensus.Proofs.ForkChoiceNetworkModel
public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.SharedAncestry
import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
import EthLib.Consensus.Proofs.ForkChoice.StoreEntries

/-!
# Agreement of held block states

Honest stores run the same checks and execution engine from one anchor.

When their held blocks agree at shared roots, the corresponding states agree too.

The shared store dichotomy supplies agreement or names a collision, without hash injectivity.

From Gloas, synchrony also delivers each verified payload, through the envelope that verified it.
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
    (e : Execution (forkChoice config checks sources signed sends) J) {u : ν}
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
        exact step ih' (incl mem) added
      | blockAttestation _ _ _ _ a =>
        exact maps ih' (fun _ h => h) (Store.onAttestation_frame a).2.1
          (Store.onAttestation_frame a).2.2.1
      | blockAttesterSlashing _ _ _ _ a =>
        exact maps ih' (fun _ h => h) (Store.onAttesterSlashing_frame a).2.1
          (Store.onAttesterSlashing_frame a).2.2.1
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
    {u w : ν} (startFirst : e.start u = anchor)
    (startSecond : e.start w = anchor) {n k : ℕ}
    (sameBlocks : ∀ (root : Root) left right, ((e.world n).state u).blocks[root]? = some left →
      ((e.world k).state w).blocks[root]? = some right → left = right)
    {root : Root} {left right : BeaconState preset fork}
    (leftFound : ((e.world n).state u).blockStates[root]? = some left)
    (rightFound : ((e.world k).state w).blockStates[root]? = some right) :
    left = right := by
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
      | block _ a => exact blockStep ih a
      | blockAttestation _ _ _ _ a =>
        exact maps ih (Store.onAttestation_frame a).2.1 (Store.onAttestation_frame a).2.2.1
      | blockAttesterSlashing _ _ _ _ a =>
        exact maps ih (Store.onAttesterSlashing_frame a).2.1
          (Store.onAttesterSlashing_frame a).2.2.1
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
  | ind height ih =>
    obtain ⟨lb, lbFound⟩ :=
      (e.reachable_of_start (startFirst ▸ Store.Reachable.anchor anchored) n).known_of_blockState
        leftFound
    obtain ⟨rb, rbFound⟩ :=
      (e.reachable_of_start (startSecond ▸ Store.Reachable.anchor anchored) k).known_of_blockState
        rightFound
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
      rcases e.exists_signed_of_blocks lbFound with old | lnew
      · rw [startFirst, initial] at old
        cases old.1
      rcases e.exists_signed_of_blocks rbFound with old | rnew
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

/-- From Gloas, a verified payload was verified at the start, or came from an accepted envelope.

The envelope was in the holder's view, and the handler accepted it at an earlier event. -/
private theorem Execution.exists_envelope_of_verified
    (e : Execution (forkChoice config checks sources signed sends) J)
    (gloas : .glamsterdam ≤ fork) {v : ν} {n : ℕ} {root : Root}
    (verified : ((e.world n).state v).isPayloadVerified gloas root = true) :
    (e.start v).isPayloadVerified gloas root = true ∨
      ∃ i, i < n ∧ ∃ envelope : SignedExecutionPayloadEnvelope preset fork, ∃ after,
        .envelope gloas envelope ∈ (e.world i).view v ∧
        envelope.message.beaconBlockRoot = root ∧
        ((e.world i).state v).onExecutionPayloadEnvelope config checks sources gloas envelope =
          .ok after := by
  induction n with
  | zero => exact .inl verified
  | succ n ih =>
    by_cases held : ((e.world n).state v).isPayloadVerified gloas root = true
    · rcases ih held with old | ⟨i, lt, rest⟩
      · exact .inl old
      · exact .inr ⟨i, Nat.lt_succ_of_lt lt, rest⟩
    -- A step that keeps the payloads cannot verify a new one.
    have kept {s t : Store preset fork} (same : t.payloads gloas = s.payloads gloas)
        (old : s = (e.world n).state v) (new : t = (e.world (n + 1)).state v) : False := by
      subst s t
      apply held
      unfold Store.isPayloadVerified at verified ⊢
      rw [← same]
      exact verified
    rcases e.state_succ n v with same | ⟨_, moved⟩
    · exact absurd (same ▸ verified) held
    cases moved with
    | tick _ _ h => exact (kept (Store.onTick_payloads h gloas) rfl rfl).elim
    | block _ h => exact (kept (Store.onBlock_payloads h gloas) rfl rfl).elim
    | blockAttestation _ _ _ _ h => exact (kept (Store.onAttestation_payloads h gloas) rfl rfl).elim
    | blockAttesterSlashing _ _ _ _ h =>
      exact (kept (Store.onAttesterSlashing_payloads h gloas) rfl rfl).elim
    | attestation _ h => exact (kept (Store.onAttestation_payloads h gloas) rfl rfl).elim
    | attesterSlashing _ h => exact (kept (Store.onAttesterSlashing_payloads h gloas) rfl rfl).elim
    | payloadAttestation _ h =>
      obtain ⟨_, _, same⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes h
      exact (kept (by rw [same]) rfl rfl).elim
    | @inclusionList heze _ _ h =>
      obtain ⟨_, _, same⟩ := Store.onInclusionList_ok heze h
      exact (kept (by rw [same]) rfl rfl).elim
    | @envelope _ envelope mem h =>
      by_cases same : envelope.message.beaconBlockRoot = root
      · exact .inr ⟨n, Nat.lt_succ_self n, envelope, _, mem, same, h⟩
      -- An envelope for another block leaves this payload as it was.
      obtain ⟨_, _, _, _, recorded, record, after⟩ := Store.onExecutionPayloadEnvelope_ok h
      obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
      rw [after] at verified
      apply absurd _ held
      simpa [Store.isPayloadVerified, Std.TreeMap.contains_insert, same] using verified

end ForkChoice

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

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

/-- Two honest stores read equal cached target states, or their bounded stores name a collision. -/
theorem Execution.targetStates_eq_or_collision {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {last : ℕ}
    {u w : ValidatorIndex} (first : u ∈ J) (second : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ last) (kBound : (e.world k).time ≤ last)
    {target : Checkpoint} {leftStore rightStore : Store preset fork}
    {left right : BeaconState preset fork}
    (leftStored : ((e.world n).state u).storeTargetCheckpointState config checks target =
      .ok leftStore)
    (leftRead : leftStore.checkpointState target = .ok left)
    (rightStored : ((e.world k).state w).storeTargetCheckpointState config checks target =
      .ok rightStore)
    (rightRead : rightStore.checkpointState target = .ok right) : left = right ∨
    ∃ u ∈ J, ∃ v ∈ J, ∃ n m, (e.world n).time ≤ last ∧ (e.world m).time ≤ last ∧
      ∃ root collision, Store.findBlockCollision ((e.world n).state u)
        ((e.world m).state v) [root] = some collision := by
  rcases Store.blocks_agree_or_collision
      (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ last) with agree | collision
  swap
  · obtain ⟨⟨u, n⟩, ⟨hu, hn⟩, ⟨v, m⟩, ⟨hv, hm⟩, root, collision, found⟩ := collision
    exact .inr ⟨u, hu, v, hv, n, m, hn, hm, root, collision, found⟩
  left
  obtain ⟨leftBase, leftSlot, leftFound, leftSlotOk, leftRun⟩ :=
    e.targetState_fixedChecks anchored start first leftStored leftRead
  obtain ⟨rightBase, rightSlot, rightFound, rightSlotOk, rightRun⟩ :=
    e.targetState_fixedChecks anchored start second rightStored rightRead
  have baseEq := e.blockStates_eq anchored (start u first) (start w second)
    (agree (u, n) ⟨first, nBound⟩ (w, k) ⟨second, kBound⟩) leftFound rightFound
  have slotEq := Except.ok.inj (leftSlotOk.symm.trans rightSlotOk)
  subst rightBase
  subst rightSlot
  exact Except.ok.inj (leftRun.symm.trans rightRun)

/-- Two honest stores collide on one root, by a time. -/
def HonestCollision (time : ℕ) : Prop :=
  ∃ a ∈ J, ∃ b ∈ J, ∃ i j, (e.world i).time ≤ time ∧ (e.world j).time ≤ time ∧
    ∃ r evidence, Store.findBlockCollision ((e.world i).state a) ((e.world j).state b) [r] =
      some evidence

/-- Honest stores up to a time agree on every block they both hold, or two of them collide. -/
theorem Execution.blocksAgree_or_collision (time : ℕ) :
    (∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right) ∨
      HonestCollision (e := e) time := by
  rcases Store.blocks_agree_or_collision (fun i : ValidatorIndex × ℕ => (e.world i.2).state i.1)
      (fun i => i.1 ∈ J ∧ (e.world i.2).time ≤ time) with agree | collision
  · exact .inl fun a ha b hb i j hi hj => agree (a, i) ⟨ha, hi⟩ (b, j) ⟨hb, hj⟩
  · obtain ⟨⟨a, i⟩, ⟨ha, hi⟩, ⟨b, j⟩, ⟨hb, hj⟩, r, evidence, searched⟩ := collision
    exact .inr ⟨a, ha, b, hb, i, j, hi, hj, r, evidence, searched⟩

/-- Honest stores that agree on every block they both hold do not collide. -/
theorem Execution.not_honestCollision_of_agree {time : ℕ}
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ time → (e.world j).time ≤ time →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right) :
    ¬HonestCollision (e := e) time := by
  rintro ⟨a, ha, b, hb, i, j, hi, hj, _, ⟨r, left, right⟩, found⟩
  obtain ⟨leftFound, rightFound, different⟩ := Store.findBlockCollision_held found
  exact different (agree a ha b hb i j hi hj r left right leftFound rightFound)

/-- Synchrony and compatible finality deliver a block, when the sender agrees with the receiver.

The sender's store at each event up to its own agrees with the receiver's store on shared roots.

The receiver must pass the check of the parent's payload of each block that the sender validated.

Admission uses the separate handler-success hypothesis, not synchrony alone. -/
private theorem Execution.blocks_of_partiallySynchronous_core {GST Δ last : ℕ}
    (sync : e.PartiallySynchronous GST Δ)
    (admitted : BlocksAdmitted e GST Δ last)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {v u : ValidatorIndex} (honest : v ∈ J) (receiver : u ∈ J) (startSender : e.start v = anchor)
    (startReceiver : e.start u = anchor) {n k : ℕ}
    (agree : ∀ i ≤ n, ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state v).blocks[r]? = some left →
      ((e.world k).state u).blocks[r]? = some right → left = right)
    (late : max (e.world n).time GST + Δ ≤ (e.world k).time) (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    (finalizedKnown : ∃ finalizedBlock,
      ((e.world k).state u).blocks[((e.world k).state u).finalizedCheckpoint.root]? =
        some finalizedBlock)
    (parentPayload : ∀ i, i < n → ∀ (signed : SignedBeaconBlock preset fork) blockRoot post,
      ((e.world i).state v).validateOnBlock config checks sources signed blockRoot = .ok post →
      (∃ parent, ((e.world k).state u).blocks[signed.message.parentRoot]? = some parent) →
      ((e.world k).state u).validateParentPayload signed.message = .ok ())
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
  have ordered : n ≤ k := by
    by_contra! before
    have time := e.monotone_time (Nat.le_of_lt before)
    change (e.world k).time ≤ (e.world n).time at time
    have positive := sync.1
    omega
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
        rw [startReceiver, ← startSender]
        exact old
      exact e.blocks_of_le (Nat.zero_le k) initial
    have memN := e.monotone_view v (Nat.le_of_lt before) mem
    have memK := sync.2.2 n k ordered v honest u receiver (.block sb) memN late
    obtain ⟨pre, preFound, _, _, _⟩ := Store.validateOnBlock_ok valid
    obtain ⟨other, otherFound, _⟩ :=
      Store.Reachable.blockStatesFromParents
        (e.reachable_of_start (startReceiver ▸ Store.Reachable.anchor anchored) k) pk
    have states : pre = other := e.blockStates_eq anchored startSender
      startReceiver (agree i (Nat.le_of_lt before)) preFound (msg ▸ otherFound)
    have otherPre : ((e.world k).state u).blockStates[sb.message.parentRoot]? = some pre := by
      rw [states, msg]
      exact otherFound
    have parentCheck : ((e.world k).state u).validateParentPayload sb.message = .ok () :=
      parentPayload i before sb r post valid ⟨p, msg ▸ pk⟩
    have ci := e.clock_bounds v i
    have ck := e.clock_bounds u k
    rw [startSender] at ci
    rw [startReceiver] at ck
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
      by_cases known : ((e.world k).state u).blocks.contains r
      · have same := Store.onBlock_known (config := config) (checks := checks)
          (sources := sources) hash known
        rw [same] at added
        cases added
        obtain ⟨existing, existingFound⟩ := Option.isSome_iff_exists.mp
          (by rwa [Std.TreeMap.contains_eq_isSome_getElem?] at known)
        have eq := agree n le_rfl r b existing bf existingFound
        simpa [msg, eq] using existingFound
      · exact (Store.onBlock_new hash known added).2.1
    simpa [fixed, msg] using inserted
  obtain ⟨⟨b, bf, bk⟩, agree⟩ := Store.getAncestor_of_admission
    (agree n le_rfl) base admission walk
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

/-- From Gloas, synchrony delivers a payload that an honest sender verified to a later receiver.

Both stores start at the anchor store, and the receiver holds the state of the payload's block.

For each envelope in its view that the receiver accepts, its store already marks the root verified.

The anchor block must not be after the anchor state, so that no walk reaches the anchor's parent.

Otherwise two honest stores at bounded times collide.

Those stores may be any honest ones, so the result has content when all start at the anchor. -/
theorem Execution.payloadVerified_of_partiallySynchronous {GST Δ last : ℕ}
    (sync : e.PartiallySynchronous GST Δ) (gloas : .glamsterdam ≤ fork)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot) {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {v u : ValidatorIndex} (honest : v ∈ J) (receiver : u ∈ J) (startSender : e.start v = anchor)
    (startReceiver : e.start u = anchor) {n k : ℕ}
    (late : max (e.world n).time GST + Δ ≤ (e.world k).time) (bounded : (e.world k).time ≤ last)
    (closed : ∀ (signed : SignedExecutionPayloadEnvelope preset fork) after,
      .envelope gloas signed ∈ (e.world k).view u →
      ((e.world k).state u).onExecutionPayloadEnvelope config checks sources gloas signed =
        .ok after →
      ((e.world k).state u).isPayloadVerified gloas signed.message.beaconBlockRoot = true)
    {root : Root} (verified : ((e.world n).state v).isPayloadVerified gloas root = true)
    (held : ∃ state, ((e.world k).state u).blockStates[root]? = some state) :
    ((e.world k).state u).isPayloadVerified gloas root = true ∨ HonestCollision (e := e) last := by
  rcases e.blocksAgree_or_collision last with agree | collision
  swap
  · exact .inr collision
  have oneBlock v hv u hu n k hn hk := agree v hv u hu n k hn hk
  left
  have reachedSender := e.reachable_of_start (startSender ▸ Store.Reachable.anchor anchored)
  have reachedReceiver := e.reachable_of_start (startReceiver ▸ Store.Reachable.anchor anchored)
  -- The payload came from an envelope that the sender accepted before.
  rcases e.exists_envelope_of_verified gloas verified with
    initial | ⟨i, before, envelope, _, mem, rfl, handled⟩
  · obtain ⟨_, -, -, -, fields⟩ := getForkchoiceStore_fields anchored
    rw [startSender] at initial
    simp [Store.isPayloadVerified, (fields gloas).2.1] at initial
  have iTime : (e.world i).time ≤ (e.world n).time := e.monotone_time (Nat.le_of_lt before)
  have ordered : i ≤ k := by
    by_contra! after
    have time := e.monotone_time (Nat.le_of_lt after)
    change (e.world k).time ≤ (e.world i).time at time
    have positive := sync.1
    omega
  have iBound : (e.world i).time ≤ last := by omega
  -- Synchrony puts the envelope in the receiver's view.
  have memK := sync.2.2 i k ordered v honest u receiver _ mem (by omega)
  obtain ⟨state, stateFound, dataOk, envelopeOk, recorded, record, -⟩ :=
    Store.onExecutionPayloadEnvelope_ok handled
  obtain ⟨other, otherFound⟩ := held
  have sameState : state = other := e.blockStates_eq anchored startSender
    startReceiver (oneBlock v honest u receiver i k iBound bounded) stateFound otherFound
  subst sameState
  -- The receiver records the envelope as the sender did.
  obtain ⟨recordedHere, recordHere⟩ : ∃ recordedHere, ((e.world k).state u).recordEnvelope
      sources envelope.message.beaconBlockRoot envelope.message.payload = .ok recordedHere := by
    unfold Store.recordEnvelope at record ⊢
    split
    · rename_i heze
      simp only [heze, dite_true, Store.recordPayloadInclusionListSatisfaction, bind_ok_iff,
        mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at record
      obtain ⟨block, blockOk, slot, slotOk, dependent, dependentOk, -⟩ := record
      simp only [Store.getShufflingDependentRoot, bind_ok_iff, mapError_ok_iff, pure,
        Except.pure, Except.ok.injEq] at dependentOk
      obtain ⟨dependentSlot, dependentSlotOk, ancestor, walk, -⟩ := dependentOk
      -- The receiver holds the block, so the sender's walk from it succeeds there too.
      obtain ⟨here, hereFound⟩ := (reachedReceiver k).known_of_blockState otherFound
      obtain rfl := oneBlock v honest u receiver i k iBound bounded _ _ _
        (Store.block_ok_iff.mp blockOk) hereFound
      -- The walk ends at a held block of the sender, which is not below the anchor block.
      obtain ⟨reached, reachedHeld, reachedLe⟩ := Store.getAncestor_le walk
      have walkHere := Store.getAncestor_of_same_blocks (reachedReceiver k)
        (oneBlock v honest u receiver i k iBound bounded)
        (UInt64.le_trans ((reachedSender i).anchorSlot_le anchorSlot reachedHeld) reachedLe)
        ⟨_, hereFound⟩ walk
      exact ⟨_, by simp [Store.recordPayloadInclusionListSatisfaction,
        Store.block_ok_iff.mpr hereFound, slotOk, Store.getShufflingDependentRoot,
        dependentSlotOk, walkHere, bind, Except.bind, pure, Except.pure, Except.mapError]; rfl⟩
    · exact ⟨_, rfl⟩
  have acceptedHere : ((e.world k).state u).onExecutionPayloadEnvelope config checks sources gloas
      envelope = .ok { recordedHere with payloads := fun _ => ((recordedHere.payloads gloas).insert
        envelope.message.beaconBlockRoot envelope.message) } := by
    unfold Store.onExecutionPayloadEnvelope
    simp only [Store.blockState_ok_iff.mpr otherFound, bind, Except.bind]
    rw [dataOk]
    simp only [Except.mapError, envelopeOk, recordHere, pure, Except.pure]
  -- The receiver already marks verified the root of each envelope of its view that it accepts.
  exact closed _ _ memK acceptedHere

/-- At every fork, synchrony and compatible finality deliver a block or name a collision.

Admission uses the separate handler-success hypothesis, not synchrony alone.

From Gloas a block on its parent's payload needs that payload, which synchrony delivers too.

From Gloas the anchor block must not be after the anchor state. -/
theorem Execution.blocks_of_partiallySynchronous_of_anchorSlot {GST Δ last : ℕ}
    (sync : e.PartiallySynchronous GST Δ)
    (anchorSlot : .glamsterdam ≤ fork → anchorBlock.slot ≤ anchorState.slot)
    (admitted : BlocksAdmitted e GST Δ last)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {v u : ValidatorIndex} (honest : v ∈ J) (receiver : u ∈ J) (startSender : e.start v = anchor)
    (startReceiver : e.start u = anchor) {n k : ℕ}
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
    (((e.world k).state u).blocks[root]? = some block ∧
      ∀ epoch checkpointRoot,
        ((e.world k).state u).finalizedCheckpoint.epoch ≤ epoch →
        ((e.world n).state v).getCheckpointBlock root epoch = .ok checkpointRoot →
        ((e.world k).state u).getCheckpointBlock root epoch = .ok checkpointRoot) ∨
    HonestCollision (e := e) last := by
  have senderBound : ∀ i ≤ n, (e.world i).time ≤ last := fun i le => by
    have time : (e.world i).time ≤ (e.world n).time := e.monotone_time le
    have := le_max_left (e.world n).time GST
    omega
  rcases e.blocksAgree_or_collision last with agree | collision
  swap
  · exact .inr collision
  refine .inl (e.blocks_of_partiallySynchronous_core sync admitted anchored honest receiver
    startSender startReceiver
    (fun i le => agree v honest u receiver i k (senderBound i le) bounded) late bounded
    upToDate finalizedKnown ?_ found final)
  intro i before signed blockRoot post valid ⟨parent, parentFound⟩
  by_cases gloas : .glamsterdam ≤ fork
  swap
  · exact Store.validateParentPayload_of_lt (Nat.lt_of_not_le gloas)
  have iTime : (e.world i).time ≤ (e.world n).time := e.monotone_time (Nat.le_of_lt before)
  have iBound : (e.world i).time ≤ last := by omega
  -- A full parent had its payload verified at the sender, so synchrony delivers it.
  obtain ⟨_, -, senderCheck, -, -⟩ := Store.validateOnBlock_ok valid
  obtain ⟨sent, sentFound, sentVerified⟩ :=
    (Store.validateParentPayload_ok_iff gloas).mp senderCheck
  obtain rfl := agree v honest u receiver i k iBound bounded _ _ _ sentFound parentFound
  refine (Store.validateParentPayload_ok_iff gloas).mpr ⟨sent, parentFound, fun full => ?_⟩
  -- The receiver holds the parent's state, as it holds the parent.
  have reached := e.reachable_of_start (startReceiver ▸ Store.Reachable.anchor anchored) k
  obtain ⟨parentState, parentStateFound, -⟩ := reached.blockStatesFromParents parentFound
  rcases e.payloadVerified_of_partiallySynchronous sync gloas (anchorSlot gloas) anchored honest
      receiver
      startSender startReceiver (n := i) (by omega) bounded
      (fun _ _ mem accepted => upToDate.2 _ (.envelope mem accepted) ▸
        Store.onExecutionPayloadEnvelope_verified accepted) (sentVerified full)
      ⟨parentState, parentStateFound⟩ with delivered | collision
  · exact delivered
  · -- A collision of bounded honest stores contradicts their agreement.
    exact absurd collision (e.not_honestCollision_of_agree agree)

end EthLib.Consensus.Models.Network
