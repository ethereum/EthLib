module

public import EthLib.Consensus.Proofs.ForkChoice.ProposerHead
public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: each known block of a reachable store has its entries

The anchor store gives the anchor an unrealized justification.

From Gloas it also gives the anchor its timeliness and its timeliness for the payload committee.

It also gives the anchor an empty entry in each of the two votes of that committee.

Before Gloas the anchor has no timeliness, so the late test returns an error on the anchor.

The block handler gives a new block each of these entries.

No handler of a reachable store removes an entry.

So in a reachable store each known block has them, with that one exception.

The late test then answers for each known head other than the anchor before Gloas.

The test on justification answers for any two known blocks.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

namespace Store

/-- Each key of the five maps of the first store is a key of the same map of the second store. -/
private abbrev Keeps (a b : Store preset fork) : Prop :=
  (∀ r : Root, (a.unrealizedJustifications[r]?).isSome →
      (b.unrealizedJustifications[r]?).isSome) ∧
    (∀ r : Root, (a.blockTimeliness[r]?).isSome → (b.blockTimeliness[r]?).isSome) ∧
    ∀ gloas : .glamsterdam ≤ fork,
      (∀ r : Root, ((a.ptcTimeliness gloas)[r]?).isSome → ((b.ptcTimeliness gloas)[r]?).isSome) ∧
      (∀ r : Root, ((a.payloadTimelinessVote gloas)[r]?).isSome →
        ((b.payloadTimelinessVote gloas)[r]?).isSome) ∧
      (∀ r : Root, ((a.payloadDataAvailabilityVote gloas)[r]?).isSome →
        ((b.payloadDataAvailabilityVote gloas)[r]?).isSome)

private theorem Keeps.refl (a : Store preset fork) : Keeps a a :=
  ⟨fun _ h => h, fun _ h => h, fun _ => ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩⟩

private theorem Keeps.trans {a b c : Store preset fork} (ab : Keeps a b) (bc : Keeps b c) :
    Keeps a c :=
  ⟨fun r h => bc.1 r (ab.1 r h), fun r h => bc.2.1 r (ab.2.1 r h), fun g =>
    ⟨fun r h => (bc.2.2 g).1 r ((ab.2.2 g).1 r h),
      fun r h => (bc.2.2 g).2.1 r ((ab.2.2 g).2.1 r h),
      fun r h => (bc.2.2 g).2.2 r ((ab.2.2 g).2.2 r h)⟩⟩

private theorem Keeps.of_fields {a b : Store preset fork}
    (unrealized : b.unrealizedJustifications = a.unrealizedJustifications)
    (timeliness : b.blockTimeliness = a.blockTimeliness)
    (ptc : ∀ g, b.ptcTimeliness g = a.ptcTimeliness g)
    (timelyVote : ∀ g, b.payloadTimelinessVote g = a.payloadTimelinessVote g)
    (availableVote : ∀ g, b.payloadDataAvailabilityVote g = a.payloadDataAvailabilityVote g) :
    Keeps a b := by
  refine ⟨fun r h => ?_, fun r h => ?_, fun g => ⟨fun r h => ?_, fun r h => ?_, fun r h => ?_⟩⟩
  · rwa [unrealized]
  · rwa [timeliness]
  · rwa [ptc]
  · rwa [timelyVote]
  · rwa [availableVote]

/-- A store that keeps those keys and leaves its map of timeliness as it is. -/
private abbrev Fixes (a b : Store preset fork) : Prop :=
  Keeps a b ∧ b.blockTimeliness = a.blockTimeliness

private theorem Fixes.refl (a : Store preset fork) : Fixes a a := ⟨.refl _, rfl⟩

private theorem Fixes.trans {a b c : Store preset fork} (ab : Fixes a b) (bc : Fixes b c) :
    Fixes a c :=
  ⟨ab.1.trans bc.1, bc.2.trans ab.2⟩

private theorem Fixes.of_fields {a b : Store preset fork}
    (unrealized : b.unrealizedJustifications = a.unrealizedJustifications)
    (timeliness : b.blockTimeliness = a.blockTimeliness)
    (ptc : ∀ g, b.ptcTimeliness g = a.ptcTimeliness g)
    (timelyVote : ∀ g, b.payloadTimelinessVote g = a.payloadTimelinessVote g)
    (availableVote : ∀ g, b.payloadDataAvailabilityVote g = a.payloadDataAvailabilityVote g) :
    Fixes a b :=
  ⟨Keeps.of_fields unrealized timeliness ptc timelyVote availableVote, timeliness⟩

private theorem isSome_insert_of {α : Type} {m : Std.TreeMap Root α} {k r : Root} {v : α}
    (h : (m[r]?).isSome) : ((m.insert k v)[r]?).isSome := by
  rw [getElem?_insert_root]
  split <;> simp_all

private theorem isSome_insert_self {α : Type} {m : Std.TreeMap Root α} {k : Root} {v : α} :
    ((m.insert k v)[k]?).isSome := by
  simp

private theorem contains_insert_root {α : Type} {m : Std.TreeMap Root α} {k r : Root} {v : α} :
    (m.insert k v).contains r = true ↔ k = r ∨ m.contains r = true := by
  simp only [Std.TreeMap.contains_insert, Bool.or_eq_true, Std.LawfulEqCmp.compare_eq_iff_eq,
    beq_iff_eq]

variable {config : Config} {a : Store preset fork}

private theorem updateCheckpoints_keeps (justified finalized : Checkpoint) :
    Fixes a (a.updateCheckpoints justified finalized) := by
  unfold updateCheckpoints
  by_cases j : a.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : a.finalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [j, f, ↓reduceIte] <;>
    exact Fixes.of_fields rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem updateUnrealizedCheckpoints_keeps (justified finalized : Checkpoint) :
    Fixes a (a.updateUnrealizedCheckpoints justified finalized) := by
  unfold updateUnrealizedCheckpoints
  by_cases j : a.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : a.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [j, f, ↓reduceIte] <;>
    exact Fixes.of_fields rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem onTickPerSlot_keeps {timeMs : UInt64} {after : Store preset fork}
    (ticked : a.onTickPerSlot config timeMs = .ok after) : Fixes a after := by
  unfold onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    · obtain ⟨_, _, ticked⟩ := ticked
      split at ticked
      · simp only [pure, Except.pure, Except.ok.injEq] at ticked
        subst ticked
        exact (Fixes.of_fields (by rfl) (by rfl) (fun _ => by rfl) (fun _ => by rfl)
          (fun _ => by rfl)).trans (updateCheckpoints_keeps _ _)
      · simp only [pure, Except.pure, Except.ok.injEq] at ticked
        subst ticked
        exact Fixes.of_fields rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem catchUp_keeps {tickSlot : Slot} {start after : Store preset fork}
    (caught : catchUp config start tickSlot = .ok after) : Fixes start after := by
  induction start using catchUp.induct config tickSlot with
  | _ start ih =>
    rw [catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTimeMs, -, ticked, tick, caught⟩ := caught
      split at caught
      · exact (onTickPerSlot_keeps tick).trans (ih ticked ‹_› caught)
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst caught
      exact .refl _

private theorem onTick_keeps {timeMs : UInt64} {after : Store preset fork}
    (ticked : a.onTick config timeMs = .ok after) : Fixes a after := by
  unfold onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨tickSlot, -, caught, caughtUp, ticked⟩ := ticked
  exact (catchUp_keeps caughtUp).trans (onTickPerSlot_keeps ticked)

private theorem storeTargetCheckpointState_keeps {checks : SignatureChecks} {target : Checkpoint}
    {after : Store preset fork}
    (stored : a.storeTargetCheckpointState config checks target = .ok after) : Fixes a after := by
  unfold storeTargetCheckpointState at stored
  split at stored
  · simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst stored
    exact .refl _
  · simp only [bind_ok_iff] at stored
    obtain ⟨_, _, stored⟩ := stored
    simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst stored
    exact Fixes.of_fields rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem onAttestation_keeps {checks : SignatureChecks}
    {attestation : Attestation preset fork} {isFromBlock : Bool} {after : Store preset fork}
    (attested : a.onAttestation config checks attestation isFromBlock = .ok after) :
    Fixes a after := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, _, _, valid, _, attested⟩ := attested
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact (storeTargetCheckpointState_keeps storing).trans (Fixes.of_fields (by rfl) (by rfl)
      (fun _ => by rfl) (fun _ => by rfl) (fun _ => by rfl))
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

private theorem onAttesterSlashing_keeps {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork} {after : Store preset fork}
    (slashed : a.onAttesterSlashing config checks slashing = .ok after) : Fixes a after := by
  unfold onAttesterSlashing at slashed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
  obtain ⟨_, _, slashed⟩ := slashed
  subst slashed
  exact Fixes.of_fields rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem recordPtcVotes_keeps {gloas : .glamsterdam ≤ fork}
    {data : PayloadAttestationData} {positions : List (Fin preset.PTC_SIZE.toNat)}
    {after : Store preset fork}
    (recorded : a.recordPtcVotes gloas data positions = .ok after) : Fixes a after := by
  unfold recordPtcVotes at recorded
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at recorded
  obtain ⟨_, _, _, _, rfl⟩ := recorded
  exact ⟨⟨fun _ h => h, fun _ h => h, fun g =>
    ⟨fun _ h => h, fun _ h => isSome_insert_of h, fun _ h => isSome_insert_of h⟩⟩, rfl⟩

private theorem onPayloadAttestationMessage_keeps {checks : SignatureChecks}
    {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} {isFromBlock : Bool}
    {after : Store preset fork}
    (accepted : a.onPayloadAttestationMessage config checks gloas message isFromBlock =
      .ok after) : Fixes a after := by
  unfold onPayloadAttestationMessage at accepted
  simp only [bind_ok_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  split at accepted
  · simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    exact .refl _
  · simp only [bind_ok_iff] at accepted
    obtain ⟨_, _, _, _, accepted⟩ := accepted
    cases isFromBlock
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at accepted
      obtain ⟨_, -, accepted⟩ := accepted
      exact recordPtcVotes_keeps accepted
    · exact recordPtcVotes_keeps (by simpa using accepted)

private theorem notifyPtcMessages_keeps {checks : SignatureChecks}
    {gloas : .glamsterdam ≤ fork} {state : BeaconState preset fork}
    {attestations : List (PayloadAttestation preset)} {after : Store preset fork}
    (notified : a.notifyPtcMessages config checks gloas state attestations = .ok after) :
    Fixes a after := by
  unfold notifyPtcMessages at notified
  split at notified
  · simp only [pure, Except.pure, Except.ok.injEq] at notified
    subst notified
    exact .refl _
  · refine foldlM_ok_invariant (Fixes a) (fun other attestation next held step => ?_)
      (.refl _) notified
    simp only [bind_ok_iff] at step
    obtain ⟨_, _, step⟩ := step
    exact foldlM_ok_invariant (Fixes a) (fun _ _ _ held step =>
      held.trans (onPayloadAttestationMessage_keeps step)) held step

private theorem recordBlockPtcVotes_entries {checks : SignatureChecks}
    {signed : SignedBeaconBlock preset fork} {blockRoot : Root}
    {state : BeaconState preset fork} {after : Store preset fork}
    (recorded : a.recordBlockPtcVotes config checks signed blockRoot state = .ok after) :
    Fixes a after ∧ ∀ gloas : .glamsterdam ≤ fork,
      ((after.payloadTimelinessVote gloas)[blockRoot]?).isSome ∧
        ((after.payloadDataAvailabilityVote gloas)[blockRoot]?).isSome := by
  unfold recordBlockPtcVotes at recorded
  split at recorded
  · dsimp only at recorded
    have kept := notifyPtcMessages_keeps recorded
    refine ⟨Fixes.trans ?_ kept, fun g => ⟨(kept.1.2.2 g).2.1 _ isSome_insert_self,
      (kept.1.2.2 g).2.2 _ isSome_insert_self⟩⟩
    exact ⟨⟨fun _ h => h, fun _ h => h, fun g =>
      ⟨fun _ h => h, fun _ h => isSome_insert_of h, fun _ h => isSome_insert_of h⟩⟩, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at recorded
    subst recorded
    exact ⟨.refl _, fun g => absurd g ‹_›⟩

private theorem recordBlockTimeliness_entries {root : Root} {after : Store preset fork}
    (recorded : a.recordBlockTimeliness config root = .ok after) :
    Keeps a after ∧ (after.blockTimeliness[root]?).isSome ∧
      (∀ gloas : .glamsterdam ≤ fork, ((after.ptcTimeliness gloas)[root]?).isSome) ∧
      ∀ r, r ≠ root → after.blockTimeliness[r]? = a.blockTimeliness[r]? := by
  unfold recordBlockTimeliness at recorded
  simp only [bind_ok_iff, pure, Except.pure] at recorded
  obtain ⟨_, _, _, _, _, _, _, _, recorded⟩ := recorded
  split at recorded
  · simp only [bind_ok_iff, Except.ok.injEq] at recorded
    obtain ⟨_, _, rfl⟩ := recorded
    exact ⟨⟨fun _ h => h, fun _ h => isSome_insert_of h, fun g =>
      ⟨fun _ h => isSome_insert_of h, fun _ h => h, fun _ h => h⟩⟩, isSome_insert_self,
      fun g => isSome_insert_self, fun r ne => by simp [getElem?_insert_root, Ne.symm ne]⟩
  · cases recorded
    exact ⟨⟨fun _ h => h, fun _ h => isSome_insert_of h, fun g =>
      ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩⟩, isSome_insert_self,
      fun g => absurd g ‹_›, fun r ne => by simp [getElem?_insert_root, Ne.symm ne]⟩

private theorem updateProposerBoostRoot_keeps {head root : Root} {after : Store preset fork}
    (updated : a.updateProposerBoostRoot config head root = .ok after) : Fixes a after := by
  unfold updateProposerBoostRoot at updated
  split at updated
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at updated
  simp only [bind_ok_iff, pure_bind] at updated
  obtain ⟨_, _, _, _, _, _, updated⟩ := updated
  split at updated <;> simp only [pure, Except.pure, Except.ok.injEq] at updated <;>
    subst updated <;> exact Fixes.of_fields rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem computePulledUpTip_entries {root : Root} {after : Store preset fork}
    (pulled : a.computePulledUpTip config root = .ok after) :
    Fixes a after ∧ (after.unrealizedJustifications[root]?).isSome := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨state, -, pulledState, -, block, -, epoch, -, pulled⟩ := pulled
  have ins : ∀ (s : Store preset fork) (cp : Checkpoint),
      Fixes s { s with unrealizedJustifications := s.unrealizedJustifications.insert root cp } :=
    fun s cp => ⟨⟨fun _ h => isSome_insert_of h, fun _ h => h, fun _ => ⟨fun _ h => h,
      fun _ h => h, fun _ h => h⟩⟩, rfl⟩
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled
  · exact ⟨(ins _ _).trans ((updateUnrealizedCheckpoints_keeps _ _).trans
      (updateCheckpoints_keeps _ _)), (updateCheckpoints_keeps _ _).1.1 _
      ((updateUnrealizedCheckpoints_keeps _ _).1.1 _ isSome_insert_self)⟩
  · exact ⟨(ins _ _).trans (updateUnrealizedCheckpoints_keeps _ _),
      (updateUnrealizedCheckpoints_keeps _ _).1.1 _ isSome_insert_self⟩

private theorem addBlock_entries {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {blockRoot : Root} {after : Store preset fork}
    (added : a.addBlock config checks sources signed blockRoot = .ok after) :
    Keeps a after ∧ (after.unrealizedJustifications[blockRoot]?).isSome ∧
      (after.blockTimeliness[blockRoot]?).isSome ∧
      (∀ gloas : .glamsterdam ≤ fork, ((after.ptcTimeliness gloas)[blockRoot]?).isSome ∧
        ((after.payloadTimelinessVote gloas)[blockRoot]?).isSome ∧
        ((after.payloadDataAvailabilityVote gloas)[blockRoot]?).isSome) ∧
      ∀ r, r ≠ blockRoot → after.blockTimeliness[r]? = a.blockTimeliness[r]? := by
  unfold addBlock at added
  simp only [bind_ok_iff] at added
  obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
  obtain ⟨k1, v1⟩ := recordBlockPtcVotes_entries vote
  obtain ⟨k2, t2, p2, o2⟩ := recordBlockTimeliness_entries record
  have k3 := updateProposerBoostRoot_keeps boost
  obtain ⟨k5, u5⟩ := computePulledUpTip_entries added
  have tail := k3.trans ((updateCheckpoints_keeps _ _).trans k5)
  refine ⟨(Fixes.of_fields (by rfl) (by rfl) (fun _ => by rfl) (fun _ => by rfl)
      (fun _ => by rfl)).1.trans (k1.1.trans (k2.trans tail.1)), u5, tail.1.2.1 _ t2,
      fun g => ?_, fun r ne => ?_⟩
  · exact ⟨(tail.1.2.2 g).1 _ (p2 g), ((k2.trans tail.1).2.2 g).2.1 _ (v1 g).1,
      ((k2.trans tail.1).2.2 g).2.2 _ (v1 g).2⟩
  · rw [tail.2, o2 r ne, k1.2]

private theorem onBlock_entries {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {after : Store preset fork}
    (added : a.onBlock config checks sources signed = .ok after) :
    after = a ∨ ∃ blockRoot, Keeps a after ∧
      after.blocks = a.blocks.insert blockRoot signed.message ∧
      (after.unrealizedJustifications[blockRoot]?).isSome ∧
      (after.blockTimeliness[blockRoot]?).isSome ∧
      (∀ gloas : .glamsterdam ≤ fork, ((after.ptcTimeliness gloas)[blockRoot]?).isSome ∧
        ((after.payloadTimelinessVote gloas)[blockRoot]?).isSome ∧
        ((after.payloadDataAvailabilityVote gloas)[blockRoot]?).isSome) ∧
      (∀ r, r ≠ blockRoot → after.blockTimeliness[r]? = a.blockTimeliness[r]?) ∧
      ¬ a.blocks.contains blockRoot := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e => simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : a.blocks.contains blockRoot
    · rw [onBlock_known root known] at added
      cases added
      exact .inl rfl
    · obtain ⟨blocks, -⟩ := onBlock_insert root known added
      simp only [onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
        Bool.false_eq_true] at added
      obtain ⟨k, u, t, p, o⟩ := addBlock_entries added
      exact .inr ⟨blockRoot, k, blocks, u, t, p, o, known⟩

private theorem getForkchoiceStore_unrealized {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) {anchorRoot : Root}
    (hashed : SszType.hashTreeRoot anchorBlock = .ok anchorRoot) :
    (store.unrealizedJustifications[anchorRoot]?).isSome := by
  unfold getForkchoiceStore at made
  cases stateRoot : SszType.hashTreeRoot anchorState with
  | error e => simp [stateRoot, bind, Except.bind, Except.mapError] at made
  | ok stateRoot' =>
    simp only [stateRoot, Except.mapError, bind, Except.bind] at made
    split at made
    · simp [throw, throwThe, MonadExceptOf.throw] at made
    · cases blockRoot : SszType.hashTreeRoot anchorBlock with
      | error e => simp [blockRoot] at made
      | ok anchorRoot' =>
        simp only [blockRoot] at made
        cases time : computeTimeAtSlotMs config (secondsToMilliseconds anchorState.genesisTime)
            anchorState.slot with
        | error e => simp [time] at made
        | ok timeMs =>
          simp only [time, pure, Except.pure, Except.ok.injEq] at made
          subst made
          rw [blockRoot] at hashed
          cases hashed
          exact isSome_insert_self

/-- The entries of a known block, as the statement of the theorem gives them. -/
private abbrev Entries (anchorBlock : BeaconBlock preset fork) (store : Store preset fork)
    (root : Root) : Prop :=
  (store.unrealizedJustifications[root]?).isSome ∧
    ((store.blockTimeliness[root]?).isSome ∨
      (fork < .glamsterdam ∧ SszType.hashTreeRoot anchorBlock = .ok root)) ∧
    ∀ gloas : .glamsterdam ≤ fork, ((store.ptcTimeliness gloas)[root]?).isSome ∧
      ((store.payloadTimelinessVote gloas)[root]?).isSome ∧
      ((store.payloadDataAvailabilityVote gloas)[root]?).isSome

private theorem Entries.mono {anchorBlock : BeaconBlock preset fork} {b : Store preset fork}
    {root : Root} (kept : Keeps a b) (entries : Entries anchorBlock a root) :
    Entries anchorBlock b root :=
  ⟨kept.1 _ entries.1, entries.2.1.imp (kept.2.1 _) id, fun g =>
    ⟨(kept.2.2 g).1 _ (entries.2.2 g).1, (kept.2.2 g).2.1 _ (entries.2.2 g).2.1,
      (kept.2.2 g).2.2 _ (entries.2.2 g).2.2⟩⟩

private theorem Reachable.entries_aux {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (reachable : Reachable config anchorState anchorBlock store) {root : Root}
    (known : store.blocks.contains root = true) : Entries anchorBlock store root := by
  induction reachable generalizing root with
  | anchor made =>
    obtain ⟨anchorRoot, hashed, blocks, -⟩ := getForkchoiceStore_maps made
    obtain ⟨anchorRoot', hashed', -, timeliness, fields⟩ := getForkchoiceStore_fields made
    rw [hashed] at hashed'
    cases hashed'
    have rootEq : anchorRoot = root := by
      rw [blocks] at known
      rcases contains_insert_root.mp known with h | h
      · exact h
      · simp at h
    subst rootEq
    refine ⟨getForkchoiceStore_unrealized made hashed, ?_, fun g => ?_⟩
    · by_cases g : Fork.glamsterdam ≤ fork
      · left
        rw [timeliness]
        simp only [g, ↓reduceIte]
        exact isSome_insert_self
      · exact .inr ⟨(Nat.lt_of_not_ge g : fork.ctorIdx < Fork.glamsterdam.ctorIdx), hashed⟩
    · obtain ⟨ptc, -, timely, available⟩ := fields g
      rw [ptc, timely, available]
      exact ⟨isSome_insert_self, isSome_insert_self, isSome_insert_self⟩
  | tick _ ticked ih =>
    obtain ⟨-, -, blocks, -⟩ := onTick_frame ticked
    exact Entries.mono (onTick_keeps ticked).1 (ih (by rwa [blocks] at known))
  | @block prior _ checks sources signed previous added ih =>
    rcases onBlock_entries added with
      same | ⟨blockRoot, kept, blocks, unrealized, timely, ptc, -, -⟩
    · subst same
      exact ih known
    · rw [blocks] at known
      rcases contains_insert_root.mp known with rfl | old
      · exact ⟨unrealized, .inl timely, ptc⟩
      · exact Entries.mono kept (ih old)
  | attestation _ attested ih =>
    obtain ⟨-, blocks, -⟩ := onAttestation_frame attested
    exact Entries.mono (onAttestation_keeps attested).1 (ih (by rwa [blocks] at known))
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, -⟩ := onAttesterSlashing_frame slashed
    exact Entries.mono (onAttesterSlashing_keeps slashed).1 (ih (by rwa [blocks] at known))
  | payloadAttestation _ voted ih =>
    obtain ⟨-, blocks, -⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    exact Entries.mono (onPayloadAttestationMessage_keeps voted).1 (ih (by rwa [blocks] at known))
  | envelope _ accepted ih =>
    obtain ⟨-, blocks, -⟩ := onExecutionPayloadEnvelope_frame accepted
    obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := recordEnvelope_frame record
    exact Entries.mono (Keeps.of_fields rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
      (ih (by rwa [blocks] at known))
  | @inclusionList _ _ _ heze _ _ accepted ih =>
    obtain ⟨-, blocks, -⟩ := onInclusionList_frame accepted
    obtain ⟨_, _, rfl⟩ := onInclusionList_ok heze accepted
    exact Entries.mono (Keeps.of_fields rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
      (ih (by rwa [blocks] at known))

private theorem Reachable.anchor_untimely {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (reachable : Reachable config anchorState anchorBlock store) {root : Root}
    (before : fork < .glamsterdam) (hashed : SszType.hashTreeRoot anchorBlock = .ok root) :
    store.blocks.contains root = true ∧ store.blockTimeliness[root]? = none := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, hashedMaps, blocks, -⟩ := getForkchoiceStore_maps made
    obtain ⟨anchorRoot', hashedFields, -, timeliness, -⟩ := getForkchoiceStore_fields made
    rw [hashed] at hashedMaps hashedFields
    cases hashedMaps
    cases hashedFields
    have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => by
      have lt : fork.ctorIdx < Fork.glamsterdam.ctorIdx := before
      have le : Fork.glamsterdam.ctorIdx ≤ fork.ctorIdx := h
      omega
    refine ⟨?_, ?_⟩
    · rw [blocks]
      exact contains_insert_root.mpr (.inl rfl)
    · rw [timeliness]
      simp only [notGloas, ↓reduceIte]
      simp
  | tick _ ticked ih =>
    obtain ⟨-, -, blocks, -⟩ := onTick_frame ticked
    exact ⟨by rw [blocks]; exact ih.1, by rw [(onTick_keeps ticked).2]; exact ih.2⟩
  | @block prior _ checks sources signed previous added ih =>
    rcases onBlock_entries added with same | ⟨blockRoot, -, blocks, -, -, -, others, fresh⟩
    · subst same
      exact ih
    · refine ⟨?_, ?_⟩
      · rw [blocks]
        exact contains_insert_root.mpr (.inr ih.1)
      · rw [others root (fun h => fresh (h ▸ ih.1))]
        exact ih.2
  | attestation _ attested ih =>
    obtain ⟨-, blocks, -⟩ := onAttestation_frame attested
    exact ⟨by rw [blocks]; exact ih.1, by rw [(onAttestation_keeps attested).2]; exact ih.2⟩
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, blocks, -⟩ := onAttesterSlashing_frame slashed
    exact ⟨by rw [blocks]; exact ih.1, by rw [(onAttesterSlashing_keeps slashed).2]; exact ih.2⟩
  | payloadAttestation _ voted ih =>
    obtain ⟨-, blocks, -⟩ := (onPayloadAttestationMessage_onlyPtcVotes voted).frame
    exact ⟨by rw [blocks]; exact ih.1,
      by rw [(onPayloadAttestationMessage_keeps voted).2]; exact ih.2⟩
  | envelope _ accepted ih =>
    obtain ⟨-, blocks, -⟩ := onExecutionPayloadEnvelope_frame accepted
    obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := recordEnvelope_frame record
    exact ⟨by rw [blocks]; exact ih.1, ih.2⟩
  | @inclusionList _ _ _ heze _ _ accepted ih =>
    obtain ⟨-, blocks, -⟩ := onInclusionList_frame accepted
    obtain ⟨_, _, rfl⟩ := onInclusionList_ok heze accepted
    exact ⟨by rw [blocks]; exact ih.1, ih.2⟩

end Store

/-- In a reachable store, each known block has an unrealized justification. -/
theorem Store.Reachable.unrealizedJustification_isSome
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    (known : store.blocks.contains root) :
    (store.unrealizedJustifications[root]?).isSome :=
  (reachable.entries_aux known).1

/-- In a reachable store, each known block has a timeliness, except the anchor before Gloas. -/
theorem Store.Reachable.blockTimeliness_isSome
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    (known : store.blocks.contains root)
    (notAnchor : .glamsterdam ≤ fork ∨ SszType.hashTreeRoot anchorBlock ≠ .ok root) :
    (store.blockTimeliness[root]?).isSome := by
  rcases (reachable.entries_aux known).2.1 with found | ⟨before, hashed⟩
  · exact found
  · rcases notAnchor with gloas | differ
    · have lt : fork.ctorIdx < Fork.glamsterdam.ctorIdx := before
      have le : Fork.glamsterdam.ctorIdx ≤ fork.ctorIdx := gloas
      omega
    · exact absurd hashed differ

/-- Before Gloas, the anchor of a reachable store has no timeliness.

No handler records the timeliness of a block that the store already knows. -/
theorem Store.Reachable.blockTimeliness_anchor
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    (before : fork < .glamsterdam) (hashed : SszType.hashTreeRoot anchorBlock = .ok root) :
    store.blockTimeliness[root]? = none :=
  (reachable.anchor_untimely before hashed).2

/-- From Gloas, in a reachable store, each known block has a timeliness for the payload committee.
-/
theorem Store.Reachable.ptcTimeliness_isSome
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    (known : store.blocks.contains root) (gloas : .glamsterdam ≤ fork) :
    ((store.ptcTimeliness gloas)[root]?).isSome :=
  ((reachable.entries_aux known).2.2 gloas).1

/-- From Gloas, in a reachable store, each known block has its timeliness votes of the committee.
-/
theorem Store.Reachable.payloadTimelinessVote_isSome
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    (known : store.blocks.contains root) (gloas : .glamsterdam ≤ fork) :
    ((store.payloadTimelinessVote gloas)[root]?).isSome :=
  ((reachable.entries_aux known).2.2 gloas).2.1

/-- From Gloas, in a reachable store, each known block has its availability votes of the committee.
-/
theorem Store.Reachable.payloadDataAvailabilityVote_isSome
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    (known : store.blocks.contains root) (gloas : .glamsterdam ≤ fork) :
    ((store.payloadDataAvailabilityVote gloas)[root]?).isSome :=
  ((reachable.entries_aux known).2.2 gloas).2.2

/-- In a reachable store, each known block has an unrealized justified checkpoint. -/
theorem Store.Reachable.unrealizedJustification_ok
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    (known : store.blocks.contains root) :
    ∃ checkpoint, store.unrealizedJustification root = .ok checkpoint := by
  obtain ⟨checkpoint, h⟩ :=
    Option.isSome_iff_exists.mp (reachable.unrealizedJustification_isSome known)
  exact ⟨checkpoint, by simp [Store.unrealizedJustification, h, pure, Except.pure]⟩

/-- In a reachable store, the late test answers for each known block but the anchor before Gloas.
-/
theorem Store.Reachable.isHeadLate_ok
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    (known : store.blocks.contains root)
    (notAnchor : .glamsterdam ≤ fork ∨ SszType.hashTreeRoot anchorBlock ≠ .ok root) :
    ∃ late, store.isHeadLate root = .ok late := by
  obtain ⟨t, h⟩ := Option.isSome_iff_exists.mp (reachable.blockTimeliness_isSome known notAnchor)
  exact ⟨!t, Store.isHeadLate_ok_iff.mpr ⟨t, h, rfl⟩⟩

/-- In a reachable store, the test of two known blocks on justification answers. -/
theorem Store.Reachable.isFfgCompetitive_ok
    (reachable : Store.Reachable config anchorState anchorBlock store) {headRoot parentRoot : Root}
    (headKnown : store.blocks.contains headRoot) (parentKnown : store.blocks.contains parentRoot) :
    ∃ competitive, store.isFfgCompetitive headRoot parentRoot = .ok competitive := by
  obtain ⟨first, hFirst⟩ :=
    Option.isSome_iff_exists.mp (reachable.unrealizedJustification_isSome headKnown)
  obtain ⟨second, hSecond⟩ :=
    Option.isSome_iff_exists.mp (reachable.unrealizedJustification_isSome parentKnown)
  exact ⟨decide (first = second),
    Store.isFfgCompetitive_ok_iff.mpr ⟨first, second, hFirst, hSecond, rfl⟩⟩

/-- The choice of a proposer in a reachable store, from the answers of its tests.

The store answers the late test and the test on justification by itself.

The head must not be the anchor before Gloas.

The other tests and conditions are those of the choice in any store. -/
theorem Store.Reachable.getProposerHead_eq
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {headNode : ForkChoiceNode} {slot : Slot} {head parent : BeaconBlock preset fork}
    {shuffling recent onTime weak strong equivocation : Bool}
    (notAnchor : .glamsterdam ≤ fork ∨ SszType.hashTreeRoot anchorBlock ≠ .ok headNode.root)
    (unboosted : store.proposerBoostRoot ≠ headNode.root)
    (headKnown : store.blocks[headNode.root]? = some head)
    (parentKnown : store.blocks[head.parentRoot]? = some parent)
    (shufflingFound : shufflingAllowsReorg preset fork slot = .ok shuffling)
    (recentFound : store.isFinalizationOk config slot = .ok recent)
    (onTimeFound : store.isProposingOnTime config = .ok onTime)
    (parentFits : parent.slot.toNat + 1 < 2 ^ 64) (headFits : head.slot.toNat + 1 < 2 ^ 64)
    (weakFound : store.isHeadWeak config headNode.root = .ok weak)
    (strongFound : store.isParentStrong config headNode.root = .ok strong)
    (equivocationFound : store.isProposerEquivocation headNode.root = .ok equivocation) :
    ∃ late competitive, store.isHeadLate headNode.root = .ok late ∧
      store.isFfgCompetitive headNode.root head.parentRoot = .ok competitive ∧
      store.getProposerHead config headNode slot = .ok
        (if (late ∧ shuffling ∧ competitive ∧ recent ∧ onTime ∧
              (parent.slot.toNat + 1 = head.slot.toNat ∧ head.slot.toNat + 1 = slot.toNat) ∧
              weak ∧ strong) ∨
            (weak ∧ head.slot.toNat + 1 = slot.toNat ∧ equivocation)
          then ⟨head.parentRoot, parentPayloadStatus head parent⟩
          else headNode) := by
  have headContains : store.blocks.contains headNode.root = true := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?, headKnown]
    rfl
  have parentContains : store.blocks.contains head.parentRoot = true := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?, parentKnown]
    rfl
  obtain ⟨late, lateFound⟩ := reachable.isHeadLate_ok headContains notAnchor
  obtain ⟨competitive, competitiveFound⟩ :=
    reachable.isFfgCompetitive_ok headContains parentContains
  exact ⟨late, competitive, lateFound, competitiveFound, Store.getProposerHead_eq unboosted
    headKnown parentKnown lateFound shufflingFound competitiveFound recentFound onTimeFound
    parentFits headFits weakFound strongFound equivocationFound⟩

end EthLib.Consensus
