module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
public import EthLib.Consensus.Proofs.Models.Network.Model

/-!
# Joint signature and accepted-vote provenance

A latest message in an honest store comes from one attestation that was both signed and accepted.

Keeping those witnesses together permits the duty of an honest signer to constrain that vote.

The signature model follows [arXiv 2405.00549v4, Section 2][fcr].

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A statement of an honest signer in a sent message was allowed at an earlier event. -/
theorem Execution.exists_maySign_of_signed {n : ℕ} {m : Message preset fork}
    (sent : m ∈ (e.world n).sent) {v : ValidatorIndex} {data : AttestationData}
    (signed : (v, data) ∈ statements config checks anchorState anchorBlock m) (honest : v ∈ J) :
    ∃ k < n, MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k).time ((e.world k).view v) ((e.world k).state v) data := by
  obtain ⟨k, before, first, sends, carries, fresh⟩ :=
    e.exists_first_send_of_signed sent signed honest
  have allowed := e.allowed_world k
  rw [sends] at allowed
  rcases allowed.2 honest (v, data) carries rfl with ⟨earlier, seen, carried⟩ | duty
  · exact (fresh earlier (e.view_subset_sent k v seen) carried).elim
  · exact ⟨k, before, duty⟩

/-- One attestation witnesses both the signature and the accepted origin of a latest vote. -/
theorem Execution.exists_signed_origin_of_latestMessages {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {u : ValidatorIndex} (receiver : u ∈ J) {n : ℕ}
    {v : ValidatorIndex} {message : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[v]? = some message) :
    ∃ attestation : Attestation preset fork, ∃ m ∈ (e.world n).view u,
      message = LatestMessage.ofAttestation attestation ∧
      (v, attestation.data) ∈ statements config checks anchorState anchorBlock m ∧
      ((e.world n).state u).VoteOrigin config v attestation := by
  let Origin := fun (view : Set (Message preset fork)) (store : Store preset fork) =>
    ∀ (v : ValidatorIndex) (message : LatestMessage fork),
      store.latestMessages[v]? = some message →
      ∃ a : Attestation preset fork, ∃ m ∈ view,
        message = LatestMessage.ofAttestation a ∧
          (v, a.data) ∈ statements config checks anchorState anchorBlock m ∧
          store.VoteOrigin config v a
  have keep {s t : Store preset fork} {view} (old : Origin view s)
      (messages : t.latestMessages = s.latestMessages)
      (blocks : ∀ {r : Root} {b : BeaconBlock preset fork},
        s.blocks[r]? = some b → t.blocks[r]? = some b)
      (states : ∀ {c : Checkpoint} {st : BeaconState preset fork},
        s.checkpointStates[c]? = some st → t.checkpointStates[c]? = some st)
      (clock : ∀ {slot}, s.getCurrentSlot config = .ok slot →
        ∃ later, t.getCurrentSlot config = .ok later ∧ slot ≤ later) : Origin view t := by
    intro validator latest found
    obtain ⟨a, m, seen, same, signed, origin⟩ := old validator latest (messages ▸ found)
    exact ⟨a, m, seen, same, signed, origin.mono blocks states clock⟩
  have slash {s t : Store preset fork} {view sl} (old : Origin view s)
      (handled : s.onAttesterSlashing config checks sl = .ok t) : Origin view t :=
    keep old (Store.onAttesterSlashing_checkpointStates_latestMessages handled).2
      (fun known => (Store.onAttesterSlashing_frame handled).2.1 ▸ known)
      (fun known => (Store.onAttesterSlashing_checkpointStates_latestMessages handled).1 ▸ known)
      (fun slotOk => ⟨_, slotOk ▸ (Store.onAttesterSlashing_sameClock handled).getCurrentSlot,
        UInt64.le_refl _⟩)
  have attestationStep : ∀ {store after : Store preset fork} {view}
      {a : Attestation preset fork} {fromBlock : Bool},
      Store.Reachable config anchorState anchorBlock store → Origin view store →
      (∃ m ∈ view, attestationStatements (config := config) (checks := checks)
        anchorState anchorBlock a ⊆ statements config checks anchorState anchorBlock m) →
      store.onAttestation config checks a fromBlock = .ok after → Origin view after := by
    intro store after view a fromBlock reachable old ⟨m, seen, carried⟩ handled v message found
    have keepOld {message} (previous : store.latestMessages[v]? = some message) :
        ∃ b, ∃ m ∈ view, message = LatestMessage.ofAttestation b ∧
          (v, b.data) ∈ statements config checks anchorState anchorBlock m ∧
          after.VoteOrigin config v b := by
      obtain ⟨b, m, seen, same, signed, origin⟩ := old v message previous
      exact ⟨b, m, seen, same, signed, origin.mono
        (fun known => (Store.onAttestation_frame handled).2.1 ▸ known)
        (Store.onAttestation_checkpointStates_of_found handled)
        (fun slotOk => ⟨_, slotOk ▸ (Store.onAttestation_sameClock handled).getCurrentSlot,
          UInt64.le_refl _⟩)⟩
    rcases Store.onAttestation_latestMessages_read_cases handled found with previous |
      ⟨same, origin, stored, target, indexed, storing, targetOk, indexedOk, validOk, member⟩
    · exact keepOld previous
    have dataSame : indexed.data = a.data := by
      obtain ⟨indices, indicesOk, _⟩ := getAttestingIndices_of_getIndexedAttestation indexedOk
      obtain ⟨indexed', made, _, dataSame, _⟩ :=
        getIndexedAttestation_of_getAttestingIndices indicesOk
      have same := Except.ok.inj (indexedOk.symm.trans made)
      exact same ▸ dataSame
    refine ⟨a, m, seen, same, carried ?_, origin⟩
    exact ⟨store, indexed, reachable, ⟨stored, target, storing, targetOk, indexedOk, validOk⟩,
      by simpa [indexedStatements, dataSame] using member⟩
  have invariant : ∀ n, Origin ((e.world n).view u) ((e.world n).state u) := by
    intro n
    induction n with
    | zero =>
      intro v message found
      change (e.start u).latestMessages[v]? = some message at found
      obtain ⟨_, _, empty, _⟩ := getForkchoiceStore_fields anchored
      rw [start u receiver, empty] at found
      simp at found
    | succ n ih =>
      have extend : ∀ {s}, Origin ((e.world n).view u) s →
          Origin ((e.world (n + 1)).view u) s := by
        intro s origin v message found
        obtain ⟨a, m, seen, same, signed, accepted⟩ := origin v message found
        exact ⟨a, m, e.monotone_view u (Nat.le_succ n) seen, same, signed, accepted⟩
      rcases e.state_succ n u with same | ⟨_, handles⟩
      · rw [same]
        exact extend ih
      apply extend
      have reachable := e.reachable
        (fun w hw => (start w hw) ▸ Store.Reachable.anchor anchored) n u receiver
      cases handles with
      | tick timeLe fits ticked =>
        have clockLe : ((e.world n).state u).timeMs ≤ (e.world n).time.toUInt64 := by
          rw [UInt64.le_iff_toNat_le, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' fits]
          exact timeLe
        exact keep ih (Store.onTick_checkpointStates_latestMessages ticked).2
          (fun known => (Store.onTick_frame ticked).2.2.1 ▸ known)
          (fun known => (Store.onTick_checkpointStates_latestMessages ticked).1 ▸ known)
          (Store.exists_getCurrentSlot_onTick_ge clockLe ticked)
      | attestation seen handled =>
        exact attestationStep reachable ih ⟨_, seen, fun _ h => h⟩ handled
      | attesterSlashing _ handled => exact slash ih handled
      | block _ blockOk =>
        exact keep ih (Store.onBlock_checkpointStates_latestMessages blockOk).2
          (Store.onBlock_blocks_of_found blockOk)
          (fun known => (Store.onBlock_checkpointStates_latestMessages blockOk).1 ▸ known)
          (fun slotOk => ⟨_, slotOk ▸ (Store.onBlock_sameClock blockOk).getCurrentSlot,
            UInt64.le_refl _⟩)
      | blockAttestation seen carried handled =>
        exact attestationStep reachable ih
          ⟨_, seen, fun _ statement => Or.inl ⟨_, carried, statement⟩⟩ handled
      | blockAttesterSlashing _ _ handled => exact slash ih handled
      | payloadAttestation _ handled =>
        obtain ⟨_, _, same⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes handled
        rw [same]
        exact keep ih rfl (fun h => h) (fun h => h)
          (fun slotOk => ⟨_, slotOk, UInt64.le_refl _⟩)
      | envelope _ handled =>
        obtain ⟨_, _, _, _, _, record, same⟩ := Store.onExecutionPayloadEnvelope_ok handled
        rw [same]
        obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
        exact keep ih rfl (fun h => h) (fun h => h)
          (fun slotOk => ⟨_, slotOk, UInt64.le_refl _⟩)
      | inclusionList _ handled =>
        obtain ⟨_, _, same⟩ := Store.onInclusionList_ok ‹_› handled
        rw [same]
        exact keep ih rfl (fun h => h) (fun h => h)
          (fun slotOk => ⟨_, slotOk, UInt64.le_refl _⟩)
  exact invariant n v message found

end EthLib.Consensus.Models.Network
