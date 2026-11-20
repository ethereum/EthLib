module

public import EthLib.Consensus.RemoteSigningApi.Endpoints
public import EthLib.Consensus.Proofs.SlashingProtection
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect
public import EthLib.Consensus.Transition.Block

/-!
# Proofs: the endpoints of a remote signer

The sign endpoint answers 404 exactly when the request reads and its key is not held.

A signature that it returns verifies under the key of the path, for the signer's own root.

A call that does not sign leaves the state as it was.

With the rule of EIP-3076, each signed block or vote passed its check, and enters the record.

No call removes a record.

So in any run of calls, two blocks of one slot signed for one key have one signing root.

So do two votes signed for one key that slash each other, whatever the record the run starts with.
-/

@[expose] public section

namespace EthLib.Consensus.RemoteSigningApi

open Lean Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {config : Config} {protect : SlashingPolicy preset}
  {state : SignerState} {identifier : String} {document : Json}

/-! ## Status codes and signatures -/

/-- The last step never answers 404. -/
theorem protectAndSign_status_ne_404 (protect : SlashingPolicy preset) (state : SignerState)
    (pubkey : BLSPubkey) (key : Signatures.SecretKey) (request : SigningRequest preset)
    (root : Root) : (protectAndSign protect state pubkey key request root).1.status ≠ 404 := by
  unfold protectAndSign
  split
  · simp [SignResult.status]
  · split <;> simp [SignResult.status]

/-- A key is held exactly when the search over the secret keys finds one for it. -/
theorem find?_eq_none_iff_not_mem_publicKeys (pubkey : BLSPubkey) :
    state.keys.find? (Signatures.skToPk · = pubkey) = none ↔ pubkey ∉ publicKeys state := by
  simp [publicKeys, List.find?_eq_none]

/-- The sign endpoint answers 404 exactly when the request reads and its key is not held.

It reads the request first, so a request that does not read gets 400 whatever its key. -/
theorem sign_status_eq_404_iff :
    (sign preset config protect state identifier document).1.status = 404 ↔
      (∃ request, SigningRequest.ofJson preset document = .ok request) ∧
      ∃ pubkey, readIdentifier identifier = some pubkey ∧ pubkey ∉ publicKeys state := by
  unfold sign
  cases hr : SigningRequest.ofJson preset document with
  | error e => simp [SignResult.status]
  | ok request =>
    cases hi : readIdentifier identifier with
    | none => simp [SignResult.status]
    | some pubkey =>
      cases hf : state.keys.find? (Signatures.skToPk · = pubkey) with
      | none =>
        simp [hf, SignResult.status, (find?_eq_none_iff_not_mem_publicKeys pubkey).mp hf]
      | some key =>
        have held : pubkey ∈ publicKeys state := by
          by_contra absent
          rw [← find?_eq_none_iff_not_mem_publicKeys] at absent
          simp [absent] at hf
        simp only [hf, Option.some.injEq, exists_eq_left', held, not_true_eq_false, and_false,
          iff_false]
        split
        · simp [SignResult.status]
        · split
          · simp [SignResult.status]
          · exact protectAndSign_status_ne_404 _ _ _ _ _ _

/-- A signature of the last step is a signature of the root by the key. -/
theorem protectAndSign_signed {pubkey : BLSPubkey} {key : Signatures.SecretKey}
    {request : SigningRequest preset} {root : Root} {signature : BLSSignature}
    (signed : (protectAndSign protect state pubkey key request root).1 = .signed signature) :
    Signatures.verify (Signatures.skToPk key) (packBytes root) signature = true := by
  obtain ⟨signature', signs, verifies⟩ := Signatures.verify_sign key (packBytes root)
  unfold protectAndSign at signed
  split at signed
  · simp at signed
  · rw [signs] at signed
    simp only [SignResult.signed.injEq] at signed
    subst signed
    exact verifies

/-- A signature that the sign endpoint returns verifies under the key of the path.

It signs the root that the signer computes for the request, not a root that the client sends.

The key is one that the signer holds. -/
theorem sign_signed {signature : BLSSignature}
    (signed : (sign preset config protect state identifier document).1 = .signed signature) :
    ∃ request pubkey root, SigningRequest.ofJson preset document = .ok request ∧
      readIdentifier identifier = some pubkey ∧ pubkey ∈ publicKeys state ∧
      requestSigningRoot config request = .ok root ∧
      Signatures.verify pubkey (packBytes root) signature = true := by
  unfold sign at signed
  split at signed
  · simp at signed
  · rename_i request hr
    split at signed
    · simp at signed
    · rename_i pubkey hi
      split at signed
      · simp at signed
      · rename_i key hf
        have keyed : Signatures.skToPk key = pubkey := by
          simpa using List.find?_some hf
        have held : pubkey ∈ publicKeys state := by
          rw [← keyed]
          exact List.mem_map_of_mem (List.mem_of_find?_eq_some hf)
        split at signed
        · simp at signed
        · rename_i root hroot
          split at signed
          · simp at signed
          · refine ⟨request, pubkey, root, hr, hi, held, hroot, ?_⟩
            rw [← keyed]
            exact protectAndSign_signed signed

/-- A call that the sign endpoint does not answer with a signature leaves the state as it was. -/
theorem sign_state_of_not_signed
    (unsigned : ∀ signature, (sign preset config protect state identifier document).1 ≠
      .signed signature) :
    (sign preset config protect state identifier document).2 = state := by
  unfold sign protectAndSign at *
  repeat' split
  all_goals simp_all

/-! ## Slashing protection under EIP-3076 -/

/-- The rule of EIP-3076 removes no record of any key. -/
theorem eip3076Policy_keeps {record next : Interchange} {pubkey : BLSPubkey}
    {request : SigningRequest preset} {root : Root}
    (passed : eip3076Policy record pubkey request root = .ok next) (other : BLSPubkey) :
    (∀ block ∈ record.blocksOf other, block ∈ next.blocksOf other) ∧
      ∀ vote ∈ record.attestationsOf other, vote ∈ next.attestationsOf other := by
  unfold eip3076Policy at passed
  split at passed
  all_goals first
    | (obtain ⟨_, rest⟩ := bind_unit_ok_iff.mp passed
       simp only [pure, Except.pure, Except.ok.injEq] at rest
       subst rest
       refine ⟨fun block member => ?_, fun vote member => ?_⟩
       · by_cases same : other = pubkey
         · subst same
           rw [blocksOf_recordBlock]
           exact List.mem_append_left _ member
         · rw [blocksOf_recordBlock_of_ne same]
           exact member
       · rw [attestationsOf_recordBlock]
         exact member)
    | (obtain ⟨_, rest⟩ := bind_unit_ok_iff.mp passed
       simp only [pure, Except.pure, Except.ok.injEq] at rest
       subst rest
       refine ⟨fun block member => ?_, fun vote member => ?_⟩
       · rw [blocksOf_recordAttestation]
         exact member
       · by_cases same : other = pubkey
         · subst same
           rw [attestationsOf_recordAttestation]
           exact List.mem_append_left _ member
         · rw [attestationsOf_recordAttestation_of_ne same]
           exact member)
    | (simp only [Except.ok.injEq] at passed
       subst passed
       exact ⟨fun _ member => member, fun _ member => member⟩)

/-- The record after a call, as the rule of EIP-3076 left it.

The call leaves the keys as they were.

It leaves the record as it was, or the rule passed and gave the new record. -/
theorem sign_protection_eq (identifier : String) (document : Json) :
    (sign preset config eip3076Policy state identifier document).2.keys = state.keys ∧
      ((sign preset config eip3076Policy state identifier document).2.protection =
          state.protection ∨
        ∃ (pubkey : BLSPubkey) (request : SigningRequest preset) (root : Root),
          eip3076Policy state.protection pubkey request root =
            .ok (sign preset config eip3076Policy state identifier document).2.protection) := by
  unfold sign protectAndSign
  repeat' split
  all_goals first
    | exact ⟨rfl, Or.inl rfl⟩
    | exact ⟨rfl, Or.inr ⟨_, _, _, by assumption⟩⟩

/-- A call of the sign endpoint with the rule of EIP-3076 removes no record of any key. -/
theorem sign_keeps (identifier : String) (document : Json) (other : BLSPubkey) :
    let next := (sign preset config eip3076Policy state identifier document).2
    (∀ block ∈ state.protection.blocksOf other, block ∈ next.protection.blocksOf other) ∧
      ∀ vote ∈ state.protection.attestationsOf other,
        vote ∈ next.protection.attestationsOf other := by
  intro next
  rcases (sign_protection_eq (config := config) (state := state) identifier document).2 with
    same | ⟨_, _, _, passed⟩
  · simp only [next]
    rw [same]
    exact ⟨fun _ member => member, fun _ member => member⟩
  · exact eip3076Policy_keeps passed other

/-- A call that the sign endpoint answers with a signature leaves the record that the rule gave.

The rule saw the request, the key of the path and the root that the endpoint signed. -/
theorem sign_recorded {signature : BLSSignature}
    (signed : (sign preset config eip3076Policy state identifier document).1 = .signed signature) :
    ∃ request pubkey root, SigningRequest.ofJson preset document = .ok request ∧
      readIdentifier identifier = some pubkey ∧ requestSigningRoot config request = .ok root ∧
      eip3076Policy state.protection pubkey request root =
        .ok (sign preset config eip3076Policy state identifier document).2.protection := by
  unfold sign protectAndSign at signed ⊢
  split at signed
  · simp at signed
  · rename_i request hr
    split at signed
    · simp at signed
    · rename_i pubkey hi
      split at signed
      · simp at signed
      · split at signed
        · simp at signed
        · rename_i root hroot
          split at signed
          · simp at signed
          · split at signed
            · simp at signed
            · rename_i protection passed
              split at signed
              · simp at signed
              · refine ⟨request, pubkey, root, hr, hi, hroot, ?_⟩
                simp [passed]

/-- A signed block passed its check against the record before the call, and enters the record. -/
theorem sign_block {signature : BLSSignature} {pubkey : BLSPubkey} {slot : Slot} {root : Root}
    (signed : (sign preset config eip3076Policy state identifier document).1 = .signed signature)
    (named : blockOfCall? preset config identifier document = some (pubkey, slot, root)) :
    state.protection.checkBlock pubkey slot root = .ok () ∧
      ⟨slot, some root⟩ ∈
        (sign preset config eip3076Policy state identifier document).2.protection.blocksOf
          pubkey := by
  obtain ⟨request, pubkey', root', hr, hi, hroot, passed⟩ := sign_recorded signed
  simp only [blockOfCall?, hr, hi, hroot, Except.toOption, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def] at named
  generalize (sign preset config eip3076Policy state identifier document).2.protection = next
    at passed ⊢
  cases request <;> simp [SigningRequest.blockSlot?] at named
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := named
    obtain ⟨checked, rest⟩ := bind_unit_ok_iff.mp passed
    simp only [pure, Except.pure, Except.ok.injEq] at rest
    subst rest
    exact ⟨checked, by simp [blocksOf_recordBlock]⟩

/-- A signed vote passed its check against the record before the call, and enters the record. -/
theorem sign_vote {signature : BLSSignature} {pubkey : BLSPubkey} {data : AttestationData}
    {root : Root}
    (signed : (sign preset config eip3076Policy state identifier document).1 = .signed signature)
    (named : voteOfCall? preset config identifier document = some (pubkey, data, root)) :
    state.protection.checkAttestation pubkey data.source.epoch data.target.epoch root = .ok () ∧
      ⟨data.source.epoch, data.target.epoch, some root⟩ ∈
        (sign preset config eip3076Policy state identifier document).2.protection.attestationsOf
          pubkey := by
  obtain ⟨request, pubkey', root', hr, hi, hroot, passed⟩ := sign_recorded signed
  simp only [voteOfCall?, hr, hi, hroot, Except.toOption, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def] at named
  generalize (sign preset config eip3076Policy state identifier document).2.protection = next
    at passed ⊢
  cases request <;> simp [SigningRequest.attestationData?] at named
  obtain ⟨rfl, rfl, rfl⟩ := named
  obtain ⟨checked, rest⟩ := bind_unit_ok_iff.mp passed
  simp only [pure, Except.pure, Except.ok.injEq] at rest
  subst rest
  exact ⟨checked, by simp [attestationsOf_recordAttestation]⟩

/-! ## A run of calls -/

/-- Each block that a run signs agrees with every block of its slot in the record it started with.

Every such recorded block has the root of the signed block. -/
theorem signedBlocks_fresh (calls : List (String × Json)) (state : SignerState) :
    ∀ signed ∈ signedBlocks preset config state calls,
      ∀ block ∈ state.protection.blocksOf signed.1, block.slot = signed.2.1 →
        block.signingRoot = some signed.2.2 := by
  induction calls generalizing state with
  | nil => simp [signedBlocks]
  | cons call rest ih =>
    obtain ⟨identifier, document⟩ := call
    intro entry member block recorded sameSlot
    simp only [signedBlocks, List.mem_append] at member
    rcases member with now | later
    · split at now
      · rename_i signature result
        obtain ⟨pubkey, slot, root⟩ := entry
        have named : blockOfCall? preset config identifier document = some (pubkey, slot, root) :=
          by simpa using now
        have checked := (sign_block result named).1
        have := (checkBlockSigning_eq_ok_iff.mp checked).1 block recorded
        simpa [SignedBlockRecord.conflictsWith, sameSlot] using this
      · simp at now
    · exact ih _ entry later block ((sign_keeps identifier document entry.1).1 block recorded)
        sameSlot

/-- Two blocks of one slot that a run signs for one key have one signing root.

This holds from any record, whatever the calls before, between and after them. -/
theorem signingRoot_eq_of_signedBlocks {calls : List (String × Json)} {state : SignerState}
    {first second : BLSPubkey × Slot × Root}
    (firstSigned : first ∈ signedBlocks preset config state calls)
    (secondSigned : second ∈ signedBlocks preset config state calls)
    (sameKey : first.1 = second.1) (sameSlot : first.2.1 = second.2.1) :
    first.2.2 = second.2.2 := by
  induction calls generalizing state with
  | nil => simp [signedBlocks] at firstSigned
  | cons call rest ih =>
    obtain ⟨identifier, document⟩ := call
    simp only [signedBlocks, List.mem_append] at firstSigned secondSigned
    -- A block signed by this call enters the record that the later calls start from.
    have recorded : ∀ entry, entry ∈ (match
        (sign preset config eip3076Policy state identifier document).1 with
        | .signed _ => (blockOfCall? preset config identifier document).toList
        | _ => []) →
        ⟨entry.2.1, some entry.2.2⟩ ∈
          (sign preset config eip3076Policy state identifier document).2.protection.blocksOf
            entry.1 := by
      intro entry now
      split at now
      · rename_i signature result
        obtain ⟨pubkey, slot, root⟩ := entry
        exact (sign_block result (by simpa using now)).2
      · simp at now
    have single : ∀ entry entry', entry ∈ (match
        (sign preset config eip3076Policy state identifier document).1 with
        | .signed _ => (blockOfCall? preset config identifier document).toList
        | _ => []) → entry' ∈ (match
        (sign preset config eip3076Policy state identifier document).1 with
        | .signed _ => (blockOfCall? preset config identifier document).toList
        | _ => []) → entry = entry' := by
      intro entry entry' now now'
      cases result : (sign preset config eip3076Policy state identifier document).1 <;>
        simp only [result, List.not_mem_nil] at now now'
      simp only [Option.mem_toList] at now now'
      rw [now] at now'
      simpa using now'
    rcases firstSigned with firstNow | firstLater <;>
      rcases secondSigned with secondNow | secondLater
    · rw [single _ _ firstNow secondNow]
    · have := signedBlocks_fresh rest _ second secondLater _
        (sameKey ▸ recorded first firstNow) sameSlot
      simpa using this
    · have := signedBlocks_fresh rest _ first firstLater _
        (sameKey.symm ▸ recorded second secondNow) sameSlot.symm
      simpa using this.symm
    · exact ih firstLater secondLater

/-- Each vote that a run signs is not slashable with a vote of the record it started with. -/
theorem signedVotes_fresh (calls : List (String × Json)) (state : SignerState) :
    ∀ signed ∈ signedVotes preset config state calls,
      ∀ vote ∈ state.protection.attestationsOf signed.1,
        vote.isSlashableWith signed.2.1.source.epoch signed.2.1.target.epoch signed.2.2 =
          false := by
  induction calls generalizing state with
  | nil => simp [signedVotes]
  | cons call rest ih =>
    obtain ⟨identifier, document⟩ := call
    intro entry member vote recorded
    simp only [signedVotes, List.mem_append] at member
    rcases member with now | later
    · split at now
      · rename_i signature result
        obtain ⟨pubkey, data, root⟩ := entry
        have named : voteOfCall? preset config identifier document = some (pubkey, data, root) :=
          by simpa using now
        exact (checkAttestationSigning_eq_ok_iff.mp (sign_vote result named).1).1 vote recorded
      · simp at now
    · exact ih _ entry later vote ((sign_keeps identifier document entry.1).2 vote recorded)

/-- Two votes that a run signs for one key and that slash each other have one signing root.

This holds from any record, whatever the calls before, between and after them. -/
theorem signingRoot_eq_of_signedVotes {calls : List (String × Json)} {state : SignerState}
    {first second : BLSPubkey × AttestationData × Root}
    (firstSigned : first ∈ signedVotes preset config state calls)
    (secondSigned : second ∈ signedVotes preset config state calls)
    (sameKey : first.1 = second.1)
    (slashable : isSlashableAttestationData first.2.1 second.2.1 = true) :
    first.2.2 = second.2.2 := by
  induction calls generalizing state with
  | nil => simp [signedVotes] at firstSigned
  | cons call rest ih =>
    obtain ⟨identifier, document⟩ := call
    simp only [signedVotes, List.mem_append] at firstSigned secondSigned
    -- A vote signed by this call enters the record that the later calls start from.
    have recorded : ∀ entry, entry ∈ (match
        (sign preset config eip3076Policy state identifier document).1 with
        | .signed _ => (voteOfCall? preset config identifier document).toList
        | _ => []) →
        ⟨entry.2.1.source.epoch, entry.2.1.target.epoch, some entry.2.2⟩ ∈
          (sign preset config eip3076Policy state identifier document).2.protection.attestationsOf
            entry.1 := by
      intro entry now
      split at now
      · rename_i signature result
        obtain ⟨pubkey, data, root⟩ := entry
        exact (sign_vote result (by simpa using now)).2
      · simp at now
    have single : ∀ entry entry', entry ∈ (match
        (sign preset config eip3076Policy state identifier document).1 with
        | .signed _ => (voteOfCall? preset config identifier document).toList
        | _ => []) → entry' ∈ (match
        (sign preset config eip3076Policy state identifier document).1 with
        | .signed _ => (voteOfCall? preset config identifier document).toList
        | _ => []) → entry = entry' := by
      intro entry entry' now now'
      cases result : (sign preset config eip3076Policy state identifier document).1 <;>
        simp only [result, List.not_mem_nil] at now now'
      simp only [Option.mem_toList] at now now'
      rw [now] at now'
      simpa using now'
    rcases firstSigned with firstNow | firstLater <;>
      rcases secondSigned with secondNow | secondLater
    · rw [single _ _ firstNow secondNow]
    · exact root_eq_of_isSlashableWith_eq_false
        (signedVotes_fresh rest _ second secondLater _ (sameKey ▸ recorded first firstNow))
        (Or.inl slashable)
    · exact (root_eq_of_isSlashableWith_eq_false
        (signedVotes_fresh rest _ first firstLater _ (sameKey.symm ▸ recorded second secondNow))
        (Or.inr slashable)).symm
    · exact ih firstLater secondLater

end EthLib.Consensus.RemoteSigningApi
