module

public import EthLib.Consensus.RelayApi
public import EthLib.Consensus.Proofs.BuilderApi
public import EthLib.Consensus.Proofs.BuilderApi.Bid
public import EthLib.Consensus.Proofs.BeaconApi.Encoding
public import EthLib.Consensus.Proofs.Proposers
public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import Std.Data.String.ToInt
-- The received bid proofs unfold how Lean builds a JSON object.
import all Lean.Data.Json.Basic

/-!
# Proofs: what a relay keeps from a submission, and the bid it serves

A submission for the slot of a store replaces the entry of its builder, whatever the values.

No other entry changes, and a submission for another slot changes nothing.

The served bid holds the header, the value, the key and, from Deneb, the commitments of the bundle.

A blinded body that carries the header of that bid unblinds with the payload of the submission.

The JSON that the writer gives for a delivered payload reads back as that payload.

So does the JSON of a received bid, whose reader takes the two timestamps out first.

A filter with no field keeps every entry.

A filter with only a slot keeps exactly the entries of that slot.

A sort by value orders the payloads that it is given, and keeps them all.

From Fulu, each entry of the listed validators names the proposer of its slot.

That proposer is the one that the state gives once the slots of the transition reach that slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz BuilderApi

variable {preset : Preset} {fork : Fork}

namespace RelayApi

/-- After a submission for the slot of the store, the entry of its builder is that submission.

This holds whatever the value of the entry before, even when it was higher. -/
theorem SubmissionStore.submit_overwrites (store : SubmissionStore preset fork)
    {request : SubmitBlockRequest preset fork} (slot : request.message.slot = store.slot) :
    (store.submit request).get request.message.builderPubkey = some request := by
  simp [SubmissionStore.submit, SubmissionStore.get, slot]

/-- A submission leaves the entries of other builders unchanged. -/
theorem SubmissionStore.submit_other (store : SubmissionStore preset fork)
    (request : SubmitBlockRequest preset fork) {pubkey : BLSPubkey}
    (other : pubkey ≠ request.message.builderPubkey) :
    (store.submit request).get pubkey = store.get pubkey := by
  unfold SubmissionStore.submit
  split
  · unfold SubmissionStore.get
    dsimp only
    rw [List.find?_cons_of_neg (by simpa using fun h => other h.symm)]
    induction store.entries with
    | nil => rfl
    | cons head rest ih =>
      by_cases same : head.message.builderPubkey = request.message.builderPubkey
      · have mine : ¬head.message.builderPubkey = pubkey := fun h => other (h.symm.trans same)
        rw [List.filter_cons_of_neg (by simpa using same),
          List.find?_cons_of_neg (by simpa using mine), ih]
      · rw [List.filter_cons_of_pos (by simpa using same)]
        by_cases mine : head.message.builderPubkey = pubkey
        · rw [List.find?_cons_of_pos (by simpa using mine),
            List.find?_cons_of_pos (by simpa using mine)]
        · rw [List.find?_cons_of_neg (by simpa using mine),
            List.find?_cons_of_neg (by simpa using mine), ih]
  · rfl

/-- A submission for another slot leaves the store as it was. -/
theorem SubmissionStore.submit_other_slot (store : SubmissionStore preset fork)
    {request : SubmitBlockRequest preset fork} (slot : request.message.slot ≠ store.slot) :
    store.submit request = store := by
  simp [SubmissionStore.submit, slot]

/-! ## The data API -/

instance : LawfulSszType BidTraceV2 :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- The JSON reader gives back every delivered payload that the writer writes. -/
theorem BidTraceV2.ofApiJson_toApiJson {entry : BidTraceV2} {document : Lean.Json}
    (wrote : BeaconApi.toApiJson entry = .ok document) :
    BeaconApi.ofApiJson BidTraceV2 document = .ok entry :=
  BeaconApi.ofApiJson_toApiJson wrote

/-- The document of a bid is a well-formed object whose names are all among the declared ones. -/
private theorem toApiJson_bid_obj (x : BidTraceV2) {document : Lean.Json}
    (wrote : BeaconApi.toApiJson x = .ok document) :
    ∃ m, document = .obj m ∧ m.WF ∧ ∀ name ∈ objectNames document,
      name ∈ BidTrace.names ++ ["block_number", "num_tx"] := by
  unfold BeaconApi.toApiJson at wrote
  simp only [SszType.desc, SszType.toValue, jsonOf] at wrote
  generalize jsonOfFields _ _ 0 _ = written at wrote
  cases written with
  | error err => simp [Bind.bind, Except.bind] at wrote
  | ok parts =>
    simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
    subst wrote
    refine ⟨Std.TreeMap.Raw.ofList ((BidTrace.names ++ ["block_number", "num_tx"]).zip parts)
      (cmp := compare), by simp only [Lean.Json.mkObj], Std.TreeMap.Raw.WF.ofList,
      fun name member => ?_⟩
    obtain ⟨pair, mem, rfl⟩ := List.mem_map.mp (objectNames_mkObj member)
    exact (List.of_mem_zip mem).1

namespace BidTraceV2WithTimestamp

/-- The decimal text of an integer reads back as that integer. -/
theorem decimalInt_toString (i : Int) : decimalInt (toString i) = i := by
  have noMinus (n : Nat) (rest : List Char) : Nat.toDigits 10 n ≠ '-' :: rest := fun h => by
    have digit := Nat.isDigit_of_mem_toDigits (c := '-') (n := n) (by decide) (by decide)
      (h ▸ List.mem_cons_self)
    exact absurd digit (by decide)
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · unfold decimalInt
    rw [Nat.toList_repr]
    split
    · next rest h => exact absurd h (noMinus _ rest)
    · rw [Nat.ofDigitChars_ten_toDigits]
      omega
  · unfold decimalInt
    simp only [String.toList_append, Nat.toList_repr]
    simp [Nat.ofDigitChars_ten_toDigits]
    omega

/-- A signed integer of 64 bits reads back from its JSON. -/
theorem readInt64_int64Json (x : Int64) : readInt64 (int64Json x) = .ok x := by
  have low := Int64.le_toInt x
  have high := Int64.toInt_lt x
  simp only [readInt64, int64Json, decimalInt_toString]
  have inside : -2 ^ 63 ≤ x.toInt ∧ x.toInt < 2 ^ 63 := ⟨low, high⟩
  simp only [true_and, Int64.ofInt_toInt, inside, ite_true]

/-- A string that the reader accepts is the one that the writer gives for its value. -/
theorem int64Json_of_readInt64 {document : Lean.Json} {x : Int64}
    (read : readInt64 document = .ok x) : document = int64Json x := by
  unfold readInt64 at read
  split at read
  · simp only at read
    split at read
    · rename_i canonical
      obtain ⟨spelled, low, high⟩ := canonical
      cases read
      simp only [int64Json, Int64.toInt_ofInt_of_le low high, spelled]
    · cases read
  · cases read

/-- The writer never fails on a received bid. -/
theorem toJson_total (entry : BidTraceV2WithTimestamp) :
    ∃ document, entry.toJson = .ok document := by
  obtain ⟨document, wrote⟩ := BeaconApi.toApiJson_total entry.bid
  obtain ⟨m, rfl, -, -⟩ := toApiJson_bid_obj entry.bid wrote
  refine ⟨.obj ((m.insert "timestamp" (int64Json entry.timestamp)).insert "timestamp_ms"
    (int64Json entry.timestampMs)), ?_⟩
  simp only [toJson, wrote, Bind.bind, Except.bind]
  rfl

/-- The JSON reader gives back every received bid that the writer writes. -/
theorem ofJson_toJson {entry : BidTraceV2WithTimestamp} {document : Lean.Json}
    (wrote : entry.toJson = .ok document) : ofJson document = .ok entry := by
  have bid := BeaconApi.toApiJson_total entry.bid
  obtain ⟨written, hb⟩ := bid
  obtain ⟨m, rfl, wf, names⟩ := toApiJson_bid_obj entry.bid hb
  have absent : ∀ name, name ∉ BidTrace.names ++ ["block_number", "num_tx"] → name ∉ m :=
    fun name out member => out (names name (mem_objectNames wf member))
  have noTs : "timestamp" ∉ m := absent _ (by decide)
  have noMs : "timestamp_ms" ∉ m := absent _ (by decide)
  simp only [toJson, hb, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
  subst wrote
  have wf₁ : (m.insert "timestamp" (int64Json entry.timestamp)).WF := wf.insert
  have wf₂ : ((m.insert "timestamp" (int64Json entry.timestamp)).insert "timestamp_ms"
      (int64Json entry.timestampMs)).WF := wf₁.insert
  have noMs₁ : "timestamp_ms" ∉ m.insert "timestamp" (int64Json entry.timestamp) := by
    rw [Std.TreeMap.Raw.mem_insert wf]
    simpa using noMs
  have first := erase_insert_equiv wf₁ noMs₁ (value := int64Json entry.timestampMs)
  have second :=
    Std.TreeMap.Raw.Equiv.erase (wf₂.erase (a := "timestamp_ms")) wf₁ first "timestamp"
  have third := erase_insert_equiv wf noTs (value := int64Json entry.timestamp)
  have same := second.trans third
  have gMs : (Lean.Json.obj ((m.insert "timestamp" (int64Json entry.timestamp)).insert
      "timestamp_ms" (int64Json entry.timestampMs))).getObjVal? "timestamp_ms"
        = .ok (int64Json entry.timestampMs) := by
    simp [Lean.Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?,
      Std.TreeMap.Raw.getElem?_insert_self wf₁]
    rfl
  have gTs : (Lean.Json.obj ((m.insert "timestamp" (int64Json entry.timestamp)).insert
      "timestamp_ms" (int64Json entry.timestampMs))).getObjVal? "timestamp"
        = .ok (int64Json entry.timestamp) := by
    simp [Lean.Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?,
      Std.TreeMap.Raw.getElem?_insert wf₁, Std.TreeMap.Raw.getElem?_insert_self wf]
    rfl
  have wfe := (wf₂.erase (a := "timestamp_ms")).erase (a := "timestamp")
  have back : BeaconApi.ofApiJson BidTraceV2 (.obj ((((m.insert "timestamp"
      (int64Json entry.timestamp)).insert "timestamp_ms" (int64Json entry.timestampMs)).erase
      "timestamp_ms").erase "timestamp")) = .ok entry.bid := by
    unfold BeaconApi.ofApiJson
    rw [valueOf_obj_of_equiv wfe wf same]
    exact BidTraceV2.ofApiJson_toApiJson hb
  unfold ofJson
  simp only [gTs, gMs, Except.toOption, back, readInt64_int64Json, Bind.bind, Except.bind,
    pure, Except.pure]

end BidTraceV2WithTimestamp

/-- The string of an order names that order. -/
theorem OrderBy.ofName?_name (order : OrderBy) : OrderBy.ofName? order.name = some order := by
  cases order <;> rfl

/-- A string names an order exactly when it is the string of that order, so others name none. -/
theorem OrderBy.ofName?_eq_some {text : String} {order : OrderBy} :
    OrderBy.ofName? text = some order ↔ order.name = text := by
  constructor
  · intro named
    unfold OrderBy.ofName? at named
    split at named <;> cases named <;> rfl
  · rintro rfl
    exact OrderBy.ofName?_name order

/-- The filter with no field keeps every delivered payload. -/
theorem DeliveredFilter.keeps_empty (entry : BidTraceV2) : ({} : DeliveredFilter).keeps entry := by
  rfl

/-- The filter with no field keeps every received bid. -/
theorem ReceivedFilter.keeps_empty (entry : BidTraceV2WithTimestamp) :
    ({} : ReceivedFilter).keeps entry := by
  rfl

/-- The filter with only a slot keeps exactly the delivered payloads of that slot. -/
theorem DeliveredFilter.keeps_slot (slot : Slot) (entry : BidTraceV2) :
    ({ slot := some slot } : DeliveredFilter).keeps entry ↔ entry.trace.slot = slot := by
  simp [DeliveredFilter.keeps, eq_comm]

/-- The filter with only a slot keeps exactly the received bids of that slot. -/
theorem ReceivedFilter.keeps_slot (slot : Slot) (entry : BidTraceV2WithTimestamp) :
    ({ slot := some slot } : ReceivedFilter).keeps entry ↔ entry.bid.trace.slot = slot := by
  simp [ReceivedFilter.keeps, eq_comm]

/-- Sorted lowest first, the values never decrease, and the payloads are those of the input. -/
theorem sortBy_ascending (entries : List BidTraceV2) :
    (sortBy .ascending entries).Pairwise (fun a b => a.trace.value ≤ b.trace.value) ∧
      (sortBy .ascending entries).Perm entries := by
  refine ⟨?_, List.mergeSort_perm _ _⟩
  have sorted := List.pairwise_mergeSort
    (le := fun a b : BidTraceV2 => decide (a.trace.value ≤ b.trace.value))
    (fun a b c first second => by
      simp only [decide_eq_true_eq] at first second ⊢
      bv_omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      bv_omega)
    entries
  simpa [sortBy] using sorted

/-- Sorted highest first, the values never increase, and the payloads are those of the input. -/
theorem sortBy_descending (entries : List BidTraceV2) :
    (sortBy .descending entries).Pairwise (fun a b => b.trace.value ≤ a.trace.value) ∧
      (sortBy .descending entries).Perm entries := by
  refine ⟨?_, List.mergeSort_perm _ _⟩
  have sorted := List.pairwise_mergeSort
    (le := fun a b : BidTraceV2 => decide (b.trace.value ≤ a.trace.value))
    (fun a b c first second => by
      simp only [decide_eq_true_eq] at first second ⊢
      bv_omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      bv_omega)
    entries
  simpa [sortBy] using sorted

/-- Payloads of equal value keep their input order, in either order of the sort. -/
theorem sortBy_stable (order : OrderBy) (entries : List BidTraceV2) (value : U256) :
    (sortBy order entries).filter (fun entry => entry.trace.value = value) =
      entries.filter (fun entry => entry.trace.value = value) := by
  -- The payloads of one value form a sublist of the input that the sort keeps in place.
  have stable (le : BidTraceV2 → BidTraceV2 → Bool)
      (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
      (total : ∀ a b, (le a b || le b a) = true)
      (equal : ∀ a b, a.trace.value = b.trace.value → le a b = true) :
      (entries.mergeSort le).filter (fun entry => entry.trace.value = value) =
        entries.filter (fun entry => entry.trace.value = value) := by
    have ordered : (entries.filter fun entry => entry.trace.value = value).Pairwise
        (fun a b => le a b = true) := by
      rw [List.pairwise_filter]
      exact List.pairwise_of_forall fun a b first second => by
        simp only [decide_eq_true_eq] at first second
        exact equal a b (first.trans second.symm)
    have kept := (List.sublist_mergeSort trans total ordered List.filter_sublist).filter
      (fun entry : BidTraceV2 => decide (entry.trace.value = value))
    rw [List.filter_filter, show (fun entry : BidTraceV2 =>
        (decide (entry.trace.value = value) && decide (entry.trace.value = value)))
          = fun entry => decide (entry.trace.value = value) by simp] at kept
    exact (kept.eq_of_length ((List.mergeSort_perm _ _).filter _).length_eq.symm).symm
  cases order
  · exact stable _ (fun a b c first second => by
      simp only [decide_eq_true_eq] at first second ⊢
      bv_omega) (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      bv_omega) fun a b same => by simp [same]
  · exact stable _ (fun a b c first second => by
      simp only [decide_eq_true_eq] at first second ⊢
      bv_omega) (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      bv_omega) fun a b same => by simp [same]

/-! ## The validators that a relay lists -/

instance : LawfulSszType ValidatorsResponseEntry :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- The JSON reader gives back every entry that the writer writes. -/
theorem ValidatorsResponseEntry.ofApiJson_toApiJson {entry : ValidatorsResponseEntry}
    {document : Lean.Json} (wrote : BeaconApi.toApiJson entry = .ok document) :
    BeaconApi.ofApiJson ValidatorsResponseEntry document = .ok entry :=
  BeaconApi.ofApiJson_toApiJson wrote

/-- An entry is in the list of a schedule exactly when it lies in its slots and names its proposer.

Its registration must also be the one kept for the key of that proposer. -/
theorem mem_scheduledEntries {schedule : Slot → Option ValidatorIndex}
    {keyOf : ValidatorIndex → Option BLSPubkey} {registry : Registry} {first count : Nat}
    {entry : ValidatorsResponseEntry} :
    entry ∈ scheduledEntries schedule keyOf registry first count ↔
      first ≤ entry.slot.toNat ∧ entry.slot.toNat < first + count ∧
        schedule entry.slot = some entry.validatorIndex ∧
        ∃ key, keyOf entry.validatorIndex = some key ∧ registry.find? key = some entry.entry := by
  unfold scheduledEntries
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨offset, member, made⟩
    split at made
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at made
      obtain ⟨index, scheduled, key, keyed, signed, found, rfl⟩ := made
      have toNat : UInt64.toNat ⟨⟨first + offset, ‹_›⟩⟩ = first + offset := rfl
      simp only [toNat]
      exact ⟨by omega, by simp at member; omega, scheduled, key, keyed, found⟩
    · cases made
  · rintro ⟨low, high, scheduled, key, keyed, found⟩
    refine ⟨entry.slot.toNat - first, List.mem_range.mpr (by omega), ?_⟩
    have fits : first + (entry.slot.toNat - first) < 2 ^ 64 := by
      have := entry.slot.toNat_lt; omega
    have same : (⟨⟨first + (entry.slot.toNat - first), fits⟩⟩ : Slot) = entry.slot :=
      UInt64.toNat_inj.mp (by change first + (entry.slot.toNat - first) = _; omega)
    simp only [fits, ↓reduceDIte, same, scheduled, keyed, found, Option.bind_eq_bind,
      Option.bind_some]

/-- The slots of the entries of a schedule are distinct. -/
theorem scheduledEntries_slots_nodup (schedule : Slot → Option ValidatorIndex)
    (keyOf : ValidatorIndex → Option BLSPubkey) (registry : Registry) (first count : Nat) :
    ((scheduledEntries schedule keyOf registry first count).map (·.slot)).Nodup := by
  unfold scheduledEntries
  rw [List.map_filterMap]
  refine List.Pairwise.filterMap _ ?_ List.nodup_range
  have slotOf : ∀ offset slot, (fun offset => Option.map (·.slot) (if fits :
      first + offset < 2 ^ 64 then do
        let slot : Slot := ⟨⟨first + offset, fits⟩⟩
        let index ← schedule slot
        let key ← keyOf index
        let entry ← registry.find? key
        some (⟨slot, index, entry⟩ : ValidatorsResponseEntry)
      else none)) offset = some slot → slot.toNat = first + offset := by
    intro offset slot member
    obtain ⟨entry, made, rfl⟩ := Option.map_eq_some_iff.mp member
    split at made
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at made
      obtain ⟨_, _, _, _, _, _, rfl⟩ := made
      rfl
    · cases made
  intro one two apart slot made slot' made' same
  have := slotOf one slot made
  have := slotOf two slot' made'
  subst same
  omega

/-- For any schedule, its entries over an epoch and the next are what a relay serves. -/
theorem scheduledEntries_sound (schedule : Slot → Option ValidatorIndex)
    (keyOf : ValidatorIndex → Option BLSPubkey) (registry : Registry) (epoch : Epoch) :
    ValidatorsResponse.Sound preset schedule keyOf registry epoch
      (scheduledEntries schedule keyOf registry (epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
        (2 * preset.SLOTS_PER_EPOCH.toNat)) := by
  constructor
  · intro entry member
    obtain ⟨low, high, scheduled, registered⟩ := mem_scheduledEntries.mp member
    exact ⟨⟨low, by rw [Nat.add_mul]; omega⟩, scheduled, registered⟩
  · intro slot index key signed within scheduled keyed found
    have member : (⟨slot, index, signed⟩ : ValidatorsResponseEntry) ∈
        scheduledEntries schedule keyOf registry (epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
          (2 * preset.SLOTS_PER_EPOCH.toNat) :=
      mem_scheduledEntries.mpr ⟨within.1, by have := within.2; rw [Nat.add_mul] at this; omega,
        scheduled, key, keyed, found⟩
    have counted := (scheduledEntries_slots_nodup schedule keyOf registry _ _).count_of_mem
      (List.mem_map_of_mem (f := (·.slot)) member)
    rw [List.count, List.countP_map] at counted
    refine Eq.trans (List.countP_congr fun x _ => ?_) counted
    simp

/-- From Fulu, the list that a relay builds from its state is what it serves, by the lookahead. -/
theorem validatorsResponse_sound (state : BeaconState preset fork) (fulu : .fusaka ≤ fork)
    (registry : Registry) :
    ValidatorsResponse.Sound preset (lookaheadSchedule state fulu) (validatorPubkey? state)
      registry (getCurrentEpoch state) (validatorsResponse state fulu registry) :=
  scheduledEntries_sound _ _ _ _

/-! ## The lookahead of proposers through the slots -/

section Lookahead

variable {config : Config} {checks : SignatureChecks} {state after : BeaconState preset fork}

/-- Two states with the same lookahead of proposers. -/
private def Kept (state after : BeaconState preset fork) : Prop :=
  after.proposerLookahead = state.proposerLookahead

/-- Every state keeps its own lookahead. -/
private theorem Kept.refl (state : BeaconState preset fork) : Kept state state :=
  rfl

/-- Two steps in a row that keep the lookahead keep it. -/
private theorem Kept.trans {first second third : BeaconState preset fork}
    (one : Kept first second) (two : Kept second third) : Kept first third :=
  Eq.trans two one

/-- A fold whose every step keeps the lookahead keeps it. -/
private theorem Kept.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (kept : ∀ s x s', step s x = .ok s' → Kept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Kept state after :=
  foldlM_ok_invariant (Kept state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (Kept.refl state) computed

/-- A step that keeps the inputs of a payload keeps the lookahead. -/
private theorem Kept.of_payloadInputs (inputs : PayloadInputs state after) : Kept state after :=
  inputs.proposerLookahead

/-- Adding a validator keeps the lookahead. -/
private theorem kept_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    Kept state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    rfl
  split at computed
  · cases computed
    rfl
  · cases computed

/-- A pending deposit keeps the lookahead. -/
private theorem kept_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    Kept state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact Kept.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact kept_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Kept.refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact Kept.of_payloadInputs (payloadInputs_increaseBalance computed)

/-- Justification and finalization keep the lookahead. -/
private theorem kept_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) : Kept state after := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · exact Kept.refl _
  · exact congrArg (·.proposerLookahead)
      (weighJustificationAndFinalization_checkpoints weighed).2.2.2

/-- The inactivity updates keep the lookahead. -/
private theorem kept_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) : Kept state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    rfl

/-- The rewards and penalties keep the lookahead. -/
private theorem kept_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) : Kept state after := by
  have deltas : ∀ {state after : BeaconState preset fork} {all : Array Gwei × Array Gwei},
      applyAllDeltas state all = .ok after → Kept state after := fun computed =>
    Kept.foldlM (fun _ _ _ ok => by
      simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, raised, lowered⟩ := ok
      exact (Kept.of_payloadInputs (payloadInputs_increaseBalance raised)).trans
        (Kept.of_payloadInputs (payloadInputs_decreaseBalance lowered))) computed
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact Kept.foldlM (fun _ _ _ ok => deltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact deltas applied

/-- The registry updates keep the lookahead. -/
private theorem kept_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : Kept state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine Kept.foldlM (fun _ _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact Kept.of_payloadInputs (payloadInputs_setValidatorAt set)
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact Kept.of_payloadInputs (payloadInputs_initiateValidatorExit exited)
    split at ok
    · exact Kept.of_payloadInputs (payloadInputs_setValidatorAt (liftAccessor_ok.mp ok))
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Kept.refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, updatedOk, activated⟩ := computed
  refine (Kept.foldlM (fun _ _ _ ok => ?_) updatedOk).trans
    (Kept.foldlM (fun _ _ _ ok => ?_) activated)
  · simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, markedOk, ok⟩ := ok
    have set := Kept.of_payloadInputs (payloadInputs_setValidatorAt markedOk)
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact set.trans (Kept.of_payloadInputs (payloadInputs_initiateValidatorExit exited))
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ set
  · simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, set⟩ := ok
    exact Kept.of_payloadInputs (payloadInputs_setValidator set)

/-- The slashing penalties keep the lookahead. -/
private theorem kept_processSlashings (computed : processSlashings state = .ok after) :
    Kept state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine Kept.foldlM (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact Kept.of_payloadInputs (payloadInputs_decreaseBalance lowered)
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ Kept.refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Kept.refl _
  · refine Kept.foldlM (fun _ _ _ ok => ?_) computed
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, _, _, lowered⟩ := ok
        exact Kept.of_payloadInputs (payloadInputs_decreaseBalance lowered)
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ Kept.refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Kept.refl _

/-- The reset of the deposit votes keeps the lookahead. -/
private theorem kept_processEth1DataReset {hegota : fork < .hegota}
    (computed : processEth1DataReset hegota state = .ok after) : Kept state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

/-- A pass over the pending deposits keeps the lookahead. -/
private theorem kept_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      Kept state pass.1.state :=
  fun computed => passPendingDeposits_of Kept Kept.refl
    (fun one two => one.trans two) (fun ok => kept_applyPendingDeposit ok) computed

/-- A pass over the pending consolidations keeps the lookahead. -/
private theorem kept_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      Kept state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Kept.refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact kept_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact Kept.refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact ((Kept.of_payloadInputs (payloadInputs_decreaseBalance loweredOk)).trans
      (Kept.of_payloadInputs (payloadInputs_increaseBalance raisedOk))).trans
      (kept_passPendingConsolidations (result := (passed, read)) passedOk)

/-- The updates of the effective balances keep the lookahead. -/
private theorem kept_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : Kept state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine Kept.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact Kept.of_payloadInputs (payloadInputs_setValidatorAt set)

/-- The historical summaries update keeps the lookahead. -/
private theorem kept_processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (computed : processHistoricalSummariesUpdate state capella = .ok after) :
    Kept state after := by
  unfold processHistoricalSummariesUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals rfl

/-- The sync committee updates keep the lookahead. -/
private theorem kept_processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (computed : processSyncCommitteeUpdates state altair = .ok after) : Kept state after := by
  unfold processSyncCommitteeUpdates at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals rfl

/-- The move of the window of payload committees keeps the lookahead. -/
private theorem kept_processPtcWindow {gloas : .glamsterdam ≤ fork}
    (computed : processPtcWindow state gloas = .ok after) : Kept state after := by
  simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

/-- From Fulu, the epoch transition moves each kept proposer of the lookahead back by one epoch. -/
theorem processEpoch_proposerLookahead (fulu : .fusaka ≤ fork)
    (computed : processEpoch config checks state = .ok after) {position : Nat}
    (inside : position + preset.SLOTS_PER_EPOCH.toNat <
      (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) :
    (after.proposerLookahead fulu)[position]? =
      (state.proposerLookahead fulu)[position + preset.SLOTS_PER_EPOCH.toNat]? := by
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) fulu
  have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) fulu
  obtain ⟨cleared, mixed, rooted, rotated, synced, looked, initial, mixedOk, rootedOk, rotation,
    syncedOk, lookedOk, windowed⟩ := processEpoch_randaoCut computed
  have head : Kept state cleared := by
    apply initial.transport Kept Kept.refl (fun a b => a.trans b)
    intro k member a b ok
    have edge := EpochStage.action_cases.mp ok
    cases k <;> simp only [EpochStage.Edge, altair, ↓reduceDIte] at edge
    · exact kept_processJustificationAndFinalization edge
    · exact kept_processInactivityUpdates edge
    · exact kept_processRewardsAndPenalties edge
    · exact kept_processRegistryUpdates edge
    · exact kept_processSlashings edge
    · split at edge
      · exact kept_processEth1DataReset edge
      · exact edge ▸ Kept.refl _
    · split at edge
      · unfold processPendingDeposits at edge
        simp only [bind, Except.bind, pure, Except.pure] at edge
        repeat' (split at edge <;> try cases edge)
        all_goals exact (kept_passPendingDeposits ‹_›).trans rfl
      · exact edge ▸ Kept.refl _
    · split at edge
      · unfold processPendingConsolidations at edge
        simp only [bind, Except.bind, pure, Except.pure] at edge
        repeat' (split at edge <;> try cases edge)
        all_goals exact (kept_passPendingConsolidations ‹_›).trans rfl
      · exact edge ▸ Kept.refl _
    · split at edge
      · rw [processBuilderPendingPayments_eq edge]
        rfl
      · exact edge ▸ Kept.refl _
    · exact kept_processEffectiveBalanceUpdates edge
    · obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge
      rfl
    all_goals simp [EpochStage.prefixStages] at member
  simp only [EpochStage.Edge, altair, capella, ↓reduceDIte] at rootedOk rotation syncedOk
  simp only [EpochStage.Edge, fulu, ↓reduceDIte] at lookedOk windowed
  have middle : Kept cleared synced := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    subst rotation
    exact (kept_processHistoricalSummariesUpdate rootedOk).trans
      ((show Kept rooted (processParticipationFlagUpdates rooted altair) from rfl).trans
        (kept_processSyncCommitteeUpdates syncedOk))
  have tail : Kept looked after := by
    split at windowed
    · exact kept_processPtcWindow windowed
    · exact windowed ▸ Kept.refl _
  obtain ⟨_, _, _, _, shifted⟩ := processProposerLookahead_spec lookedOk
  have before : synced.proposerLookahead = state.proposerLookahead := head.trans middle
  rw [show after.proposerLookahead = looked.proposerLookahead from tail, ← before,
    Vector.getElem?_eq_getElem (by omega), Vector.getElem?_eq_getElem inside,
    shifted _ (by omega)]
  simp only [Vector.size, inside, ↓reduceDIte]

/-- Two states whose lookaheads agree on each slot that both cover, from Fulu.

The epoch of the second state starts no earlier than that of the first. -/
private def Shifted (state after : BeaconState preset fork) : Prop :=
  currentEpochStart state ≤ currentEpochStart after ∧
    ∀ (fulu : .fusaka ≤ fork) (slot : Nat), currentEpochStart after ≤ slot →
      slot < currentEpochStart state +
        (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat →
      (after.proposerLookahead fulu)[slot - currentEpochStart after]? =
        (state.proposerLookahead fulu)[slot - currentEpochStart state]?

/-- Every state agrees with itself. -/
private theorem Shifted.refl (state : BeaconState preset fork) : Shifted state state :=
  ⟨Nat.le_refl _, fun _ _ _ _ => rfl⟩

/-- Two agreements in a row give one. -/
private theorem Shifted.trans {first second third : BeaconState preset fork}
    (one : Shifted first second) (two : Shifted second third) : Shifted first third :=
  ⟨Nat.le_trans one.1 two.1, fun fulu slot low high => by
    rw [two.2 fulu slot low (by have := one.1; omega),
      one.2 fulu slot (by have := two.1; omega) high]⟩

/-- The first slot of the epoch of a state, by the slot of the state. -/
private theorem currentEpochStart_eq (state : BeaconState preset fork) :
    currentEpochStart state =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat := by
  simp [currentEpochStart, getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]

/-- One slot keeps the proposer of each slot that both lookaheads cover. -/
private theorem shifted_advanceSlot (computed : advanceSlot config checks state = .ok after) :
    Shifted state after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have startAfter : currentEpochStart { epoched with slot := next } =
      (state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [currentEpochStart_eq, sum]
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have mod : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have := congrArg UInt64.toNat boundary
      simpa [UInt64.toNat_mod, sum] using this
    have up := Nat.succ_div_of_mod_eq_zero mod
    rw [up, Nat.add_mul, Nat.one_mul] at startAfter
    refine ⟨by rw [startAfter, currentEpochStart_eq]; omega, fun fulu slot low high => ?_⟩
    rw [startAfter] at low ⊢
    rw [currentEpochStart_eq] at high ⊢
    have moved := processEpoch_proposerLookahead fulu epochedOk
      (position := slot - (state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat *
        preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat)) (by omega)
    rw [show slot - state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat =
      slot - (state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_EPOCH.toNat) + preset.SLOTS_PER_EPOCH.toNat by omega]
    exact moved
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    rename_i inside
    have mod : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 := fun zero =>
      inside (UInt64.toNat_inj.mp (by simpa [UInt64.toNat_mod, sum] using zero))
    rw [Nat.succ_div_of_mod_ne_zero mod, ← currentEpochStart_eq] at startAfter
    exact ⟨Nat.le_of_eq startAfter.symm, fun _ _ _ _ => by rw [startAfter]⟩

/-- Any count of slots keeps the proposer of each slot that both lookaheads cover. -/
private theorem shifted_advanceSlots :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after → Shifted state after
  | 0, _, _, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Shifted.refl _
  | count + 1, _, _, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨_, first, rest⟩ := computed
    exact (shifted_advanceSlot first).trans (shifted_advanceSlots count rest)

/-- From Fulu, the proposer of a state is the entry of its lookahead at its slot. -/
private theorem getBeaconProposerIndex_of_lookahead (fulu : .fusaka ≤ fork)
    (nonzero : preset.SLOTS_PER_EPOCH ≠ 0) {index : ValidatorIndex}
    (found : (state.proposerLookahead fulu)[state.slot.toNat - currentEpochStart state]? =
      some index) :
    getBeaconProposerIndex state = .ok index := by
  have position : (state.slot % preset.SLOTS_PER_EPOCH).toNat =
      state.slot.toNat - currentEpochStart state := by
    rw [UInt64.toNat_mod, currentEpochStart_eq]
    have := Nat.mod_add_div' state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    omega
  unfold getBeaconProposerIndex
  simp only [fulu, nonzero, ↓reduceDIte, position]
  rw [Vector.getElem?_eq_some_iff] at found
  obtain ⟨_, found⟩ := found
  rw [found]
  rfl

/-- From Fulu, an entry of the list lies in the lookahead of the state, at its slot. -/
private theorem lookahead_of_mem {fulu : .fusaka ≤ fork} {registry : Registry}
    {entry : ValidatorsResponseEntry} (listed : entry ∈ validatorsResponse state fulu registry) :
    preset.SLOTS_PER_EPOCH ≠ 0 ∧ currentEpochStart state ≤ entry.slot.toNat ∧
      (state.proposerLookahead fulu)[entry.slot.toNat - currentEpochStart state]? =
        some entry.validatorIndex := by
  obtain ⟨low, high, scheduled, -⟩ := mem_scheduledEntries.mp listed
  refine ⟨fun zero => ?_, low, ?_⟩
  · simp only [zero, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at high
    omega
  · unfold lookaheadSchedule at scheduled
    simp only [low, high, and_self, ↓reduceIte] at scheduled
    exact scheduled

end Lookahead

/-- From Fulu, each entry after the slot of the state names the proposer of its slot.

The proposer is that of the state that the slots of the transition reach, when they succeed. -/
theorem validatorsResponse_proposer {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {fulu : .fusaka ≤ fork} {registry : Registry}
    {entry : ValidatorsResponseEntry} (listed : entry ∈ validatorsResponse state fulu registry)
    (advanced : processSlots config checks state entry.slot = .ok after) :
    getBeaconProposerIndex after = .ok entry.validatorIndex := by
  obtain ⟨nonzero, low, found⟩ := lookahead_of_mem listed
  obtain ⟨-, reached⟩ := processSlots_slot advanced
  have shifted : Shifted state after := by
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at advanced
    obtain ⟨_, _, run⟩ := advanced
    exact shifted_advanceSlots _ run
  have inside : entry.slot.toNat - currentEpochStart state <
      (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    obtain ⟨bound, -⟩ := Vector.getElem?_eq_some_iff.mp found
    exact bound
  apply getBeaconProposerIndex_of_lookahead fulu nonzero
  rw [reached, shifted.2 fulu entry.slot.toNat
    (by rw [currentEpochStart_eq, reached]; exact Nat.div_mul_le_self _ _) (by omega)]
  exact found

/-- From Fulu, an entry for the slot of the state names the proposer of the state. -/
theorem validatorsResponse_proposer_self {state : BeaconState preset fork}
    {fulu : .fusaka ≤ fork} {registry : Registry} {entry : ValidatorsResponseEntry}
    (listed : entry ∈ validatorsResponse state fulu registry) (current : entry.slot = state.slot) :
    getBeaconProposerIndex state = .ok entry.validatorIndex := by
  obtain ⟨nonzero, -, found⟩ := lookahead_of_mem listed
  rw [current] at found
  exact getBeaconProposerIndex_of_lookahead fulu nonzero found

end RelayApi

/-- The served bid always computes. -/
theorem SubmitBlockRequest.bid_total (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) :
    ∃ bid, request.bid range pubkey = .ok bid :=
  getBid_total _ _ _ _ _

/-- The served bid holds the header of the payload of the submission. -/
theorem SubmitBlockRequest.bid_header (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) :
    BuilderBid.header <$> request.bid range pubkey = request.executionPayload.header :=
  getBid_header _ _ _ _ _

/-- The served bid holds the value of the bid trace and the key it is served under. -/
theorem SubmitBlockRequest.bid_value_pubkey (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) :
    (fun bid => (bid.value, bid.pubkey)) <$> request.bid range pubkey =
      .ok (request.message.value, pubkey) := by
  obtain ⟨header, made⟩ := ExecutionPayload.header_total request.executionPayload
  simp [SubmitBlockRequest.bid, getBid, made, bind, Except.bind, pure, Except.pure, Functor.map,
    Except.map]

/-- From Deneb, the served bid holds the commitments of the blobs bundle of the submission. -/
theorem SubmitBlockRequest.bid_commitments (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) (deneb : .dencun ≤ fork) :
    (fun bid => bid.blobKzgCommitments deneb) <$> request.bid range pubkey =
      .ok (.ofSszList (request.blobsBundle ⟨deneb, range.2⟩).commitments) := by
  obtain ⟨header, made⟩ := ExecutionPayload.header_total request.executionPayload
  simp [SubmitBlockRequest.bid, getBid, made, bind, Except.bind, pure, Except.pure, Functor.map,
    Except.map]

/-- From Electra, the served bid holds the requests of the submission. -/
theorem SubmitBlockRequest.bid_requests (request : SubmitBlockRequest preset fork)
    (range : HasBuilderApi fork) (pubkey : BLSPubkey) (electra : .pectra ≤ fork) :
    (fun bid => bid.executionRequests electra) <$> request.bid range pubkey =
      .ok (request.executionRequests ⟨electra, range.2⟩) := by
  obtain ⟨header, made⟩ := ExecutionPayload.header_total request.executionPayload
  simp [SubmitBlockRequest.bid, getBid, made, bind, Except.bind, pure, Except.pure, Functor.map,
    Except.map]

/-- A blinded body that carries the header of the served bid unblinds with the payload.

The unblinded body holds the payload of the submission. -/
theorem SubmitBlockRequest.bid_unblind {request : SubmitBlockRequest preset fork}
    {range : HasBuilderApi fork} {pubkey : BLSPubkey} {bid : BuilderBid preset fork}
    (served : request.bid range pubkey = .ok bid) {body : BlindedBeaconBlockBody preset fork}
    (carries : body.executionPayloadHeader range = bid.header) :
    ∃ full, body.unblind range request.executionPayload = .ok full ∧
      full.executionPayload range = request.executionPayload := by
  have computed : request.executionPayload.header = .ok bid.header := by
    rw [← SubmitBlockRequest.bid_header request range pubkey, served]
    rfl
  simp only [BlindedBeaconBlockBody.unblind, computed, carries, ↓reduceIte]
  exact ⟨_, rfl, rfl⟩

end EthLib.Consensus
