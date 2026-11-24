module

public import EthLib.Consensus.BeaconApi.LightClient
public import EthLib.Consensus.Proofs.ForkDigest
public import EthLib.Consensus.Proofs.LightClient.Containers
public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Consensus.Proofs.BeaconApi.Responses
import EthLib.Base.Proofs.MapM
import EthLib.Consensus.Proofs.BeaconApi.Encoding

/-!
# Proofs: the light client answers of the Beacon API

Which updates a range answer holds, how their SSZ chunks round trip, and when each answer refuses.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Serialization.Ssz

variable {preset : Preset}

/-- The run of known updates from a period holds at most the given number of updates. -/
private theorem updatesFrom_length_le {α : Type} (known : Std.TreeMap UInt64 α)
    (startPeriod count : UInt64) :
    ∀ period bound, (updatesFrom known startPeriod count period bound).length ≤ bound
  | _, 0 => by simp [updatesFrom]
  | period, bound + 1 => by
    have rest := updatesFrom_length_le known startPeriod count (period + 1) bound
    unfold updatesFrom
    split
    · split
      · simp only [List.length_cons]
        omega
      · simp
    · simp

/-- Entry `j` of the run from a period is the known update of the period `j` after it.

That period is below the size of 64 bits and lies in the range. -/
private theorem updatesFrom_getElem {α : Type} (known : Std.TreeMap UInt64 α)
    (startPeriod count : UInt64) :
    ∀ period bound j (h : j < (updatesFrom known startPeriod count period bound).length),
      period + j < UInt64.size ∧ InCountRange startPeriod count (UInt64.ofNat (period + j)) ∧
        known[UInt64.ofNat (period + j)]? =
          some (updatesFrom known startPeriod count period bound)[j]
  | _, 0, j, h => by simp [updatesFrom] at h
  | period, bound + 1, j, h => by
    by_cases hc : period < UInt64.size ∧ InCountRange startPeriod count (UInt64.ofNat period)
    · cases hk : known[UInt64.ofNat period]? with
      | none => simp [updatesFrom, hc, hk] at h
      | some update =>
        cases j with
        | zero => simp [updatesFrom, hc, hk]
        | succ j =>
          have hlen : j < (updatesFrom known startPeriod count (period + 1) bound).length := by
            simpa [updatesFrom, hc, hk] using h
          obtain ⟨small, range, value⟩ :=
            updatesFrom_getElem known startPeriod count (period + 1) bound j hlen
          rw [show period + (j + 1) = period + 1 + j by omega]
          simpa [updatesFrom, hc, hk] using And.intro small (And.intro range value)
    · simp [updatesFrom, hc] at h

/-- Updates of consecutive periods from a period, each known and in the range, start the run. -/
private theorem prefix_updatesFrom {α : Type} (known : Std.TreeMap UInt64 α)
    (startPeriod count : UInt64) :
    ∀ period bound (values : List α), values.length ≤ bound →
      (∀ j (h : j < values.length), period + j < UInt64.size ∧
        InCountRange startPeriod count (UInt64.ofNat (period + j)) ∧
          known[UInt64.ofNat (period + j)]? = some values[j]) →
      values <+: updatesFrom known startPeriod count period bound
  | _, _, [], _, _ => List.nil_prefix
  | _, 0, _ :: _, bounded, _ => by simp at bounded
  | period, bound + 1, value :: values, bounded, each => by
    obtain ⟨small, range, known_value⟩ := each 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at small range known_value
    have rest := prefix_updatesFrom known startPeriod count (period + 1) bound values
      (by simp only [List.length_cons] at bounded; omega) fun j h => by
        obtain ⟨small', range', value'⟩ := each (j + 1) (by simp only [List.length_cons]; omega)
        rw [show period + 1 + j = period + (j + 1) by omega]
        exact ⟨small', range', by simpa using value'⟩
    simp only [updatesFrom, small, range, and_self, ite_true, known_value, List.cons_prefix_cons,
      true_and]
    exact rest

/-- What the search for the earliest known period of the range finds, when it finds one.

It is a known period of the range, and no known period of the range comes before it. -/
private theorem find?_known_eq_some {α : Type} {known : Std.TreeMap UInt64 α}
    {startPeriod count first : UInt64} {value : α}
    (found : known.toList.find? (fun entry => decide (InCountRange startPeriod count entry.1)) =
      some (first, value)) :
    known[first]? = some value ∧ InCountRange startPeriod count first ∧
      ∀ period, InCountRange startPeriod count period → period ∈ known → first ≤ period := by
  obtain ⟨range, before, after, split, skipped⟩ := List.find?_eq_some_iff_append.mp found
  have sorted : known.toList.Pairwise (fun a b => a.1 < b.1) :=
    known.ordered_keys_toList.imp fun h => compareOfLessAndEq_eq_lt.mp h
  have mem : (first, value) ∈ known.toList :=
    split ▸ List.mem_append_right _ List.mem_cons_self
  refine ⟨Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp mem, by simpa using range, ?_⟩
  intro period in_range known_mem
  have entry : (period, known[period]) ∈ known.toList :=
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr
      (Std.TreeMap.getElem?_eq_some_getElem known_mem)
  rw [split] at entry sorted
  rcases List.mem_append.mp entry with early | late
  · have := skipped _ early
    simp [in_range] at this
  · rcases List.mem_cons.mp late with same | later
    · rw [show period = first from congrArg Prod.fst same]
      exact UInt64.le_refl _
    · exact UInt64.le_of_lt
        (List.rel_of_pairwise_cons (List.pairwise_append.mp sorted).2.1 later)

/-- When the search finds nothing, the node knows no period of the range. -/
private theorem find?_known_eq_none {α : Type} {known : Std.TreeMap UInt64 α}
    {startPeriod count : UInt64}
    (found : known.toList.find? (fun entry => decide (InCountRange startPeriod count entry.1)) =
      none)
    (period : UInt64) (in_range : InCountRange startPeriod count period) : period ∉ known := by
  intro known_mem
  have entry : (period, known[period]) ∈ known.toList :=
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr
      (Std.TreeMap.getElem?_eq_some_getElem known_mem)
  exact List.find?_eq_none.mp found _ entry (by simpa using in_range)

/-- In periods where each is the one after the one before it, each is the first plus its index. -/
private theorem toNat_of_consecutive {periods : List UInt64}
    (next : ∀ i (h : i + 1 < periods.length), periods[i + 1].toNat = periods[i].toNat + 1) :
    ∀ j (h : j < periods.length), periods[j].toNat = (periods[0]'(by omega)).toNat + j
  | 0, _ => rfl
  | j + 1, h => by
    rw [next j h, toNat_of_consecutive next j (by omega)]
    omega

/-- The answers that the source accepts are the starts of the longest one.

The empty answer is accepted only when the longest one is empty too. -/
theorem isUpdatesAnswer_iff {α : Type} (known : Std.TreeMap UInt64 α)
    (startPeriod count : UInt64) (answer : List α) :
    IsUpdatesAnswer known startPeriod count answer ↔
      answer <+: updatesInRange known startPeriod count ∧
        (answer = [] → updatesInRange known startPeriod count = []) := by
  rcases found : known.toList.find? (fun entry => decide (InCountRange startPeriod count entry.1))
    with _ | ⟨first, value⟩
  · -- The range has no known period, so only the empty answer is accepted.
    have none_known := find?_known_eq_none found
    simp only [updatesInRange, found, List.prefix_nil, implies_true, and_true]
    constructor
    · rintro ⟨periods, values, range, -, -, -⟩
      cases periods with
      | nil => simpa using values.symm
      | cons period _ =>
        obtain ⟨update, hupdate⟩ : ∃ update, known[period]? = some update := by
          have := values ▸ List.mem_map_of_mem (f := (known[·]?)) List.mem_cons_self
          obtain ⟨update, -, h⟩ := List.mem_map.mp this
          exact ⟨update, h.symm⟩
        exact absurd (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by simp [hupdate]))
          (none_known period (range period List.mem_cons_self))
    · rintro rfl
      exact ⟨[], by simp, by simp, by simp,
        fun period range known_mem => absurd known_mem (none_known period range), by simp⟩
  · obtain ⟨known_first, first_range, earliest⟩ := find?_known_eq_some found
    simp only [updatesInRange, found]
    have first_small : first.toNat < UInt64.size := first.toNat_lt
    have first_back : UInt64.ofNat first.toNat = first := UInt64.ofNat_toNat
    have positive : 0 < lightClientUpdatesLimit count := by
      have : (128 : UInt64).toNat = 128 := rfl
      simp only [lightClientUpdatesLimit, InCountRange, MAX_REQUEST_LIGHT_CLIENT_UPDATES]
        at first_range ⊢
      omega
    -- The run starts with the update of the first period, so it is not empty.
    have run_ne :
        updatesFrom known startPeriod count first.toNat (lightClientUpdatesLimit count) ≠ [] := by
      obtain ⟨limit, hlimit⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
      rw [hlimit]
      simp [updatesFrom, first_small, first_back, first_range, known_first]
    constructor
    · rintro ⟨periods, values, range, next, head, bounded⟩
      have same_length : periods.length = answer.length := by
        simpa using congrArg List.length values
      obtain ⟨start, hstart, start_le⟩ :=
        head first first_range (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by simp [known_first]))
      have nonempty : 0 < periods.length := by
        cases periods with
        | nil => simp at hstart
        | cons _ _ => simp
      have hzero : periods[0] = start := by
        cases periods with
        | nil => simp at nonempty
        | cons _ _ => simpa using hstart
      -- Each period of the answer is known, so the first one is the earliest known period.
      have known_at : ∀ j (h : j < periods.length),
          known[periods[j]]? = some (answer[j]'(by omega)) := by
        intro j h
        have := congrArg (·[j]?) values
        simpa [List.getElem?_map, List.getElem?_eq_getElem h,
          List.getElem?_eq_getElem (same_length ▸ h)] using this
      have start_eq : start = first := by
        have := known_at 0 nonempty
        rw [hzero] at this
        exact UInt64.le_antisymm start_le
          (earliest start (hzero ▸ range _ (List.getElem_mem nonempty))
            (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by simp [this])))
      refine ⟨prefix_updatesFrom known startPeriod count first.toNat _ answer bounded
        fun j h => ?_, fun empty => ?_⟩
      · have hj : j < periods.length := same_length ▸ h
        have at_j := toNat_of_consecutive next j hj
        rw [hzero, start_eq] at at_j
        have back : UInt64.ofNat (first.toNat + j) = periods[j] := by
          rw [← at_j]
          exact UInt64.ofNat_toNat
        rw [back]
        exact ⟨at_j ▸ periods[j].toNat_lt, range _ (List.getElem_mem hj), known_at j hj⟩
      · subst empty
        have := same_length ▸ nonempty
        simp at this
    · rintro ⟨pre, nonempty⟩
      have long := pre.length_le
      have short := updatesFrom_length_le known startPeriod count first.toNat
        (lightClientUpdatesLimit count)
      refine ⟨(List.range answer.length).map fun j => UInt64.ofNat (first.toNat + j), ?_, ?_, ?_,
        ?_, by omega⟩
      · refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
        simp only [List.length_map, List.length_range] at h₁ h₂
        have entry := updatesFrom_getElem known startPeriod count first.toNat
          (lightClientUpdatesLimit count) j (by omega)
        simp only [List.getElem_map, List.getElem_range, entry.2.2, pre.getElem h₂]
      · intro period mem
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp mem
        exact (updatesFrom_getElem known startPeriod count first.toNat
          (lightClientUpdatesLimit count) j (by simp at hj; omega)).2.1
      · intro i h
        simp only [List.length_map, List.length_range] at h
        have small := (updatesFrom_getElem known startPeriod count first.toNat
          (lightClientUpdatesLimit count) (i + 1) (by omega)).1
        simp only [List.getElem_map, List.getElem_range, UInt64.toNat_ofNat_of_lt' small,
          UInt64.toNat_ofNat_of_lt' (show first.toNat + i < UInt64.size by omega)]
        omega
      · intro period range known_mem
        have answer_ne : answer ≠ [] := fun empty => run_ne (nonempty empty)
        obtain ⟨update, rest, rfl⟩ := List.exists_cons_of_ne_nil answer_ne
        exact ⟨first, by simp [List.head?_range, first_back], earliest period range known_mem⟩

/-- The longest answer to an updates request is one that the source accepts.

It holds the known updates of the range from its earliest known period, with no gap, to the limit.
-/
theorem updatesInRange_answer {α : Type} (known : Std.TreeMap UInt64 α)
    (startPeriod count : UInt64) :
    IsUpdatesAnswer known startPeriod count (updatesInRange known startPeriod count) :=
  (isUpdatesAnswer_iff known startPeriod count _).mpr ⟨List.prefix_refl _, id⟩

/-- No accepted answer holds more updates than the longest one.

The longest one holds the known updates of the range from its earliest known period, with no gap.

It stops at the limit. -/
theorem IsUpdatesAnswer.length_le {α : Type} {known : Std.TreeMap UInt64 α}
    {startPeriod count : UInt64} {answer : List α}
    (accepted : IsUpdatesAnswer known startPeriod count answer) :
    answer.length ≤ (updatesInRange known startPeriod count).length :=
  ((isUpdatesAnswer_iff known startPeriod count answer).mp accepted).1.length_le

/-- An accepted answer holds at most the smaller of the request limit and the count. -/
theorem IsUpdatesAnswer.length_le_limit {α : Type} {known : Std.TreeMap UInt64 α}
    {startPeriod count : UInt64} {answer : List α}
    (accepted : IsUpdatesAnswer known startPeriod count answer) :
    answer.length ≤ lightClientUpdatesLimit count := by
  obtain ⟨_, -, -, -, -, bounded⟩ := accepted
  exact bounded

/-- The pieces of an encoded chunk: the fork, the digest of its epoch and the update's bytes. -/
private theorem encodeUpdateChunk_ok {config : Config} {genesisValidatorsRoot : Root}
    {fork : Fork} {update : LightClientUpdate preset fork} {chunk : ByteArray}
    (encoded : encodeUpdateChunk config genesisValidatorsRoot update = .ok chunk) :
    ∃ digest payload, .altair ≤ fork ∧ fork = config.forkAtEpoch (contextEpoch update) ∧
      computeForkDigest config genesisValidatorsRoot (contextEpoch update) = .ok digest ∧
      SszType.serialize update = .ok payload ∧ 4 + payload.size < 2 ^ 64 ∧
      chunk = ⟨(uintToBytes 8 (4 + payload.size)).toArray⟩ ++ ⟨digest.toArray⟩ ++ payload := by
  by_cases altair : .altair ≤ fork
  · by_cases same : fork = config.forkAtEpoch (contextEpoch update)
    · cases digested : computeForkDigest config genesisValidatorsRoot (contextEpoch update) with
      | error fault =>
        simp [encodeUpdateChunk, checkUpdateFork, eq_true altair, eq_true same, digested,
          Except.mapError, bind, Except.bind, pure, Except.pure] at encoded
      | ok digest =>
      have four : (⟨digest.toArray⟩ : ByteArray).size = 4 := by simp [ByteArray.size]
      cases wrote : SszType.serialize update with
      | error fault =>
        simp [encodeUpdateChunk, checkUpdateFork, eq_true altair, eq_true same, digested, wrote,
          Except.mapError, bind, Except.bind, pure, Except.pure] at encoded
      | ok payload =>
      simp [encodeUpdateChunk, checkUpdateFork, eq_true altair, eq_true same, digested, wrote,
          Except.mapError, bind, Except.bind] at encoded
      rw [four] at encoded
      by_cases small : 4 + payload.size < 18446744073709551616
      · rw [ite_eq_left small] at encoded
        refine ⟨digest, payload, altair, same, rfl, rfl, small, ?_⟩
        rw [ByteArray.append_assoc]
        exact (Except.ok.inj encoded).symm
      · rw [ite_eq_right small] at encoded
        cases encoded
    · simp [encodeUpdateChunk, checkUpdateFork, eq_true altair, eq_false same, bind,
        Except.bind] at encoded
  · simp [encodeUpdateChunk, checkUpdateFork, eq_false altair, bind, Except.bind] at encoded

/-- A byte read inside a piece of bytes gives the byte of that piece. -/
private theorem getElem_append_vector {n : Nat} (pre tail : ByteArray) (piece : Vector UInt8 n)
    {i : Nat} (inside : i < n) (bound : pre.size + i < (pre ++ ⟨piece.toArray⟩ ++ tail).size) :
    (pre ++ ⟨piece.toArray⟩ ++ tail)[pre.size + i] = piece[i] := by
  show (pre ++ ⟨piece.toArray⟩ ++ tail).data[pre.size + i] = _
  have size : pre.size = pre.data.size := rfl
  simp only [ByteArray.data_append, Array.append_assoc]
  rw [Array.getElem_append_right (by omega)]
  simp [← size, Array.getElem_append_left (by simp; omega : i < piece.toArray.size)]

/-- The bytes read at the start of a piece are that piece. -/
private theorem ofFn_getElem_append {n : Nat} {data pre tail : ByteArray}
    {piece : Vector UInt8 n} {start : Nat} (split : data = pre ++ ⟨piece.toArray⟩ ++ tail)
    (at_start : start = pre.size) (bound : ∀ i : Fin n, start + i < data.size) :
    Vector.ofFn (fun i : Fin n => data[start + i]'(bound i)) = piece := by
  subst split at_start
  ext i inside
  simp [getElem_append_vector _ _ _ inside]

/-- The chunk of an update, between any bytes, decodes to the update and then reads on. -/
private theorem decodeUpdateChunksFrom_chunk {config : Config} {genesisValidatorsRoot : Root}
    {fork : Fork} {update : LightClientUpdate preset fork} {chunk pre rest : ByteArray}
    {updates : List (AnyLightClientUpdate preset)}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (roundtrip : ∀ {fork : Fork} {update : LightClientUpdate preset fork} {payload : ByteArray},
      SszType.serialize update = .ok payload →
        SszType.deserialize (LightClientUpdate preset fork) payload = .ok update)
    (encoded : encodeUpdateChunk config genesisValidatorsRoot update = .ok chunk)
    (next : decodeUpdateChunksFrom preset config genesisValidatorsRoot (pre ++ chunk ++ rest)
      (pre.size + chunk.size) = .ok updates) :
    decodeUpdateChunksFrom preset config genesisValidatorsRoot (pre ++ chunk ++ rest) pre.size =
      .ok (⟨fork, update⟩ :: updates) := by
  obtain ⟨digest, payload, altair, same, digested, wrote, small, rfl⟩ :=
    encodeUpdateChunk_ok encoded
  obtain ⟨start, found⟩ := Option.isSome_iff_exists.mp (forkOfDigest_isSome digested)
  have recovers := forkOfDigest_recovers identify digested
  rw [found] at recovers
  have fork_eq : config.forkAtEpoch start = fork := by
    rw [same]
    simpa using recovers
  subst fork_eq
  have eight : (⟨(uintToBytes 8 (4 + payload.size)).toArray⟩ : ByteArray).size = 8 :=
    Vector.size_toArray _
  have four : (⟨digest.toArray⟩ : ByteArray).size = 4 := Vector.size_toArray _
  have position : pre.size + 8 + (4 + payload.size) = pre.size +
      (⟨(uintToBytes 8 (4 + payload.size)).toArray⟩ ++ ⟨digest.toArray⟩ ++ payload).size := by
    rw [ByteArray.size_append, ByteArray.size_append, eight, four]
    omega
  rw [← position] at next
  generalize split : pre ++ (⟨(uintToBytes 8 (4 + payload.size)).toArray⟩ ++ ⟨digest.toArray⟩ ++
      payload) ++ rest = data at next ⊢
  have total : data.size = pre.size + 8 + (4 + payload.size) + rest.size := by
    rw [← split]
    simp only [ByteArray.size_append, eight, four]
    omega
  have length : ∀ bound : ∀ i : Fin 8, pre.size + i < data.size,
      bytesToUint (Vector.ofFn fun i : Fin 8 => data[pre.size + i]'(bound i)) =
        4 + payload.size := by
    intro bound
    rw [ofFn_getElem_append (piece := uintToBytes 8 (4 + payload.size))
      (tail := ⟨digest.toArray⟩ ++ payload ++ rest)
      (by rw [← split]; simp only [ByteArray.append_assoc]) rfl, bytesToUint_uintToBytes,
      Nat.mod_eq_of_lt small]
  have digest_read : ∀ bound : ∀ i : Fin 4, pre.size + 8 + i < data.size,
      (Vector.ofFn fun i : Fin 4 => data[pre.size + 8 + i]'(bound i)) = digest := fun bound =>
    ofFn_getElem_append (pre := pre ++ ⟨(uintToBytes 8 (4 + payload.size)).toArray⟩)
      (tail := payload ++ rest) (by rw [← split]; simp only [ByteArray.append_assoc])
      (by simp [eight]) bound
  have payload_read :
      data.extract (pre.size + 12) (pre.size + 8 + (4 + payload.size)) = payload := by
    rw [← split, ← ByteArray.append_assoc, ← ByteArray.append_assoc, ByteArray.extract_append,
      ByteArray.extract_append_eq_right (by simp [eight, four]) (by simp [eight, four]; omega)]
    simp only [ByteArray.size_append, eight, four,
      show pre.size + 8 + (4 + payload.size) - (pre.size + 8 + 4 + payload.size) = 0 by omega]
    rw [ByteArray.extract_eq_empty_iff.mpr (by simp), ByteArray.append_empty]
  rw [decodeUpdateChunksFrom, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp only [length (fun i => by omega), digest_read (fun i => by omega), found, payload_read,
    roundtrip wrote, next, altair, show ¬4 + payload.size < 4 by omega,
    show pre.size + 8 + (4 + payload.size) ≤ data.size by omega, ↓reduceIte, ↓reduceDIte]
  simp only [Except.mapError, digested, bind, Except.bind, ↓reduceIte]
  rfl

/-- The chunks that the encoder appends decode back to their updates, after any bytes. -/
private theorem decodeUpdateChunksFrom_foldlM {config : Config} {genesisValidatorsRoot : Root}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (roundtrip : ∀ {fork : Fork} {update : LightClientUpdate preset fork} {payload : ByteArray},
      SszType.serialize update = .ok payload →
        SszType.deserialize (LightClientUpdate preset fork) payload = .ok update)
    {updates : List (AnyLightClientUpdate preset)} {out data : ByteArray}
    (encoded : updates.foldlM (fun out ⟨_, update⟩ => do
      return out ++ (← encodeUpdateChunk config genesisValidatorsRoot update)) out = .ok data) :
    ∃ rest, data = out ++ rest ∧ ∀ pre : ByteArray,
      decodeUpdateChunksFrom preset config genesisValidatorsRoot (pre ++ rest) pre.size =
        .ok updates := by
  induction updates generalizing out with
  | nil =>
    refine ⟨ByteArray.empty, ?_, fun pre => ?_⟩
    · simpa [pure, Except.pure, ByteArray.append_empty] using encoded.symm
    · rw [decodeUpdateChunksFrom, dite_eq_left (by simp [ByteArray.append_empty])]
  | cons head tail ih =>
    obtain ⟨fork, update⟩ := head
    cases chunked : encodeUpdateChunk config genesisValidatorsRoot update with
    | error fault => simp [chunked, bind, Except.bind] at encoded
    | ok chunk =>
    obtain ⟨rest, hdata, decodes⟩ := ih (out := out ++ chunk) (by
      rw [List.foldlM_cons] at encoded
      dsimp only at encoded
      rw [chunked] at encoded
      exact encoded)
    refine ⟨chunk ++ rest, by rw [hdata, ByteArray.append_assoc], fun pre => ?_⟩
    rw [← ByteArray.append_assoc]
    refine decodeUpdateChunksFrom_chunk identify roundtrip chunked ?_
    have := decodes (pre ++ chunk)
    rwa [ByteArray.size_append] at this

/-- The bytes read from a position are the slice of the data from there. -/
private theorem ofFn_getElem_eq_extract {n : Nat} {data : ByteArray} {start : Nat}
    (fits : start + n ≤ data.size) (bound : ∀ i : Fin n, start + i < data.size) :
    (⟨(Vector.ofFn fun i : Fin n => data[start + i]'(bound i)).toArray⟩ : ByteArray) =
      data.extract start (start + n) := by
  have size : (⟨(Vector.ofFn fun i : Fin n => data[start + i]'(bound i)).toArray⟩ :
      ByteArray).size = n := Vector.size_toArray _
  apply ByteArray.ext_getElem
  · rw [size, ByteArray.size_extract]
    omega
  · intro i hi hi'
    rw [size] at hi
    rw [ByteArray.getElem_extract]
    show (Vector.ofFn fun i : Fin n => data[start + i]'(bound i)).toArray[i] = _
    simp

/-- A chunk that the decoder reads is the chunk that the encoder gives its update. -/
private theorem encodeUpdateChunk_of_read [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {config : Config} {genesisValidatorsRoot : Root}
    {data : ByteArray} {start length : Nat} {epoch : Epoch}
    {update : LightClientUpdate preset (config.forkAtEpoch epoch)}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (bound8 : ∀ i : Fin 8, start + i < data.size)
    (read_length : bytesToUint (Vector.ofFn fun i : Fin 8 => data[start + i]'(bound8 i)) = length)
    (bound4 : ∀ i : Fin 4, start + 8 + i < data.size)
    (found : forkOfDigest config genesisValidatorsRoot
      (Vector.ofFn fun i : Fin 4 => data[start + 8 + i]'(bound4 i)) = some epoch)
    (altair : .altair ≤ config.forkAtEpoch epoch) (long : 4 ≤ length)
    (inside : start + 8 + length ≤ data.size)
    (read : SszType.deserialize (LightClientUpdate preset (config.forkAtEpoch epoch))
      (data.extract (start + 12) (start + 8 + length)) = .ok update)
    (digested : computeForkDigest config genesisValidatorsRoot (contextEpoch update) =
      .ok (Vector.ofFn fun i : Fin 4 => data[start + 8 + i]'(bound4 i))) :
    encodeUpdateChunk config genesisValidatorsRoot update =
      .ok (data.extract start (start + 8 + length)) := by
  have recovers := forkOfDigest_recovers identify digested
  rw [found] at recovers
  have same : config.forkAtEpoch epoch = config.forkAtEpoch (contextEpoch update) := by
    simpa using recovers
  have wrote := SszType.serialize_deserialize read
  have small : length < 2 ^ 64 := read_length ▸ bytesToUint_lt _
  have rest_size : ((⟨(Vector.ofFn fun i : Fin 4 => data[start + 8 + i]'(bound4 i)).toArray⟩ :
      ByteArray) ++ data.extract (start + 12) (start + 8 + length)).size = length := by
    have four : (⟨(Vector.ofFn fun i : Fin 4 => data[start + 8 + i]'(bound4 i)).toArray⟩ :
        ByteArray).size = 4 := Vector.size_toArray _
    rw [ByteArray.size_append, ByteArray.size_extract, four]
    omega
  simp only [encodeUpdateChunk, checkUpdateFork, eq_true altair, eq_true same, digested, wrote,
    Except.mapError, bind, Except.bind, pure, Except.pure, rest_size, small, ↓reduceIte]
  have length_bytes : (⟨(uintToBytes 8 length).toArray⟩ : ByteArray) =
      data.extract start (start + 8) := by
    rw [← read_length, uintToBytes_bytesToUint, ofFn_getElem_eq_extract (by omega) bound8]
  rw [length_bytes, ofFn_getElem_eq_extract (by omega) bound4, ByteArray.extract_append_extract,
    Nat.min_eq_left (by omega), Nat.max_eq_right (by omega), ByteArray.extract_append_extract,
    Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]

/-- The updates that the decoder reads from a position encode back to the bytes from there. -/
private theorem foldlM_of_decodeUpdateChunksFrom [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {config : Config} {genesisValidatorsRoot : Root}
    {data : ByteArray} (identify : digestsIdentify config genesisValidatorsRoot = true)
    (bound : Nat) {start : Nat} {updates : List (AnyLightClientUpdate preset)} (out : ByteArray)
    (budget : data.size - start ≤ bound)
    (decoded : decodeUpdateChunksFrom preset config genesisValidatorsRoot data start =
      .ok updates) :
    updates.foldlM (fun out ⟨_, update⟩ => do
      return out ++ (← encodeUpdateChunk config genesisValidatorsRoot update)) out =
        .ok (out ++ data.extract start data.size) := by
  induction bound generalizing start updates out with
  | zero =>
    rw [decodeUpdateChunksFrom, dite_eq_left (by omega)] at decoded
    cases decoded
    rw [ByteArray.extract_eq_empty_iff.mpr (by omega), ByteArray.append_empty]
    rfl
  | succ bound ih =>
    rw [decodeUpdateChunksFrom] at decoded
    by_cases done : data.size ≤ start
    · rw [dite_eq_left done] at decoded
      cases decoded
      rw [ByteArray.extract_eq_empty_iff.mpr (by omega), ByteArray.append_empty]
      rfl
    rw [dite_eq_right done] at decoded
    by_cases header : start + 8 ≤ data.size
    swap
    · rw [dite_eq_right header] at decoded
      cases decoded
    rw [dite_eq_left header] at decoded
    have bound8 : ∀ i : Fin 8, start + i < data.size := fun i => by omega
    obtain ⟨length, read_length⟩ : ∃ length,
        bytesToUint (Vector.ofFn fun i : Fin 8 => data[start + i]'(bound8 i)) = length :=
      ⟨_, rfl⟩
    simp only [read_length] at decoded
    by_cases short : length < 4
    · rw [dite_eq_left short] at decoded
      cases decoded
    rw [dite_eq_right short] at decoded
    by_cases inside : start + 8 + length ≤ data.size
    swap
    · rw [dite_eq_right inside] at decoded
      cases decoded
    rw [dite_eq_left inside] at decoded
    have bound4 : ∀ i : Fin 4, start + 8 + i < data.size := fun i => by omega
    obtain ⟨digest, read_digest⟩ : ∃ digest : ForkDigest,
        (Vector.ofFn fun i : Fin 4 => data[start + 8 + i]'(bound4 i)) = digest := ⟨_, rfl⟩
    simp only [read_digest] at decoded
    cases found : forkOfDigest config genesisValidatorsRoot digest with
    | none =>
      simp only [found] at decoded
      cases decoded
    | some epoch =>
    simp only [found] at decoded
    by_cases altair : .altair ≤ config.forkAtEpoch epoch
    swap
    · rw [ite_eq_right altair] at decoded
      cases decoded
    rw [ite_eq_left altair] at decoded
    cases read : SszType.deserialize (LightClientUpdate preset (config.forkAtEpoch epoch))
        (data.extract (start + 12) (start + 8 + length)) with
    | error fault =>
      simp only [read, Except.mapError, bind, Except.bind] at decoded
      cases decoded
    | ok update =>
    cases digested : computeForkDigest config genesisValidatorsRoot (contextEpoch update) with
    | error fault =>
      simp only [read, digested, Except.mapError, bind, Except.bind] at decoded
      cases decoded
    | ok expected =>
    by_cases agrees : expected = digest
    swap
    · simp only [read, digested, agrees, Except.mapError, bind, Except.bind, ↓reduceIte] at decoded
      cases decoded
    subst agrees
    cases next : decodeUpdateChunksFrom preset config genesisValidatorsRoot data
        (start + 8 + length) with
    | error fault =>
      simp only [read, digested, next, Except.mapError, bind, Except.bind, ↓reduceIte] at decoded
      cases decoded
    | ok tail =>
    simp only [read, digested, next, Except.mapError, bind, Except.bind, ↓reduceIte, pure,
      Except.pure] at decoded
    cases decoded
    have chunk := encodeUpdateChunk_of_read identify bound8 read_length bound4
      (by rw [read_digest]; exact found) altair (by omega) inside read
      (by rw [read_digest]; exact digested)
    rw [List.foldlM_cons]
    dsimp only
    rw [chunk]
    refine (ih (out ++ data.extract start (start + 8 + length)) (by omega) next).trans ?_
    rw [ByteArray.append_assoc, ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right (by omega)]

/-- The SSZ chunks of updates decode back to the updates, each with its fork.

This holds on a chain whose digests name their forks, as the check of digests asks. -/
theorem decodeUpdateChunks_encode [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {config : Config} {genesisValidatorsRoot : Root}
    {updates : List (AnyLightClientUpdate preset)} {data : ByteArray}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (encoded : encodeUpdateChunks config genesisValidatorsRoot updates = .ok data) :
    decodeUpdateChunks preset config genesisValidatorsRoot data = .ok updates := by
  obtain ⟨rest, rfl, decodes⟩ :=
    decodeUpdateChunksFrom_foldlM identify SszType.deserialize_serialize encoded
  simpa [decodeUpdateChunks, ByteArray.empty_append] using decodes ByteArray.empty

/-- Bytes that decode to updates are the SSZ chunks of those updates, so the decoder is canonical.

This holds on a chain whose digests name their forks, as the check of digests asks. -/
theorem encodeUpdateChunks_decode [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {config : Config} {genesisValidatorsRoot : Root}
    {updates : List (AnyLightClientUpdate preset)} {data : ByteArray}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (decoded : decodeUpdateChunks preset config genesisValidatorsRoot data = .ok updates) :
    encodeUpdateChunks config genesisValidatorsRoot updates = .ok data := by
  have encoded := foldlM_of_decodeUpdateChunksFrom identify data.size ByteArray.empty
    (by omega) decoded
  rw [ByteArray.empty_append, ByteArray.extract_zero_size] at encoded
  exact encoded

/-- The finality update response refuses with code 404 exactly when the node knows no update. -/
theorem finalityUpdateResponse_notFound_iff {fork : Fork}
    {latest : Option (LightClientUpdate preset fork)} :
    (∃ error, finalityUpdateResponse latest = .error error ∧ error.code = 404) ↔
      latest = none := by
  cases latest with
  | none => exact iff_of_true ⟨_, rfl, rfl⟩ rfl
  | some update =>
    refine iff_of_false ?_ (by simp)
    rw [finalityUpdateResponse, versioned_error_iff (by decide)]
    simp

/-- The optimistic update response refuses with code 404 exactly when the node knows no update. -/
theorem optimisticUpdateResponse_notFound_iff {fork : Fork}
    {latest : Option (LightClientUpdate preset fork)} :
    (∃ error, optimisticUpdateResponse latest = .error error ∧ error.code = 404) ↔
      latest = none := by
  cases latest with
  | none => exact iff_of_true ⟨_, rfl, rfl⟩ rfl
  | some update =>
    refine iff_of_false ?_ (by simp)
    rw [optimisticUpdateResponse, versioned_error_iff (by decide)]
    simp

/-- The finality update response refuses exactly when the node knows no update.

Its error is then the one with code 404 for a missing finality update.

So a known update never gets code 500.

It needs a preset with a nonempty logs bloom and sync committee. -/
theorem finalityUpdateResponse_eq_error_iff [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {fork : Fork}
    {latest : Option (LightClientUpdate preset fork)} {error : ErrorMessage} :
    finalityUpdateResponse latest = .error error ↔
      latest = none ∧ error = noLatestUpdate "finality" := by
  cases latest with
  | none =>
    exact ⟨fun refused => ⟨rfl, (Except.error.inj refused).symm⟩,
      fun ⟨_, named⟩ => by subst named; rfl⟩
  | some update =>
    rw [finalityUpdateResponse, versioned_eq_error_iff
      fun (finality : LightClientFinalityUpdate preset fork) _ => toApiJson_total finality]
    simp

/-- The optimistic update response refuses exactly when the node knows no update.

Its error is then the one with code 404 for a missing optimistic update.

So a known update never gets code 500.

It needs a preset with a nonempty logs bloom and sync committee. -/
theorem optimisticUpdateResponse_eq_error_iff [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] {fork : Fork}
    {latest : Option (LightClientUpdate preset fork)} {error : ErrorMessage} :
    optimisticUpdateResponse latest = .error error ↔
      latest = none ∧ error = noLatestUpdate "optimistic" := by
  cases latest with
  | none =>
    exact ⟨fun refused => ⟨rfl, (Except.error.inj refused).symm⟩,
      fun ⟨_, named⟩ => by subst named; rfl⟩
  | some update =>
    rw [optimisticUpdateResponse, versioned_eq_error_iff
      fun (optimistic : LightClientOptimisticUpdate preset fork) _ => toApiJson_total optimistic]
    simp

/-- The JSON answer for a range of updates never fails, so it never gets code 500.

It needs a preset with a nonempty logs bloom and sync committee. -/
theorem updatesJson_exists_ok [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] (updates : List (AnyLightClientUpdate preset)) :
    ∃ document, updatesJson updates = .ok document := by
  unfold updatesJson
  simp only [bind, Except.bind]
  split
  · -- A failed list fails on one update, whose JSON the writer still gives.
    rename_i fault failed
    obtain ⟨⟨fork, update⟩, -, refused⟩ := exists_mem_of_mapM_error failed
    obtain ⟨document, written⟩ := toApiJson_total update
    simp [apiJsonOr500, written, Except.mapError, pure, Except.pure] at refused
  · exact ⟨_, rfl⟩

end EthLib.Consensus.BeaconApi
