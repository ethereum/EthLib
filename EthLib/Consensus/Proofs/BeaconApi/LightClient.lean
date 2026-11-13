module

public import EthLib.Consensus.BeaconApi.LightClient
public import EthLib.Consensus.Proofs.ForkDigest
public import EthLib.Consensus.Proofs.LightClient.Containers
public import EthLib.Base.Proofs.LittleEndian

/-!
# Proofs: the light client answers of the Beacon API

The known updates of a range, cut to the limit, form an answer that the source accepts.

No accepted answer holds more updates than that one.

On a chain whose digests name their forks, the SSZ chunks of updates decode back to the updates.

On such a chain, bytes that decode are the chunks of the updates they give.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Serialization.Ssz

variable {preset : Preset}

/-- The known updates of a range, cut to the limit, form an answer that the source accepts. -/
theorem updatesInRange_answer {α : Type} (known : Std.TreeMap UInt64 α)
    (startPeriod count : UInt64) :
    IsUpdatesAnswer known startPeriod count (updatesInRange known startPeriod count) := by
  set filtered := known.toList.filter fun entry => decide (InRange startPeriod count entry.1)
  have sorted : filtered.Pairwise (fun a b => a.1 < b.1) :=
    (known.ordered_keys_toList.filter _).imp fun h => compareOfLessAndEq_eq_lt.mp h
  refine ⟨(filtered.take (updatesLimit count)).map (·.1), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [updatesInRange, List.map_map]
    refine List.map_congr_left fun entry mem => ?_
    exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp
      (List.mem_of_mem_filter (List.mem_of_mem_take mem))
  · intro period mem
    obtain ⟨entry, taken, rfl⟩ := List.mem_map.mp mem
    simpa using (List.mem_filter.mp (List.mem_of_mem_take taken)).2
  · exact List.Pairwise.map _ (fun _ _ h => h) (sorted.sublist (List.take_sublist _ _))
  · intro period range known_mem
    have found : (period, known[period]) ∈ filtered :=
      List.mem_filter.mpr ⟨Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr
        (Std.TreeMap.getElem?_eq_some_getElem known_mem), by simpa using range⟩
    -- A period in the range makes the count, so the limit, positive.
    have positive : 0 < updatesLimit count := by
      have : (128 : UInt64).toNat = 128 := rfl
      simp only [updatesLimit, InRange, MAX_REQUEST_LIGHT_CLIENT_UPDATES] at range ⊢
      omega
    obtain ⟨limit, hlimit⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
    rw [hlimit]
    cases hfiltered : filtered with
    | nil => simp [hfiltered] at found
    | cons first rest =>
      rw [hfiltered] at found sorted
      refine ⟨first.1, by simp, ?_⟩
      rcases List.mem_cons.mp found with same | later
      · rw [← same]
        exact UInt64.le_refl _
      · exact UInt64.le_of_lt (List.rel_of_pairwise_cons sorted later)
  · simp only [updatesInRange, List.length_map]
    exact List.length_take_le _ _

/-- No accepted answer holds more updates than the known updates of the range, cut to the limit.

So the function gives an answer of the greatest length. -/
theorem IsUpdatesAnswer.length_le {α : Type} {known : Std.TreeMap UInt64 α}
    {startPeriod count : UInt64} {answer : List α}
    (accepted : IsUpdatesAnswer known startPeriod count answer) :
    answer.length ≤ (updatesInRange known startPeriod count).length := by
  obtain ⟨periods, values, range, sorted, -, bounded⟩ := accepted
  have same_length : periods.length = answer.length := by
    simpa using congrArg List.length values
  -- The periods differ and each is a known period of the range, so they are at most as many.
  have covered : periods ⊆ (known.toList.filter fun entry =>
      decide (InRange startPeriod count entry.1)).map (·.1) := by
    intro period mem
    obtain ⟨value, hvalue⟩ : ∃ value, known[period]? = some value := by
      have : known[period]? ∈ answer.map some := values ▸ List.mem_map_of_mem mem
      obtain ⟨value, -, hvalue⟩ := List.mem_map.mp this
      exact ⟨value, hvalue.symm⟩
    exact List.mem_map.mpr ⟨(period, value), List.mem_filter.mpr
      ⟨Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hvalue, by simpa using range period mem⟩,
      rfl⟩
  have fewer := List.Nodup.length_le_of_subset (sorted.imp UInt64.ne_of_lt) covered
  simp only [List.length_map] at fewer
  simp only [updatesInRange, List.length_map, List.length_take]
  omega

/-- An accepted answer holds at most the smaller of the request limit and the count. -/
theorem IsUpdatesAnswer.length_le_limit {α : Type} {known : Std.TreeMap UInt64 α}
    {startPeriod count : UInt64} {answer : List α}
    (accepted : IsUpdatesAnswer known startPeriod count answer) :
    answer.length ≤ updatesLimit count := by
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
    (fuel : Nat) {start : Nat} {updates : List (AnyLightClientUpdate preset)} (out : ByteArray)
    (budget : data.size - start ≤ fuel)
    (decoded : decodeUpdateChunksFrom preset config genesisValidatorsRoot data start =
      .ok updates) :
    updates.foldlM (fun out ⟨_, update⟩ => do
      return out ++ (← encodeUpdateChunk config genesisValidatorsRoot update)) out =
        .ok (out ++ data.extract start data.size) := by
  induction fuel generalizing start updates out with
  | zero =>
    rw [decodeUpdateChunksFrom, dite_eq_left (by omega)] at decoded
    cases decoded
    rw [ByteArray.extract_eq_empty_iff.mpr (by omega), ByteArray.append_empty]
    rfl
  | succ fuel ih =>
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

end EthLib.Consensus.BeaconApi
