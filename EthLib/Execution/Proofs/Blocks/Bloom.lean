module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Execution.Blocks.Bloom

/-!
# Proofs: the logs Bloom filter

The filter of no logs is 0.

The filter of two lists of logs, one after the other, is the OR of their filters.

The filter has no false negative: it has every bit of the address and of each topic of each log.

A bit of the filter of an entry is set exactly when it is one of the bits of the entry.

A bit of the filter of some logs is set exactly when it is a bit of an entry of one of the logs.

The entries of a log are its address and its topics.

A query for an entry passes exactly when each bit of the entry is a bit of an entry of a log.

The 256 bytes of a filter read back, most significant byte first, as the number of the filter.

So two filters with the same bytes are the same filter.
-/

@[expose] public section

namespace EthLib.Execution.Blocks.Bloom

open EthLib.Base

/-- The OR of some filters, started from `init`, is their OR started from 0, then OR `init`. -/
theorem foldr_or_init {n : Nat} (l : List (BitVec n)) (init : BitVec n) :
    l.foldr (· ||| ·) init = l.foldr (· ||| ·) 0 ||| init := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, BitVec.or_assoc]

/-- A bit of the OR of some filters is set exactly when it is set in one of them. -/
theorem getLsbD_foldr_or {n : Nat} (l : List (BitVec n)) (k : Nat) :
    (l.foldr (· ||| ·) 0).getLsbD k = l.any (·.getLsbD k) := by
  induction l with
  | nil => simp
  | cons x xs ih => rw [List.foldr_cons, BitVec.getLsbD_or, ih, List.any_cons]

/-- Each bit of an entry is below 2048. -/
theorem lt_of_mem_bits {entry : ByteArray} {k : Nat} (hk : k ∈ bits entry) : k < 2048 := by
  simp only [bits, List.mem_cons, List.not_mem_nil, or_false] at hk
  omega

/-- A fold that sets some bits sets exactly the bits of the list below 2048. -/
theorem getLsbD_foldr_twoPow_iff (l : List Nat) (k : Nat) :
    (l.foldr (fun j acc => BitVec.twoPow 2048 j ||| acc) 0).getLsbD k = true ↔
      k ∈ l ∧ k < 2048 := by
  induction l with
  | nil => simp
  | cons j js ih =>
    rw [List.foldr_cons, BitVec.getLsbD_or, Bool.or_eq_true, ih, BitVec.getLsbD_twoPow]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (⟨hk, rfl⟩ | ⟨hk, hlt⟩)
      · exact ⟨.inl rfl, hk⟩
      · exact ⟨.inr hk, hlt⟩
    · rintro ⟨rfl | hk, hlt⟩
      · exact .inl ⟨hlt, rfl⟩
      · exact .inr ⟨hk, hlt⟩

/-- A fold that sets some bits below 2048 sets each of them. -/
theorem getLsbD_foldr_twoPow {l : List Nat} {k : Nat} (hk : k ∈ l) (hlt : k < 2048) :
    (l.foldr (fun j acc => BitVec.twoPow 2048 j ||| acc) 0).getLsbD k = true :=
  (getLsbD_foldr_twoPow_iff l k).mpr ⟨hk, hlt⟩

/-- A bit of the filter of an entry is set exactly when it is a bit of the entry. -/
theorem getLsbD_ofEntry_iff (entry : ByteArray) (k : Nat) :
    (ofEntry entry).getLsbD k = true ↔ k ∈ bits entry := by
  rw [ofEntry, getLsbD_foldr_twoPow_iff]
  exact ⟨And.left, fun hk => ⟨hk, lt_of_mem_bits hk⟩⟩

/-- The filter of an entry has each bit of the entry. -/
theorem getLsbD_ofEntry {entry : ByteArray} {k : Nat} (hk : k ∈ bits entry) :
    (ofEntry entry).getLsbD k = true :=
  (getLsbD_ofEntry_iff entry k).mpr hk

/-- A bit of the filter of some logs is set exactly when it is a bit of an entry of one of them.

The entries of a log are its address and its topics. -/
theorem getLsbD_ofLogs_iff (logs : List Log) (k : Nat) :
    (ofLogs logs).getLsbD k = true ↔ ∃ log ∈ logs, ∃ entry ∈ entries log, k ∈ bits entry := by
  rw [ofLogs, getLsbD_foldr_or, List.any_eq_true]
  simp only [List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨_, ⟨entry, ⟨log, hlog, hentry⟩, rfl⟩, hk⟩
    exact ⟨log, hlog, entry, hentry, (getLsbD_ofEntry_iff entry k).mp hk⟩
  · rintro ⟨log, hlog, entry, hentry, hk⟩
    exact ⟨_, ⟨entry, ⟨log, hlog, hentry⟩, rfl⟩, (getLsbD_ofEntry_iff entry k).mpr hk⟩

/-- A query passes on the filter of some logs exactly when each bit of its entry is set there.

A bit is set there exactly when it is a bit of an entry of one of the logs. -/
theorem mayContain_ofLogs_iff (logs : List Log) (entry : ByteArray) :
    mayContain (ofLogs logs) entry = true ↔
      ∀ k ∈ bits entry, ∃ log ∈ logs, ∃ other ∈ entries log, k ∈ bits other := by
  simp only [mayContain, List.all_eq_true, getLsbD_ofLogs_iff]

/-- The filter of no logs is 0. -/
theorem ofLogs_nil : ofLogs [] = 0 := rfl

/-- The filter of two lists of logs, one after the other, is the OR of their filters. -/
theorem ofLogs_append (a b : List Log) : ofLogs (a ++ b) = ofLogs a ||| ofLogs b := by
  simp only [ofLogs, List.flatMap_append, List.map_append, List.foldr_append]
  rw [foldr_or_init]

/-- No false negative: the filter of some logs has every bit of every entry of each log. -/
theorem mayContain_ofLogs {logs : List Log} {log : Log} (hLog : log ∈ logs) {entry : ByteArray}
    (hEntry : entry ∈ entries log) : mayContain (ofLogs logs) entry = true :=
  (mayContain_ofLogs_iff logs entry).mpr fun _ hk => ⟨log, hLog, entry, hEntry, hk⟩

/-- The filter of some logs has every bit of the address of each log. -/
theorem mayContain_address {logs : List Log} {log : Log} (hLog : log ∈ logs) :
    mayContain (ofLogs logs) ⟨log.address.toArray⟩ = true :=
  mayContain_ofLogs hLog (List.mem_cons_self ..)

/-- The filter of some logs has every bit of each topic of each log. -/
theorem mayContain_topic {logs : List Log} {log : Log} (hLog : log ∈ logs) {topic : Hash32}
    (hTopic : topic ∈ log.topics) : mayContain (ofLogs logs) ⟨topic.toArray⟩ = true :=
  mayContain_ofLogs hLog (List.mem_cons_of_mem _ (List.mem_map_of_mem hTopic))

-- The bound compares `2 ^ 2048` with `256 ^ 256`, which needs a higher threshold.
set_option exponentiation.threshold 2048 in
/-- The bytes of a filter, read most significant first, give back the number of the filter. -/
theorem bytesToNat_toBytes (bloom : BitVec 2048) :
    bytesToNat (toBytes bloom).toList = bloom.toNat := by
  simp only [toBytes, Vector.toList_mk]
  apply bytesToNat_natToBytes_of_lt
  -- 256 bytes hold 2048 bits.
  have hpow : (256 : Nat) ^ 256 = 2 ^ 2048 := (Nat.pow_mul 2 8 256).symm
  rw [hpow]
  exact bloom.isLt

/-- Two filters with the same 256 bytes are the same filter. -/
theorem toBytes_injective : Function.Injective toBytes := fun a b h => by
  apply BitVec.eq_of_toNat_eq
  rw [← bytesToNat_toBytes a, ← bytesToNat_toBytes b, h]

end EthLib.Execution.Blocks.Bloom
