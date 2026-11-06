module

public import EthLib.Execution.Blocks.Bloom

/-!
# Proofs: the logs Bloom filter

The filter of no logs is 0.

The filter of two lists of logs, one after the other, is the OR of their filters.

The filter has no false negative: it has every bit of the address and of each topic of each log.
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

/-- A fold that sets some bits below 2048 sets each of them. -/
theorem getLsbD_foldr_twoPow {l : List Nat} {k : Nat} (hk : k ∈ l) (hlt : k < 2048) :
    (l.foldr (fun j acc => BitVec.twoPow 2048 j ||| acc) 0).getLsbD k = true := by
  induction l with
  | nil => simp at hk
  | cons j js ih =>
    rw [List.foldr_cons, BitVec.getLsbD_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hk with rfl | hk
    · exact Or.inl (by simp [hlt])
    · exact Or.inr (ih hk)

/-- The filter of an entry has each bit of the entry. -/
theorem getLsbD_ofEntry {entry : ByteArray} {k : Nat} (hk : k ∈ bits entry) :
    (ofEntry entry).getLsbD k = true :=
  getLsbD_foldr_twoPow hk (lt_of_mem_bits hk)

/-- The filter of no logs is 0. -/
theorem ofLogs_nil : ofLogs [] = 0 := rfl

/-- The filter of two lists of logs, one after the other, is the OR of their filters. -/
theorem ofLogs_append (a b : List Log) : ofLogs (a ++ b) = ofLogs a ||| ofLogs b := by
  simp only [ofLogs, List.flatMap_append, List.map_append, List.foldr_append]
  rw [foldr_or_init]

/-- No false negative: the filter of some logs has every bit of every entry of each log. -/
theorem mayContain_ofLogs {logs : List Log} {log : Log} (hLog : log ∈ logs) {entry : ByteArray}
    (hEntry : entry ∈ entries log) : mayContain (ofLogs logs) entry = true := by
  simp only [mayContain, List.all_eq_true]
  intro k hk
  rw [ofLogs, getLsbD_foldr_or, List.any_eq_true]
  exact ⟨ofEntry entry, List.mem_map_of_mem (List.mem_flatMap.mpr ⟨log, hLog, hEntry⟩),
    getLsbD_ofEntry hk⟩

/-- The filter of some logs has every bit of the address of each log. -/
theorem mayContain_address {logs : List Log} {log : Log} (hLog : log ∈ logs) :
    mayContain (ofLogs logs) ⟨log.address.toArray⟩ = true :=
  mayContain_ofLogs hLog (List.mem_cons_self ..)

/-- The filter of some logs has every bit of each topic of each log. -/
theorem mayContain_topic {logs : List Log} {log : Log} (hLog : log ∈ logs) {topic : Hash32}
    (hTopic : topic ∈ log.topics) : mayContain (ofLogs logs) ⟨topic.toArray⟩ = true :=
  mayContain_ofLogs hLog (List.mem_cons_of_mem _ (List.mem_map_of_mem hTopic))

end EthLib.Execution.Blocks.Bloom
