module

public import EthLib.Engine.GetInclusionList
public import EthLib.Engine.Proofs.Json
public import EthLib.Consensus.Gossip.InclusionList

/-!
# Proofs: `engine_getInclusionListV1`

Every answer keeps the two rules of the method.

Each transaction has at least one byte.

The lengths of the transactions add up to at most 8192 bytes.

The answer keeps the order of the candidates.

So a list of candidates that already keeps both rules is the answer itself.

An inclusion list that carries an answer passes the two reject checks of its gossip.

They are the check of the total size and the check of empty transactions.

An empty answer, which comes when no candidate fits, is ignored by gossip all the same.
-/

public section

namespace EthLib.Engine

open EthLib.Serialization.JsonRpc

/-- Every transaction of the selection has at least one byte. -/
theorem size_pos_of_mem_selectInclusionList {taken : Nat} {candidates : List ByteArray}
    {tx : ByteArray} (h : tx ∈ selectInclusionList taken candidates) : 0 < tx.size := by
  induction candidates generalizing taken with
  | nil => cases h
  | cons c rest ih =>
    unfold selectInclusionList at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · omega
      · exact ih h
    · exact ih h

/-- The bytes taken before the selection and those of the selection stay within the bound. -/
theorem taken_add_sum_le_of_selectInclusionList {taken : Nat} {candidates : List ByteArray}
    (start : taken ≤ MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST) :
    taken + ((selectInclusionList taken candidates).map (·.size)).sum ≤
      MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST := by
  induction candidates generalizing taken with
  | nil => simpa [selectInclusionList]
  | cons c rest ih =>
    unfold selectInclusionList
    split
    · next fits =>
      have := ih fits.2
      simp only [List.map_cons, List.sum_cons]
      omega
    · exact ih start

/-- The candidates in the selection keep their order: the selection is a sublist of them. -/
theorem selectInclusionList_sublist (taken : Nat) (candidates : List ByteArray) :
    (selectInclusionList taken candidates).Sublist candidates := by
  induction candidates generalizing taken with
  | nil => exact List.Sublist.slnil
  | cons c rest ih =>
    unfold selectInclusionList
    split
    · exact (ih _).cons_cons c
    · exact (ih _).cons c

/-- Candidates that already keep both rules are the selection itself, in full. -/
theorem selectInclusionList_of_valid {taken : Nat} {candidates : List ByteArray}
    (nonempty : ∀ tx ∈ candidates, 0 < tx.size)
    (bound : taken + (candidates.map (·.size)).sum ≤ MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST) :
    selectInclusionList taken candidates = candidates := by
  induction candidates generalizing taken with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, List.sum_cons] at bound
    have hc : 0 < c.size := nonempty c (List.mem_cons_self ..)
    unfold selectInclusionList
    have fits : c.size ≠ 0 ∧ taken + c.size ≤ MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST :=
      ⟨by omega, by omega⟩
    rw [ih (fun tx h => nonempty tx (List.mem_cons_of_mem _ h)) (by omega)]
    simp [fits]

/-- An answer of the method is the selection from the candidates, for an empty parameter array. -/
theorem getInclusionList_eq_ok_iff {candidates : List ByteArray} {params : Lean.Json}
    {answer : List ByteArray} :
    getInclusionList candidates params = .ok answer ↔
      paramsArray params = .ok [] ∧ answer = selectInclusionList 0 candidates := by
  unfold getInclusionList getInclusionListParams
  cases h : paramsArray params with
  | error e => simp [bind, Except.bind, liftM, monadLift, MonadLift.monadLift, Json.lift,
      Except.mapError]
  | ok items =>
    cases items with
    | nil => simp [bind, Except.bind, liftM, monadLift, MonadLift.monadLift, Json.lift,
        Except.mapError, pure, Except.pure, eq_comm]
    | cons j rest => simp [bind, Except.bind, liftM, monadLift, MonadLift.monadLift,
        Json.lift, Except.mapError, Json.invalid, throw, throwThe, MonadExceptOf.throw]

/-- Rule 1: every transaction of an answer has at least one byte. -/
theorem size_pos_of_getInclusionList {candidates : List ByteArray} {params : Lean.Json}
    {answer : List ByteArray} (h : getInclusionList candidates params = .ok answer)
    {tx : ByteArray} (mem : tx ∈ answer) : 0 < tx.size := by
  rw [(getInclusionList_eq_ok_iff.mp h).2] at mem
  exact size_pos_of_mem_selectInclusionList mem

/-- Rule 2: the transactions of an answer hold at most 8192 bytes together. -/
theorem sum_le_of_getInclusionList {candidates : List ByteArray} {params : Lean.Json}
    {answer : List ByteArray} (h : getInclusionList candidates params = .ok answer) :
    (answer.map (·.size)).sum ≤ MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST := by
  rw [(getInclusionList_eq_ok_iff.mp h).2]
  simpa using
    taken_add_sum_le_of_selectInclusionList (taken := 0) (candidates := candidates) (Nat.zero_le _)

/-- An inclusion list whose transactions are those of an answer passes two checks of its gossip.

The bound of the configuration must be at least that of the method, as on mainnet.

Its transactions hold at most the bytes that the configuration allows.

None of its transactions is empty. -/
theorem gossip_size_checks_of_getInclusionList {candidates : List ByteArray}
    {params : Lean.Json} {answer : List ByteArray}
    (h : getInclusionList candidates params = .ok answer) {config : Consensus.Config}
    (bound : MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST ≤
      config.MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST.toNat)
    {list : Consensus.InclusionList}
    (carried : list.transactions.data.toList.map (fun tx => tx.data) =
      answer.map (·.data)) :
    list.transactionsSize ≤ config.MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST.toNat ∧
      list.transactions.data.toList.all (·.data.size != 0) = true := by
  -- The sizes of the transactions of the list are those of the answer.
  have sizes : list.transactions.data.toList.map (·.data.size) = answer.map (·.size) := by
    have := congrArg (List.map Array.size) carried
    simpa [List.map_map, Function.comp_def] using this
  refine ⟨?_, ?_⟩
  · unfold Consensus.InclusionList.transactionsSize
    rw [sizes]
    exact Nat.le_trans (sum_le_of_getInclusionList h) bound
  · rw [List.all_eq_true]
    intro x hx
    have hm : x.data.size ∈ answer.map (·.size) :=
      sizes ▸ List.mem_map_of_mem (f := (·.data.size)) hx
    obtain ⟨tx, htx, hsize⟩ := List.mem_map.mp hm
    have := size_pos_of_getInclusionList h htx
    simp only [bne_iff_ne, ne_eq]
    omega

/-- The bound of the method is the bound of inclusion list gossip on mainnet. -/
theorem mainnet_maxTransactionsBytesPerInclusionList :
    Consensus.Config.mainnet.MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST.toNat =
      MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST := rfl

end EthLib.Engine
