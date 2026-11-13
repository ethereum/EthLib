module

public import EthLib.Consensus.BeaconApi.Submit

/-!
# Proofs: the answer to a list submitted to a pool endpoint

An item with one message fails exactly when gossip validation does not accept that message.

Its reason is the reason of the gossip outcome, and the keys seen after it are those of gossip.

The answer lists each failed position once, in increasing order.

The entry at a position is the failure of its item, given the keys after the items before it.

So the answer is a success exactly when every item passes, each after the items before it.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Networking.Gossip

variable {preset : Preset} {fork : Fork} {context : SubmitContext preset fork} {seen : Seen}
  {items : List (SubmitItem preset fork)}

/-- A run from a position names failed positions in increasing order, all within its items. -/
private theorem submitFrom_failures_sorted {position : Nat} :
    ((submitFrom context position seen items).1.map Prod.fst).Pairwise (· < ·) ∧
      ∀ failure ∈ (submitFrom context position seen items).1,
        position ≤ failure.1 ∧ failure.1 < position + items.length := by
  induction items generalizing position seen with
  | nil => simp [submitFrom]
  | cons item rest ih =>
    obtain ⟨sorted, bounds⟩ := @ih (validateItem context seen item).2 (position + 1)
    simp only [submitFrom]
    refine ⟨?_, fun entry mem => ?_⟩
    · cases (validateItem context seen item).1 with
      | none => simpa using sorted
      | some reason =>
        simp only [Option.map_some, Option.toList_some, List.singleton_append, List.map_cons,
          List.pairwise_cons, List.mem_map]
        refine ⟨?_, sorted⟩
        rintro _ ⟨entry, mem, rfl⟩
        have := bounds entry mem
        omega
    · rcases List.mem_append.mp mem with head | mem
      · cases hf : (validateItem context seen item).1 <;> simp [hf] at head
        subst head
        simp
      · have := bounds entry mem
        simp only [List.length_cons]
        omega

/-- From a position, the entry at a later position is the failure of its item. -/
private theorem submitFrom_lookup {position index : Nat} (inList : index < items.length) :
    (validateItem context (submitFrom context position seen (items.take index)).2
      items[index]).1 = (submitFrom context position seen items).1.lookup (position + index) := by
  induction items generalizing position seen index with
  | nil => simp at inList
  | cons item rest ih =>
    have bounds := (submitFrom_failures_sorted (context := context)
      (seen := (validateItem context seen item).2) (items := rest) (position := position + 1)).2
    cases index with
    | zero =>
      have absent : (submitFrom context (position + 1) (validateItem context seen item).2
          rest).1.lookup position = none :=
        List.lookup_eq_none_iff.mpr fun entry mem => by
          have := bounds entry mem
          simp
          omega
      cases h : (validateItem context seen item).1 <;> simp [submitFrom, h, absent]
    | succ index =>
      have step := @ih (validateItem context seen item).2 (position + 1) index
        (by simpa using inList)
      have shift : position + (index + 1) = position + 1 + index := by omega
      have differ : (position + 1 + index == position) = false := by simp; omega
      simp only [List.take_succ_cons, List.getElem_cons_succ, submitFrom]
      cases h : (validateItem context seen item).1 <;>
        simpa [shift, List.lookup, differ, h] using step

/-- The answer is a success exactly when the run has no failure. -/
private theorem submitList_accepted_iff_nil :
    (submitList context seen items).1 = .accepted ↔
      (submitFrom context 0 seen items).1 = [] := by
  unfold submitList
  rcases h : submitFrom context 0 seen items with ⟨failures, after⟩
  by_cases empty : failures = [] <;> simp [empty]

/-- The failures of the answer are those of the run from the first position. -/
private theorem submitList_failures_eq :
    (submitList context seen items).1.failures = (submitFrom context 0 seen items).1 := by
  unfold submitList
  rcases h : submitFrom context 0 seen items with ⟨failures, after⟩
  by_cases empty : failures = [] <;> simp [empty, SubmitOutcome.failures]

/-- The keys seen after the answer are those of the run from the first position. -/
private theorem submitList_snd_eq :
    (submitList context seen items).2 = (submitFrom context 0 seen items).2 := rfl

/-- A message that gossip judges fails with the reason of gossip, and the keys after it. -/
theorem messageFailure_of_ok {message : GossipMessage preset fork} {outcome : ValidationResult}
    {after : Seen}
    (gossip : validateGossipMessage context.config context.checks context.setup seen
      context.store context.statuses context.currentTimeMs message = .ok (outcome, after)) :
    messageFailure context seen message = (failureReason outcome, after) := by
  simp [messageFailure, gossip]

/-- An error of the fork choice on a message fails it, with the keys from before it. -/
theorem messageFailure_of_error {message : GossipMessage preset fork}
    {error : ForkChoiceError}
    (gossip : validateGossipMessage context.config context.checks context.setup seen
      context.store context.statuses context.currentTimeMs message = .error error) :
    messageFailure context seen message = (some s!"fork choice: {reprStr error}", seen) := by
  simp [messageFailure, gossip]

/-- An item validates its first message, then the rest after its keys.

It fails with the reason of the first message that fails. -/
theorem validateItem_cons {message : GossipMessage preset fork}
    {rest : SubmitItem preset fork} :
    validateItem context seen (message :: rest) =
      ((messageFailure context seen message).1.or
        (validateItem context (messageFailure context seen message).2 rest).1,
        (validateItem context (messageFailure context seen message).2 rest).2) := rfl

/-- An item of one message fails exactly when gossip does not accept it, with the same keys. -/
theorem validateItem_single {message : GossipMessage preset fork} :
    validateItem context seen [message] = messageFailure context seen message := by
  simp [validateItem]

/-- A failed answer names at least one item. -/
theorem submitList_failed_ne_nil {failures : List (Nat × String)}
    (failed : (submitList context seen items).1 = .failed failures) : failures ≠ [] := by
  have := submitList_failures_eq (context := context) (seen := seen) (items := items)
  rw [failed] at this
  have empty := submitList_accepted_iff_nil (context := context) (seen := seen) (items := items)
  rw [failed] at empty
  simp_all [SubmitOutcome.failures]

/-- The answer names the failed positions in increasing order, so each one once. -/
theorem submitList_failures_pairwise :
    ((submitList context seen items).1.failures.map Prod.fst).Pairwise (· < ·) := by
  rw [submitList_failures_eq]
  exact (submitFrom_failures_sorted (context := context) (seen := seen) (items := items)
    (position := 0)).1

/-- The answer names only positions within the list. -/
theorem submitList_failures_lt_length {failure : Nat × String}
    (mem : failure ∈ (submitList context seen items).1.failures) : failure.1 < items.length := by
  rw [submitList_failures_eq] at mem
  simpa using ((submitFrom_failures_sorted (context := context) (seen := seen) (items := items)
    (position := 0)).2 failure mem).2

/-- The entry of the answer at a position is the failure of its item, if any.

The item is validated with the keys seen after the items before it. -/
theorem submitList_failures {position : Nat} (inList : position < items.length) :
    (validateItem context (submitList context seen (items.take position)).2 items[position]).1 =
      (submitList context seen items).1.failures.lookup position := by
  rw [submitList_failures_eq, submitList_snd_eq]
  simpa using submitFrom_lookup (context := context) (seen := seen) (position := 0) inList

/-- The answer is a success exactly when no item fails, each after the items before it. -/
theorem submitList_accepted_iff :
    (submitList context seen items).1 = .accepted ↔
      ∀ position (inList : position < items.length),
        (validateItem context (submitList context seen (items.take position)).2
          items[position]).1 = none := by
  constructor
  · intro accepted position inList
    rw [submitList_failures inList, submitList_failures_eq,
      submitList_accepted_iff_nil.mp accepted]
    rfl
  · intro passes
    rw [submitList_accepted_iff_nil, ← submitList_failures_eq,
      List.eq_nil_iff_forall_not_mem]
    intro failure mem
    have inList := submitList_failures_lt_length mem
    have none := passes failure.1 inList
    rw [submitList_failures inList, submitList_failures_eq] at none
    rw [submitList_failures_eq] at mem
    have := List.lookup_eq_none_iff.mp none failure mem
    simp at this

end EthLib.Consensus.BeaconApi
