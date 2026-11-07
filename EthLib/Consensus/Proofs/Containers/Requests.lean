module

public import EthLib.Consensus.Containers.Requests
public import EthLib.Consensus.Proofs.Containers.Builder
public import EthLib.Consensus.Proofs.Containers.Execution
public import EthLib.Consensus.Proofs.Containers.Misc
public import Mathlib.Data.List.Forall2

/-!
# Proofs: the request and queue containers are lawful

Each container has distinct field names, and converts to and from its fields.

So its bytes decode back to it, at every fork.

The request types are distinct bytes, so a request list names its type without doubt.

The list that the execution layer receives keeps the nonempty lists, in increasing order of type.

Each of its entries has at least one byte, so its first byte exists.

At Gloas, with no builder request, it is the list of Electra for the same requests.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

instance : LawfulSszType PendingDeposit := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType PendingPartialWithdrawal :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType PendingConsolidation :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType DepositRequest := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType WithdrawalRequest := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType ConsolidationRequest :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

namespace ExecutionRequests

variable {preset : Preset} {fork : Fork}

/-- The field names of the requests are distinct at every fork. -/
theorem names_nodup : (names fork).Nodup := by
  have all : (["deposits", "withdrawals", "consolidations", "builder_deposits",
      "builder_exits"] : List String).Nodup := by decide
  exact all.sublist ((List.Sublist.refl _).append (sinceNames_sublist _))

instance : LawfulSszType (ExecutionRequests preset fork) :=
  .forkContainer
    (fun gloas => ⟨rfl, by decide, by simp [activeFields, SszFields.descs, gloas]⟩)
    ⟨by
      by_cases gloas : Fork.glamsterdam ≤ fork <;>
        simp [names, sinceNames, SszFields.descs, gloas],
     by simp [names],
     firstDuplicate_of_nodup _ names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

/-- The types of the request lists, in their order: three, and from Gloas five. -/
theorem typedLists_types (requests : ExecutionRequests preset fork) :
    requests.typedLists.map (·.type) =
      [DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE] ++
        if .glamsterdam ≤ fork then [BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE]
        else [] := by
  unfold typedLists
  split <;> simp_all

/-- The types of the request lists strictly increase. -/
theorem typedLists_increasing (requests : ExecutionRequests preset fork) :
    (requests.typedLists.map (·.type[0])).Pairwise (· < ·) := by
  have types := congrArg (List.map (·[0])) (typedLists_types requests)
  rw [List.map_map] at types
  rw [show (fun list : TypedList => list.type[0]) = (fun type : Vector UInt8 1 => type[0]) ∘
    (·.type) from rfl, types]
  split <;> decide

end ExecutionRequests

/-- The results of a monadic map that succeeds, one for each input. -/
theorem forall₂_of_mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {inputs : List α} {outputs : List β}, inputs.mapM f = .ok outputs →
      List.Forall₂ (fun input output => f input = .ok output) inputs outputs
  | [], outputs, made => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at made
    subst made
    exact .nil
  | input :: inputs, outputs, made => by
    simp only [List.mapM_cons, bind, Except.bind] at made
    cases first : f input with
    | error e => simp [first] at made
    | ok output =>
      cases rest : inputs.mapM f with
      | error e => simp [first, rest] at made
      | ok others =>
        simp only [first, rest, pure, Except.pure, Except.ok.injEq] at made
        subst made
        exact .cons first (forall₂_of_mapM_ok rest)

/-- The list that the execution layer receives: the nonempty request lists, in their order.

Each one gives its type byte followed by its SSZ bytes. -/
theorem getExecutionRequestsList_spec {preset : Preset} {fork : Fork}
    {requests : ExecutionRequests preset fork} {out : List ByteArray}
    (made : getExecutionRequestsList requests = .ok out) :
    List.Forall₂
      (fun list bytes => ∃ data, list.bytes = .ok data ∧ bytes = ⟨list.type.toArray⟩ ++ data)
      (requests.typedLists.filter (·.count != 0)) out := by
  refine (forall₂_of_mapM_ok made).imp fun list bytes step => ?_
  cases data : list.bytes with
  | error e => simp [data, bind, Except.bind] at step
  | ok data' =>
    simp only [data, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at step
    exact ⟨data', rfl, step.symm⟩

/-- In the list that the execution layer receives, every entry comes from a nonempty list. -/
theorem getExecutionRequestsList_length {preset : Preset} {fork : Fork}
    {requests : ExecutionRequests preset fork} {out : List ByteArray}
    (made : getExecutionRequestsList requests = .ok out) :
    out.length = (requests.typedLists.filter (·.count != 0)).length :=
  (getExecutionRequestsList_spec made).length_eq.symm

/-- In the list that the execution layer receives, every entry has at least one byte. -/
theorem getExecutionRequestsList_size_pos {preset : Preset} {fork : Fork}
    {requests : ExecutionRequests preset fork} {out : List ByteArray}
    (made : getExecutionRequestsList requests = .ok out) :
    ∀ b ∈ out, 0 < b.size := by
  have spec := getExecutionRequestsList_spec made
  clear made
  generalize requests.typedLists.filter (·.count != 0) = lists at spec
  induction spec with
  | nil => simp
  | @cons list _ _ _ head _ rest =>
    obtain ⟨data, -, rfl⟩ := head
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [ByteArray.size_append]
      have : (⟨list.type.toArray⟩ : ByteArray).size = 1 := by simp [ByteArray.size]
      omega
    · exact rest b hb

/-- In the list that the execution layer receives, the type bytes strictly increase. -/
theorem getExecutionRequestsList_increasing {preset : Preset} {fork : Fork}
    {requests : ExecutionRequests preset fork} {out : List ByteArray}
    (made : getExecutionRequestsList requests = .ok out) :
    (out.map (·.data[0]?)).Pairwise (· < ·) := by
  have first : ((requests.typedLists.filter (·.count != 0)).map (·.type[0])).map some =
      out.map (·.data[0]?) := by
    have spec := getExecutionRequestsList_spec made
    clear made
    generalize requests.typedLists.filter (·.count != 0) = lists at spec ⊢
    induction spec with
    | nil => rfl
    | cons head _ rest =>
      obtain ⟨data, -, bytes⟩ := head
      subst bytes
      simp only [List.map_cons, rest, List.cons.injEq, and_true]
      rw [ByteArray.data_append, Array.getElem?_append_left (by simp)]
      simp
  rw [← first, List.pairwise_map]
  simp only [Option.some_lt_some]
  exact (ExecutionRequests.typedLists_increasing requests).sublist
    ((List.filter_sublist).map _)

/-- At Gloas, with no builder request, the list is that of Electra for the same requests.

The request lists then have the same bytes as at Electra, and the two new lists are empty. -/
theorem getExecutionRequestsList_glamsterdam {preset : Preset}
    {requests : ExecutionRequests preset .glamsterdam} {electra : ExecutionRequests preset .pectra}
    (deposits : requests.deposits.data = electra.deposits.data)
    (withdrawals : requests.withdrawals.data = electra.withdrawals.data)
    (consolidations : requests.consolidations.data = electra.consolidations.data)
    (noBuilderDeposits : (requests.builderDeposits (by decide)).data = #[])
    (noBuilderExits : (requests.builderExits (by decide)).data = #[]) :
    getExecutionRequestsList requests = getExecutionRequestsList electra := by
  unfold getExecutionRequestsList ExecutionRequests.typedLists
  simp [deposits, withdrawals, consolidations, noBuilderDeposits, noBuilderExits,
    serialize_forkList_across (by decide) (by decide) deposits,
    serialize_forkList_across (by decide) (by decide) withdrawals,
    serialize_forkList_across (by decide) (by decide) consolidations, List.filter_cons,
    (by decide : ¬Fork.glamsterdam ≤ Fork.pectra)]

/-- The five request types are five distinct bytes. -/
theorem requestTypes_nodup :
    [DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
      BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE].Nodup := by
  decide

namespace NewPayloadRequest

variable {preset : Preset} {fork : Fork}

/-- The field names of a new payload request are distinct at every fork. -/
theorem names_nodup : (names fork).Nodup := by
  have all : (["execution_payload", "versioned_hashes", "parent_beacon_block_root",
      "execution_requests"] : List String).Nodup := by decide
  exact all.sublist (((List.Sublist.refl _).append (sinceNames_sublist _)).append
    (sinceNames_sublist _))

/-- At every fork, a new payload request is lawful, when its logs bloom has a byte. -/
instance [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] :
    LawfulSszType (NewPayloadRequest preset fork) :=
  .forkContainer
    (fun gloas => by
      have electra : Fork.pectra ≤ fork := Nat.le_trans (by decide) gloas
      have deneb : Fork.dencun ≤ fork := Nat.le_trans (by decide) gloas
      exact ⟨rfl, by decide, by simp [activeFields, SszFields.descs, electra, deneb]⟩)
    ⟨by
      by_cases deneb : Fork.dencun ≤ fork <;> by_cases electra : Fork.pectra ≤ fork <;>
        simp [names, sinceNames, SszFields.descs, deneb, electra],
     by simp [names],
     firstDuplicate_of_nodup _ names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

end NewPayloadRequest

end EthLib.Consensus
