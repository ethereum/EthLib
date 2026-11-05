module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.SystemCall

/-!
# Proofs: the system calls of a block

A checked system call fails when its contract has no code.

When it succeeds, its contract has code and the call stopped with no error.

The requests of a block come in the order of their types, withdrawals before consolidations.

Each list holds its type byte and at least one byte of data.

Before Pectra a block reads no request.

From Glamsterdam a system call fails as not yet specified.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState)

variable {fork : Fork} {env : BlockEnvironment fork} {block : BlockState} {target : Address}
  {data : ByteArray}

/-! ## The call -/

/-- From Glamsterdam, a system call fails, since the rules of that fork are not here yet. -/
theorem systemCall_of_glamsterdam_le (h : .glamsterdam ≤ fork) :
    systemCall env block target data = .error (.forkNotYetSpecified fork) := by
  simp only [systemCall, h, ↓reduceIte]
  rfl

/-- A checked system call to a contract with no code makes the block invalid. -/
theorem checkedSystemCall_of_size_eq_zero {code : ByteArray}
    (hCode : codeAt block target = .ok code) (hEmpty : code.size = 0) :
    checkedSystemCall env block target data = .error (.systemContractEmpty target) := by
  simp [checkedSystemCall, hCode, hEmpty, Except.mapError, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- A checked system call that succeeds calls a contract with code, and stops with no error. -/
theorem checkedSystemCall_ok {out : SystemCallOutput}
    (h : checkedSystemCall env block target data = .ok out) :
    (∃ code, codeAt block target = .ok code ∧ code.size ≠ 0) ∧
      systemCall env block target data = .ok out ∧ out.error = none := by
  unfold checkedSystemCall at h
  obtain ⟨code, hCode, h⟩ := bind_ok_iff.mp h
  by_cases hEmpty : code.size = 0
  · simp [hEmpty, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · simp only [hEmpty, ↓reduceIte] at h
    obtain ⟨call, hCall, h⟩ := bind_ok_iff.mp h
    cases hError : call.error with
    | some e => simp [hError, throw, throwThe, MonadExceptOf.throw] at h
    | none =>
      simp only [hError] at h
      cases h
      exact ⟨⟨code, mapError_ok_iff.mp hCode, hEmpty⟩, mapError_ok_iff.mp hCall, hError⟩

/-! ## The requests -/

/-- A list made by `requestList` holds its type byte first, then at least one byte. -/
theorem mem_requestList {type : UInt8} {r : ByteArray} (h : r ∈ requestList type data) :
    1 < r.size ∧ r[0]! = type := by
  unfold requestList at h
  split at h
  · simp at h
  · rename_i hSize
    simp only [List.mem_singleton] at h
    subst h
    refine ⟨?_, ?_⟩
    · simp only [ByteArray.size_append]
      have : (⟨#[type]⟩ : ByteArray).size = 1 := rfl
      omega
    · rfl

/-- The requests that a fold over request contracts adds come in the order of the contracts. -/
theorem foldlM_requests {contracts : List (UInt8 × Address)} {start : BlockState × List ByteArray}
    {result : BlockState × List ByteArray}
    (h : contracts.foldlM
      (fun (acc : BlockState × List ByteArray) (contract : UInt8 × Address) => do
        let out ← checkedSystemCall env acc.1 contract.2 .empty
        return (out.block, acc.2 ++ requestList contract.1 out.output))
      start = .ok result) :
    ∃ added, result.2 = start.2 ++ added ∧ (∀ r ∈ added, 1 < r.size) ∧
      (added.map (·[0]!)).Sublist (contracts.map Prod.fst) := by
  induction contracts generalizing start with
  | nil =>
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨[], by simp, by simp, by simp⟩
  | cons contract rest ih =>
    simp only [List.foldlM_cons] at h
    obtain ⟨next, hNext, hRest⟩ := bind_ok_iff.mp h
    obtain ⟨out, hOut, hEq⟩ := bind_ok_iff.mp hNext
    cases hEq
    obtain ⟨added, hAdded, hSize, hSub⟩ := ih hRest
    refine ⟨requestList contract.1 out.output ++ added, by simp [hAdded], ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact (mem_requestList hr).1
      · exact hSize r hr
    · simp only [List.map_append, List.map_cons]
      unfold requestList
      split
      · exact hSub.cons _
      · simp only [List.map_cons, List.map_nil, List.singleton_append]
        have : (⟨#[contract.1]⟩ ++ out.output : ByteArray)[0]! = contract.1 := rfl
        rw [this]
        exact hSub.cons_cons _

/-- Before Pectra, a block reads no request and its state is unchanged. -/
theorem readRequests_of_lt_pectra (h : fork < .pectra) :
    readRequests env block = .ok (block, []) := by
  unfold readRequests
  split
  · exact absurd ‹_› (Nat.not_le_of_lt h)
  · rfl

/-- The requests of a block have data, and come in the order of their types.

Withdrawals, of type 1, come before consolidations, of type 2, and each type comes at most once.
-/
theorem readRequests_requests {result : BlockState × List ByteArray}
    (h : readRequests env block = .ok result) :
    (∀ r ∈ result.2, 1 < r.size) ∧
      (result.2.map (·[0]!)).Sublist [WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE] := by
  unfold readRequests at h
  split at h
  · obtain ⟨added, hAdded, hSize, hSub⟩ := foldlM_requests h
    simp only [List.nil_append] at hAdded
    rw [hAdded]
    exact ⟨hSize, hSub⟩
  · cases h
    simp

end EthLib.Execution.Blocks
