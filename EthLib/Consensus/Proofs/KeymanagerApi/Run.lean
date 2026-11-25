module

public import EthLib.Consensus.KeymanagerApi.Server

/-!
# Proofs: a property that every call keeps holds after every run of calls

A run of calls is a sequence of states, each the one that a call leaves from the state before it.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean

/-- A call on the key that a segment of a path names keeps what the call keeps for every key.

A segment that names no key leaves the state as it was. -/
theorem KeyState.of_withPubkey {holds : KeyState → Prop} {state : KeyState} (start : holds state)
    {segment : String} {call : Cryptography.Bls.BLSPubkey → Response × KeyState}
    (step : ∀ pubkey, holds (call pubkey).2) : holds (withPubkey segment state call).2 := by
  unfold withPubkey
  split
  · exact step _
  · exact start

/-- A property that every call of the Keymanager API keeps holds after a run of calls.

Each state of the run is the one that a call leaves from the state before it. -/
theorem KeyState.of_run {holds : KeyState → Prop}
    (step : ∀ state, holds state → ∀ text client chain method path body,
      holds (handle text client chain state method path body).2)
    {states : Nat → KeyState} {k : Nat} (start : holds (states 0))
    (run : ∀ i < k, ∃ text client chain method path body,
      states (i + 1) = (handle text client chain (states i) method path body).2) :
    holds (states k) := by
  induction k with
  | zero => exact start
  | succ n ih =>
    obtain ⟨text, client, chain, method, path, body, next⟩ := run n (Nat.lt_succ_self n)
    rw [next]
    exact step _ (ih fun i hi => run i (Nat.lt_succ_of_lt hi)) text client chain method path body

end EthLib.Consensus.KeymanagerApi
