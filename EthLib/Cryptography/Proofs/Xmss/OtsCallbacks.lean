module

public import EthLib.Cryptography.Xmss.Ots

/-!
# Delayed callbacks of the one-time signer

The one-time signer has four stages: the base, the search, the chain starts and the chain values.

A reduction may replace a stage and keep the others.

This file writes the signer with one callback per stage, for the proofs only.

The specification's signer is this form with its own stages, for every monad.

A failed search returns before the chain callbacks, and success keeps their order.

State and errors stay part of the result.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open Constants

/-- The one-time signer with one callback per stage.

The search receives the base, and a failed search skips both chain callbacks.

Each callback takes `Unit`, so its computation starts only when the signer reaches it.
-/
def otsSignWithCallbacks {m : Type → Type} [Monad m]
    (getBase : Unit → m Randomizer)
    (getSearch : Randomizer → Unit → m (Option (Randomizer × Vector (Fin CHAIN_LENGTH) V)))
    (getStarts : Unit → m (Vector Digest V))
    (getValues : Vector Digest V → Vector (Fin CHAIN_LENGTH) V → Unit →
      m (Vector Digest V)) : m (Option (Randomizer × Vector Digest V)) := do
  let base ← getBase ()
  let some (rho, digits) ← getSearch base () | return none
  let starts ← getStarts ()
  let values ← getValues starts digits ()
  return some (rho, values)

/-- With the signer's own stages as callbacks, the callback form is the signer, in every monad. -/
theorem otsSign_eq_otsSignWithCallbacks {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (seed : Seed)
    (layer : Layer) (key : UInt32) (msg : ByteArray) :
    otsSign H pp seed layer key msg = otsSignWithCallbacks
      (fun () => randomizerBase H pp seed layer key msg)
      (fun base () => Internal.findCodeword H pp layer key msg base 0 MAX_RANDOMIZER_TRIALS)
      (fun () => chainStarts H pp seed layer key)
      (fun starts digits () => ofFnInOrder V fun i =>
        chain H pp layer key i 0 digits[i] (by simp) starts[i]) := by
  rfl

section Branches

variable {m : Type → Type} [Monad m] [LawfulMonad m]
    (getBase : Unit → m Randomizer) (getStarts : Unit → m (Vector Digest V))
    (getValues : Vector Digest V → Vector (Fin CHAIN_LENGTH) V → Unit → m (Vector Digest V))

/-- An exhausted search keeps the base's effects and skips the chain callbacks. -/
theorem otsSignWithCallbacks_none :
    otsSignWithCallbacks getBase (fun _ _ => pure none) getStarts getValues =
      (do let _ ← getBase (); pure none) := by
  simp only [otsSignWithCallbacks, pure_bind]

/-- A successful search runs starts and values after the base, using the returned digits. -/
theorem otsSignWithCallbacks_some (rho : Randomizer) (digits : Vector (Fin CHAIN_LENGTH) V) :
    otsSignWithCallbacks getBase (fun _ _ => pure (some (rho, digits))) getStarts getValues =
      (do
        let _ ← getBase ()
        let starts ← getStarts ()
        let values ← getValues starts digits ()
        pure (some (rho, values))) := by
  simp only [otsSignWithCallbacks, pure_bind]

end Branches

/-- A failed search keeps exactly the effects of the base and the search, from any trace. -/
theorem otsSignWithCallbacks_none_trace {ε τ : Type} (initial : List τ)
    (base : Randomizer) (baseEvent : τ) (searchEvent : Randomizer → τ)
    (getStarts : Unit → ExceptT ε (StateT (List τ) Id) (Vector Digest V))
    (getValues : Vector Digest V → Vector (Fin CHAIN_LENGTH) V → Unit →
      ExceptT ε (StateT (List τ) Id) (Vector Digest V)) :
    ((otsSignWithCallbacks
      (fun () => do modify (· ++ [baseEvent]); pure base)
      (fun b () => do modify (· ++ [searchEvent b]); pure none)
      getStarts getValues).run.run initial) =
        (.ok none, initial ++ [baseEvent, searchEvent base]) := by
  -- Evaluate only the two abstract callbacks, with every input and trace still symbolic.
  change ((Except.ok none : Except ε (Option (Randomizer × Vector Digest V))),
    (initial ++ [baseEvent]) ++ [searchEvent base]) = _
  simp only [List.append_assoc]
  rfl

/-- On success, the trace lists the four callbacks in order, each with the arguments it got. -/
theorem otsSignWithCallbacks_some_trace {ε τ : Type} (initial : List τ)
    (base rho : Randomizer) (digits : Vector (Fin CHAIN_LENGTH) V)
    (starts values : Vector Digest V) (baseEvent startsEvent : τ)
    (searchEvent : Randomizer → τ)
    (valuesEvent : Vector Digest V → Vector (Fin CHAIN_LENGTH) V → τ) :
    ((otsSignWithCallbacks (m := ExceptT ε (StateT (List τ) Id))
      (fun () => do modify (· ++ [baseEvent]); pure base)
      (fun b () => do modify (· ++ [searchEvent b]); pure (some (rho, digits)))
      (fun () => do modify (· ++ [startsEvent]); pure starts)
      (fun s x () => do modify (· ++ [valuesEvent s x]); pure values)).run.run initial) =
        (.ok (some (rho, values)),
          initial ++ [baseEvent, searchEvent base, startsEvent, valuesEvent starts digits]) := by
  -- The state transformer keeps each callback's state before the result is returned.
  change ((Except.ok (some (rho, values)) : Except ε (Option (Randomizer × Vector Digest V))),
    (((initial ++ [baseEvent]) ++ [searchEvent base]) ++ [startsEvent]) ++
      [valuesEvent starts digits]) = _
  simp only [List.append_assoc]
  rfl

/-- An error of the outer monad at a callback keeps exactly the effects up to that callback. -/
theorem otsSignWithCallbacks_error_trace {ε τ : Type} (initial : List τ) (stop : Fin 4)
    (error : ε) (base rho : Randomizer) (digits : Vector (Fin CHAIN_LENGTH) V)
    (starts values : Vector Digest V) (baseEvent startsEvent : τ)
    (searchEvent : Randomizer → τ)
    (valuesEvent : Vector Digest V → Vector (Fin CHAIN_LENGTH) V → τ) :
    ((otsSignWithCallbacks (m := ExceptT ε (StateT (List τ) Id))
      (fun () => do
        modify (· ++ [baseEvent])
        if stop.val = 0 then throw error else pure base)
      (fun b () => do
        modify (· ++ [searchEvent b])
        if stop.val = 1 then throw error else pure (some (rho, digits)))
      (fun () => do
        modify (· ++ [startsEvent])
        if stop.val = 2 then throw error else pure starts)
      (fun s x () => do
        modify (· ++ [valuesEvent s x])
        if stop.val = 3 then throw error else pure values)).run.run initial) =
      (.error error, initial ++
        [baseEvent, searchEvent base, startsEvent, valuesEvent starts digits].take
          (stop.val + 1)) := by
  rcases stop with ⟨stop, hstop⟩
  have hcases : stop = 0 ∨ stop = 1 ∨ stop = 2 ∨ stop = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals
    -- Only the callbacks up to the failing one ran.
    change ((Except.error error : Except ε (Option (Randomizer × Vector Digest V))), _) = _
    simp only [List.append_assoc]
    rfl

end EthLib.Cryptography.Xmss
