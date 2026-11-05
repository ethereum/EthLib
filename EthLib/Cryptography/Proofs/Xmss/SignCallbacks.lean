module

public import EthLib.Cryptography.Xmss.Sign

/-!
# Delayed callbacks of one layer's signer

The default callbacks give the actual layer signer for every monad.

A failed one-time signature skips the path, and success keeps the returned path.

A symbolic trace separates normal signing errors from errors of the outer monad.
-/

public section

namespace EthLib.Cryptography.Xmss

open Constants

/-- Actual one-time signing and path callbacks give exactly the existing layer signer. -/
theorem signLayer_eq_signLayerWithCallbacks {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (seed : Seed)
    (layer : Layer) (e : Nat) (msg : ByteArray) :
    signLayer H pp seed layer e msg = signLayerWithCallbacks layer e
      (fun () => otsSign H pp seed layer (UInt32.ofNat e) msg)
      (fun () => path H pp seed layer e) := by
  rfl

section Branches

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Failure skips the path and reports the original natural-number key, without a cast. -/
theorem signLayerWithCallbacks_none (layer : Layer) (e : Nat)
    (getPath : Unit → m (Vector Digest LAYER_HEIGHT)) :
    signLayerWithCallbacks layer e (fun () => pure none) getPath =
      pure (.error (.noAdmissibleEncoding layer e)) := by
  simp only [signLayerWithCallbacks, pure_bind]

/-- Success packs the actual one-time signature with the path returned by the callback. -/
theorem signLayerWithCallbacks_some (layer : Layer) (e : Nat)
    (rho : Randomizer) (values : Vector Digest V)
    (getPath : Unit → m (Vector Digest LAYER_HEIGHT)) :
    signLayerWithCallbacks layer e (fun () => pure (some (rho, values))) getPath =
      (do return .ok { randomizer := rho, chainValues := values, path := ← getPath () }) := by
  simp only [signLayerWithCallbacks, pure_bind]

end Branches

/-- Both callback replies determine the complete result and prefix trace at every initial trace.

An outer error is distinct from the normal `noAdmissibleEncoding` result.
-/
theorem signLayerWithCallbacks_trace {ε τ : Type} (initial : List τ)
    (layer : Layer) (e : Nat) (otsEvent pathEvent : τ)
    (otsReply : Except ε (Option (Randomizer × Vector Digest V)))
    (pathReply : Except ε (Vector Digest LAYER_HEIGHT)) :
    ((signLayerWithCallbacks (m := ExceptT ε (StateT (List τ) Id)) layer e
      (fun () => ExceptT.mk (do modify (· ++ [otsEvent]); pure otsReply))
      (fun () => ExceptT.mk (do modify (· ++ [pathEvent]); pure pathReply))).run.run initial) =
      match otsReply with
      | .error error => (.error error, initial ++ [otsEvent])
      | .ok none => (.ok (.error (.noAdmissibleEncoding layer e)), initial ++ [otsEvent])
      | .ok (some (rho, values)) =>
          (pathReply.map (fun pi =>
            .ok ({ randomizer := rho, chainValues := values, path := pi } : LayerSignature)),
            initial ++ [otsEvent, pathEvent]) := by
  cases otsReply with
  | error error => rfl
  | ok reply =>
      cases reply with
      | none => rfl
      | some signature =>
          obtain ⟨rho, values⟩ := signature
          -- On success the path's effect is retained, whether its reply is an error or a value.
          cases pathReply
          all_goals
            change (_, (initial ++ [otsEvent]) ++ [pathEvent]) = _
            simp only [List.append_assoc]
            rfl

end EthLib.Cryptography.Xmss
