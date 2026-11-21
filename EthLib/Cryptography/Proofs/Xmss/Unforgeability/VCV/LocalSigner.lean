module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.StatefulPairs
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerDelayed

/-!
# Signing with a local private cache

A message randomizer can update a table the graph does not manage.

The one-time signer keeps that state when the bounded search fails or when it returns chain values.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open EthLib.Cryptography OracleComp OracleSpec HashSig Constants LayerGraph.Hidden

variable {R α β : Type}

/-- Compare computations from each local state before running their shared graph queries. -/
@[expose] def SameLocal (pp : PublicParam) (p q : WithLocal R α) : Prop :=
  ∀ r, simulateQ (graph pp).eagerImpl (p.run r) = simulateQ (graph pp).eagerImpl (q.run r)

protected theorem SameLocal.trans {pp : PublicParam} {p q s : WithLocal R α}
    (h : SameLocal pp p q) (k : SameLocal pp q s) : SameLocal pp p s := fun r => (h r).trans (k r)

protected theorem SameLocal.bind {pp : PublicParam} {p q : WithLocal R α} {f g : α → WithLocal R β}
    (head : SameLocal pp p q) (tail : ∀ x, SameLocal pp (f x) (g x)) :
    SameLocal pp (p >>= f) (q >>= g) := by
  intro r
  simp only [StateT.run_bind, simulateQ_bind, head r]
  exact bind_congr fun z => tail z.1 z.2

theorem sameLocal_lift {pp : PublicParam} {p q : OracleComp SharedSpec α}
    (same : simulateQ (graph pp).eagerImpl p = simulateQ (graph pp).eagerImpl q) :
    SameLocal pp (liftM p : WithLocal R α) (liftM q) := by
  intro r
  simp [StateT.run_monadLift, same]

local notation "LH" => (fun b => (liftM (hash b) : WithLocal R (Vector UInt8 32)))

/-- Run the actual local randomizer before the public finder and selected chain-value schedule. -/
@[expose] noncomputable def localOts (pp : PublicParam) (cb : SeedPrf (WithLocal R)) (l : Layer)
    (e : UInt32) (msg : ByteArray) : WithLocal R (Option (Randomizer × Vector Digest V)) := do
  let base ← randomizerBase pp cb l e msg
  let some (rho, x) ← liftM (Xmss.Internal.findCodeword hash pp l e msg base 0
      MAX_RANDOMIZER_TRIALS)
    | return none
  let v := selection pp l
  let ys ← liftM (simulateQ v.liftQuery (beforeValues pp l e x >>= fun _ => revealValues e x))
  return some (rho, ys)

/-- The selected values and remaining local state agree for every warm initial graph. -/
theorem ots_local (pp : PublicParam) (cb : SeedPrf (WithLocal R)) (l : Layer)
    (base : SeedPrf (OracleComp SharedSpec)) (pairs : LocalPairs pp l cb base)
    (selected : Pairs pp l base)
    (e : UInt32) (msg : ByteArray) : SameLocal pp (otsSign LH pp cb l e msg)
    (localOts pp cb l e msg) := by
  unfold otsSign Internal.otsSignTrials localOts
  apply SameLocal.bind (fun _ => rfl)
  intro rnd
  rw [← findCodeword_map_monad (fun {_} p => (liftM p : WithLocal R _)) (fun _ => liftM_pure _)
    (fun _ _ => liftM_bind _ _) hash]
  apply SameLocal.bind (fun _ => rfl)
  rintro (_ | ⟨rho, x⟩)
  · intro _
    rfl
  · have same : SameLocal pp (chainValues LH cb pp l e x)
        (liftM (simulateQ (selection pp l).liftQuery (beforeValues pp l e x >>=
          fun _ => revealValues e x))) := by
      rw [chainValues_lift pp l cb base pairs]
      exact sameLocal_lift (values_schedule pp l base selected e x)
    have complete := same.bind (f := fun ys => pure (some (rho, ys)))
        (g := fun ys => pure (some (rho, ys)))
      (fun _ _ => rfl)
    simpa only [chainValues, bind_assoc] using complete

/-- The top finder carries the residual state even when it rejects. -/
@[expose] noncomputable def localLayer (pp : PublicParam) (cb : SeedPrf (WithLocal R))
    (l : Layer) (e : Nat) (msg : ByteArray) : WithLocal R (Except XmssError LayerSignature) := do
  let some (rho, vals) ← localOts pp cb l (UInt32.ofNat e) msg
    | return .error (.noAdmissibleEncoding l e)
  return .ok {randomizer := rho, chainValues := vals, path := ← liftM (pathSchedule pp l e)}

theorem signLayer_local (pp : PublicParam) (cb : SeedPrf (WithLocal R)) (l : Layer)
    (base : SeedPrf (OracleComp SharedSpec)) (pairs : LocalPairs pp l cb base)
    (selected : Pairs pp l base)
    (e : Nat) (msg : ByteArray) :
    SameLocal pp (signLayer LH pp cb l e msg) (localLayer pp cb l e msg) := by
  unfold signLayer localLayer
  apply SameLocal.bind (ots_local pp cb l base pairs selected _ msg)
  rintro (_ | ⟨rho, vals⟩)
  · exact fun _ => rfl
  · rw [path_lift pp l cb base pairs]
    exact (sameLocal_lift (path_pairs pp l base selected e)).bind (fun _ _ => rfl)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
