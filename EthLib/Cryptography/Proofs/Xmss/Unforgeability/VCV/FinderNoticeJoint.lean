module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistry
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialGraphPost

/-!
# Joint observation of first-search snapshots and later hits

Each full word updates the search ledger and the registered-hit flag from the same prior state.

The two projections preserve the guard's returned value, including a refusal.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig CachedCodeword OracleSpec OracleComp EarlierDigest EarlierDigest.Ledger TrialGraphWatch

abbrev WatchedState := Observed Registry × History

/-- The prospective hit and its actual response are those observed by the registered-hit handler. -/
@[expose] noncomputable def joint (pp : PublicParam) (q : Nat) :=
  (watched pp cut register (fun s b => (target pp s b).isSome) q).extendState
    (fun t s w t' flag => MarkedHit.update (activePost pp (target pp))
      (matchesPost (target pp)) t s.1 w t'.1 flag)

/-- Dropping the hit flag gives the original search ledger on the very same capped path. -/
theorem joint_ledger {α : Type} (pp : PublicParam) (q : Nat) (p : OracleComp Queries α)
    (s : WatchedState)
    (flag : Bool) :
    Prod.map id Prod.fst <$> (simulateQ (joint pp q) p).run (s, flag) =
      (simulateQ (watched pp cut register (fun r b => (target pp r b).isSome) q) p).run s :=
  extendState_run_proj_eq _ _ p s flag

/-- Projecting away the search history recovers the registered-hit run and its complete counters. -/
theorem joint_post {α : Type} (pp : PublicParam) (q : Nat) (p : OracleComp Queries α)
    (s : WatchedState × Bool) :
    Prod.map id (fun z : WatchedState × Bool => (z.1.1, z.2)) <$> (simulateQ (joint pp q) p).run s =
      (simulateQ (trackPost pp register (target pp) q fun w => (digits w).isSome) p).run
        (s.1.1, s.2) := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro t st
  simp [joint, watched, trackPost, QueryImpl.extendState_apply, Functor.map_map,
    bind_pure_comp]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
