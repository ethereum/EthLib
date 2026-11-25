module

public import EthLib.Cryptography.Proofs.Sponge.Games

/-!
# Proofs: exact projections between the intermediate games of the sponge

The ideal side of the combined game is the visible game, once the full view is forgotten.

The visible game without the queries of the sponge is the simulator over path values.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge.Indiff

open OracleComp OracleSpec LazyPermutation Indifferentiability

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E] [DecidableEq Dg] [DecidableEq E] [DecidableEq C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

/-- The walk of the full view makes the queries of its skeleton. -/
theorem map_allWalk (used : List (Dg × E) → Bool) (pre : List (Dg × E)) (s : SpongeState Dg E C)
    (A : PermCache (SpongeState Dg E C)) (bs : List (Dg × E)) :
    (fun _ => ()) <$> allWalk (Msg := Msg) P used pre s A bs = skel (C := C) P pre bs := by
  induction bs generalizing pre s A with
  | nil => simp [allWalk, skel]
  | cons B bs ih =>
    simp only [allWalk, skel, map_bind]
    refine bind_congr fun v => bind_congr fun u => ?_
    split <;> exact ih _ _ _

/-- One step of the ideal side of the combined game is one step of the visible game. -/
theorem combIdeal_proj (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (cs : CState Dg E C Msg) :
    Prod.map id CState.vis <$> (combIdeal P iv t).run cs = (visImpl P iv true t).run cs.vis := by
  rcases t with (n | x | y) | m
  · simp [combIdeal, combStep, visImpl, CState.vis]
  · simp only [combIdeal, combStep, combFwd, visImpl, StateT.run_map, StateT.run_mk,
      map_bind, map_pure]
    rfl
  · simp only [combIdeal, combStep, combInverse, visImpl, StateT.run_map, StateT.run_mk,
      map_bind, map_pure]
    rfl
  · simp only [combIdeal, combStep, combHash, visImpl, StateT.run_map, StateT.run_mk,
      map_bind, map_pure, ite_true]
    rw [← map_allWalk P (usedPath P cs.sim.chains cs.hashed) [] iv cs.all (P.pad m)]
    simp only [bind_map_left]
    rfl

/-- **The ideal side of the combined game is the visible game**, once the full view is forgotten. -/
theorem map_run_combIdeal {α : Type} (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α)
    (cs : CState Dg E C Msg) :
    Prod.map id CState.vis <$> (simulateQ (combIdeal P iv) oa).run cs =
      (simulateQ (visImpl P iv true) oa).run cs.vis :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (combIdeal_proj P iv) oa cs

/-- One step of the visible game without the queries of the sponge is one simulator step. -/
theorem visImpl_false_proj (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (vs : VState Dg E C Msg) :
    Prod.map id Prod.fst <$> (visImpl P iv false t).run vs = (idealTImpl P t).run vs.1 := by
  rcases t with (n | x | y) | m <;> simp [visImpl, idealTImpl]

/-- **The visible game without the queries of the sponge is the simulator over path values.**

The hashed messages and the collision flag are forgotten. -/
theorem map_run_visImpl_false {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) (vs : VState Dg E C Msg) :
    Prod.map id Prod.fst <$> (simulateQ (visImpl P iv false) oa).run vs =
      (simulateQ (idealTImpl P) oa).run vs.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (visImpl_false_proj P iv) oa vs

end EthLib.Cryptography.Sponge.Indiff
