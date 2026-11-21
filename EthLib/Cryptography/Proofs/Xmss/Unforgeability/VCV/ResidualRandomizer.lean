module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ResidualSchedule
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerReleaseTrace

/-!
# The actual private randomizer reads used during a two-layer signing call

The bottom randomizer uses the entry cache and the top randomizer uses the cache after that draw.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig OracleSpec OracleComp TwoLayerGraph Honest
open Classical

/-- Project the word returned by the actual residual-state callback at a saved state. -/
noncomputable def savedPrf (pp : PublicParam) (before : ResidualCache pp) :
    SeedPrf (OracleComp SharedSpec) :=
  fun p a bytes => Prod.fst <$> (graphPrf pp p a bytes).run before

/-- Use the lower saved cache at a bottom randomizer address and the upper saved cache otherwise. -/
noncomputable def signingPrf (pp : PublicParam) (lower upper : ResidualCache pp) :
    SeedPrf (OracleComp SharedSpec) :=
  fun p a bytes => if ∃ e, a = addrRnd .bottom e then savedPrf pp lower p a bytes
    else savedPrf pp upper p a bytes

@[simp] theorem signingPrf_bottom (pp : PublicParam) (lower upper : ResidualCache pp)
    (p : PublicParam) (e : UInt32) (bytes : ByteArray) :
    signingPrf pp lower upper p (addrRnd .bottom e) bytes =
      Prod.fst <$> (graphPrf pp p (addrRnd .bottom e) bytes).run lower := by
  rw [signingPrf, ite_eq_left ⟨e, rfl⟩]
  rfl

@[simp] theorem signingPrf_top (pp : PublicParam) (lower upper : ResidualCache pp)
    (p : PublicParam) (e : UInt32) (bytes : ByteArray) :
    signingPrf pp lower upper p (addrRnd .top e) bytes =
      Prod.fst <$> (graphPrf pp p (addrRnd .top e) bytes).run upper := by
  have sep : ¬ ∃ n, addrRnd .top e = addrRnd .bottom n :=
    fun ⟨_, same⟩ => Layer.noConfusion (addrRnd_inj.mp same).1
  rw [signingPrf, ite_eq_right sep]
  rfl

private theorem lifted_random {α : Type} (p : ProbComp α) :
    AllQueriesSatisfy (liftComp (liftM p : OracleComp ChainWorld α) SharedSpec) (Within ∅) := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    apply allQueriesSatisfy_bind _ ih
    apply (allQueriesSatisfy_query_iff _ _).2
    intro c eq
    cases eq

private theorem saved_random (pp : PublicParam) (extra : ResidualCache pp) (l : Layer)
    (e : UInt32) (msg : ByteArray) :
    AllQueriesSatisfy (savedPrf pp extra pp (addrRnd l e) msg) (Within ∅) := by
  obtain ⟨lo, hi⟩ := randomizer_residual pp l e msg
  unfold savedPrf graphPrf sourcePrf
  have distribute {α β : Type} (f : α → β) (body : OracleComp Source α) :
      inGraph pp (f <$> body) = f <$> inGraph pp body := by
    simp only [← bind_pure_comp, inGraph_bind, inGraph_pure]
  rw [distribute, StateT.run_map]
  simp only [inGraph, StateT.run_mk, residual_other pp _ lo hi extra, liftComp_bind, liftComp_pure,
    ← bind_pure_comp, bind_assoc, pure_bind]
  apply allQueriesSatisfy_bind (lifted_random _)
  intro first
  apply allQueriesSatisfy_bind (lifted_random _)
  intro second
  exact allQueriesSatisfy_pure _ _

/-- Drawing the private randomizer only consults its residual table or issues uniform coins. -/
theorem signingPrf_residual (pp : PublicParam) (lower upper : ResidualCache pp) :
    ResidualReads pp (signingPrf pp lower upper) := by
  intro l e msg
  cases l with
  | bottom => rw [signingPrf_bottom]; exact saved_random pp lower .bottom e msg
  | top => rw [signingPrf_top]; exact saved_random pp upper .top e msg

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
