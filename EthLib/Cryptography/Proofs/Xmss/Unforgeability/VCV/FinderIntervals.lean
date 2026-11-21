module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFrames
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructure

/-!
# Same-key intervals of the actual signing algorithm

The bottom finder can be followed by a failed or successful upper finder.

The upper finder calls only its own key and preserves the lower message rows.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleComp
    OracleSpec LayerGraph.Hidden
open EarlierDigest EarlierDigest.Ledger

private def Protects (pp : PublicParam) (k : Key) {α : Type} (p : Program pp α) : Prop :=
  ∀ r, AllQueriesSatisfy (p.run r) (Outside pp k)

private theorem protects_bind {pp k} {α β : Type} {p : Program pp α} {f : α → Program pp β}
    (first : Protects pp k p) (rest : ∀ a, Protects pp k (f a)) : Protects pp k (p >>= f) := by
  intro r
  rw [StateT.run_bind]
  exact allQueriesSatisfy_bind (first r) fun z => rest _ _

private theorem protects_pure {pp k} {α : Type} (a : α) : Protects pp k (pure a) :=
  fun _ => allQueriesSatisfy_pure _ _

private theorem protects_notice {pp k} (n : FinderNotice) : Protects pp k (emit n) := by
  intro r
  rw [emit, StateT.run_mk, ← bind_pure_comp]
  apply allQueriesSatisfy_bind
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · exact fun _ => allQueriesSatisfy_pure _ _

/-- After upper selection, chain and path reads and both registrations preserve physical rows. -/
theorem upper_interval (pp : PublicParam) (idx : LeafIndex) (lower upper : ByteArray)
    (rho tau : Randomizer) (x y : Vector (Fin CHAIN_LENGTH) V) (k : Key) :
    ∀ r, AllQueriesSatisfy ((afterUpper pp idx lower upper rho tau x y).run r) (Outside pp k) := by
  change Protects pp k _
  unfold afterUpper
  apply protects_bind
  · apply structural_outside
    rw [simulateQ_bind]
    exact bind_structural (beforeValues_structural ..) fun _ => revealValues_structural ..
  intro _
  apply protects_bind (structural_outside (path_structural ..) pp k)
  intro _
  apply protects_bind (structural_outside (bottomPath_structural ..) pp k)
  intro _
  apply protects_bind (structural_outside (revealValues_structural ..) pp k)
  intro _
  exact protects_bind (protects_notice _) fun _ =>
    protects_bind (protects_notice _) fun _ => protects_pure _

/-- The upper search and both registrations preserve the lower rows after lower selection. -/
theorem lower_interval (pp : PublicParam) (idx : LeafIndex) (lower : ByteArray)
    (rho : Randomizer) (x : Vector (Fin CHAIN_LENGTH) V) :
    ∀ r, AllQueriesSatisfy ((afterLower pp idx lower rho x).run r) (Outside pp (.bottom,idx)) := by
  change Protects pp (.bottom,idx) _
  unfold afterLower
  apply protects_bind (structural_outside (beforeValues_structural ..) pp _)
  intro _
  apply protects_bind (structural_outside (root_structural ..) pp _)
  intro root
  apply protects_bind (find_outside pp .top _ _ (.bottom,idx) (by simp))
  rintro (_ | ⟨tau,y⟩)
  · exact protects_pure _
  · exact upper_interval pp idx lower (packBytes root) rho tau x y (.bottom,idx)

/-- Both upper outcomes preserve the lower message words present when its finder stopped. -/
theorem lower_rows {pp idx msg rho x r s z} (actual : z ∈ support ((simulateQ (handler pp cut)
    ((afterLower pp idx msg rho x).run r)).run s)) :
    ∀ b, PostSigning.messageKey pp b = some (.bottom,idx) → z.2.2.1.1 b = s.2.1.1 b :=
  outside_frame pp _ _ (lower_interval ..) actual

/-- The upper key's message rows keep their values from the end of its finder. -/
theorem upper_rows {pp idx lower upper rho tau x y r s z}
    (actual : z ∈ support ((simulateQ (handler pp cut)
      ((afterUpper pp idx lower upper rho tau x y).run r)).run s)) :
    let k := (Layer.top, UInt32.ofNat (bottomTree idx))
    ∀ b, PostSigning.messageKey pp b = some k → z.2.2.1.1 b = s.2.1.1 b :=
  outside_frame pp _ _ (upper_interval ..) actual

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
