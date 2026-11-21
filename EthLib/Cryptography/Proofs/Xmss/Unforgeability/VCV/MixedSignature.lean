module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.GuardedSigner
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedVerifier
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructureCalls
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructure

/-!
# A normalized signer in the physical mixed query language

Recursive structural programs are interpreted as internal graph operations.

The public full-word port carries only the original message digest trials.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig OracleComp OracleSpec Constants TwoLayerGraph Honest
open LayerGraph.Hidden


-- The digest and the randomizer have separately named 16-byte lengths.
set_option backward.isDefEq.respectTransparency false in
theorem guarded_mixed_find (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    SameMixed pp (guardedFind pp l e msg) (mixedFind pp l e msg) := by
  unfold guardedFind mixedFind randomizerBase
  simp only [liftM_bind, liftM_pure, bind_assoc, pure_bind]
  exact (selected_mixed_randomizer pp l e msg).bind fun value =>
    mixed_finder pp l e msg (halfOf 0 value) _ _

/-- Each structural lookup agrees with its pre-cap internal program and preserves local state. -/
structure StructuralAt (emit : Structural) (pp : PublicParam) where
  topValues : ∀ e x, let sel := selection pp .top
    let op := simulateQ sel.liftQuery (beforeValues pp .top e x >>= fun _ => revealValues e x)
    SameMixed pp (liftM op) (emitted emit pp op)
  topPath : ∀ e, let op := pathSchedule pp .top e
    SameMixed pp (liftM op) (emitted emit pp op)
  root : ∀ idx, let op := bottomRootSchedule pp idx
    SameMixed pp (liftM op) (emitted emit pp op)
  path : ∀ idx, let op := bottomPathSchedule pp idx
    SameMixed pp (liftM op) (emitted emit pp op)
  touch : ∀ e x, let op := simulateQ (selection pp .bottom).liftQuery (beforeValues pp .bottom e x)
    SameMixed pp (liftM op) (emitted emit pp op)
  values : ∀ e x, let op := simulateQ (selection pp .bottom).liftQuery (revealValues e x)
    SameMixed pp (liftM op) (emitted emit pp op)

private theorem mixed_ots (emit : Structural) (pp : PublicParam) (structural : StructuralAt emit pp)
    (e : UInt32) (msg : ByteArray) :
    SameMixed pp (guardedOts pp .top e msg) (mixedOts emit pp .top e msg) := by
  unfold guardedOts mixedOts
  apply SameMixed.bind (guarded_mixed_find pp .top e msg)
  rintro (_ | ⟨rho,x⟩)
  · apply SameMixed.pure
  · exact (structural.topValues e x).bind (fun ys => SameMixed.pure _)

private theorem mixed_top (emit : Structural) (pp : PublicParam) (structural : StructuralAt emit pp)
    (e : Nat) (msg : ByteArray) :
    SameMixed pp (guardedTop pp e msg) (mixedTop emit pp e msg) := by
  unfold guardedTop mixedTop
  apply SameMixed.bind (mixed_ots emit pp structural _ msg)
  rintro (_ | ⟨rho,v⟩)
  · apply SameMixed.pure
  · exact (structural.topPath e).bind fun _ => SameMixed.pure _

private theorem mixed_tree (emit : Structural) (pp : PublicParam)
    (structural : StructuralAt emit pp)
    (idx : LeafIndex) : SameMixed pp (guardedTree pp idx) (mixedTree emit pp idx) := by
  unfold guardedTree mixedTree
  apply SameMixed.bind (structural.root idx)
  intro root
  apply SameMixed.bind (mixed_top emit pp structural _ _)
  rintro (_ | top)
  · apply SameMixed.pure
  · exact (structural.path idx).bind (fun path => SameMixed.pure _)

/-- Both signing layers use the same mixed physical budget at the genuinely selected parameter. -/
theorem mixed_signature (emit : Structural) (pp : PublicParam) (structural : StructuralAt emit pp)
    (idx : LeafIndex) (msg : Message) :
    SameMixed pp (simulateQ (selectedImpl pp) (simulateQ (mark IsTrial)
      (signDerived (hashOf sourcePass) sourcePrf pp idx msg))) (mixedSignature emit pp idx msg) :=
        by
  apply SameMixed.of_eager (guarded_signature pp idx msg)
  unfold guardedSignature mixedSignature
  apply SameMixed.bind (guarded_mixed_find pp .bottom _ _)
  rintro (_ | ⟨rho,x⟩)
  · apply SameMixed.pure
  · apply SameMixed.bind (structural.touch _ x)
    intro _
    apply SameMixed.bind (mixed_tree emit pp structural idx)
    rintro (_ | top)
    · apply SameMixed.pure
    · exact (structural.values _ x).bind fun _ => SameMixed.pure _

/-- The real structural encoder satisfies every use of the two-layer signing schedule. -/
theorem actual_structure (pp : PublicParam) : StructuralAt emitStructure pp := by
  constructor
  · intro e x
    apply structural_call
    rw [simulateQ_bind]
    exact bind_structural (beforeValues_structural pp .top e x) fun _ =>
      revealValues_structural pp .top e x
  · intro e
    exact structural_call pp (path_structural pp .top e)
  · intro idx
    exact structural_call pp (root_structural pp .bottom LAYER_HEIGHT (bottomTree idx))
  · intro idx
    exact structural_call pp (bottomPath_structural pp idx)
  · intro e x
    exact structural_call pp (beforeValues_structural pp .bottom e x)
  · intro e x
    exact structural_call pp (revealValues_structural pp .bottom e x)

/-- The production signer with phase marks has this concrete pre-cap mixed implementation. -/
theorem actual_mixed_signature (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    SameMixed pp (simulateQ (selectedImpl pp) (simulateQ (mark IsTrial)
      (signDerived (hashOf sourcePass) sourcePrf pp idx msg)))
        (mixedSignature emitStructure pp idx msg) :=
  mixed_signature emitStructure pp (actual_structure pp) idx msg

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
