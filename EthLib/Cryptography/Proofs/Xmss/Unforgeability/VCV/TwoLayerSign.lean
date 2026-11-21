module

public import EthLib.Cryptography.Proofs.Xmss.Reference
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerBuildPath

/-!
# The current two-layer signing computation

The leanXMSS draft, section "The scheme", signs the message below and its root above.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants HashSig OracleComp Merkle

/-- A layer returns its original no-codeword error before traversing the path. -/
noncomputable def layerSchedule (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (l : Layer) (e : Nat) (msg : ByteArray) :
    OracleComp SharedSpec (Except XmssError LayerSignature) := do
  let some (randomizer, chainValues) ← signSchedule pp l cb (UInt32.ofNat e) msg
    | return .error (.noAdmissibleEncoding l e)
  return .ok { randomizer, chainValues, path := ← pathSchedule pp l e }

theorem signLayer_schedule (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (l : Layer) (paired : Pairs pp l cb) (e : Nat) (msg : ByteArray) :
    simulateQ (graph pp).eagerImpl (Xmss.signLayer hash pp cb l e msg) =
      simulateQ (graph pp).eagerImpl (layerSchedule pp cb l e msg) := by
  simp only [Xmss.signLayer, layerSchedule, simulateQ_bind, ots_schedule pp l cb paired]
  apply bind_congr
  rintro (_ | ⟨rho, vals⟩)
  · rfl
  · simp only [simulateQ_bind, path_pairs pp l cb paired]

private theorem afterBuild {α : Type} (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (paired : Pairs pp .bottom cb) (idx : LeafIndex)
    (k : Digest × Vector Digest LAYER_HEIGHT → OracleComp SharedSpec α) :
    simulateQ (graph pp).eagerImpl
      (Xmss.build hash pp cb .bottom LAYER_HEIGHT (bottomTree idx) >>=
        fun t => k (t.value, t.path LAYER_HEIGHT idx.toNat)) =
    simulateQ (graph pp).eagerImpl
      (builtPathSchedule pp .bottom LAYER_HEIGHT (bottomTree idx) idx.toNat >>= k) := by
  have same := build_path_pairs pp .bottom cb paired LAYER_HEIGHT (bottomTree idx)
    idx.toNat le_rfl rfl
  have joined := congrArg (fun p => p >>= fun z => simulateQ (graph pp).eagerImpl (k z)) same
  simpa only [simulateQ_map, bind_map_left, simulateQ_bind] using joined

/-- The bottom tree is built once; the root and path supplied to both layers share that build. -/
noncomputable def singleBuildSchedule (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (idx : LeafIndex) (msg : Message) : OracleComp SharedSpec (Except XmssError Signature) := do
  let some (randomizer, chainValues) ←
      signSchedule pp .bottom cb (UInt32.ofNat idx.toNat) (packBytes msg)
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  let both ← builtPathSchedule pp .bottom LAYER_HEIGHT (bottomTree idx) idx.toNat
  let bottom : LayerSignature := {randomizer, chainValues, path := both.2}
  let top ← match ← layerSchedule pp cb .top (bottomTree idx) (packBytes both.1) with
    | .ok sig => pure sig
    | .error err => return .error err
  return .ok {leafIndex := idx, bottom, top}

/-- Both finder failure branches and all successful signature bytes keep their native eager law. -/
theorem signDerived_schedule (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (pairs : ∀ l, Pairs pp l cb) (idx : LeafIndex) (msg : Message) :
    simulateQ (graph pp).eagerImpl (Xmss.signDerived hash cb pp idx msg) =
      simulateQ (graph pp).eagerImpl (singleBuildSchedule pp cb idx msg) := by
  unfold Xmss.signDerived singleBuildSchedule
  simp only [simulateQ_bind, ots_schedule pp .bottom cb (pairs .bottom)]
  apply bind_congr
  rintro (_ | ⟨rho, vals⟩)
  · rfl
  · let finish := fun (both : Digest × Vector Digest LAYER_HEIGHT) => do
      let bottom : LayerSignature := {randomizer := rho, chainValues := vals, path := both.2}
      let t ← Xmss.signLayer hash pp cb .top (bottomTree idx) (packBytes both.1)
      match t with
      | .ok top => pure (Except.ok ({leafIndex := idx, bottom, top} : Signature))
      | .error err => pure (.error err)
    trans simulateQ (graph pp).eagerImpl
      (Xmss.build hash pp cb .bottom LAYER_HEIGHT (bottomTree idx) >>=
        fun t => finish (t.value, t.path LAYER_HEIGHT idx.toNat))
    · simp only [finish, simulateQ_bind]
      apply bind_congr
      intro tree
      apply bind_congr
      intro reply
      cases reply <;> rfl
    · rw [afterBuild pp cb (pairs .bottom) idx finish]
      simp only [finish, simulateQ_bind]
      apply bind_congr
      intro both
      rw [signLayer_schedule pp cb .top (pairs .top)]
      apply bind_congr
      intro reply
      cases reply <;> rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
