module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedSignerProgram
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedParameter

/-!
# Private-cache growth through both signing layers

The native tag for the sampled parameter stays available after every attempted signature.

The two private randomizer lookups can add entries.

Internal graph operations and public digest trials preserve the complete residual cache.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleComp OracleSpec HashSig Constants TwoLayerGraph Honest

/-- Every supported return, including a signing error, extends the local derivation table. -/
@[expose] def ExtendsPrivate {α : Type} {pp : PublicParam} (p : MixedLocal pp α) :=
  ∀ s z, z ∈ support (p.run s) → s.2 ≤ z.2.2

theorem ExtendsPrivate.bind {α β : Type} {pp : PublicParam} {p : MixedLocal pp α}
    {f : α → MixedLocal pp β} (first : ExtendsPrivate p) (tail : ∀ a, ExtendsPrivate (f a)) :
    ExtendsPrivate (p >>= f) := by
  intro s z ran
  rw [StateT.run_bind, mem_support_bind_iff] at ran
  obtain ⟨⟨a,mid⟩, h, k⟩ := ran
  exact (first _ _ h).trans (tail a _ _ k)

theorem ExtendsPrivate.pure {α : Type} {pp : PublicParam}
    (a : α) : ExtendsPrivate (pure a : MixedLocal pp α) := by
  intro s z ran
  simp only [StateT.run_pure, mem_support_pure_iff] at ran
  subst z
  exact le_rfl

theorem ExtendsPrivate.lift {α : Type} {pp : PublicParam} (p : OracleComp MixedWorld α) :
    ExtendsPrivate (liftM p : MixedLocal pp α) := by
  intro s z ran
  simp only [StateT.run_monadLift, monadLift_self, mem_support_bind_iff,
    mem_support_pure_iff] at ran
  obtain ⟨_, _, rfl⟩ := ran
  exact le_rfl

theorem mixed_signature_grows (emit : Structural) (pp : PublicParam) (idx : LeafIndex)
    (msg : Message) :
    ExtendsPrivate (mixedSignature emit pp idx msg) := by
  have finder (l : Layer) (e : UInt32) (bytes : ByteArray) :
      ExtendsPrivate (mixedFind pp l e bytes) := by
    apply ExtendsPrivate.bind (fun s _ h => mixedRandomizer_extends pp l e bytes s h)
    exact fun _ => ExtendsPrivate.lift _
  have ots (e : UInt32) (bytes : ByteArray) : ExtendsPrivate (mixedOts emit pp .top e bytes) := by
    apply ExtendsPrivate.bind (finder .top e bytes)
    rintro (_ | ⟨rho,x⟩)
    · apply ExtendsPrivate.pure
    · exact (ExtendsPrivate.lift _).bind (fun _ => ExtendsPrivate.pure _)
  have top (e : Nat) (bytes : ByteArray) : ExtendsPrivate (mixedTop emit pp e bytes) := by
    apply ExtendsPrivate.bind (ots _ bytes)
    rintro (_ | ⟨rho,ys⟩)
    · apply ExtendsPrivate.pure
    · exact (ExtendsPrivate.lift _).bind (fun _ => ExtendsPrivate.pure _)
  have tree : ExtendsPrivate (mixedTree emit pp idx) := by
    apply ExtendsPrivate.bind (ExtendsPrivate.lift _)
    intro root
    apply ExtendsPrivate.bind (top _ _)
    rintro (_ | sig)
    · apply ExtendsPrivate.pure
    · exact (ExtendsPrivate.lift _).bind (fun _ => ExtendsPrivate.pure _)
  apply ExtendsPrivate.bind (finder .bottom _ _)
  rintro (_ | ⟨rho,x⟩)
  · apply ExtendsPrivate.pure
  · apply ExtendsPrivate.bind (ExtendsPrivate.lift _)
    intro _
    apply ExtendsPrivate.bind tree
    rintro (_ | sig)
    · apply ExtendsPrivate.pure
    · exact (ExtendsPrivate.lift _).bind (fun _ => ExtendsPrivate.pure _)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
