module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistrationProjection

/-!
# The two registrations returned by a successful signing call

The lower finder signs the input message.

The upper finder signs the root returned by this call's bottom tree computation.

A failure at either layer leaves the registration list unchanged.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig OracleComp OracleSpec Constants TwoLayerGraph
    Honest LayerGraph.Hidden

/-- Each registered digest comes from an actual successful finder with the returned randomizer. -/
structure Receipt (pp : PublicParam) (q : Nat) (idx : LeafIndex) (msg : Message)
    (sig : Signature) where
  root : Digest
  x : Vector (Fin CHAIN_LENGTH) V
  y : Vector (Fin CHAIN_LENGTH) V
  lowerPrior : JointState
  upperPrior : JointState
  leaf : sig.leafIndex = idx
  lower : ∃ r s out t, Ran q (find pp .bottom (UInt32.ofNat idx.toNat) (packBytes msg))
    r s (some (sig.bottom.randomizer, x)) out t ∧ (physical t.1).1 ≤ (physical lowerPrior).1
  tree : ∃ r s out t, Ran q (carry (emitted emitStructure pp (bottomRootSchedule pp idx)))
    r s root out t ∧
    (physical t.1).1 ≤ (physical lowerPrior).1
  upper : ∃ r s out t, Ran q (find pp .top (UInt32.ofNat (bottomTree idx)) (packBytes root))
    r s (some (sig.top.randomizer, y)) out t ∧ (physical t.1).1 ≤ (physical upperPrior).1

/-- The upper registration is the newer of the two entries in reverse execution order. -/
@[expose] noncomputable def Receipt.notes {pp q idx msg sig}
    (c : Receipt pp q idx msg sig) : List Registered :=
  [(selectedNotice pp .top (UInt32.ofNat (bottomTree idx)) (packBytes c.root)
    sig.top.randomizer c.y, c.upperPrior),
   (selectedNotice pp .bottom (UInt32.ofNat idx.toNat) (packBytes msg) sig.bottom.randomizer c.x,
     c.lowerPrior)]

/-- Exact effect of one native response on the registration stream. -/
@[expose] def Records (pp : PublicParam) (q : Nat) (idx : LeafIndex) (msg : Message)
    (ans : Except XmssError Signature) (before after : List Registered) : Prop :=
  match ans with
  | .error _ => after = before
  | .ok sig => ∃ c : Receipt pp q idx msg sig, after = c.notes ++ before

attribute [local irreducible] find mixedFind emitStructure beforeValues revealValues pathSchedule

/-- A successful reply emits exactly two registrations after its graph operations. -/
theorem signing_receipt {pp q idx msg r s ans out t}
    (ran : Ran q (signature pp idx msg) r s ans out t) :
    Records pp q idx msg ans (registrations s.2) (registrations t.2) := by
  unfold signature at ran
  obtain ⟨a,_,_,lower,rest⟩ := ran.bind
  rcases a with _ | ⟨rho, x⟩
  · obtain ⟨rfl, _, rfl⟩ := rest.pure_result
    exact lower.find_registers
  · obtain ⟨_,_,_,structural,rest⟩ := rest.bind
    obtain ⟨root,_,_,tree,rest⟩ := rest.bind
    obtain ⟨a,_,_,upper,rest⟩ := rest.bind
    rcases a with _ | ⟨tau, y⟩
    · obtain ⟨rfl, _, rfl⟩ := rest.pure_result
      change registrations _ = _
      rw [upper.find_registers, tree.carry_registers, structural.carry_registers,
        lower.find_registers]
    · obtain ⟨tops,_,_,signTop,rest⟩ := rest.bind
      obtain ⟨auth,_,_,topPath,rest⟩ := rest.bind
      obtain ⟨bottom,_,_,lowPath,rest⟩ := rest.bind
      obtain ⟨ys,_,g,reveal,rest⟩ := rest.bind
      obtain ⟨_,_,g',emitLow,rest⟩ := rest.bind
      obtain ⟨_,_,_,emitTop,done⟩ := rest.bind
      obtain ⟨rfl,_,rfl⟩ := done.pure_result
      have schedule := signTop.graph_mono.trans (topPath.graph_mono.trans
        (lowPath.graph_mono.trans reveal.graph_mono))
      have toLower := upper.graph_mono.trans schedule
      refine ⟨⟨root, x, y, g.1, g'.1, rfl,
        ⟨_,_,_,_,lower,structural.graph_mono.trans (tree.graph_mono.trans toLower)⟩,
        ⟨_,_,_,_,tree,toLower⟩, ⟨_,_,_,_,upper,schedule.trans emitLow.graph_mono⟩⟩, ?_⟩
      rw [emitTop.emitted, emitLow.emitted]
      change _ :: _ :: registrations g.2 = _ :: _ :: registrations s.2
      rw [reveal.carry_registers, lowPath.carry_registers, topPath.carry_registers,
        signTop.carry_registers, upper.find_registers, tree.carry_registers,
        structural.carry_registers, lower.find_registers]
      rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
