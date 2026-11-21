module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedPrivacy
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainDisclosure

/-!
# The signed position behind an opened WOTS+C chain

A verifier can use a disclosed chain value to compute later positions.

A position already open on one chain therefore needs an actual release at that position or earlier.

The accounting identifies the layer, key, chain and digit.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleSpec OracleComp
open ChainDisclosure
open ChainGraph (Word)

/-- A successful signing reply that disclosed this chain no later than the specified digit. -/
@[expose] def ReleasedBefore (pp : PublicParam) (s : SharedState) (log : RawLog) (l : Layer)
    (e : UInt32) (i : Fin V) (d : Fin CHAIN_LENGTH) : Prop :=
  ∃ (req : SignRequest) (sig : Signature), (req,.ok sig) ∈ log ∧ sig.leafIndex = req.leafIndex ∧
    ∃ (root : Digest) (x y : Vector (Fin CHAIN_LENGTH) V),
    s.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT (bottomTree req.leafIndex)))) =
      some (ChainGraph.digestEquiv root) ∧
    Trial pp .bottom (UInt32.ofNat req.leafIndex.toNat)
      (packBytes req.message) sig.bottom.randomizer x s ∧
    Trial pp .top (UInt32.ofNat (bottomTree req.leafIndex))
      (packBytes root) sig.top.randomizer y s ∧
    ((l = .bottom ∧ e = UInt32.ofNat req.leafIndex.toNat ∧ x[i] ≤ d) ∨
      (l = .top ∧ e = UInt32.ofNat (bottomTree req.leafIndex) ∧ y[i] ≤ d))

attribute [local irreducible] simulateQ graph mixedGame mixedOracle Xmss.verifyWith

/-- A nonterminal cell present after verification comes from this signed chain. -/
theorem release_of_present (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    (obs : Outcome) (out : ResidualCache pp) (t : DeferredState)
    (actual : (some (obs,out),t) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run ((∅,∅),[])))
    (l : Layer) (e : UInt32) (i : Fin V) (d : Fin CHAIN_LENGTH)
    (nonterminal : d.val < CHAIN_LENGTH - 1)
    (value : Word) (present : t.1.2 (inLayer l (LayerGraph.position e i d.val)) = some value) :
    ReleasedBefore pp t.1 obs.log l e i d := by
  classical
  let cut : Vector (Fin CHAIN_LENGTH) V :=
    Vector.ofFn fun j => if j = i then ⟨d.val + 1, by omega⟩ else ⟨0, by decide⟩
  have inside : inLayer l (LayerGraph.position e i d.val) ∈ prefixCells l e cut := by
    refine ⟨i,d,?_,rfl⟩
    simp [cut, Fin.lt_def]
  have disclosed : ∃ c ∈ releasedCells pp t.1 obs.log, c ∈ prefixCells l e cut := by
    by_contra! absent
    have none := mixed_prefix_absent pp A left r obs out t actual l e cut absent _ inside
    rw [present] at none
    cases none
  obtain ⟨c, ⟨req,sig,mem,index,root,x,y,row,bottom,top,selected⟩, j,early,lt,pos⟩ := disclosed
  have ji : j = i := by by_contra different; simp [cut, different, Fin.lt_def] at lt
  subst j
  have endDigit : cut[i].val = d.val + 1 := by simp only [cut, Fin.getElem_fin,
      Vector.getElem_ofFn, ite_true]
  have upper : early ≤ d := by
    change early.val ≤ d.val
    change early.val < cut[i].val at lt
    rw [endDigit] at lt
    exact Nat.le_of_lt_succ lt
  refine ⟨req,sig,mem,index,root,x,y,row,bottom,top,?_⟩
  rcases selected with ⟨k,eq⟩ | ⟨k,eq⟩
  · have same := congrArg coordinates (eq.symm.trans pos)
    rw [coordinates_at, coordinates_at] at same
    simp only [Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl,rfl,rfl,matched⟩ := same
    exact Or.inl ⟨rfl,rfl,(Fin.ext matched).symm ▸ upper⟩
  · have same := congrArg coordinates (eq.symm.trans pos)
    rw [coordinates_at, coordinates_at] at same
    simp only [Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl,rfl,rfl,matched⟩ := same
    exact Or.inr ⟨rfl,rfl,(Fin.ext matched).symm ▸ upper⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
