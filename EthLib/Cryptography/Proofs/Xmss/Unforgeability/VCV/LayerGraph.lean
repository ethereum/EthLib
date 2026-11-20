module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LeafGraph
public import VCVio.OracleComp.QueryTracking.RandomOracle.ProjectedHazards
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# A layer of the leanXMSS hash graph

The leanXMSS draft, sections "WOTS+C" and "Trees", fixes the order and addresses of the hashes.
An OTS leaf reads the last low row of each chain.
A tree node reads the low rows of its two children.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

open Constants HashSig OracleSpec OracleComp
open ChainGraph (Word Public)

/-- Each role describes one physical hash within a fixed layer and public parameter.
A node stores its child's level, so its own level ranges from one to the layer height. -/
inductive Role where
  | chain (epoch : UInt32) (index : Fin V) (step : Fin (CHAIN_LENGTH - 1))
  | leaf (epoch : UInt32)
  | node (childLevel : Fin LAYER_HEIGHT) (index : UInt32)
  deriving DecidableEq

abbrev Start := UInt32 × Fin V
abbrev Row := Role ⊕ Role
abbrev Cell := Start ⊕ Row

/-- Position zero of a chain comes from the private derivation.
Every later position is its previous step's low row. -/
def chainCell (e : UInt32) (i : Fin V) (step : Fin (CHAIN_LENGTH - 1)) : Cell :=
  if h : step.val = 0 then .inl (e, i)
  else .inr (.inl (.chain e i ⟨step.val - 1, by have := step.isLt; omega⟩))

/-- The leaf at level zero and the internal nodes above it share one numbering. -/
def atDepth (level : Fin (LAYER_HEIGHT + 1)) (index : UInt32) : Role :=
  if h : level.val = 0 then .leaf index
  else .node ⟨level.val - 1, by have := level.isLt; omega⟩ index

/-- The actual low outputs that supply each hash payload, in specification order. -/
def children : Role → List Cell
  | .chain e i j => [chainCell e i j]
  | .leaf e => List.ofFn (n := V) fun i => .inr (.inl (.chain e i ⟨CHAIN_LENGTH - 2, by decide⟩))
  | .node level j =>
    [.inr (.inl (atDepth level.castSucc (2 * j))), .inr (.inl (atDepth level.castSucc (2 * j + 1)))]

def arity : Role → Nat
  | .chain .. => 1
  | .leaf .. => V
  | .node .. => 2

@[simp] theorem length_children (r : Role) : (children r).length = arity r := by
  cases r <;> simp [children, arity]

def address (layer : Layer) : Role → Address
  | .chain e _ step => addrChain layer e step
  | .leaf e => addrLeaf layer e
  | .node level j => addrNode layer level.succ j

def payload (r : Role) (vs : List Word) : ByteArray :=
  match r with
  | .chain _ i _ => packBytes (ofBV 16 (vs.headD 0)) ++ packBytes (uintToBytes 16 i.val)
  | .leaf _ => packDigests (LeafGraph.digests V vs)
  | .node .. => packDigests (LeafGraph.digests 2 vs)

/-- The complete byte string passed to the hash at a role. -/
def input (pp : PublicParam) (layer : Layer) (r : Role) (vs : List Word) : HashInput :=
  (thInput pp (address layer r) (payload r vs)).data.toList

/-- A valid input determines its role and its complete ordered list of children.
The domain tag separates chains, leaves and tree nodes. -/
theorem input_injective {pp : PublicParam} {layer : Layer} {r s : Role} {vs ws : List Word}
    (hv : vs.length = arity r) (hw : ws.length = arity s)
    (same : input pp layer r vs = input pp layer s ws) : r = s ∧ vs = ws := by
  have addr : address layer r = address layer s :=
    (thInput_inj (ByteArray.ext (Array.toList_inj.mp same))).2.1
  cases r <;> cases s
  case chain.chain e i j e' i' j' =>
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hv
    obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hw
    have eqn : ChainGraph.input pp (⟨layer, e, i⟩, j) v =
        ChainGraph.input pp (⟨layer, e', i'⟩, j') w := same
    obtain ⟨steps, values⟩ := ChainGraph.input_injective eqn
    exact ⟨congrArg (fun z : ChainGraph.Step => Role.chain z.1.epoch z.1.index z.2) steps,
      congrArg (fun x => [x]) values⟩
  case leaf.leaf e e' =>
    have key := (addrLeaf_inj.mp addr).2
    subst e'
    exact ⟨rfl, LeafGraph.input_injective hv hw same⟩
  case node.node l j l' j' =>
    obtain ⟨_, levels, rfl⟩ := addrNode_inj.mp addr
    have hl : l = l' := Fin.succ_inj.mp levels
    subst l'
    exact ⟨rfl, LeafGraph.input_injective hv hw same⟩
  all_goals
    exact False.elim (encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide) addr)

/-- Both public halves use the same physical input and the same low predecessor rows. -/
def graph (pp : PublicParam) (layer : Layer) : CanonicalGraph Public Start Row Word where
  ch r := r.elim children children
  pt r vs := r.elim (fun k => .inl (input pp layer k vs)) (fun k => .inr (input pp layer k vs))
  range_eq _ _ := rfl
  pt_inj := by
    intro r s vs ws hv hw same
    cases r <;> cases s <;> simp at same hv hw
    all_goals
      obtain ⟨rfl, rfl⟩ := input_injective hv hw same
      exact ⟨rfl, rfl⟩

/-- Decode one target role for any valid physical hash input in the layer. -/
noncomputable def decode (pp : PublicParam) (layer : Layer) (b : HashInput) : Option Role := open Classical in
  if h : ∃ r, ∃ vs : List Word, vs.length = arity r ∧ input pp layer r vs = b
    then some h.choose else none

theorem decode_input (pp : PublicParam) (layer : Layer) (r : Role) (vs : List Word)
    (size : vs.length = arity r) : decode pp layer (input pp layer r vs) = some r := by
  have h : ∃ s, ∃ ws : List Word, ws.length = arity s ∧ input pp layer s ws = input pp layer r vs :=
    ⟨r, vs, size, rfl⟩
  obtain ⟨ws, width, same⟩ := h.choose_spec
  exact (dite_eq_left h).trans (congrArg some (input_injective width size same).1)

/-- Chain steps, leaves and tree nodes share one low-row projected-hit potential. -/
noncomputable def lowKeys (pp : PublicParam) (layer : Layer) : (graph pp layer).ProjKeys where
  node := Sum.elim (fun b => (decode pp layer b).map Sum.inl) (fun _ => none)
  proj _ v := v
  prEvent_proj_le _ _ _ v := (SampleableType.prEvent_uniformSample_eq_singleton_natCard v).le

end EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph
