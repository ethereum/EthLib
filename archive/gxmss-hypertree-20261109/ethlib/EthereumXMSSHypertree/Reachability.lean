/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.Coordinates
public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Proofs.Xmss.Encoding

/-!
# Concrete source hash-call counts and legal tree coordinates

The counting interpreter runs the existing source definitions. Each invocation
of the supplied hash costs one, even if an earlier invocation used identical
bytes. Seed derivations use this same hash through the source `seedPrf`.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography
open Xmss Xmss.Constants

namespace Reachability

/-- A deterministic result together with the number of source hash invocations. -/
structure Counted (α : Type) where
  /-- The value returned by the source computation. -/
  result : α
  /-- Hash invocations, including repeated inputs. -/
  calls : Nat
  /-- Actual hash inputs in execution order, retaining duplicates. -/
  inputs : List ByteArray

/-- Sequence deterministic computations and add their invocation counts. -/
@[expose] def Counted.bind {α β : Type} (x : Counted α) (f : α → Counted β) : Counted β :=
  let y := f x.result
  ⟨y.result, x.calls + y.calls, x.inputs ++ y.inputs⟩

/-- Counting computations have the source's ordinary sequential monadic structure. -/
instance : Monad Counted where
  pure x := ⟨x, 0, []⟩
  bind := Counted.bind

/-- One invocation returns the full deterministic response and costs exactly one. -/
@[expose] def countedHash (H : ByteArray → Vector UInt8 32) (input : ByteArray) :
    Counted (Vector UInt8 32) := ⟨H input, 1, [input]⟩

/-- Computing a source vector in order adds one fixed cost for each entry. -/
theorem ofFnInOrder_calls {α : Type} (n c : Nat) (f : Fin n → Counted α)
    (hf : ∀ i, (f i).calls = c) : (HashSig.ofFnInOrder n f).calls = n * c := by
  induction n with
  | zero => simp [HashSig.ofFnInOrder, pure]
  | succ n ih =>
    simp only [HashSig.ofFnInOrder, bind, pure, Counted.bind]
    change (f 0).calls + (HashSig.ofFnInOrder n (fun i => f i.succ)).calls + 0 = (n + 1) * c
    rw [hf, ih (fun i => f i.succ) (fun i => hf i.succ)]
    simp [Nat.add_mul, Nat.add_comm]

/-- Ordered source vector evaluation sums its actual per-entry invocation counts. -/
theorem ofFnInOrder_calls_sum {α : Type} (n : Nat) (f : Fin n → Counted α) :
    (HashSig.ofFnInOrder n f).calls = ∑ i : Fin n, (f i).calls := by
  induction n with
  | zero => simp [HashSig.ofFnInOrder, pure]
  | succ n ih =>
    change (f 0).calls + (HashSig.ofFnInOrder n (fun i => f i.succ)).calls + 0 = _
    rw [ih, Fin.sum_univ_succ]
    simp

/-- A tweakable hash is exactly one invocation of the supplied full hash. -/
@[simp] theorem th_calls (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (address : Address) (payload : ByteArray) :
    (th (countedHash H) pp address payload).calls = 1 := rfl

/-- A source seed derivation is one full hash invocation, without half-response splitting. -/
@[simp] theorem seedPrf_calls (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (address : Address) (suffix : ByteArray) :
    (seedPrf (countedHash H) seed pp address suffix).calls = 1 := rfl

/-- The source makes 29 full derivations for its 58 chain starts. -/
@[simp] theorem chainStarts_calls (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : UInt32) :
    (chainStarts pp (seedPrf (countedHash H) seed) layer e).calls = 29 := by
  change (HashSig.ofFnInOrder (V / 2)
    (fun j => seedPrf (countedHash H) seed pp (addrPrf layer e j) .empty)).calls + 0 = 29
  rw [ofFnInOrder_calls (V / 2) 1 _ (fun _ => rfl)]
  rfl

/-- A source chain costs its exact number of steps at every legal starting position. -/
@[simp] theorem chain_calls (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    (Xmss.chain (countedHash H) pp layer e i start steps h value).calls = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    change (Wots.chain (chainStep (countedHash H) pp layer e i) start steps _ value).calls + 1 =
      steps + 1
    rw [show (Wots.chain (chainStep (countedHash H) pp layer e i) start steps _ value).calls =
      steps from ih (by omega)]

/-- The source public leaf costs 29 full derivations, 174 chain steps and one leaf hash. -/
@[simp] theorem publicLeaf_calls (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : UInt32) :
    (otsPublicLeaf (countedHash H) pp (seedPrf (countedHash H) seed) layer e).calls = 204 := by
  change (chainStarts pp (seedPrf (countedHash H) seed) layer e).calls +
    ((HashSig.ofFnInOrder V (fun i => Xmss.chain (countedHash H) pp layer e i 0
      (CHAIN_LENGTH - 1) (by decide)
      ((chainStarts pp (seedPrf (countedHash H) seed) layer e).result[i]))).calls + 1) = 204
  rw [chainStarts_calls, ofFnInOrder_calls V (CHAIN_LENGTH - 1) _ (fun i => chain_calls ..)]
  rfl

/-- The actual successful source reveal phase costs 29 starts plus 106 chain steps. -/
theorem reveal_calls (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : UInt32) (d : Digest)
    (x : Vector (Fin CHAIN_LENGTH) V) (hx : codeword? d = some x) :
    ((do
      let starts ← chainStarts pp (seedPrf (countedHash H) seed) layer e
      HashSig.ofFnInOrder V fun i =>
        Xmss.chain (countedHash H) pp layer e i 0 x[i] (by simp) starts[i]) :
      Counted (Vector Digest V)).calls = 135 := by
  change (chainStarts pp (seedPrf (countedHash H) seed) layer e).calls +
    (HashSig.ofFnInOrder V (fun i => Xmss.chain (countedHash H) pp layer e i 0
      x[i] (by simp)
      ((chainStarts pp (seedPrf (countedHash H) seed) layer e).result[i]))).calls = 135
  rw [chainStarts_calls, ofFnInOrder_calls_sum]
  simp only [chain_calls]
  rw [sum_of_codeword hx]
  rfl

/-- On an admissible successful search, source OTS cost retains the actual trial count. -/
theorem otsSign_calls_of_search_success (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer)
    (d : Digest) (x : Vector (Fin CHAIN_LENGTH) V) (hx : codeword? d = some x)
    (hs : (Internal.findCodeword (countedHash H) pp layer e msg
      (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result
      0 MAX_RANDOMIZER_TRIALS).result = some (rho, x)) :
    (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).calls =
      1 + (Internal.findCodeword (countedHash H) pp layer e msg
        (randomizerBase pp (seedPrf (countedHash H) seed) layer e msg).result
        0 MAX_RANDOMIZER_TRIALS).calls + 135 := by
  simp only [otsSign, bind, Counted.bind]
  rw [hs]
  change 1 + (_ + ((chainStarts pp (seedPrf (countedHash H) seed) layer e).calls +
    ((HashSig.ofFnInOrder V (fun i => Xmss.chain (countedHash H) pp layer e i 0
      x[i] (by simp)
      ((chainStarts pp (seedPrf (countedHash H) seed) layer e).result[i]))).calls + 0))) = _
  rw [chainStarts_calls, ofFnInOrder_calls_sum]
  simp only [chain_calls]
  rw [sum_of_codeword hx]
  simp [TARGET_SUM, Nat.add_assoc]

/-- The recurrence of the actual source node's invocation count. -/
@[expose] def nodeCalls : Nat → Nat
  | 0 => 204
  | level + 1 => nodeCalls level + nodeCalls level + 1

/-- The source recursively computes both subtrees and then hashes their parent. -/
theorem node_calls (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (level j : Nat) :
    (node (countedHash H) pp (seedPrf (countedHash H) seed) layer level j).calls =
      nodeCalls level := by
  induction level generalizing j with
  | zero => exact publicLeaf_calls H seed pp layer (UInt32.ofNat j)
  | succ level ih =>
    change (node (countedHash H) pp (seedPrf (countedHash H) seed) layer level (2 * j)).calls +
      ((node (countedHash H) pp (seedPrf (countedHash H) seed) layer level (2 * j + 1)).calls + 1) =
      nodeCalls (level + 1)
    rw [ih, ih]
    simp [nodeCalls, Nat.add_assoc]

/-- Closed node cost, with every source public leaf and internal node counted. -/
theorem nodeCalls_eq (level : Nat) : nodeCalls level = 204 * 2 ^ level + (2 ^ level - 1) := by
  induction level with
  | zero => rfl
  | succ level ih =>
    simp only [nodeCalls, ih, Nat.pow_succ]
    have hp := Nat.two_pow_pos level
    omega

/-- The source computes each authentication sibling subtree separately. -/
@[expose] def siblingsCalls : Nat → Nat → Nat
  | _, 0 => 0
  | level, n + 1 => nodeCalls level + siblingsCalls (level + 1) n

/-- Sibling cost is the sum of the full source subtree costs at the visited levels. -/
theorem siblingsCalls_eq_sum (level n : Nat) :
    siblingsCalls level n = ∑ i : Fin n, nodeCalls (level + i.val) := by
  induction n generalizing level with
  | zero => simp [siblingsCalls]
  | succ n ih =>
    simp [siblingsCalls, ih, Fin.sum_univ_succ, Nat.add_left_comm, Nat.add_comm]

/-- Exact invocation count for the source's recursive sibling-vector computation. -/
theorem siblings_calls (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (level j n : Nat) :
    (Merkle.siblings (nodeHash (countedHash H) pp layer)
      (leaves (countedHash H) pp (seedPrf (countedHash H) seed) layer) level j n).calls =
      siblingsCalls level n := by
  induction n generalizing level j with
  | zero => rfl
  | succ n ih =>
    change (node (countedHash H) pp (seedPrf (countedHash H) seed) layer level (j ^^^ 1)).calls +
      ((Merkle.siblings (nodeHash (countedHash H) pp layer)
        (leaves (countedHash H) pp (seedPrf (countedHash H) seed) layer)
        (level + 1) (j / 2) n).calls + 0) = siblingsCalls level (n + 1)
    rw [node_calls, ih]
    simp [siblingsCalls]

/-- The unoptimized source path contains 16 independently computed sibling subtrees. -/
theorem path_calls (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : Nat) :
    (path (countedHash H) pp (seedPrf (countedHash H) seed) layer e).calls = 13434659 := by
  rw [path, Merkle.path, siblings_calls]
  decide

/-- A successful source layer adds its complete path computation after the OTS phase. -/
theorem signLayer_calls_of_success (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : Nat) (msg : ByteArray)
    (rho : Randomizer) (values : Vector Digest V)
    (h : (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer
      (UInt32.ofNat e) msg).result = some (rho, values)) :
    (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).calls =
      (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer
        (UInt32.ofNat e) msg).calls + 13434659 := by
  simp only [signLayer, bind, Counted.bind]
  rw [h]
  change _ + ((path (countedHash H) pp (seedPrf (countedHash H) seed) layer e).calls + 0) = _
  rw [path_calls]

/-- Source OTS exhaustion rejects before making any authentication-path calls. -/
theorem signLayer_calls_of_failure (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (e : Nat) (msg : ByteArray)
    (h : (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer
      (UInt32.ofNat e) msg).result = none) :
    (signLayer (countedHash H) pp (seedPrf (countedHash H) seed) layer e msg).calls =
      (otsSign (countedHash H) pp (seedPrf (countedHash H) seed) layer
        (UInt32.ofNat e) msg).calls := by
  simp only [signLayer, bind, Counted.bind]
  rw [h]
  exact Nat.add_zero _

/-- A source tree root of height 16 costs 65,536 public leaves and 65,535 internal hashes. -/
theorem height16_node_calls (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (layer : Layer) (j : Nat) :
    (node (countedHash H) pp (seedPrf (countedHash H) seed) layer LAYER_HEIGHT j).calls =
      13434879 := by
  rw [node_calls]
  decide

/-- Symbolic source key-generation cost includes its scheme-seed and parameter derivations. -/
theorem keyGenWith_calls (H : ByteArray → Vector UInt8 32) (rawSeed : Seed) :
    (keyGenWith (countedHash H) rawSeed).calls = 13434881 := by
  change 1 + (1 +
    ((node (countedHash H)
      (publicParamOf (seedPrf (countedHash H)
        (schemeSeed (countedHash H) rawSeed).result)).result
      (seedPrf (countedHash H) (schemeSeed (countedHash H) rawSeed).result)
      .top LAYER_HEIGHT 0).calls + 0) + 0) = 13434881
  rw [height16_node_calls]

/-- The global source index width on a layer. -/
@[expose] def layerBits : Layer → Nat
  | .bottom => 32
  | .top => 16

/-- A source key coordinate in its layer's actual index domain. -/
abbrev KeyCoordinate (layer : Layer) := Fin (2 ^ layerBits layer)

/-- A source node coordinate at one of the layer's seventeen levels. -/
structure NodeCoordinate (layer : Layer) where
  /-- The leaf level is zero and the tree-root level is sixteen. -/
  level : Fin (LAYER_HEIGHT + 1)
  /-- Bottom indices are global; top indices belong to the single top tree. -/
  index : Fin (2 ^ (layerBits layer - level.val))

/-- Typed source hash sites reached while computing public leaves and tree nodes. -/
inductive QuerySite (layer : Layer) where
  /-- One full response starts two adjacent chains. -/
  | start (key : KeyCoordinate layer) (pair : Fin (V / 2))
  /-- A chain step keeps its actual position and revealed value. -/
  | chain (key : KeyCoordinate layer) (chain : Fin V)
      (position : Fin (CHAIN_LENGTH - 1)) (value : Digest)
  /-- The ordered vector of all 58 chain ends is hashed into one leaf. -/
  | leaf (key : KeyCoordinate layer) (ends : Vector Digest V)
  /-- A non-leaf parent hashes its left child before its right child. -/
  | node (coordinate : NodeCoordinate layer) (nonzero : 0 < coordinate.level.val)
      (left right : Digest)

/-- The exact source byte input associated with one typed site. -/
@[expose] def QuerySite.input {layer : Layer} (seed : Seed) (pp : PublicParam) :
    QuerySite layer → ByteArray
  | .start key pair =>
    thInput pp (addrPrf layer (UInt32.ofNat key.val) pair) (packBytes seed ++ .empty)
  | .chain key i mu value =>
    thInput pp (addrChain layer (UInt32.ofNat key.val) mu)
      (packBytes value ++ packBytes (uintToBytes 16 i.val))
  | .leaf key ends => thInput pp (addrLeaf layer (UInt32.ofNat key.val)) (packDigests ends)
  | .node coordinate _ left right =>
    thInput pp (addrNode layer coordinate.level (UInt32.ofNat coordinate.index.val))
      (packBytes left ++ packBytes right)

/-- Every logged source input has a witness in the exact layer-specific site type. -/
@[expose] def LegalInput (seed : Seed) (pp : PublicParam) (layer : Layer) (input : ByteArray) :
    Prop := ∃ site : QuerySite layer, site.input seed pp = input

/-- Counts match the complete input log and every logged input satisfies a predicate. -/
@[expose] def Sound {α : Type} (P : ByteArray → Prop) (x : Counted α) : Prop :=
  x.calls = x.inputs.length ∧ ∀ input ∈ x.inputs, P input

/-- Returning a value makes no hash calls and has an empty log. -/
theorem sound_pure {α : Type} (P : ByteArray → Prop) (a : α) :
    Sound P (pure a : Counted α) := by
  simp [Sound, pure]

/-- Sequential source computations concatenate all calls and retain their witnesses. -/
theorem sound_bind {α β : Type} {P : ByteArray → Prop} (x : Counted α)
    (f : α → Counted β) (hx : Sound P x) (hf : ∀ a, Sound P (f a)) :
    Sound P (x >>= f) := by
  constructor
  · simp only [Counted.bind, bind, List.length_append]
    rw [hx.1, (hf x.result).1]
  · intro input hi
    obtain h | h := List.mem_append.mp hi
    · exact hx.2 input h
    · exact (hf x.result).2 input h

/-- The counting hash logs one invocation and retains its legal-input witness. -/
theorem sound_countedHash (H : ByteArray → Vector UInt8 32) {P : ByteArray → Prop}
    (input : ByteArray) (hp : P input) : Sound P (countedHash H input) := by
  simp [Sound, countedHash, hp]

/-- Ordered source vector evaluation preserves count/log agreement and legal inputs. -/
theorem sound_ofFnInOrder {α : Type} {P : ByteArray → Prop} (n : Nat)
    (f : Fin n → Counted α) (hf : ∀ i, Sound P (f i)) :
    Sound P (HashSig.ofFnInOrder n f) := by
  induction n with
  | zero => exact sound_pure P _
  | succ n ih =>
    apply sound_bind (f 0) _ (hf 0)
    intro head
    apply sound_bind (HashSig.ofFnInOrder n (fun i => f i.succ)) _
      (ih (fun i => f i.succ) (fun i => hf i.succ))
    intro tail
    exact sound_pure P _

/-- A source tweakable hash retains the exact legal full-input witness. -/
theorem sound_th (H : ByteArray → Vector UInt8 32) {P : ByteArray → Prop}
    (pp : PublicParam) (address : Address) (payload : ByteArray)
    (hp : P (thInput pp address payload)) : Sound P (th (countedHash H) pp address payload) := by
  apply sound_bind _ _ (sound_countedHash H _ hp)
  intro full
  exact sound_pure P _

/-- Every source chain step has its typed chain/key/position witness. -/
theorem sound_chainStep (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (key : KeyCoordinate layer) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) :
    Sound (LegalInput seed pp layer)
      (chainStep (countedHash H) pp layer (UInt32.ofNat key.val) i mu value) := by
  apply sound_th
  exact ⟨.chain key i mu value, rfl⟩

/-- Source chains preserve legal typed sites at all reached positions. -/
theorem sound_chain (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (key : KeyCoordinate layer) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    Sound (LegalInput seed pp layer)
      (Xmss.chain (countedHash H) pp layer (UInt32.ofNat key.val) i start steps h value) := by
  induction steps with
  | zero => exact sound_pure _ _
  | succ steps ih =>
    apply sound_bind _ _ (ih (by omega))
    intro previous
    exact sound_chainStep H seed pp layer key i _ previous

/-- All 29 source derivations have typed paired-chain sites and are counted once each. -/
theorem sound_chainStarts (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (key : KeyCoordinate layer) :
    Sound (LegalInput seed pp layer)
      (chainStarts pp (seedPrf (countedHash H) seed) layer (UInt32.ofNat key.val)) := by
  apply sound_bind
  · apply sound_ofFnInOrder
    intro pair
    exact sound_countedHash H _ ⟨.start key pair, rfl⟩
  · intro pairs
    exact sound_pure _ _

/-- Every call in the actual source public leaf is witnessed by a typed legal site. -/
theorem sound_publicLeaf (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (key : KeyCoordinate layer) :
    Sound (LegalInput seed pp layer)
      (otsPublicLeaf (countedHash H) pp (seedPrf (countedHash H) seed) layer
        (UInt32.ofNat key.val)) := by
  apply sound_bind _ _ (sound_chainStarts H seed pp layer key)
  intro starts
  apply sound_bind
  · apply sound_ofFnInOrder
    intro i
    exact sound_chain H seed pp layer key i _ _ _ starts[i]
  · intro ends
    apply sound_th
    exact ⟨.leaf key ends, rfl⟩

/-- Both source layers have at least sixteen global index bits and at most thirty-two. -/
theorem layerBits_bounds (layer : Layer) : LAYER_HEIGHT ≤ layerBits layer ∧ layerBits layer ≤ 32 :=
  by cases layer <;> decide

/-- Every typed source key coordinate survives its address-word conversion exactly. -/
theorem keyCoordinate_no_wrap {layer : Layer} (key : KeyCoordinate layer) :
    (UInt32.ofNat key.val).toNat = key.val :=
  nodeIndex_no_wrap (level := 0) (layerBits_bounds layer).2 key.isLt

/-- Every typed source node index survives its address-word conversion exactly. -/
theorem nodeCoordinate_no_wrap {layer : Layer} (coordinate : NodeCoordinate layer) :
    (UInt32.ofNat coordinate.index.val).toNat = coordinate.index.val :=
  nodeIndex_no_wrap (layerBits_bounds layer).2 coordinate.index.isLt

/-- Source parent hashing preserves its typed level and global node index. -/
theorem sound_nodeHash (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (level j : Nat) (hl : level ≤ LAYER_HEIGHT) (hpos : 0 < level)
    (hj : NodeBound (layerBits layer) level j) (left right : Digest) :
    Sound (LegalInput seed pp layer) (nodeHash (countedHash H) pp layer level j left right) := by
  apply sound_th
  let coordinate : NodeCoordinate layer :=
    ⟨⟨level, by omega⟩, ⟨j, hj⟩⟩
  refine ⟨.node coordinate hpos left right, ?_⟩
  have hfin : coordinate.level = Fin.ofNat (LAYER_HEIGHT + 1) level := by
    apply Fin.ext
    exact (nodeLevel_no_wrap level hl).symm
  change thInput pp (addrNode layer coordinate.level (UInt32.ofNat j)) _ = _
  rw [hfin]

/-- Every input in the actual recursively computed source node has a legal typed witness. -/
theorem sound_node (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (level j : Nat) (hl : level ≤ LAYER_HEIGHT)
    (hj : NodeBound (layerBits layer) level j) :
    Sound (LegalInput seed pp layer)
      (node (countedHash H) pp (seedPrf (countedHash H) seed) layer level j) := by
  induction level generalizing j with
  | zero => exact sound_publicLeaf H seed pp layer ⟨j, hj⟩
  | succ level ih =>
    have hlevel : level < layerBits layer := by
      have := (layerBits_bounds layer).1
      omega
    obtain ⟨hleft, hright⟩ := children_bound hlevel hj
    apply sound_bind _ _ (ih (2 * j) (by omega) hleft)
    intro left
    apply sound_bind _ _ (ih (2 * j + 1) (by omega) hright)
    intro right
    exact sound_nodeHash H seed pp layer (level + 1) j hl (by omega) hj left right

/-- Parent division preserves the source's level-dependent index bound. -/
theorem parent_bound {bits level j : Nat} (hj : NodeBound bits level j) (hl : level < bits) :
    NodeBound bits (level + 1) (j / 2) := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
  have hp : bits - level = bits - (level + 1) + 1 := by omega
  simpa only [NodeBound, hp, Nat.pow_succ] using hj

/-- Every input in the source's sibling-vector recursion has a legal typed witness. -/
theorem sound_siblings (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (level j n : Nat) (hl : level + n ≤ LAYER_HEIGHT)
    (hj : NodeBound (layerBits layer) level j) :
    Sound (LegalInput seed pp layer)
      (Merkle.siblings (nodeHash (countedHash H) pp layer)
        (leaves (countedHash H) pp (seedPrf (countedHash H) seed) layer) level j n) := by
  induction n generalizing level j with
  | zero => exact sound_pure _ _
  | succ n ih =>
    have hlevel : level < layerBits layer := by
      have := (layerBits_bounds layer).1
      omega
    apply sound_bind _ _ (sound_node H seed pp layer level (j ^^^ 1) (by omega)
      (sibling_bound hj hlevel))
    intro sibling
    apply sound_bind _ _ (ih (level + 1) (j / 2) (by omega) (parent_bound hj hlevel))
    intro rest
    exact sound_pure _ _

/-- Every actual source path call has a typed site, without discarding repeated calls. -/
theorem sound_path (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (key : KeyCoordinate layer) :
    Sound (LegalInput seed pp layer)
      (path (countedHash H) pp (seedPrf (countedHash H) seed) layer key.val) :=
  sound_siblings H seed pp layer 0 key.val LAYER_HEIGHT (by omega) key.isLt

/-- The bottom path keeps the signature's original complete 32-bit global index. -/
theorem sound_bottom_path (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (idx : LeafIndex) : Sound (LegalInput seed pp .bottom)
      (path (countedHash H) pp (seedPrf (countedHash H) seed) .bottom idx.toNat) :=
  sound_path H seed pp .bottom (leafIndexEquiv idx)

/-- The top path uses the original bottom tree number as its bounded key index. -/
theorem sound_top_path (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (idx : LeafIndex) : Sound (LegalInput seed pp .top)
      (path (countedHash H) pp (seedPrf (countedHash H) seed) .top (bottomTree idx)) :=
  sound_path H seed pp .top ⟨bottomTree idx, bottomTree_lt idx⟩

/-- The bottom root recomputed by source signing has legal global coordinates throughout. -/
theorem sound_bottom_root (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (idx : LeafIndex) : Sound (LegalInput seed pp .bottom)
      (node (countedHash H) pp (seedPrf (countedHash H) seed) .bottom
        LAYER_HEIGHT (bottomTree idx)) :=
  sound_node H seed pp .bottom LAYER_HEIGHT (bottomTree idx) (by omega) (bottomTree_lt idx)

/-- Source key generation's top root has legal coordinates throughout. -/
theorem sound_top_root (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam) :
    Sound (LegalInput seed pp .top)
      (node (countedHash H) pp (seedPrf (countedHash H) seed) .top LAYER_HEIGHT 0) :=
  sound_node H seed pp .top LAYER_HEIGHT 0 (by omega) (by change 0 < 1; decide)

/-- A legal source node logs all its invocations, including repeated inputs. -/
theorem node_inputs_length (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (level j : Nat) (hl : level ≤ LAYER_HEIGHT)
    (hj : NodeBound (layerBits layer) level j) :
    (node (countedHash H) pp (seedPrf (countedHash H) seed) layer level j).inputs.length =
      204 * 2 ^ level + (2 ^ level - 1) := by
  rw [← (sound_node H seed pp layer level j hl hj).1, node_calls, nodeCalls_eq]

/-- The actual source path logs exactly its invocation count. -/
theorem path_inputs_length (H : ByteArray → Vector UInt8 32) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (key : KeyCoordinate layer) :
    (path (countedHash H) pp (seedPrf (countedHash H) seed) layer key.val).inputs.length =
      13434659 := by
  rw [← (sound_path H seed pp layer key).1, path_calls]

/-- The source's top certificate, evaluated under a fixed deterministic hash and scheme seed. -/
@[expose] def topCertificate (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (idx : LeafIndex) : Except XmssError LayerSignature :=
  (do
    let root ← node (pureHash H) pp (seedPrf (pureHash H) seed) .bottom
      LAYER_HEIGHT (bottomTree idx)
    signLayer (pureHash H) pp (seedPrf (pureHash H) seed) .top (bottomTree idx)
      (packBytes root) : Id (Except XmssError LayerSignature)).run

/-- Repeated top certificates for one bottom tree have identical pure source outputs. -/
theorem topCertificate_eq (H : ByteArray → Vector UInt8 32) (seed : Seed)
    (pp : PublicParam) (first second : LeafIndex)
    (h : bottomTree first = bottomTree second) :
    topCertificate H seed pp first = topCertificate H seed pp second := by
  simp only [topCertificate, h]

end Reachability

end EthereumXMSSHypertree
