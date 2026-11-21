/- Authors: Matthias Meijers -/

module
public import EthereumXMSSHypertree.HypertreeCoordinates
public import EthereumXMSSHypertree.FullInputs
public import EthereumXMSSHypertree.Functional
public import HashSig.GXMSS.Hypertree.HashInstance

/-!
# A functional hash instance for the concrete hypertree

Abstract tweaks retain tagged complete coordinates. Reached chain, leaf and
node inputs are the exact source bytes. Unused rectangle cells and input forms
are totalized under reserved address type 31, without claiming physical source
address injectivity on the whole Merkle rectangle.
-/

public section

namespace EthereumXMSSHypertree.ConcreteHypertree

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants

/-- The full generic Merkle rectangle, including unreachable cells. -/
abbrev TreeRectangle := GXMSS.Hypertree.TreePosition shape × Fin 17 × Fin (2 ^ 16)

/-- Tagged complete coordinates label tweaks injectively throughout the finite forest. -/
abbrev Tweak := GXMSS.Hypertree.ChainPosition shape ⊕ TreeRectangle

/-- The three input forms retain their typed data without changing source payload order. -/
inductive Input where
  /-- One chain value. -/
  | digest (value : Digest)
  /-- Ordered Merkle children. -/
  | pair (left right : Digest)
  /-- All ordered chain endpoints. -/
  | ends (values : Fin 58 → Digest)

/-- Fixed-width little-endian words in a canonical virtual coordinate frame. -/
@[expose] def frameWords (words : List Nat) : ByteArray :=
  words.foldl (fun bytes word => bytes ++ packBytes (uintToBytes 4 word)) .empty

/-- A tag and every abstract coordinate field, including unused rectangle coordinates. -/
@[expose] def tweakFrame : Tweak → ByteArray
  | .inl c => frameWords [0, c.1.1.1.val, c.1.1.2.val, c.1.2.val, c.2.1.val, c.2.2.val]
  | .inr t => frameWords [1, t.1.1.val, t.1.2.val, t.2.1.val, t.2.2.val, 0]

/-- The tagged complete input data of a virtual call. -/
@[expose] def inputFrame : Input → ByteArray
  | .digest value => ByteArray.mk #[0] ++ packBytes value
  | .pair left right => ByteArray.mk #[1] ++ packBytes left ++ packBytes right
  | .ends values => ByteArray.mk #[2] ++ packDigests (Vector.ofFn values)

/-- Address type 31 is reserved for the unused functional extension. -/
@[expose] def virtualAddress : Address := encodeAddress 31 0 0 0

/-- Unused calls have an explicit tagged coordinate/data frame under the reserved address. -/
@[expose] def virtualInput (pp : PublicParam) (tweak : Tweak) (input : Input) : ByteArray :=
  thInput pp virtualAddress (tweakFrame tweak ++ inputFrame input)

/-- A local node lies in the real source component at its own level. -/
@[expose] def ReachedNode (level : Fin 17) (node : Fin (2 ^ 16)) : Prop :=
  0 < level.val ∧ node.val < 2 ^ (16 - level.val)

instance (level : Fin 17) (node : Fin (2 ^ 16)) : Decidable (ReachedNode level node) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Exact source inputs on reached forms, with an explicit unused-domain totalization. -/
@[expose] def hashInput (pp : PublicParam) (tweak : Tweak) (input : Input) : ByteArray :=
  match tweak, input with
  | .inl c, .digest value =>
    chainInput pp (sourceLayer c.1.1) (sourceKey c.1) c.2.1 c.2.2 value
  | .inr (tree, level, node), .ends values =>
    if level.val = 0 then
      FullInputs.leafInput pp (sourceLayer tree) (sourceKey (tree, node)) (Vector.ofFn values)
    else virtualInput pp tweak input
  | .inr (tree, level, node), .pair left right =>
    if ReachedNode level node then
      FullInputs.nodeInput pp (sourceLayer tree) level
        (UInt32.ofNat (nodeGlobalIndex tree level.val node.val)) left right
    else virtualInput pp tweak input
  | _, _ => virtualInput pp tweak input

/-- Every complete chain coordinate injects as a tagged abstract tweak. -/
@[expose] def chainTweak : GXMSS.Hypertree.ChainPosition shape ↪ Tweak :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The entire rectangle injects as a tagged abstract tweak, including invalid physical cells. -/
@[expose] def treeTweak : TreeRectangle ↪ Tweak := ⟨Sum.inr, Sum.inr_injective⟩

/-- A functional instance of the reviewed generic global hash interface. -/
@[expose] def hashInstance (H : ByteArray → Vector UInt8 32) (seedGen : ProbComp PublicParam) :
    GXMSS.Hypertree.HashInstance PublicParam Tweak Input Digest shape where
  thf := ⟨seedGen, fun pp tweak input => halfOf 0 (H (hashInput pp tweak input))⟩
  digestInput := ⟨Input.digest, fun _ _ h => Input.digest.inj h⟩
  pairInput := ⟨fun pair => .pair pair.1 pair.2, by
    intro first second h
    obtain ⟨hleft, hright⟩ := Input.pair.inj h
    exact Prod.ext hleft hright⟩
  vectorInput := ⟨Input.ends, fun _ _ h => Input.ends.inj h⟩
  chainTweak := chainTweak
  treeTweak := treeTweak
  chain_ne_tree _ _ h := by simp [chainTweak, treeTweak] at h

/-- A reached generic chain uses the complete physical source input, including its chain index. -/
theorem hashInput_chain (pp : PublicParam) (position : GXMSS.Hypertree.OTSPosition shape)
    (i : Fin 58) (mu : Fin 3) (value : Digest) :
    hashInput pp (chainTweak (position, i, mu)) (.digest value) =
      chainInput pp (sourceLayer position.1) (sourceKey position) i mu value := rfl

/-- A level-zero endpoint vector uses the exact physical source leaf input. -/
theorem hashInput_leaf (pp : PublicParam) (tree : GXMSS.Hypertree.TreePosition shape)
    (node : Fin (2 ^ 16)) (values : Fin 58 → Digest) :
    hashInput pp (treeTweak (tree, 0, node)) (.ends values) =
      FullInputs.leafInput pp (sourceLayer tree) (sourceKey (tree, node))
        (Vector.ofFn values) := rfl

/-- A reached generic Merkle parent uses the exact source level, global index, and child order. -/
theorem hashInput_node (pp : PublicParam) (tree : GXMSS.Hypertree.TreePosition shape)
    (level : Fin 17) (node : Fin (2 ^ 16)) (left right : Digest) (h : ReachedNode level node) :
    hashInput pp (treeTweak (tree, level, node)) (.pair left right) =
      FullInputs.nodeInput pp (sourceLayer tree) level
        (UInt32.ofNat (nodeGlobalIndex tree level.val node.val)) left right := by
  simp [hashInput, treeTweak, h]

/-- Generic chain evaluation equals the exact source deterministic step. -/
theorem chain_eval (H : ByteArray → Vector UInt8 32) (seedGen : ProbComp PublicParam)
    (pp : PublicParam) (position : GXMSS.Hypertree.OTSPosition shape) (i : Fin 58)
    (mu : Fin 3) (value : Digest) :
    (hashInstance H seedGen).thf.eval pp
      ((hashInstance H seedGen).chainTweak (position, i, mu))
      ((hashInstance H seedGen).digestInput value) =
      Pure.step H pp (sourceLayer position.1) (sourceKey position) i mu value := rfl

/-- Generic leaf evaluation equals the exact source deterministic leaf hash. -/
theorem leaf_eval (H : ByteArray → Vector UInt8 32) (seedGen : ProbComp PublicParam)
    (pp : PublicParam) (tree : GXMSS.Hypertree.TreePosition shape) (node : Fin (2 ^ 16))
    (values : Fin 58 → Digest) :
    (hashInstance H seedGen).thf.eval pp
      ((hashInstance H seedGen).treeTweak (tree, 0, node))
      ((hashInstance H seedGen).vectorInput values) =
      Pure.leafHash H pp (sourceLayer tree) (sourceKey (tree, node)) (Vector.ofFn values) := rfl

/-- Generic reached-node evaluation equals the exact source deterministic node hash. -/
theorem node_eval (H : ByteArray → Vector UInt8 32) (seedGen : ProbComp PublicParam)
    (pp : PublicParam) (tree : GXMSS.Hypertree.TreePosition shape) (level : Fin 17)
    (node : Fin (2 ^ 16)) (left right : Digest) (h : ReachedNode level node) :
    (hashInstance H seedGen).thf.eval pp
      ((hashInstance H seedGen).treeTweak (tree, level, node))
      ((hashInstance H seedGen).pairInput (left, right)) =
      Pure.nodeHash H pp (sourceLayer tree) level.val
        (nodeGlobalIndex tree level.val node.val) left right := by
  change halfOf 0 (H (hashInput pp (treeTweak (tree, level, node)) (.pair left right))) = _
  rw [hashInput_node pp tree level node left right h]
  simp only [FullInputs.nodeInput, Pure.nodeHash, Pure.addressed]
  have hlevel : Fin.ofNat (LAYER_HEIGHT + 1) level.val = level := Fin.ofNat_val_eq_self level
  rw [hlevel]

/-- The virtual address is outside all seven physical source address-type domains. -/
theorem virtualAddress_ne_source (kind : AddressType) (mu : Fin 8)
    (hi : Fin (2 ^ 24)) (lo : UInt32) :
    virtualAddress ≠ encodeAddress kind.code mu hi lo := by
  intro he
  have hc := (encodeAddress_inj.mp he).1
  have hn : (31 : Fin 32) ≠ kind.code := by cases kind <;> decide
  exact hn hc

/-- Totalized virtual inputs cannot equal an addressed physical source input of any purpose. -/
theorem virtualInput_ne_source (pp pp' : PublicParam) (tweak : Tweak) (input : Input)
    (kind : AddressType) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32)
    (payload : ByteArray) :
    virtualInput pp tweak input ≠ thInput pp' (encodeAddress kind.code mu hi lo) payload := by
  intro he
  exact virtualAddress_ne_source kind mu hi lo (thInput_inj he).2.1

/-- An unreachable rectangle cell is evaluated only through the reserved virtual extension. -/
theorem hashInput_unreached_node (pp : PublicParam)
    (tree : GXMSS.Hypertree.TreePosition shape) (level : Fin 17) (node : Fin (2 ^ 16))
    (left right : Digest) (h : ¬ReachedNode level node) :
    hashInput pp (treeTweak (tree, level, node)) (.pair left right) =
      virtualInput pp (treeTweak (tree, level, node)) (.pair left right) := by
  simp [hashInput, treeTweak, h]

/-- Injectivity of the unused coordinate/data byte frame, proved in `HypertreeFrames`. -/
@[expose] def VirtualFrameInjective : Prop :=
  Function.Injective (fun call : Tweak × Input => tweakFrame call.1 ++ inputFrame call.2)

/-- Injectivity of the full-input interpretation, proved in `HypertreeFullInput`. -/
@[expose] def FullInputInjective : Prop :=
  Function.Injective (fun call : PublicParam × Tweak × Input =>
    hashInput call.1 call.2.1 call.2.2)

end EthereumXMSSHypertree.ConcreteHypertree
