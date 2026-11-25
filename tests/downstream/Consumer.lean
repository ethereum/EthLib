module

public import EthLib.Base.Proofs.Hex
public import EthLib.Cryptography.Bls.Fp12
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.Proofs.Xmss.Bytes
public import EthLib.Cryptography.Proofs.Xmss.Constants
public import EthLib.Execution.Proofs.Transactions.Envelope
public import EthLib.Networking.Proofs.Quic.Frame
public import EthLib.Networking.Proofs.Quic.Packet
public import EthLib.Networking.Proofs.Quic.Tls.Messages
public import EthLib.Networking.Proofs.Quic.Varint
public import EthLib.Serialization.Proofs.Exports.Ssz
public import EthLib.Serialization.Proofs.Rlp
public import EthLib.Serialization.Proofs.Ssz.Typed.Root

/-!
# A downstream consumer of EthLib

A package that depends on EthLib imports these modules and relies on what this file states.

Each example states one declaration that downstream proofs use, with its type written out.

An example that unfolds a definition pins its exposed body.

When an example fails, the public surface of EthLib changed: keep it, or mark the change breaking.
-/

open EthLib

-- A proof that a Keccak-256 circuit or program is right compares its output with this function.
example : (Cryptography.Hash.Keccak.keccak256 : ByteArray → Vector UInt8 32) =
    Cryptography.Hash.Keccak.keccak256 := rfl

-- A proof about a multiplication in Fp12 unfolds the product, so its body stays exposed.
example (a b : Cryptography.Bls.Fp12) :
    Cryptography.Bls.Fp12.mul a b =
      ⟨a.c0 * b.c0 + (a.c1 * b.c1).mulByV,
        (a.c0 + a.c1) * (b.c0 + b.c1) - a.c0 * b.c0 - a.c1 * b.c1⟩ := by
  unfold Cryptography.Bls.Fp12.mul
  rfl

-- A proof that its own RLP decoder is right reads back each encoding through this theorem.
example (x : Serialization.Rlp.Item) (b : ByteArray) (h : Serialization.Rlp.encode x = .ok b) :
    Serialization.Rlp.decode b = .ok x :=
  Serialization.Rlp.decode_encode x b h

-- A proof about an SSZ root of a typed value reduces it to the root of the untyped value.
example {α : Type} [Serialization.Ssz.SszType α] [Serialization.Ssz.LawfulSszType α] {a : α}
    {root : Vector UInt8 32} :
    Serialization.Ssz.SszType.hashTreeRoot a = .ok root ↔
      Serialization.Ssz.hashTreeRoot (Serialization.Ssz.SszType.desc α)
        (Serialization.Ssz.SszType.toValue a) = .ok ⟨root.toArray⟩ :=
  Serialization.Ssz.SszType.hashTreeRoot_ok_iff

-- An SSZ export consumer relates the writer's result to its JSON reference.
example (value : Serialization.Ssz.Value) :
    Serialization.Ssz.Exports.pyOfValue value =
      Exports.PyValue.ofJson (Serialization.Ssz.Exports.Proofs.jsonOfValue value) :=
  Serialization.Ssz.Exports.Proofs.pyOfValue_eq_json value

-- A transaction decoder is checked against the specification through this equivalence.
example (fork : Base.Fork) (bytes : ByteArray) (t : Execution.Transactions.Transaction) :
    Execution.Transactions.decodeTransaction fork bytes = .ok t ↔
      Execution.Transactions.encodeTransaction t = .ok bytes ∧ t.fork ≤ fork :=
  Execution.Transactions.decodeTransaction_eq_ok_iff fork bytes t

-- A proof that its own hex encoder is right reads its output back through this theorem.
example (bytes : List UInt8) :
    Base.hexBytes? (bytes.flatMap Base.byteHexDigits) = some ⟨bytes.toArray⟩ :=
  Base.hexBytes?_flatMap bytes

-- A QUIC integer consumer recovers the value and packed bytes after its encoding.
example (value : Networking.Quic.Varint) (rest : ByteArray) :
    Networking.Quic.Varint.decode (Networking.Quic.Varint.encode value ++ rest) =
      .ok (value, rest) :=
  Networking.Quic.Varint.decode_encode value rest

-- A packet consumer retains the packed payload after a valid encoded header.
example (header : Networking.Quic.Packet.Header) (encoded rest : ByteArray)
    (valid : header.Valid) (written : Networking.Quic.Packet.encode header = .ok encoded)
    (follows : Networking.Quic.Packet.permitsFollowing header rest) :
    Networking.Quic.Packet.decode (Networking.Quic.Packet.shortConnectionIdLength header)
      (encoded ++ rest) = .ok (header, rest) :=
  Networking.Quic.Packet.decode_encode header encoded rest valid written follows

-- A frame consumer preserves packed trailing bytes when the frame permits them.
example (frame : Networking.Quic.Frame.Frame) (packet : Networking.Quic.Packet.PacketType)
    (encoded rest : ByteArray) (written : Networking.Quic.Frame.encode frame = .ok encoded)
    (allowed : frame.allowed packet = true)
    (follows : Networking.Quic.Frame.permitsFollowing frame rest) :
    Networking.Quic.Frame.decode packet (encoded ++ rest) = .ok (frame, rest) :=
  Networking.Quic.Frame.decode_encode frame packet encoded rest written allowed follows

-- A TLS consumer reads back a packed message without consuming its packed trailing bytes.
example (hashLength : Nat) (message : Networking.Quic.Tls.Message) (encoded rest : ByteArray)
    (written : Networking.Quic.Tls.encode hashLength message = .ok encoded) :
    Networking.Quic.Tls.decode hashLength (encoded ++ rest) = .ok (message, rest) :=
  Networking.Quic.Tls.decode_encode written rest

-- A TLS consumer characterizes accepted packed input by its encoded prefix and exact suffix.
example (hashLength : Nat) (message : Networking.Quic.Tls.Message) (input rest : ByteArray) :
    Networking.Quic.Tls.decode hashLength input = .ok (message, rest) ↔
      ∃ encoded, Networking.Quic.Tls.encode hashLength message = .ok encoded ∧
        input = encoded ++ rest :=
  Networking.Quic.Tls.decode_eq_ok_iff

-- A leanXMSS circuit hard-codes the 58 chains of a one-time key.
example : Cryptography.Xmss.Constants.V = 58 := Cryptography.Xmss.Constants.v_eq

-- A leanXMSS circuit hard-codes the 4 positions of a chain.
example : Cryptography.Xmss.Constants.CHAIN_LENGTH = 4 :=
  Cryptography.Xmss.Constants.chain_length_eq

-- A leanXMSS circuit reads 64 digits of a digest.
example : Cryptography.Xmss.Constants.DIGITS = 64 := Cryptography.Xmss.Constants.digits_eq

-- A leanXMSS circuit checks that the digits sum to 106.
example : Cryptography.Xmss.Constants.TARGET_SUM = 106 :=
  Cryptography.Xmss.Constants.target_sum_eq

-- A leanXMSS circuit climbs 16 levels per tree.
example : Cryptography.Xmss.Constants.LAYER_HEIGHT = 16 :=
  Cryptography.Xmss.Constants.layer_height_eq

-- A leanXMSS circuit accepts when the bottom layer's root leads the top layer to the key's root.
example (f : Array UInt64 → Cryptography.Xmss.Lanes4) (pk : Cryptography.Xmss.PublicKey)
    (m : Cryptography.Xmss.Message) (sig : Cryptography.Xmss.Signature) :
    (Cryptography.Xmss.verifyWith (Cryptography.Xmss.pureHash f) pk m sig).run = true ↔
      ∃ bottomRoot,
        (Cryptography.Xmss.layerRoot (Cryptography.Xmss.pureHash f) pk.publicParam .bottom
          sig.leafIndex.toNat m.toArray sig.bottom).run = some bottomRoot ∧
        (Cryptography.Xmss.layerRoot (Cryptography.Xmss.pureHash f) pk.publicParam .top
          (Cryptography.Xmss.bottomTree sig.leafIndex) bottomRoot.toArray sig.top).run
            = some pk.root :=
  Cryptography.Xmss.verify_iff

-- A leanXMSS circuit computes a layer's root as the recovered leaf folded up the path.
example (f : Array UInt64 → Cryptography.Xmss.Lanes4) (P : Cryptography.Xmss.PublicParam)
    (layer : Cryptography.Xmss.Layer) (e : Nat) (msg : Array UInt64)
    (sig : Cryptography.Xmss.LayerSignature) :
    (Cryptography.Xmss.layerRoot (Cryptography.Xmss.pureHash f) P layer e msg sig).run
      = (Cryptography.Xmss.otsLeaf (Cryptography.Xmss.pureHash f) P layer
        (UInt32.ofNat e) msg sig.randomizer sig.chainValues).run.map
          fun leaf => (Cryptography.Xmss.fold (Cryptography.Xmss.pureHash f) P layer e leaf
            sig.path).run :=
  Cryptography.Xmss.layerRoot_run

-- A leanXMSS circuit recovers a leaf from the codeword and the chains walked to their ends.
example (f : Array UInt64 → Cryptography.Xmss.Lanes4) (P : Cryptography.Xmss.PublicParam)
    (layer : Cryptography.Xmss.Layer) (e : UInt32) (msg : Array UInt64)
    (rho : Cryptography.Xmss.Randomizer)
    (y : Vector Cryptography.Xmss.Digest Cryptography.Xmss.Constants.V) :
    (Cryptography.Xmss.otsLeaf (Cryptography.Xmss.pureHash f) P layer e msg rho y).run
      = (Cryptography.Xmss.codeword? (Cryptography.Xmss.messageDigest
          (Cryptography.Xmss.pureHash f) P layer e msg rho).run).map
        fun (x : Vector (Fin Cryptography.Xmss.Constants.CHAIN_LENGTH)
            Cryptography.Xmss.Constants.V) =>
          (Cryptography.Xmss.otsLeafHash (Cryptography.Xmss.pureHash f) P layer e
            (Vector.ofFn fun i => (Cryptography.Xmss.chain (Cryptography.Xmss.pureHash f) P
              layer e i x[i] (Cryptography.Xmss.Constants.CHAIN_LENGTH - 1 - x[i])
              (by have := x[i].isLt; omega) y[i]).run)).run :=
  Cryptography.Xmss.otsLeaf_run

-- A leanXMSS circuit hashes every call as the first half of the hash of `P | A | M`.
example (f : Array UInt64 → Cryptography.Xmss.Lanes4) (P : Cryptography.Xmss.PublicParam)
    (A : Cryptography.Xmss.Address) (M : Array UInt64) :
    (Cryptography.Xmss.th (Cryptography.Xmss.pureHash f) P A M).run
      = Cryptography.Xmss.halfOf 0 (f (Cryptography.Xmss.thInput P A M)) :=
  Cryptography.Xmss.th_run f P A M

-- A leanXMSS circuit lays out `P | A | M` as 16 bytes of `P`, 16 bytes of `A`, then `M`.
example (P : Cryptography.Xmss.PublicParam) (A : Cryptography.Xmss.Address) (M : Array UInt64) :
    Cryptography.Hash.Keccak.lanesBytes (Cryptography.Xmss.thInput P A M)
      = P.bytes.toList ++ A.encode.bytes.toList ++ Cryptography.Hash.Keccak.lanesBytes M :=
  Cryptography.Xmss.lanesBytes_thInput P A M

-- A leanXMSS circuit hashes a chain step's value, then the chain's index, at its address.
example {m : Type → Type} [Monad m] (H : Array UInt64 → m Cryptography.Xmss.Lanes4)
    (P : Cryptography.Xmss.PublicParam) (layer : Cryptography.Xmss.Layer) (e : UInt32)
    (i : Fin Cryptography.Xmss.Constants.V)
    (mu : Fin (Cryptography.Xmss.Constants.CHAIN_LENGTH - 1)) (v : Cryptography.Xmss.Digest) :
    Cryptography.Xmss.chainStep H P layer e i mu v
      = Cryptography.Xmss.th H P (.chain layer e mu)
          (v.toArray ++ (⟨i.val.toUInt64, 0⟩ : Cryptography.Xmss.Lanes2).toArray) :=
  Cryptography.Xmss.chainStep_eq_th H P layer e i mu v

-- A leanXMSS circuit hashes the 58 chain ends, in chain order, into a leaf.
example {m : Type → Type} [Monad m] (H : Array UInt64 → m Cryptography.Xmss.Lanes4)
    (P : Cryptography.Xmss.PublicParam) (layer : Cryptography.Xmss.Layer) (e : UInt32)
    (ends : Vector Cryptography.Xmss.Digest Cryptography.Xmss.Constants.V) :
    Cryptography.Xmss.otsLeafHash H P layer e ends
      = Cryptography.Xmss.th H P (.leaf layer e) (Cryptography.Xmss.digestLanes ends) :=
  Cryptography.Xmss.otsLeafHash_eq_th H P layer e ends

-- A leanXMSS circuit hashes the message, then the randomizer, into the signed digest.
example {m : Type → Type} [Monad m] (H : Array UInt64 → m Cryptography.Xmss.Lanes4)
    (P : Cryptography.Xmss.PublicParam) (layer : Cryptography.Xmss.Layer) (e : UInt32)
    (msg : Array UInt64) (rho : Cryptography.Xmss.Randomizer) :
    Cryptography.Xmss.messageDigest H P layer e msg rho
      = Cryptography.Xmss.th H P (.msg layer e) (msg ++ rho.toArray) :=
  Cryptography.Xmss.messageDigest_eq_th H P layer e msg rho

-- A leanXMSS circuit hashes a tree node's two children at the node's exact level.
example {m : Type → Type} [Monad m] (H : Array UInt64 → m Cryptography.Xmss.Lanes4)
    (P : Cryptography.Xmss.PublicParam) (layer : Cryptography.Xmss.Layer)
    (p : Cryptography.Merkle.Position) (hlevel : p.level ≤ Cryptography.Xmss.Constants.LAYER_HEIGHT)
    (left right : Cryptography.Xmss.Digest) :
    Cryptography.Xmss.nodeHash H P layer p left right
      = Cryptography.Xmss.th H P (.node layer ⟨p.level, by omega⟩ (UInt32.ofNat p.index))
          #[left.lo, left.hi, right.lo, right.hi] :=
  Cryptography.Xmss.nodeHash_of_le H P layer hlevel left right

-- A leanXMSS circuit packs a chain step's address into one integer.
example (layer : Cryptography.Xmss.Layer) (e : UInt32)
    (mu : Fin (Cryptography.Xmss.Constants.CHAIN_LENGTH - 1)) :
    (Cryptography.Xmss.Address.chain layer e mu).encode.toNat =
      e.toNat + 2 ^ 32 * (2 ^ 23 * layer.toNat) + 2 ^ 56 * (1 + 32 * mu.val) :=
  Cryptography.Xmss.Address.toNat_encode_chain layer e mu

-- A leanXMSS circuit packs a leaf's address into one integer.
example (layer : Cryptography.Xmss.Layer) (e : UInt32) :
    (Cryptography.Xmss.Address.leaf layer e).encode.toNat =
      e.toNat + 2 ^ 32 * (2 ^ 23 * layer.toNat) + 2 ^ 56 * 2 :=
  Cryptography.Xmss.Address.toNat_encode_leaf layer e

-- A leanXMSS circuit packs the signed digest's address into one integer.
example (layer : Cryptography.Xmss.Layer) (e : UInt32) :
    (Cryptography.Xmss.Address.msg layer e).encode.toNat =
      e.toNat + 2 ^ 32 * (2 ^ 23 * layer.toNat) + 2 ^ 56 * 12 :=
  Cryptography.Xmss.Address.toNat_encode_msg layer e

-- A leanXMSS circuit packs a node's address into one integer.
example (layer : Cryptography.Xmss.Layer)
    (level : Fin (Cryptography.Xmss.Constants.LAYER_HEIGHT + 1)) (j : UInt32) :
    (Cryptography.Xmss.Address.node layer level j).encode.toNat =
      j.toNat + 2 ^ 32 * (level.val + 2 ^ 23 * layer.toNat) + 2 ^ 56 * 3 :=
  Cryptography.Xmss.Address.toNat_encode_node layer level j

-- A leanXMSS circuit writes the bottom layer as 0 in an address.
example : Cryptography.Xmss.Layer.bottom.toNat = 0 := Cryptography.Xmss.Layer.toNat_bottom

-- A leanXMSS circuit writes the top layer as 1 in an address.
example : Cryptography.Xmss.Layer.top.toNat = 1 := Cryptography.Xmss.Layer.toNat_top

-- A leanXMSS circuit walks a chain one step at a time, from the last step.
example {m : Type → Type} [Monad m] (H : Array UInt64 → m Cryptography.Xmss.Lanes4)
    (P : Cryptography.Xmss.PublicParam) (layer : Cryptography.Xmss.Layer) (e : UInt32)
    (i : Fin Cryptography.Xmss.Constants.V) (start s : Nat)
    (h : start + (s + 1) < Cryptography.Xmss.Constants.CHAIN_LENGTH)
    (v : Cryptography.Xmss.Digest) :
    Cryptography.Xmss.chain H P layer e i start (s + 1) h v = (do
      let previous ← Cryptography.Xmss.chain H P layer e i start s (by omega) v
      Cryptography.Xmss.chainStep H P layer e i
        ⟨start + s, by simp only [Cryptography.Xmss.Constants.CHAIN_LENGTH] at *; omega⟩
        previous) :=
  Cryptography.Xmss.chain_succ H h

-- A leanXMSS circuit walks a chain one step at a time, from the first step.
example (f : Array UInt64 → Cryptography.Xmss.Lanes4) (P : Cryptography.Xmss.PublicParam)
    (layer : Cryptography.Xmss.Layer) (e : UInt32) (i : Fin Cryptography.Xmss.Constants.V)
    (start s : Nat) (h : start + (s + 1) < Cryptography.Xmss.Constants.CHAIN_LENGTH)
    (v : Cryptography.Xmss.Digest) :
    (Cryptography.Xmss.chain (Cryptography.Xmss.pureHash f) P layer e i start (s + 1) h v).run
      = (Cryptography.Xmss.chain (Cryptography.Xmss.pureHash f) P layer e i (start + 1) s
          (by omega) (Cryptography.Xmss.chainStep (Cryptography.Xmss.pureHash f) P layer e i
            ⟨start, by simp only [Cryptography.Xmss.Constants.CHAIN_LENGTH] at *; omega⟩
            v).run).run :=
  Cryptography.Xmss.chain_succ_run h

-- A leanXMSS circuit folds a path as the Merkle climb over the path's entries.
example {m : Type → Type} [Monad m] (H : Array UInt64 → m Cryptography.Xmss.Lanes4)
    (P : Cryptography.Xmss.PublicParam) (layer : Cryptography.Xmss.Layer) (e : Nat)
    (leaf : Cryptography.Xmss.Digest) (path : Nat → Cryptography.Xmss.Digest) :
    Cryptography.Xmss.fold H P layer e leaf
        (Vector.ofFn fun k : Fin Cryptography.Xmss.Constants.LAYER_HEIGHT => path k.val)
      = Cryptography.Merkle.climb (Cryptography.Xmss.nodeHash H P layer) ⟨0, e⟩ leaf
          (List.ofFn fun k : Fin Cryptography.Xmss.Constants.LAYER_HEIGHT => path k.val) :=
  Cryptography.Xmss.fold_ofFn H P layer e leaf path

-- A Merkle circuit climbs one level at a time, the held node's side given by a bit of its index.
example {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (hash : Cryptography.Merkle.Position → α → α → m α) (j : Nat) (path : Nat → α) (n : Nat)
    (value : α) :
    Cryptography.Merkle.climb hash ⟨0, j⟩ value
        (List.ofFn fun level : Fin (n + 1) => path level.val) = (do
      let current ← Cryptography.Merkle.climb hash ⟨0, j⟩ value
        (List.ofFn fun level : Fin n => path level.val)
      if j.testBit n then hash ⟨n + 1, j / 2 ^ (n + 1)⟩ (path n) current
      else hash ⟨n + 1, j / 2 ^ (n + 1)⟩ current (path n)) :=
  Cryptography.Merkle.climb_ofFn_succ hash j path n value

-- A leanXMSS circuit takes the top key of a leaf index as its integer divided by `2^16`.
example (idx : Cryptography.Xmss.LeafIndex) :
    Cryptography.Xmss.bottomTree idx = idx.toNat / 2 ^ Cryptography.Xmss.Constants.LAYER_HEIGHT :=
  Cryptography.Xmss.bottomTree_eq_div idx

-- A leanXMSS circuit holds the top key in a 32-bit word without wrapping.
example (idx : Cryptography.Xmss.LeafIndex) :
    (UInt32.ofNat (Cryptography.Xmss.bottomTree idx)).toNat = Cryptography.Xmss.bottomTree idx :=
  Cryptography.Xmss.toNat_ofNat_bottomTree idx

-- A leanXMSS circuit reads a codeword's digits, its six zero digits and its sum off the digest.
example {d : Cryptography.Xmss.Digest}
    {x : Vector (Fin Cryptography.Xmss.Constants.CHAIN_LENGTH) Cryptography.Xmss.Constants.V}
    (h : Cryptography.Xmss.codeword? d = some x) :
    (∀ i : Fin Cryptography.Xmss.Constants.V, (x[i] : Nat) = d.toNat / 4 ^ i.val % 4) ∧
      (∀ i, Cryptography.Xmss.Constants.V ≤ i → i < Cryptography.Xmss.Constants.DIGITS →
        d.toNat / 4 ^ i % 4 = 0) ∧
      Cryptography.Xmss.Internal.digitSum x = Cryptography.Xmss.Constants.TARGET_SUM :=
  Cryptography.Xmss.codeword?_eq_some h

-- A leanXMSS circuit takes a digest as a codeword exactly when it spells the digits summing to 106.
example {d : Cryptography.Xmss.Digest}
    {x : Vector (Fin Cryptography.Xmss.Constants.CHAIN_LENGTH) Cryptography.Xmss.Constants.V} :
    Cryptography.Xmss.codeword? d = some x ↔
      d.toNat = ∑ i : Fin Cryptography.Xmss.Constants.V, (x[i] : Nat) * 4 ^ i.val ∧
        ∑ i : Fin Cryptography.Xmss.Constants.V, (x[i] : Nat) =
          Cryptography.Xmss.Constants.TARGET_SUM :=
  Cryptography.Xmss.codeword?_eq_some_iff

-- A leanXMSS circuit walks each chain from its digit for the steps that reach its end.
example (f : Array UInt64 → Cryptography.Xmss.Lanes4) (P : Cryptography.Xmss.PublicParam)
    (layer : Cryptography.Xmss.Layer) (e : UInt32)
    (x : Vector (Fin Cryptography.Xmss.Constants.CHAIN_LENGTH) Cryptography.Xmss.Constants.V)
    (y : Vector Cryptography.Xmss.Digest Cryptography.Xmss.Constants.V)
    (i : Fin Cryptography.Xmss.Constants.V) (k : Nat)
    (hk : (x[i] : Nat) + k = Cryptography.Xmss.Constants.CHAIN_LENGTH - 1) :
    Cryptography.Xmss.chainEnd f P layer e x y i
      = (Cryptography.Xmss.chain (Cryptography.Xmss.pureHash f) P layer e i x[i] k
          (by simp only [Cryptography.Xmss.Constants.CHAIN_LENGTH] at *; omega) y[i]).run :=
  Cryptography.Xmss.chainEnd_eq_chain hk

-- A leanXMSS circuit that reaches a layer's root has decoded a codeword and climbed to the root.
example (f : Array UInt64 → Cryptography.Xmss.Lanes4) (P : Cryptography.Xmss.PublicParam)
    (layer : Cryptography.Xmss.Layer) (e : Nat) (msg : Array UInt64)
    (sig : Cryptography.Xmss.LayerSignature) (root : Cryptography.Xmss.Digest) :
    (Cryptography.Xmss.layerRoot (Cryptography.Xmss.pureHash f) P layer e msg sig).run
        = some root ↔
      ∃ x, Cryptography.Xmss.codeword? (Cryptography.Xmss.messageDigest
          (Cryptography.Xmss.pureHash f) P layer (UInt32.ofNat e) msg sig.randomizer).run
            = some x ∧
        (Cryptography.Xmss.fold (Cryptography.Xmss.pureHash f) P layer e
          (Cryptography.Xmss.otsLeafHash (Cryptography.Xmss.pureHash f) P layer (UInt32.ofNat e)
            (Vector.ofFn (Cryptography.Xmss.chainEnd f P layer (UInt32.ofNat e) x
              sig.chainValues))).run
          sig.path).run = root :=
  Cryptography.Xmss.layerRoot_eq_some_iff

-- A leanXMSS circuit rejects a layer exactly when its digest is not a codeword.
example (f : Array UInt64 → Cryptography.Xmss.Lanes4) (P : Cryptography.Xmss.PublicParam)
    (layer : Cryptography.Xmss.Layer) (e : Nat) (msg : Array UInt64)
    (sig : Cryptography.Xmss.LayerSignature) :
    (Cryptography.Xmss.layerRoot (Cryptography.Xmss.pureHash f) P layer e msg sig).run = none ↔
      Cryptography.Xmss.codeword? (Cryptography.Xmss.messageDigest
        (Cryptography.Xmss.pureHash f) P layer (UInt32.ofNat e) msg sig.randomizer).run = none :=
  Cryptography.Xmss.layerRoot_eq_none_iff

-- A leanXMSS circuit proves the deployed verifier through the one over a hash, at Keccak-256.
example (pk : Cryptography.Xmss.PublicKey) (m : Cryptography.Xmss.Message)
    (sig : Cryptography.Xmss.Signature) :
    Cryptography.Xmss.verify pk m sig
      = (Cryptography.Xmss.verifyWith Cryptography.Xmss.hashId pk m sig).run :=
  Cryptography.Xmss.verify_eq_verifyWith pk m sig

-- A leaf index is a 32-bit word, so a leanXMSS circuit uses it as the bottom key unchanged.
example (idx : Cryptography.Xmss.LeafIndex) : UInt32.ofNat idx.toNat = idx :=
  UInt32.ofNat_toNat
