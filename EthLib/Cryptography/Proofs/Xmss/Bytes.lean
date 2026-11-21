module

public import EthLib.Cryptography.Proofs.Xmss.Address
public import EthLib.Cryptography.Proofs.Xmss.Encoding
public import EthLib.Cryptography.Proofs.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.Serialization
public import EthLib.Cryptography.Proofs.Xmss.Sign
public import EthLib.Cryptography.Proofs.Xmss.Tree
public import EthLib.Cryptography.Proofs.Xmss.Verify

/-!
# Proofs: leanXMSS in bytes

The scheme holds its values as Keccak lanes, and a value is the bytes of its lanes.

These theorems state each hash of the scheme in bytes, as the specification writes it.

Each one lists the bytes that Keccak-256 hashes, in order, and the bytes the scheme keeps.

A 16-byte value is the first 16 bytes of a digest, or the last 16 for the second chain of a pair.

So a reader can check the scheme against the specification without reading a lane.

Every theorem that hashes is about the hash that runs, Keccak-256, in the identity monad.

Source: the leanXMSS specification draft.

Its sections "Hashing and parameters", "Address encoding", "WOTS+C" and "Trees" define the hashes.

Its section "The scheme" defines the keys, the signatures and their encodings.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.Hash.Keccak (keccak256 lanesBytes)

/-! ## Byte strings -/

/-- A byte string built from a list splits where the list does. -/
private theorem mk_append (l₁ l₂ : List UInt8) :
    ByteArray.mk (l₁ ++ l₂).toArray = ⟨l₁.toArray⟩ ++ ⟨l₂.toArray⟩ :=
  ByteArray.ext (by simp [ByteArray.data_append])

/-- The bytes of a fixed-size object, as a byte string, are its list of bytes. -/
private theorem packBytes_eq_mk {n : Nat} (v : Vector UInt8 n) :
    packBytes v = ⟨v.toList.toArray⟩ := by
  rcases v with ⟨a, h⟩
  simp [Base.packBytes, Vector.toList]

/-- The bytes of a list of digests, as a byte string, are the bytes of their lanes. -/
private theorem packDigests_eq_mk {n : Nat} (ds : Vector Digest n) :
    packDigests ds = ⟨(lanesBytes (digestLanes ds)).toArray⟩ := by
  rw [lanesBytes_digestLanes, packDigests, packBytes_eq_mk]
  congr 2
  rcases ds with ⟨a, h⟩
  simp [Vector.flatten, Vector.map, Vector.toList, Array.toList_flatten, Function.comp_def]

/-! ## Values -/

/-- Half `h` of a 32-byte value is its 16 bytes from byte `16 h` on. -/
theorem toList_bytes_halfOf (h : Fin 2) (w : Lanes4) :
    (halfOf h w).bytes.toList = (w.bytes.toList.drop (16 * h.val)).take 16 := by
  fin_cases h <;> rfl

/-- The all-zero parameter is 16 zero bytes. -/
theorem bytes_zero_lanes2 : (⟨0, 0⟩ : PublicParam).bytes = Vector.replicate 16 0 := by
  decide

/-! ## The tweakable hash -/

/-- `Th(P, A, M)` is the first 16 bytes of Keccak-256 of `P | A | M`.

The payload `M` is the bytes of its lanes, each lane least significant byte first. -/
theorem th_bytes (pp : PublicParam) (A : Address) (M : Array UInt64) :
    (th hashId pp A M).run.bytes.toList =
      (keccak256 (packBytes pp.bytes ++ packBytes A.bytes
        ++ ⟨(lanesBytes M).toArray⟩)).toList.take 16 := by
  show (halfOf 0 (hash (thInput pp A M))).bytes.toList = _
  rw [toList_bytes_halfOf, hash_bytes, thInput_eq_append, Hash.Keccak.lanesBytes_append,
    Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_lanes2, Hash.Keccak.lanesBytes_lanes2,
    mk_append, mk_append, ← packBytes_eq_mk, ← packBytes_eq_mk]
  rfl

/-- A derivation from the scheme seed `S` is Keccak-256 of `P | A | S | suffix`, all 32 bytes. -/
theorem seedPrf_bytes (s : Seed) (pp : PublicParam) (A : Address) (suffix : Array UInt64) :
    (seedPrf hashId s pp A suffix).run.bytes =
      keccak256 (packBytes pp.bytes ++ packBytes A.bytes ++ packBytes s.bytes
        ++ ⟨(lanesBytes suffix).toArray⟩) := by
  show (hash (thInput pp A (s.toArray ++ suffix))).bytes = _
  rw [hash_bytes, show thInput pp A (s.toArray ++ suffix) = pp.toArray ++ A.toArray ++ s.toArray
      ++ suffix from by simp only [thInput, ← Array.append_assoc]; rfl,
    Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_append,
    Hash.Keccak.lanesBytes_lanes2, Hash.Keccak.lanesBytes_lanes2, Hash.Keccak.lanesBytes_lanes4,
    mk_append, mk_append, mk_append, ← packBytes_eq_mk, ← packBytes_eq_mk, ← packBytes_eq_mk]

/-! ## Derivations from the seed -/

/-- `S = H("leanXMSS" | S_0)`: Keccak-256 of the scheme's 8-byte name, then the 32-byte seed. -/
theorem schemeSeed_bytes (seed : Seed) :
    (schemeSeed hashId seed).run.bytes =
      keccak256 (ByteArray.mk SEED_TAG.toArray ++ packBytes seed.bytes) := by
  show (hash (#[SEED_TAG_LANE] ++ seed.toArray)).bytes = _
  rw [hash_bytes, Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_singleton,
    bytesOfLane_seedTagLane, Hash.Keccak.lanesBytes_lanes4, mk_append, ← packBytes_eq_mk]

/-- `P = H_0(0^128 | A_param | S)`: the first 16 bytes of the derivation at the zero parameter. -/
theorem publicParamOf_bytes (s : Seed) :
    (publicParamOf (seedPrf hashId s)).run.bytes.toList =
      (keccak256 (packBytes (Vector.replicate 16 0) ++ packBytes addrParam.bytes
        ++ packBytes s.bytes)).toList.take 16 := by
  show (halfOf 0 (seedPrf hashId s ⟨0, 0⟩ addrParam #[]).run).bytes.toList = _
  rw [toList_bytes_halfOf, seedPrf_bytes, bytes_zero_lanes2]
  rfl

/-- The start of chain `i` of key `e` is half `i mod 2` of `H(P | A_prf(l, e, floor(i / 2)) | S)`.

Chain `2j` takes the first 16 bytes, and chain `2j + 1` the last 16. -/
theorem chainStarts_bytes (pp : PublicParam) (s : Seed) (layer : Layer) (e : UInt32) (i : Fin V) :
    ((chainStarts pp (seedPrf hashId s) layer e).run[i]).bytes.toList =
      ((keccak256 (packBytes pp.bytes
        ++ packBytes (addrPrf layer e
          ⟨i.val / 2, by have := i.isLt; simp only [V] at *; omega⟩).bytes
        ++ packBytes s.bytes)).toList.drop (16 * (i.val % 2))).take 16 := by
  rw [chainStarts, Id.run_bind, HashSig.ofFnInOrder_run]
  simp only [Id.run_pure, Fin.getElem_fin, Vector.getElem_ofFn]
  -- The suffix is empty, so it adds no byte.
  have hempty : ∀ b : ByteArray, b ++ ⟨(lanesBytes #[]).toArray⟩ = b := fun b =>
    ByteArray.ext (by simp [ByteArray.data_append, lanesBytes])
  rw [toList_bytes_halfOf, seedPrf_bytes, hempty]
  rfl

/-- The randomizer base `R_0` is the first 16 bytes of `H(P | A_rnd(l, e) | S | M)`. -/
theorem randomizerBase_bytes (pp : PublicParam) (s : Seed) (layer : Layer) (e : UInt32)
    (msg : Array UInt64) :
    (randomizerBase pp (seedPrf hashId s) layer e msg).run.bytes.toList =
      (keccak256 (packBytes pp.bytes ++ packBytes (addrRnd layer e).bytes ++ packBytes s.bytes
        ++ ⟨(lanesBytes msg).toArray⟩)).toList.take 16 := by
  show (halfOf 0 (seedPrf hashId s pp (addrRnd layer e) msg).run).bytes.toList = _
  rw [toList_bytes_halfOf, seedPrf_bytes]
  rfl

/-! ## Chains -/

/-- A chain step from position `mu` of chain `i` is `H_0(P | A_chain(l, e, mu) | v | LE_128(i))`. -/
theorem chainStep_bytes (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (v : Digest) :
    (chainStep hashId pp layer e i mu v).run.bytes.toList =
      (keccak256 (packBytes pp.bytes ++ packBytes (addrChain layer e mu).bytes ++ packBytes v.bytes
        ++ packBytes (uintToBytes 16 i.val))).toList.take 16 := by
  rw [chainStep, th_bytes,
    show (#[v.lo, v.hi, i.val.toUInt64, 0] : Array UInt64) =
      v.toArray ++ (⟨i.val.toUInt64, 0⟩ : Lanes2).toArray from rfl,
    Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_lanes2,
    lanesBytes_index _ (by have := i.isLt; simp only [V] at this; omega), mk_append,
    ← packBytes_eq_mk, ← packBytes_eq_mk]
  rfl

/-- Step `s + 1` from `start` hashes the value after `s` steps, at position `start + s`. -/
theorem chain_succ_bytes (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (start s : Nat) (h : start + (s + 1) < CHAIN_LENGTH) (v : Digest) :
    (chain hashId pp layer e i start (s + 1) h v).run.bytes.toList =
      (keccak256 (packBytes pp.bytes
        ++ packBytes (addrChain layer e ⟨start + s, by simp only [CHAIN_LENGTH] at *; omega⟩).bytes
        ++ packBytes (chain hashId pp layer e i start s (by omega) v).run.bytes
        ++ packBytes (uintToBytes 16 i.val))).toList.take 16 :=
  chainStep_bytes pp layer e i _ _

/-! ## Leaves -/

/-- The leaf of one-time key `e` is `H_0(P | A_leaf(l, e) | y_0 | ... | y_57)`.

The values `y_i` are the ends of its 58 chains. -/
theorem otsLeafHash_bytes (pp : PublicParam) (layer : Layer) (e : UInt32) (ends : Vector Digest V) :
    (otsLeafHash hashId pp layer e ends).run.bytes.toList =
      (keccak256 (packBytes pp.bytes ++ packBytes (addrLeaf layer e).bytes
        ++ packDigests ends)).toList.take 16 := by
  rw [otsLeafHash, th_bytes, packDigests_eq_mk]

/-- The leaf of key `e`: each chain walked from its derived start to position 3, then hashed.

With the derivations from the scheme seed, the starts are the halves of the derivations above. -/
theorem otsPublicLeaf_bytes (pp : PublicParam) (prf : SeedPrf Id) (layer : Layer) (e : UInt32) :
    (otsPublicLeaf hashId pp prf layer e).run.bytes.toList =
      (keccak256 (packBytes pp.bytes ++ packBytes (addrLeaf layer e).bytes
        ++ packDigests (Vector.ofFn fun i => (chain hashId pp layer e i 0 (CHAIN_LENGTH - 1)
          (by decide) (chainStarts pp prf layer e).run[i]).run))).toList.take 16 := by
  rw [otsPublicLeaf, Id.run_bind, Id.run_bind, HashSig.ofFnInOrder_run, otsLeafHash_bytes]

/-! ## The digest a key signs -/

/-- The digest of a trial is `H_0(P | A_msg(l, e) | M | rho)`, with `M` the bytes of its lanes. -/
theorem messageDigest_bytes (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : Array UInt64)
    (rho : Randomizer) :
    (messageDigest hashId pp layer e msg rho).run.bytes.toList =
      (keccak256 (packBytes pp.bytes ++ packBytes (addrMsg layer e).bytes
        ++ ⟨(lanesBytes msg).toArray⟩ ++ packBytes rho.bytes)).toList.take 16 := by
  rw [messageDigest, th_bytes, Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_lanes2,
    mk_append, ← packBytes_eq_mk]
  rfl

/-- On the bottom layer the signed bytes `M` are the 32 bytes of the message. -/
theorem messageDigest_message_bytes (pp : PublicParam) (e : UInt32) (msg : Message)
    (rho : Randomizer) :
    (messageDigest hashId pp .bottom e msg.toArray rho).run.bytes.toList =
      (keccak256 (packBytes pp.bytes ++ packBytes (addrMsg .bottom e).bytes ++ packBytes msg.bytes
        ++ packBytes rho.bytes)).toList.take 16 := by
  rw [messageDigest_bytes, Hash.Keccak.lanesBytes_lanes4, ← packBytes_eq_mk]

/-- On the top layer the signed bytes `M` are the 16 bytes of a bottom tree's root. -/
theorem messageDigest_root_bytes (pp : PublicParam) (e : UInt32) (root : Digest)
    (rho : Randomizer) :
    (messageDigest hashId pp .top e root.toArray rho).run.bytes.toList =
      (keccak256 (packBytes pp.bytes ++ packBytes (addrMsg .top e).bytes ++ packBytes root.bytes
        ++ packBytes rho.bytes)).toList.take 16 := by
  rw [messageDigest_bytes, Hash.Keccak.lanesBytes_lanes2, ← packBytes_eq_mk]

/-- Digit `i` of a digest is the base-4 digit of weight `4^i` of its 16 bytes, little-endian. -/
theorem digit_val_bytes (d : Digest) (i : Fin DIGITS) :
    (Internal.digit d i).val = bytesToUint d.bytes / 4 ^ i.val % 4 := by
  rw [digit_val, Hash.Keccak.Lanes2.bytesToUint_bytes]

/-! ## Trees -/

/-- A parent at a position is `H_0(P | A_node(l, level, j) | left | right)`. -/
theorem nodeHash_bytes (pp : PublicParam) (layer : Layer) (p : Merkle.Position)
    (left right : Digest) :
    (nodeHash hashId pp layer p left right).run.bytes.toList =
      (keccak256 (packBytes pp.bytes
        ++ packBytes (addrNode layer (Fin.ofNat _ p.level) (UInt32.ofNat p.index)).bytes
        ++ packBytes left.bytes ++ packBytes right.bytes)).toList.take 16 := by
  rw [nodeHash, th_bytes,
    show (#[left.lo, left.hi, right.lo, right.hi] : Array UInt64) =
      left.toArray ++ right.toArray from rfl,
    Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_lanes2, Hash.Keccak.lanesBytes_lanes2,
    mk_append, ← packBytes_eq_mk, ← packBytes_eq_mk]
  rfl

/-- Node `j` on level 0 is the leaf of one-time key `j`. -/
theorem node_zero_bytes (pp : PublicParam) (prf : SeedPrf Id) (layer : Layer) (j : Nat) :
    (node hashId pp prf layer 0 j).run.bytes.toList =
      (keccak256 (packBytes pp.bytes ++ packBytes (addrLeaf layer (UInt32.ofNat j)).bytes
        ++ packDigests (Vector.ofFn fun i => (chain hashId pp layer (UInt32.ofNat j) i 0
          (CHAIN_LENGTH - 1) (by decide)
          (chainStarts pp prf layer (UInt32.ofNat j)).run[i]).run))).toList.take 16 := by
  rw [node_zero, otsPublicLeaf_bytes]

/-- Node `j` one level up hashes its two children, nodes `2j` and `2j + 1` of the level below.

The root of a tree is node 0 on level 16. -/
theorem node_succ_bytes (pp : PublicParam) (prf : SeedPrf Id) (layer : Layer) (level j : Nat) :
    (node hashId pp prf layer (level + 1) j).run.bytes.toList =
      (keccak256 (packBytes pp.bytes
        ++ packBytes (addrNode layer (Fin.ofNat _ (level + 1)) (UInt32.ofNat j)).bytes
        ++ packBytes (node hashId pp prf layer level (2 * j)).run.bytes
        ++ packBytes (node hashId pp prf layer level (2 * j + 1)).run.bytes)).toList.take 16 := by
  rw [node_succ, Id.run_bind, Id.run_bind, nodeHash_bytes]

/-! ## Keys and signatures -/

/-- The public key's 32 bytes are the top tree's root, then `P`, both grown from the seed.

The root is node 0 on level 16 of the top layer. -/
theorem encodePublicKey_keyGen (seed : Seed) :
    encodePublicKey (keyGen seed).1 =
      packBytes (node hashId (publicParamOf (seedPrf hashId (schemeSeed hashId seed).run)).run
          (seedPrf hashId (schemeSeed hashId seed).run) .top LAYER_HEIGHT 0).run.bytes
        ++ packBytes (publicParamOf (seedPrf hashId (schemeSeed hashId seed).run)).run.bytes := by
  rw [keyGen, keyGenWith_fst, encodePublicKey]

/-- A signature's 2404 bytes: the leaf index, then each layer's randomizer, chain values and path.

The leaf index is 4 bytes, little-endian.

Each layer is 1200 bytes: its randomizer, 58 chain values and 16 path nodes, 16 bytes each. -/
theorem toList_encodeSignature (sig : Signature) :
    (encodeSignature sig).data.toList =
      (uintToBytes LEAF_INDEX_SIZE sig.leafIndex.toNat).toList
        ++ sig.bottom.randomizer.bytes.toList
        ++ (sig.bottom.chainValues.toList.map fun d => d.bytes.toList).flatten
        ++ (sig.bottom.path.toList.map fun d => d.bytes.toList).flatten
        ++ sig.top.randomizer.bytes.toList
        ++ (sig.top.chainValues.toList.map fun d => d.bytes.toList).flatten
        ++ (sig.top.path.toList.map fun d => d.bytes.toList).flatten := by
  simp [encodeSignature, encodeLayerSignature, packDigests_eq_mk, lanesBytes_digestLanes,
    Base.packBytes, ByteArray.data_append]
  rfl

/-- Byte strings verify exactly when they encode a key, a message and a signature reaching the root.

The left side runs the steps of the C export of verification, in its order.

So the key and the signature must decode, and the message must be 32 bytes.

The bottom layer signs the message's 32 bytes, and the top layer the bottom root's 16 bytes. -/
theorem verify_decode_iff (pkBytes msgBytes sigBytes : ByteArray) :
    (do
      let pk ← decodePublicKey pkBytes
      let _ ← Base.exactBytes MESSAGE_LEN msgBytes XmssError.badMessageSize
      let sig ← decodeSignature sigBytes
      pure (verify pk (Hash.Keccak.Lanes4.read msgBytes 0) sig)) = Except.ok true ↔
      ∃ (pk : PublicKey) (msg : Message) (sig : Signature) (bottomRoot : Digest),
        encodePublicKey pk = pkBytes ∧ packBytes msg.bytes = msgBytes ∧
        encodeSignature sig = sigBytes ∧
        (layerRoot hashId pk.publicParam .bottom sig.leafIndex.toNat msg.toArray
          sig.bottom).run = some bottomRoot ∧
        (layerRoot hashId pk.publicParam .top (bottomTree sig.leafIndex) bottomRoot.toArray
          sig.top).run = some pk.root := by
  constructor
  · intro h
    cases hpk : decodePublicKey pkBytes with
    | error _ => simp [hpk, bind, Except.bind] at h
    | ok pk =>
      cases hm : Base.exactBytes MESSAGE_LEN msgBytes XmssError.badMessageSize with
      | error _ => simp [hpk, hm, bind, Except.bind] at h
      | ok v =>
        cases hsig : decodeSignature sigBytes with
        | error _ => simp [hpk, hm, hsig, bind, Except.bind] at h
        | ok sig =>
          simp only [hpk, hm, hsig, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          obtain ⟨r, hb, ht⟩ := (verify_iff (f := hash)).mp h
          -- The message is 32 bytes, so its four lanes have its bytes.
          have hsize : msgBytes.size = 32 := by
            have := congrArg Array.size (Base.exactBytes_eq_ok_iff.mp hm)
            rw [Vector.size_toArray] at this
            exact this.symm
          refine ⟨pk, Hash.Keccak.Lanes4.read msgBytes 0, sig, r, ?_, ?_, ?_, hb, ht⟩
          · -- A decoded key encodes back to its bytes.
            have := encodePublicKey_decodePublicKey
              ((decodePublicKey_success_iff pkBytes).mp ⟨pk, hpk⟩)
            simpa [hpk, Except.map] using this
          · rw [Hash.Keccak.Lanes4.bytes_read _ _ (by omega), HashSig.packBytes_readBytes]
            apply ByteArray.ext
            simp only [ByteArray.size] at hsize
            simp [hsize]
          · -- A decoded signature encodes back to its bytes.
            have := encodeSignature_decodeSignature
              ((decodeSignature_success_iff sigBytes).mp ⟨sig, hsig⟩)
            simpa [hsig, Except.map] using this
  · rintro ⟨pk, msg, sig, r, rfl, rfl, rfl, hb, ht⟩
    -- Reading the message's bytes back as four lanes gives the message.
    have hmsg : Hash.Keccak.Lanes4.read (packBytes msg.bytes) 0 = msg :=
      Hash.Keccak.Lanes4.bytes_injective (by
        rw [Hash.Keccak.Lanes4.bytes_read _ _ (by simp), readBytes_packBytes])
    simp only [decodePublicKey_encodePublicKey, decodeSignature_encodeSignature, bind,
      Except.bind, pure, Except.pure, Except.ok.injEq, MESSAGE_LEN, Base.exactBytes_packBytes,
      hmsg]
    exact (verify_iff (f := hash)).mpr ⟨r, hb, ht⟩

end EthLib.Cryptography.Xmss
