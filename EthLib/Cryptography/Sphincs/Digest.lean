module

public import EthLib.Cryptography.Sphincs.Fors

/-!
# The leanSPHINCS message digest

The message digest `D`, and the randomizer `R` the signer hashes into it.

`H_msg` is MGF1 of RFC 8017 on Keccak-256, and `D` has `m = 34` bytes `g_0` to `g_33`.

FIPS 205 Algorithm 19 splits them into three fields, each read most significant bit first.

The fields `md`, `tree` and `leaf` take 30, 3 and 1 bytes, in this order.

- `md` gives the leaf of each FORS tree: `(s_0, ..., s_23) = base_2b(md, a, k)`.
- `tree` is a big-endian integer cut to `h - h_0 = 18` bits: the bottom tree.
- `leaf` is cut to `h_0 = 8` bits: the leaf in that tree.

The index is `idx = tree * 2^8 + leaf`, a bottom leaf and so a FORS instance.

Every index names a bottom leaf of the key, so every digest is valid.

Source: [FIPS 205][fips205] Algorithms 19 and 22, and MGF1 of [RFC 8017][rfc8017] Appendix B.2.1.

[fips205]: https://doi.org/10.6028/NIST.FIPS.205
[rfc8017]: https://www.rfc-editor.org/rfc/rfc8017
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-! ## The randomizer -/

/-- `M' = BE_8(0) | BE_8(len(ctx)) | ctx | M`: the message as pure SLH-DSA frames it.

The context `ctx` is the scheme's name, 11 bytes, so `M'` has 45 bytes.

The framing separates `PRF_msg` from the other calls.

Verification never computes `PRF_msg`, so no signature depends on the context. -/
def framedMessage (msg : Message) : ByteArray :=
  -- Algorithm 22, line 8: `M' = 0x00 | 0x0b | "leanSPHINCS" | M`.
  ByteArray.mk #[0, UInt8.ofNat SEED_TAG.length] ++ ByteArray.mk SEED_TAG.toArray ++ packBytes msg

/-- `R = PRF_msg(SK.prf, opt_rand, M') = Trunc_n(H(SK.prf | opt_rand | M'))`.

Signing is deterministic, with `opt_rand = PK.seed`, so the input has `32 + 16 + 45 = 93` bytes.

`SK.prf` is secret, so the randomizer is unpredictable to anyone without the secret key. -/
def prfMsg (skPrf : HashOutput) (optRand : PkSeed) (msg : Message) : m Randomizer := do
  -- Algorithm 19, line 3: `R = PRF_msg(SK.prf, opt_rand, M') = Trunc_n(H(SK.prf | opt_rand | M'))`.
  return trunc N (← H (packBytes skPrf ++ packBytes optRand ++ framedMessage msg))

/-! ## The digest -/

/-- The `m = 34` bytes of the message digest. -/
abbrev MessageDigest := Vector UInt8 DIGEST_BYTES

/-- `H_msg(R, PK.seed, PK.root, M)`: the first 34 bytes of two Keccak-256 calls.

Call `i` hashes `Z | BE_32(i)` with `Z = R | PK.seed | PK.root | M`, 84 bytes, call 0 first.

The message is not framed, so it stays on 16-byte boundaries. -/
def hMsg (rho : Randomizer) (pkSeed : PkSeed) (pkRoot : Digest) (msg : Message) :
    m MessageDigest := do
  -- Algorithm 19, line 5, with `M` in place of `M'`: `Z = R | PK.seed | PK.root | M`.
  let z := packBytes rho ++ packBytes pkSeed ++ packBytes pkRoot ++ packBytes msg
  -- The calls hash the same `Z`, and only their counter differs.
  let calls ← ofFnInOrder DIGEST_CALLS fun i => H (z ++ packBytes (toByte 4 i.val))
  -- `D = MGF1(Z, m) = Trunc_m(H(Z | BE_32(0)) | H(Z | BE_32(1)))`, with no inner hash of `Z`.
  --
  -- FIPS 205 §11.2 applies MGF1 to `R | PK.seed | SHA-256(R | PK.seed | PK.root | M)` instead.
  return trunc DIGEST_BYTES calls.flatten

/-- Bit `p` of a byte string, most significant bit first, as `base_2b` reads it.

Bit `p` is bit `7 - p mod 8` of byte `floor(p / 8)`, and every bit past the end is 0. -/
def msbBit {k : Nat} (x : Vector UInt8 k) (p : Nat) : Nat :=
  (((x[p / 8]?).getD 0).toNat >>> (7 - p % 8)) % 2

/-- The `width` bits of a byte string from bit `offset`, most significant first.

It is one integer of `base_2b`. -/
def msbField {k : Nat} (x : Vector UInt8 k) (offset width : Nat) : Nat :=
  (List.range width).foldl (fun value j => 2 * value + msbBit x (offset + j)) 0

/-- A bit is 0 or 1. -/
theorem msbBit_lt_two {k : Nat} (x : Vector UInt8 k) (p : Nat) : msbBit x p < 2 :=
  Nat.mod_lt _ (by decide)

/-- A field of `width` bits is below `2^width`. -/
theorem msbField_lt {k : Nat} (x : Vector UInt8 k) (offset width : Nat) :
    msbField x offset width < 2 ^ width := by
  induction width with
  | zero => simp [msbField]
  | succ width ih =>
    -- The last bit doubles the field read so far and adds itself.
    simp only [msbField, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      at ih ⊢
    have := msbBit_lt_two x (offset + width)
    rw [Nat.pow_succ]
    omega

/-- `(s_0, ..., s_23) = base_2b(md, a, k)`: the leaf of each FORS tree, from the first 30 bytes.

Leaf `s_kappa` is bits `10 kappa` to `10 kappa + 9` of the digest, most significant first. -/
def digestLeaves (d : MessageDigest) : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES :=
  -- Algorithm 19, line 6: `md <- digest[0 : ceil(k a / 8)]`.
  --
  -- Algorithm 16, line 2, reads it as `base_2b(md, a, k)`.
  Vector.ofFn fun kappa =>
    ⟨msbField d (FORS_HEIGHT * kappa.val) FORS_HEIGHT, msbField_lt d _ FORS_HEIGHT⟩

/-- The tree index: bytes 30 to 32 of the digest, as a big-endian integer cut to 18 bits. -/
def digestTree (d : MessageDigest) : Nat :=
  -- Algorithm 19, lines 7 and 9: `idx_tree <- toInt(tmp_idx_tree, ...) mod 2^(h - h/d)`.
  --
  -- Here the bottom height `h_0` stands for `h/d`, since the layers differ in height.
  EthLib.Base.ByteOrder.ofBE ((d.toList.drop MD_BYTES).take TREE_INDEX_BYTES)
    % 2 ^ (HEIGHT - LOWER_HEIGHT)

/-- The bottom leaf index: byte 33 of the digest, cut to 8 bits. -/
def digestLeaf (d : MessageDigest) : Nat :=
  -- Algorithm 19, lines 8 and 10: `idx_leaf <- toInt(tmp_idx_leaf, ...) mod 2^(h/d)`.
  --
  -- Here `h_0` stands for `h/d`.
  EthLib.Base.ByteOrder.ofBE ((d.toList.drop (MD_BYTES + TREE_INDEX_BYTES)).take LEAF_INDEX_BYTES)
    % 2 ^ LOWER_HEIGHT

/-- `idx = tree * 2^h_0 + leaf`: the bottom leaf the digest names, below `2^26`. -/
def digestIndex (d : MessageDigest) : Nat :=
  digestTree d * 2 ^ LOWER_HEIGHT + digestLeaf d

end EthLib.Cryptography.Sphincs
