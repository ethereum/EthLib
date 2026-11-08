module

public import EthLib.Cryptography.Aes.Ctr

/-!
# `Aes.Gcm`

The Galois/Counter Mode of [NIST SP 800-38D](https://doi.org/10.6028/NIST.SP.800-38D) §7.

It encrypts in counter mode and authenticates the ciphertext and the additional data with a tag.

Decryption returns the plaintext only when the tag matches.

All lengths are in bytes, since §5.2.1.1 asks for whole bytes.

The key is secret, and nothing here is constant-time, the tag comparison included.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

/-! ## Blocks as integers

SP 800-38D §6.1 reads a bit string as an integer, the first bit most significant.

So bit `x_i` of a block `x_0 ... x_127` is bit `127 - i` of its integer. -/

/-- The all-zero block `0^128`. -/
def zeroBlock : Block :=
  Vector.replicate 16 0

/-- The XOR of two blocks. -/
def xorBlock (X Y : Block) : Block :=
  Vector.zipWith (· ^^^ ·) X Y

/-- The integer of `R = 11100001 || 0^120`, SP 800-38D §6.3. -/
def R : Nat :=
  0xe1 * 2 ^ 120

/-- The product `X • Y` in GF(2^128), SP 800-38D §6.3, Algorithm 1.

The integer `v` holds `V_i`, so the right shift `V_i >> 1` halves it.

`LSB_1(V_i)` is the last bit of the string, the parity of `v`. -/
def mul (X Y : Block) : Block :=
  let x := blockToNat X
  -- Step 3, for i = 0 to 127, with `(Z_i, V_i)` as a pair of integers.
  let step (zv : Nat × Nat) (i : Nat) : Nat × Nat :=
    let (z, v) := zv
    let z := if (x / 2 ^ (127 - i)) % 2 = 1 then z ^^^ v else z
    let v := if v % 2 = 0 then v / 2 else v / 2 ^^^ R
    (z, v)
  -- Step 2 starts from `Z_0 = 0` and `V_0 = Y`, and step 4 returns `Z_128`.
  blockOfNat ((List.range 128).foldl step (0, blockToNat Y)).1

/-- GHASH of SP 800-38D §6.4, Algorithm 2, over the blocks `X_1 ... X_m`.

`Y_0` is the zero block, and `Y_i = (Y_(i-1) ^ X_i) • H`. -/
def ghash (H : Block) (X : List Block) : Block :=
  X.foldl (fun Y Xi => mul (xorBlock Y Xi) H) zeroBlock

/-- The blocks of a byte string, the last one completed with zero bytes.

For the additional data `A`, the result is `A || 0^v` of SP 800-38D §7.1, step 4, as blocks. -/
def blocksOf (data : ByteArray) : List Block :=
  (List.range ((data.size + 15) / 16)).map fun j =>
    Vector.ofFn fun i => data.data.getD (16 * j + i.val) 0

/-- GCTR of SP 800-38D §6.5, Algorithm 3.

It is the CTR mode of SP 800-38A with the incrementing function `inc_32` (§5.3). -/
def gctr (ciph : Block → Block) (icb : Block) (X : ByteArray) : ByteArray :=
  ctr ciph 32 icb X

/-! ## The authenticated encryption and decryption -/

/-- The reasons that GCM rejects an input.

Authenticated decryption returns FAIL for each of them (§7.2, steps 1 and 8). -/
inductive Error where
  /-- The tag length is not one of the seven of §5.2.1.2, or the tag has another length. -/
  | tagLength
  /-- The tag length is 64 or 32 bits, which Appendix C restricts and this module rejects. -/
  | shortTag
  /-- The IV is empty, or longer than `2^64 - 1` bits (§5.2.1.1). -/
  | ivLength
  /-- The plaintext or the ciphertext is longer than `2^39 - 256` bits (§5.2.1.1). -/
  | textLength
  /-- The additional data is longer than `2^64 - 1` bits (§5.2.1.1). -/
  | aadLength
  /-- The tag does not match (§7.2, step 8). -/
  | authentication
  deriving DecidableEq, Repr

/-- The code of each error, which the bindings report with its message. -/
def Error.code : Error → UInt32
  | .tagLength => 1
  | .shortTag => 2
  | .ivLength => 3
  | .textLength => 4
  | .aadLength => 5
  | .authentication => 6

/-- The supported tag lengths in bytes, for 128, 120, 112, 104 and 96 bits.

SP 800-38D §5.2.1.2 lets an implementation support only some of its seven tag lengths. -/
def tagLengths : List Nat :=
  [16, 15, 14, 13, 12]

/-- The short tag lengths of SP 800-38D §5.2.1.2 in bytes, for 64 and 32 bits.

Appendix C allows them only with a bound on the number of decryptions under each key.

One call cannot enforce that bound, so both functions reject these lengths. -/
def shortTagLengths : List Nat :=
  [8, 4]

/-- The length checks of SP 800-38D §5.2.1.1 and §5.2.1.2, all in bits. -/
def checkLengths (t : Nat) (iv text aad : ByteArray) : Except Error Unit := do
  if t ∈ shortTagLengths then throw .shortTag
  unless t ∈ tagLengths do throw .tagLength
  unless 1 ≤ 8 * iv.size ∧ 8 * iv.size ≤ 2 ^ 64 - 1 do throw .ivLength
  unless 8 * text.size ≤ 2 ^ 39 - 256 do throw .textLength
  unless 8 * aad.size ≤ 2 ^ 64 - 1 do throw .aadLength

/-- The pre-counter block `J_0` of SP 800-38D §7.1, step 2.

A 96-bit IV becomes `IV || 0^31 || 1`.

Any other IV is hashed with its length in bits: `GHASH_H(IV || 0^(s+64) || [len(IV)]_64)`. -/
def preCounter (H : Block) (iv : ByteArray) : Block :=
  if iv.size = 12 then
    Vector.ofFn fun i => if i.val < 12 then iv.data.getD i.val 0 else if i.val = 15 then 1 else 0
  else
    -- The padding `0^s` completes the last block, and `0^64 || [len(IV)]_64` is one more block.
    ghash H (blocksOf iv ++ [blockOfNat (8 * iv.size)])

/-- The padded input of GHASH in GCM, SP 800-38D §7.1, step 5.

It is the padded additional data, the padded ciphertext, and one block of both bit lengths. -/
def ghashInput (aad c : ByteArray) : List Block :=
  blocksOf aad ++ blocksOf c ++ [blockOfNat (8 * aad.size * 2 ^ 64 + 8 * c.size)]

/-- The tag `MSB_t(GCTR_K(J_0, S))` of SP 800-38D §7.1, steps 4 to 6, of `t` bytes.

`S` is GHASH of the padded additional data, the padded ciphertext, and both lengths in bits. -/
def tag (ciph : Block → Block) (t : Nat) (H J0 : Block) (aad c : ByteArray) : ByteArray :=
  (gctr ciph J0 ⟨(ghash H (ghashInput aad c)).toArray⟩).extract 0 t

/-- GCM-AE of SP 800-38D §7.1, Algorithm 4: the ciphertext and the tag.

The cipher argument is the forward cipher `CIPH_K`, so it carries a secret key.

The tag length `t` is in bytes. -/
def encrypt (ciph : Block → Block) (t : Nat) (iv p aad : ByteArray) :
    Except Error (ByteArray × ByteArray) := do
  checkLengths t iv p aad
  -- Step 1: the hash subkey.
  let H := ciph zeroBlock
  -- Step 2: the pre-counter block.
  let J0 := preCounter H iv
  -- Step 3: CTR encryption from the counter after `J_0`.
  let c := gctr ciph (inc 32 J0) p
  -- Steps 4 to 6: the tag over the additional data and the ciphertext.
  return (c, tag ciph t H J0 aad c)

/-- GCM-AD of SP 800-38D §7.2, Algorithm 5: the plaintext, or FAIL.

The cipher argument is the forward cipher `CIPH_K`, so it carries a secret key.

The tag length `t` is in bytes. -/
def decrypt (ciph : Block → Block) (t : Nat) (iv c aad T : ByteArray) : Except Error ByteArray := do
  -- Step 1: the supported lengths, and a tag of `t` bytes.
  checkLengths t iv c aad
  unless T.size = t do throw .tagLength
  -- Steps 2 and 3: the hash subkey and the pre-counter block.
  let H := ciph zeroBlock
  let J0 := preCounter H iv
  -- Step 4: CTR decryption from the counter after `J_0`.
  let p := gctr ciph (inc 32 J0) c
  -- Steps 5 to 8: the expected tag, then the comparison.
  if T = tag ciph t H J0 aad c then return p else throw .authentication

end EthLib.Cryptography.Aes.Gcm
