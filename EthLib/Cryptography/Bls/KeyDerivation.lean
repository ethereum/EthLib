module

public import EthLib.Cryptography.Bls.KeyGen

/-!
# ERC-2333 key derivation

[ERC-2333, Key derivation][kd] derives child keys through two Lamport secret keys.

The master and child operations reuse BLS key generation, which is [`HKDF_mod_r`][mod].

That function loops until its key is not zero, without a bound.

EthLib stops after 16 attempts, its own choice, and fails if every attempt gives zero.

Seeds and secret keys are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).

The Lamport keys follow [`IKM_to_lamport_SK`][lamport] and [`parent_SK_to_lamport_PK`][lamportPk].

The keys follow [`derive_master_SK`][master] and [`derive_child_SK`][child].

A list of child indices walks [the tree][tree] from the master key.

The links pin ERC-2333 at the commit that the Python vectors read.

[kd]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#key-derivation
[mod]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#hkdf_mod_r
[lamport]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#ikm_to_lamport_sk
[lamportPk]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#parent_sk_to_lamport_pk
[child]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#derive_child_sk
[master]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#derive_master_sk
[tree]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#the-tree-structure

-/

@[expose] public section

namespace EthLib.Cryptography.Bls.KeyDerivation

open EthLib.Cryptography.Bls.Signatures
open EthLib.Cryptography.Hash

/-- The 255 chunks of a Lamport secret key, ERC-2333 `IKM_to_lamport_SK`. -/
def LAMPORT_CHUNKS : Nat := 255

/-- The 32 bytes of each Lamport chunk, ERC-2333 `IKM_to_lamport_SK`. -/
def LAMPORT_CHUNK_SIZE : Nat := 32

/-- Expand the input to 255 consecutive 32-byte chunks, ERC-2333 `IKM_to_lamport_SK`.

ERC-2333 asks HKDF-Expand for 255 * 32 bytes, which are exactly the first 255 HKDF blocks. -/
def ikmToLamportSk (ikm salt : ByteArray) : Vector ByteArray 255 :=
  -- Step 0: `PRK = HKDF-Extract(salt, IKM)`.
  --
  -- Step 1: `OKM = HKDF-Expand(PRK, "", L)`, with `L = K * 255`, as its first 255 blocks.
  --
  -- The extracted key is 32 bytes and 255 blocks are HKDF's limit, so neither check can fail.
  let bytes := Hkdf.expandBlocks (Hkdf.extract salt ikm) ByteArray.empty ByteArray.empty
    1 LAMPORT_CHUNKS
  -- Steps 2 and 3: `lamport_SK = bytes_split(OKM, K)`, with `K = 32`: one HMAC block per chunk.
  Vector.ofFn fun i =>
    bytes.extract (LAMPORT_CHUNK_SIZE * i.val) (LAMPORT_CHUNK_SIZE * (i.val + 1))

/-- Hash each chunk in order, ERC-2333 `parent_SK_to_lamport_PK`, steps 6 and 7. -/
def hashLamportSk (key : Vector ByteArray 255) : ByteArray :=
  -- Steps 6 and 7: `lamport_PK = lamport_PK | SHA256(lamport_b[i])`, here for one `b`.
  --
  -- The Note under the procedure runs `i` from 1 to 255, one per chunk: each is hashed once.
  key.toArray.foldl (fun out chunk => out ++ Sha256.hash chunk) ByteArray.empty

/-- The compressed Lamport public key, ERC-2333 `parent_SK_to_lamport_PK`. -/
def parentSkToLamportPk (parent : SecretKey) (index : UInt32) : ByteArray :=
  -- Step 0: `salt = I2OSP(index, 4)`.
  let salt := Base.natToBytes4 index.toNat
  -- Step 1: `IKM = I2OSP(parent_SK, 32)`.
  let ikm := Fr.toBytesBE parent.val
  -- Step 2: `lamport_0 = IKM_to_lamport_SK(IKM, salt)`.
  let first := ikmToLamportSk ikm salt
  -- Steps 3 and 4: `not_IKM = flip_bits(IKM)`, and `lamport_1 = IKM_to_lamport_SK(not_IKM, salt)`.
  let second := ikmToLamportSk ⟨ikm.data.map (~~~ ·)⟩ salt
  -- Step 5: `lamport_PK = ""`; here each half starts empty and the halves are joined.
  --
  -- Steps 6 and 7: append `SHA256(lamport_0[i])`, then `SHA256(lamport_1[i])`, for each `i`.
  --
  -- Steps 8 and 9: `compressed_lamport_PK = SHA256(lamport_PK)`.
  Sha256.hash (hashLamportSk first ++ hashLamportSk second)

/-- The master key of ERC-2333 `derive_master_SK`.

It fails after 16 attempts of `HKDF_mod_r`, a bound that ERC-2333 does not have. -/
def deriveMasterSk (seed : ByteArray) : Except BlsError SecretKey :=
  -- Steps 0 and 1: `SK = HKDF_mod_r(seed)`, the key generation of the BLS draft.
  --
  -- That key generation stops after 16 attempts, and ERC-2333 sets no bound.
  keyGen seed

/-- The child key of ERC-2333 `derive_child_SK`.

It fails after 16 attempts of `HKDF_mod_r`, a bound that ERC-2333 does not have. -/
def deriveChildSk (parent : SecretKey) (index : UInt32) : Except BlsError SecretKey :=
  -- Step 0: `compressed_lamport_PK = parent_SK_to_lamport_PK(parent_SK, index)`.
  --
  -- Steps 1 and 2: `SK = HKDF_mod_r(compressed_lamport_PK)`.
  --
  -- That key generation stops after 16 attempts, and ERC-2333 sets no bound.
  keyGen (parentSkToLamportPk parent index)

/-- Follow child indices from a key, ERC-2333, The Tree Structure. -/
def deriveChildPath : SecretKey → List UInt32 → Except BlsError SecretKey
  -- A path `m / i / j / ...` derives each child from its parent, one index at a time.
  | parent, [] => .ok parent
  | parent, index :: rest => do
    let child ← deriveChildSk parent index
    deriveChildPath child rest

/-- Derive the master key and follow its child indices, ERC-2333, The Tree Structure. -/
def derivePath (seed : ByteArray) (indices : List UInt32) : Except BlsError SecretKey := do
  -- The root of the tree, `m`, is the master key.
  let master ← deriveMasterSk seed
  deriveChildPath master indices

end EthLib.Cryptography.Bls.KeyDerivation
