module

public import EthLib.Cryptography.Bls.KeyGen

/-!
# ERC-2333 key derivation

[ERC-2333, Key derivation][kd] derives child keys through two Lamport secret keys.

The master and child operations reuse [BLS key generation][mod].

That function loops until its key is not zero, without a bound.

EthLib stops after 16 attempts, its own choice, and fails if every attempt gives zero.

Seeds and secret keys are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).

The Lamport secret key follows [its derivation][lamport].

The compressed Lamport public key follows [its derivation][lamportPk].

The keys follow the derivations of the [master key][master] and of a [child key][child].

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

/-- The 255 chunks of a Lamport secret key, ERC-2333. -/
def LAMPORT_CHUNKS : Nat := 255

/-- The 32 bytes of each Lamport chunk, ERC-2333. -/
def LAMPORT_CHUNK_SIZE : Nat := 32

/-- Expand the input to 255 consecutive 32-byte chunks, the Lamport secret key of ERC-2333.

ERC-2333 asks HKDF-Expand for 255 * 32 bytes, which are exactly the first 255 HKDF blocks. -/
def ikmToLamportSk (ikm salt : ByteArray) : Vector ByteArray 255 :=
  -- Step 0: `PRK = HKDF-Extract(salt, IKM)`.
  --
  -- Step 1: `OKM = HKDF-Expand(PRK, "", L)`, with `L = K * 255`, as its first 255 blocks.
  --
  -- The extracted key is 32 bytes and 255 blocks are HKDF's limit, so neither check can fail.
  let bytes := Hkdf.expandBlocks (Hkdf.extract salt ikm) ByteArray.empty ByteArray.empty
    1 LAMPORT_CHUNKS
  -- Steps 2 and 3: the key is `OKM` split into chunks of `K = 32` bytes, one HMAC block per chunk.
  Vector.ofFn fun i =>
    bytes.extract (LAMPORT_CHUNK_SIZE * i.val) (LAMPORT_CHUNK_SIZE * (i.val + 1))

/-- Hash each chunk in order, steps 6 and 7 of the compressed Lamport public key derivation. -/
def hashLamportSk (key : Vector ByteArray 255) : ByteArray :=
  -- Steps 6 and 7: append the SHA-256 hash of chunk `i` of Lamport key `b`, here for one `b`.
  --
  -- The Note under the procedure runs `i` from 1 to 255, one per chunk: each is hashed once.
  key.toArray.foldl (fun out chunk => out ++ Sha256.hash chunk) ByteArray.empty

/-- The compressed Lamport public key of a parent key and an index, ERC-2333. -/
def parentSkToLamportPk (parent : SecretKey) (index : UInt32) : ByteArray :=
  -- Step 0: `salt = I2OSP(index, 4)`.
  let salt := Base.natToBytes4 index.toNat
  -- Step 1: `IKM` is the parent key as 32 big-endian bytes.
  let ikm := Fr.toBytesBE parent.val
  -- Step 2: the first Lamport secret key comes from `IKM` under `salt`.
  let first := ikmToLamportSk ikm salt
  -- Steps 3 and 4: the second comes from `IKM` with every bit flipped, under `salt`.
  let second := ikmToLamportSk ⟨ikm.data.map (~~~ ·)⟩ salt
  -- Step 5: the Lamport public key starts empty; here each half does, and the halves are joined.
  --
  -- Steps 6 and 7: append the SHA-256 hash of each chunk of the first key, then of the second.
  --
  -- Steps 8 and 9: the compressed Lamport public key is the SHA-256 hash of the Lamport public key.
  Sha256.hash (hashLamportSk first ++ hashLamportSk second)

/-- The master key of a seed, ERC-2333.

It fails after 16 attempts of key generation, a bound that ERC-2333 does not have. -/
def deriveMasterSk (seed : ByteArray) : Except BlsError SecretKey :=
  -- Steps 0 and 1: `SK` is the key that the key generation of the BLS draft gives for the seed.
  --
  -- That key generation stops after 16 attempts, and ERC-2333 sets no bound.
  keyGen seed

/-- The child key of a parent key and an index, ERC-2333.

It fails after 16 attempts of key generation, a bound that ERC-2333 does not have. -/
def deriveChildSk (parent : SecretKey) (index : UInt32) : Except BlsError SecretKey :=
  -- Step 0: key generation takes the compressed Lamport public key of the parent key and the index.
  --
  -- Steps 1 and 2: `SK` is the key that key generation gives for that compressed key.
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
