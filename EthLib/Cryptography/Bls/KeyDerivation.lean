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
  -- The extracted key is 32 bytes and 255 blocks are HKDF's limit, so neither check can fail.
  -- Each HMAC-SHA-256 block is one 32-byte chunk.
  let bytes := Hkdf.expandBlocks (Hkdf.extract salt ikm) ByteArray.empty ByteArray.empty
    1 LAMPORT_CHUNKS
  Vector.ofFn fun i =>
    bytes.extract (LAMPORT_CHUNK_SIZE * i.val) (LAMPORT_CHUNK_SIZE * (i.val + 1))

/-- Hash each chunk in order, ERC-2333 `parent_SK_to_lamport_PK`, steps 6 and 7. -/
def hashLamportSk (key : Vector ByteArray 255) : ByteArray :=
  key.toArray.foldl (fun out chunk => out ++ Sha256.hash chunk) ByteArray.empty

/-- The compressed Lamport public key, ERC-2333 `parent_SK_to_lamport_PK`. -/
def parentSkToLamportPk (parent : SecretKey) (index : UInt32) : ByteArray :=
  let salt := Base.natToBytes4 index.toNat
  let ikm := Fr.toBytesBE parent.val
  let first := ikmToLamportSk ikm salt
  let second := ikmToLamportSk ⟨ikm.data.map (~~~ ·)⟩ salt
  Sha256.hash (hashLamportSk first ++ hashLamportSk second)

/-- The master key of ERC-2333 `derive_master_SK`.

It fails after 16 attempts of `HKDF_mod_r`, a bound that ERC-2333 does not have. -/
def deriveMasterSk (seed : ByteArray) : Except BlsError SecretKey :=
  keyGen seed

/-- The child key of ERC-2333 `derive_child_SK`.

It fails after 16 attempts of `HKDF_mod_r`, a bound that ERC-2333 does not have. -/
def deriveChildSk (parent : SecretKey) (index : UInt32) : Except BlsError SecretKey :=
  keyGen (parentSkToLamportPk parent index)

/-- Follow child indices from a key, ERC-2333, The Tree Structure. -/
def deriveChildPath : SecretKey → List UInt32 → Except BlsError SecretKey
  | parent, [] => .ok parent
  | parent, index :: rest => do
    let child ← deriveChildSk parent index
    deriveChildPath child rest

/-- Derive the master key and follow its child indices, ERC-2333, The Tree Structure. -/
def derivePath (seed : ByteArray) (indices : List UInt32) : Except BlsError SecretKey := do
  let master ← deriveMasterSk seed
  deriveChildPath master indices

end EthLib.Cryptography.Bls.KeyDerivation
