module

public import EthLib.Cryptography.Bls.KeyGen

/-!
# ERC-2333 key derivation

[ERC-2333, Key derivation][erc2333] derives child keys through two Lamport secret keys.

ERC-2333 `HKDF_mod_r` retries until the key is nonzero, with no bound.

The master and child operations reuse BLS key generation and fail after 16 unsuccessful attempts.

Seeds and secret keys are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).

[erc2333]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#key-derivation
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.KeyDerivation

open EthLib.Cryptography.Bls.Signatures
open EthLib.Cryptography.Hash

/-- The 255 chunks of a Lamport secret key, ERC-2333 `IKM_to_lamport_SK`. -/
def LAMPORT_CHUNKS : Nat := 255

/-- The 32 bytes of each Lamport chunk, ERC-2333 `IKM_to_lamport_SK`. -/
def LAMPORT_CHUNK_SIZE : Nat := 32

/-- Expand the input to 255 consecutive 32-byte chunks, [ERC-2333 `IKM_to_lamport_SK`][erc2333].

The extracted key is 32 bytes, and the output is exactly HKDF's limit of `255 * 32` bytes.

[erc2333]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#ikm_to_lamport_sk
-/
def ikmToLamportSk (ikm salt : ByteArray) : Vector ByteArray 255 :=
  let bytes := Hkdf.expandBlocks (Hkdf.extract salt ikm) ByteArray.empty ByteArray.empty
    1 LAMPORT_CHUNKS
  Vector.ofFn fun i =>
    bytes.extract (LAMPORT_CHUNK_SIZE * i.val) (LAMPORT_CHUNK_SIZE * (i.val + 1))

/-- Hash each chunk in order, [ERC-2333 `parent_SK_to_lamport_PK`][erc2333], steps 6 and 7.

[erc2333]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#parent_sk_to_lamport_pk
-/
def hashLamportSk (key : Vector ByteArray 255) : ByteArray :=
  key.toArray.foldl (fun out chunk => out ++ Sha256.hash chunk) ByteArray.empty

/-- The compressed Lamport public key, [ERC-2333 `parent_SK_to_lamport_PK`][erc2333].

[erc2333]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#parent_sk_to_lamport_pk
-/
def parentSkToLamportPk (parent : SecretKey) (index : UInt32) : ByteArray :=
  let salt := Base.natToBytes4 index.toNat
  let ikm := Fr.toBytesBE parent.val
  let first := ikmToLamportSk ikm salt
  let second := ikmToLamportSk ⟨ikm.data.map (~~~ ·)⟩ salt
  Sha256.hash (hashLamportSk first ++ hashLamportSk second)

/-- The master key of [ERC-2333 `derive_master_SK`][erc2333], with at most 16 attempts.

ERC-2333 `HKDF_mod_r` has no retry bound.

[erc2333]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#derive_master_sk
-/
def deriveMasterSk (seed : ByteArray) : Except BlsError SecretKey :=
  keyGen seed

/-- The child key of [ERC-2333 `derive_child_SK`][erc2333], with at most 16 attempts.

ERC-2333 `HKDF_mod_r` has no retry bound.

[erc2333]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#derive_child_sk
-/
def deriveChildSk (parent : SecretKey) (index : UInt32) : Except BlsError SecretKey :=
  keyGen (parentSkToLamportPk parent index)

/-- Follow child indices from a key, [ERC-2333, The Tree Structure][erc2333].

[erc2333]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#the-tree-structure
-/
def deriveChildPath : SecretKey → List UInt32 → Except BlsError SecretKey
  | parent, [] => .ok parent
  | parent, index :: rest => do
    let child ← deriveChildSk parent index
    deriveChildPath child rest

/-- Derive the master key and follow its child indices, [ERC-2333, The Tree Structure][erc2333].

[erc2333]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#the-tree-structure
-/
def derivePath (seed : ByteArray) (indices : List UInt32) : Except BlsError SecretKey := do
  let master ← deriveMasterSk seed
  deriveChildPath master indices

end EthLib.Cryptography.Bls.KeyDerivation
