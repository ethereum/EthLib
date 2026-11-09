module

public import EthLib.Cryptography.Bls.KeyGen

/-!
# ERC-2333 key derivation

[ERC-2333, Key derivation][erc2333] derives child keys through two Lamport secret keys.

The master and child operations reuse BLS key generation, including its bound of 16 attempts.

Seeds and secret keys are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).

[erc2333]: https://eips.ethereum.org/EIPS/eip-2333#key-derivation
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.KeyDerivation

open EthLib.Cryptography.Bls.Signatures
open EthLib.Cryptography.Hash

/-- The 255 chunks of a Lamport secret key, ERC-2333 `IKM_to_lamport_SK`. -/
def LAMPORT_CHUNKS : Nat := 255

/-- The 32 bytes of each Lamport chunk, ERC-2333 `IKM_to_lamport_SK`. -/
def LAMPORT_CHUNK_SIZE : Nat := 32

/-- Expand the input to 255 consecutive 32-byte chunks, ERC-2333 `IKM_to_lamport_SK`. -/
def ikmToLamportSk (ikm salt : ByteArray) : Except BlsError (Vector ByteArray 255) := do
  let bytes ← (Hkdf.expand (Hkdf.extract salt ikm) ByteArray.empty
    (LAMPORT_CHUNKS * LAMPORT_CHUNK_SIZE)).mapError fun _ => .keyGenHkdf
  return Vector.ofFn fun i =>
    bytes.extract (LAMPORT_CHUNK_SIZE * i.val) (LAMPORT_CHUNK_SIZE * (i.val + 1))

/-- Hash each chunk in order, ERC-2333 `parent_SK_to_lamport_PK`, steps 6 and 7. -/
def hashLamportSk (key : Vector ByteArray 255) : ByteArray :=
  key.toArray.foldl (fun out chunk => out ++ Sha256.hash chunk) ByteArray.empty

/-- The compressed Lamport public key, ERC-2333 `parent_SK_to_lamport_PK`. -/
def parentSkToLamportPk (parent : SecretKey) (index : UInt32) : Except BlsError ByteArray := do
  let salt := Base.natToBytes4 index.toNat
  let ikm := Fr.toBytesBE parent.val
  let first ← ikmToLamportSk ikm salt
  let second ← ikmToLamportSk ⟨ikm.data.map (~~~ ·)⟩ salt
  return Sha256.hash (hashLamportSk first ++ hashLamportSk second)

/-- The master key of ERC-2333 `derive_master_SK`, with the BLS retry bound. -/
def deriveMasterSk (seed : ByteArray) : Except BlsError SecretKey :=
  keyGen seed

/-- The child key of ERC-2333 `derive_child_SK`, with the BLS retry bound. -/
def deriveChildSk (parent : SecretKey) (index : UInt32) : Except BlsError SecretKey := do
  let compressed ← parentSkToLamportPk parent index
  keyGen compressed

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
