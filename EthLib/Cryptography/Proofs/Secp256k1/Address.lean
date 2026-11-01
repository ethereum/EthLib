module

public import EthLib.Cryptography.Secp256k1.Address
public import EthLib.Cryptography.Proofs.Secp256k1.Recovery
public import EthLib.Cryptography.Proofs.Hash.Keccak256

/-!
# Proofs: Ethereum addresses

- `encodeUncompressed_eq`: the 64 hashed bytes are the uncompressed SEC 1 encoding without its `04` prefix.
- `addressOfPrivateKey_ne_none`: every private key in `[1, n - 1]` has an address.
- Three known answers, run by the kernel: the address of a private key, Keccak-256 and the scalar multiplication included.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

open Point

/-- The 64 bytes of `ECDSAPUBKEY` follow the prefix `04` in the uncompressed encoding. -/
theorem encodeUncompressed_eq (x y : Fp) :
    (affine x y).encodeUncompressed = ⟨#[0x04]⟩ ++ publicKeyBytes x y := by
  simp only [encodeUncompressed, publicKeyBytes]
  apply ByteArray.ext
  simp

/-- Every private key in `[1, n - 1]` has an address: `d G` is not `O`. -/
theorem addressOfPrivateKey_ne_none {d : Fn} (hd : d ≠ 0) : addressOfPrivateKey d ≠ none := by
  unfold addressOfPrivateKey
  have h := Ecdsa.mul_generator_ne_infinity hd
  split
  · rename_i heq
    exact absurd heq h
  · simp

/-! ## Known answers

All three pairs come from `ethereum/execution-specs` at commit `b758df2bcaaa95c04d31e25c94fbfb8d6de756e7`.

- [`fuzzer_bridge/README.md`](https://github.com/ethereum/execution-specs/blob/b758df2bcaaa95c04d31e25c94fbfb8d6de756e7/packages/testing/src/execution_testing/cli/fuzzer_bridge/README.md) gives the private key 1 the account `0x7e5f...5bdf`.
- [`base_types/constants.py`](https://github.com/ethereum/execution-specs/blob/b758df2bcaaa95c04d31e25c94fbfb8d6de756e7/packages/testing/src/execution_testing/base_types/constants.py) pairs `TestPrivateKey` with `TestAddress`, and `TestPrivateKey2` with `TestAddress2`.

Each claim is evaluated by the kernel, through the record form of Keccak-f, which is proved equal to the specification's. -/

/-- Whether a private key has the address a hex string spells. -/
def hasAddress (d : Fn) (hex : String) : Bool :=
  match addressOfPrivateKey d with
  | none => false
  | some a => a.toArray == (Hash.Keccak.hexBytes hex).data

/-- The private key 1, whose public key is `G`. -/
theorem address_privateKey_one : hasAddress 1 "7e5f4552091a69125d5dfcb7b8c2659029395bdf" = true := by
  simp only [hasAddress, addressOfPrivateKey, address, Hash.Keccak.Kernel.keccak256_eq]
  decide +kernel

/-- `TestPrivateKey` and `TestAddress`. -/
theorem address_testPrivateKey :
    hasAddress 0x45A915E4D060149EB4365960E6A7A45F334393093061116B197E3240065FF2D8
      "a94f5374fce5edbc8e2a8697c15331677e6ebf0b" = true := by
  simp only [hasAddress, addressOfPrivateKey, address, Hash.Keccak.Kernel.keccak256_eq]
  decide +kernel

/-- `TestPrivateKey2` and `TestAddress2`. -/
theorem address_testPrivateKey2 :
    hasAddress 0x9E7645D0CFD9C3A04EB7A9DB59A4EB7D359F2E75C9164A9D6B9A7D54E1B6A36F
      "8a0a19589531694250d570040a0c4b74576919b8" = true := by
  simp only [hasAddress, addressOfPrivateKey, address, Hash.Keccak.Kernel.keccak256_eq]
  decide +kernel

end EthLib.Cryptography.Secp256k1
