module

public import EthLib.Networking.Enr.V4
public import EthLib.Cryptography.Proofs.Hash.Keccak256
public import EthLib.Cryptography.Proofs.Hash.KeccakKernel

/-!
# Proofs: the test vector of EIP-778

The test record of EIP-778 holds the IPv4 address `127.0.0.1` and the UDP port 30303.

Source: [EIP-778](https://github.com/ethereum/EIPs/blob/7622abc1c6569b7e7ade9ed957dde4ed2271cc40/EIPS/eip-778.md).

The text of the record decodes to the RLP structure that the EIP lists.

The "v4" signature verifies, and the node ID is the one that the EIP gives.

The same record with two keys swapped, or with a key repeated, is rejected.

The kernel evaluates each claim, and Keccak-256 runs in its record form.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (hexBytes)

/-- The text form of the EIP's record. -/
def eipText : String :=
  "enr:-IS4QHCYrYZbAKWCBRlAy5zzaDZXJBGkcnh4MHcBFZntXNFrdvJjX04jRzjzCBOonrkTfj499SZuOh8R33Ls8RRc\
    y5wBgmlkgnY0gmlwhH8AAAGJc2VjcDI1NmsxoQPKY0yuDUmstAHYpMa2_oxVtw0RW_QAdpzBQA8yWM0xOIN1ZHCCdl8"

/-- The signature of the EIP's record, `r` then `s`. -/
def eipSignature : ByteArray := hexBytes
  "7098ad865b00a582051940cb9cf36836572411a47278783077011599ed5cd16b\
    76f2635f4e234738f30813a89eb9137e3e3df5266e3a1f11df72ecf1145ccb9c"

/-- The pair `id`, `v4`. -/
def pairId : ByteArray × Item := (hexBytes "6964", .bytes (hexBytes "7634"))

/-- The pair `ip`, `127.0.0.1`. -/
def pairIp : ByteArray × Item := (hexBytes "6970", .bytes (hexBytes "7f000001"))

/-- The pair `secp256k1`, the compressed public key. -/
def pairSecp256k1 : ByteArray × Item := (hexBytes "736563703235366b31",
  .bytes (hexBytes "03ca634cae0d49acb401d8a4c6b6fe8c55b70d115bf400769cc1400f3258cd3138"))

/-- The pair `udp`, the port 30303. -/
def pairUdp : ByteArray × Item := (hexBytes "756470", .bytes (hexBytes "765f"))

/-- The record as the EIP lists its RLP structure. -/
def eipRecord : Enr :=
  ⟨eipSignature, 1, [pairId, pairIp, pairSecp256k1, pairUdp]⟩

/-- The text decodes to the listed record. -/
theorem fromText_eip : (fromText eipText).toOption = some eipRecord := by
  decide +kernel

/-- The signature verifies under the public key of the record. -/
theorem verifyV4_eip : verifyV4 eipRecord = true := by
  simp only [verifyV4, Cryptography.Hash.Keccak.Kernel.keccak256_eq]
  decide +kernel

/-- The node ID is the one that the EIP gives. -/
theorem nodeId_eip : (nodeId eipRecord).toOption.map Vector.toArray
    = some (hexBytes "a448f24c6d18e575453db13171562b71999873db5b286df957af199ec94617f7").data := by
  simp only [nodeId, Cryptography.Hash.Keccak.Kernel.keccak256_eq]
  decide +kernel

/-! ## Rejections -/

/-- The error of a failed decoding, or `none` for a success. -/
def errorOf (result : Except EnrError Enr) : Option EnrError :=
  match result with
  | .error e => some e
  | .ok _ => none

/-- The RLP bytes of a record with these pairs, in this order. -/
def bytesOf (pairs : List (ByteArray × Item)) : ByteArray :=
  ((⟨eipSignature, 1, pairs⟩ : Enr).encode).toOption.getD .empty

/-- The keys `ip` and `id` out of order. -/
theorem decode_unsorted :
    errorOf (decode (bytesOf [pairIp, pairId, pairSecp256k1, pairUdp]))
      = some (.unsortedKeys pairIp.1 pairId.1) := by
  decide +kernel

/-- The key `ip` twice. -/
theorem decode_repeated :
    errorOf (decode (bytesOf [pairId, pairIp, pairIp, pairSecp256k1, pairUdp]))
      = some (.repeatedKey pairIp.1) := by
  decide +kernel

/-- The last character of the text changed from `8` to `9`, which sets an unused bit. -/
theorem fromText_nonZeroPadBits :
    errorOf (fromText
      "enr:-IS4QHCYrYZbAKWCBRlAy5zzaDZXJBGkcnh4MHcBFZntXNFrdvJjX04jRzjzCBOonrkTfj499SZuOh8R33Ls8RRc\
      y5wBgmlkgnY0gmlwhH8AAAGJc2VjcDI1NmsxoQPKY0yuDUmstAHYpMa2_oxVtw0RW_QAdpzBQA8yWM0xOIN1ZHCCdl9")
      = some (.base64 .nonZeroPadBits) := by
  decide +kernel

end EthLib.Networking.Enr
