module

public import EthLib.Execution.Trie.Proof
public import EthLib.Cryptography.Proofs.Hash.KeccakKernel
public import EthLib.Execution.Proofs.Trie.RootKnownAnswers

/-!
# Proofs: known answers for `Trie.Proof`

The two proofs that `eth_getProof` returns in `tests/eth_getProof/get-account-proof-with-storage.io` of `ethereum/execution-apis`, at commit `3284ee80c3da3e516c53782dde75157cccf1ebdc`.

The test chain is `tests/chain.rlp` at that commit.

Its block 60 has the hash `0x52bccf...32e0` that the request names, and the state root `0xa6bd...63ec`.

- The account proof of `0x7dcd...7df` against that state root gives the account that the response states.
  That account is the RLP list of its nonce 0, its balance `0x6b`, its storage root and its code hash.
- The storage proof of slot 0 against that storage root gives the value `0x33`, which is its own RLP encoding.

Both tries are secured, so the key of the account is its address, and the key of the slot is the slot on 32 bytes.

Each claim states the value with Keccak-256.

Its proof evaluates the verifier with the form of Keccak-256 that `Proofs.Hash.KeccakKernel` proves equal to it.
-/

@[expose] public section

namespace EthLib.Execution.Trie.KnownAnswers

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Cryptography.Hash.Keccak (keccak256)
open EthLib.Serialization.Rlp.Vectors (byteArrayOf)

/-- The bytes of a value of a verified proof, as a list, which the kernel compares fast. -/
def valueBytes (result : Except ProofError (Option ByteArray)) : Option (Option (List UInt8)) :=
  result.toOption.map (·.map (·.data.toList))

/-- A value that the kernel computes with the fast form of Keccak-256 is the value with Keccak-256. -/
theorem verifyProof_eq_ok_of_kernel {root : Hash32} {secured : Bool} {key : ByteArray} {proof : List ByteArray}
    {expected : ByteArray}
    (h : valueBytes (verifyProof (fun message => Cryptography.Hash.Keccak.Kernel.keccak256 message) root secured key proof)
      = some (some expected.data.toList)) :
    verifyProof keccak256 root secured key proof = .ok (some expected) := by
  -- The two hashes agree on every message.
  have hash_eq : (fun message => Cryptography.Hash.Keccak.Kernel.keccak256 message) = (keccak256 : ByteArray → Hash32) :=
    funext fun message => (Cryptography.Hash.Keccak.Kernel.keccak256_eq message).symm
  rw [hash_eq] at h
  revert h
  cases verifyProof keccak256 root secured key proof with
  | error => simp [valueBytes, Except.toOption]
  | ok value =>
    cases value with
    | none => simp [valueBytes, Except.toOption]
    | some bytes =>
      simp only [valueBytes, Except.toOption, Option.map_some, Option.some.injEq]
      intro h
      cases bytes; cases expected
      simp_all

/-- The account `0x7dcd...7df` in the state of block 60. -/
theorem verifyProof_account :
    verifyProof keccak256 (hash32 0xa6bd32516beae9780a8c90563bb28c18f4299855f3f9d7c1de2db9a609ce63ec) true
      (byteArrayOf 20 0x7dcd17433742f4c0ca53122ab541d0ba67fc27df) [
      byteArrayOf 532 0xf90211a0aa42b26668326ed5b8915d4734a797eaca897f21096d24914559498451f0b112a0cb7b17051665fb5b2b77bf1ac92eada15f7b575983ea673d3f419efbddb902b3a08efa154101fa3b77f903fb502da910f9436555d74496a0f302ef711a8802934fa02636e9d3b38f0574793e04f19d8a1c5ab17aa77224e68c1d666d1af68e4e626ea0aadc6f28342e64c7b8198585227c7319f0dff7b34621d38c009b32327011d8b5a0ca18b337318dd07912104179d7fe2d693d7789ef1907f4edf4724f145a0c813da0ef81996518e6cd33d0a40eb9f7c34e07053c50f954f4e281405eafaa4425c1eba0f97e2b25eaadef5b89e50e037c3758fcaadd046cc9fb0374ff81db5ed81c1b8da0524b0c13980fd42ed78aef5005c5c260a48b54f9a16e2b546ccc62d82db1121ba026e488ba5a41ee1d52f0be4da566ff41b5beca18610d5d6f39c56e3b95ed5565a069673657f211dfb4974b747437ed34174589a67ea219a4f6f6f1bb9a127cd844a06ee77bf1d34c453205114a34ae7d38b89a9bdc1c13dd06f445dfd2e3205a1f03a093aecbab5390783d36169bab933609ca53c0202f36af56e40b46bdfd44da7404a0fcbd1316b950aec46e4380ee182b1b1f42874efda4cee909ac01408973341c38a058686a5c6b9cd991809b0e254a9dac3cee37b88e670a2a622d171c2ef8f46d74a0b4a09a27915585f8b90a09fe28bae1b619c29f167642e576694acf31cfe9bab580,
      byteArrayOf 115 0xf87180a09101b81fa76e587d1c11b13b2aff5fd8ac8151f482da23c47ad0f4745695b2e180808080808080808080a0fffa4d312c82f9ed55e9f8ee060b868767e64d7f74960d3840ba9623185b54298080a0fffa0f58320db99e249ead208fa8c09ec252c1ba9629cdbeb4f2e6d43679470680,
      byteArrayOf 83 0xf85180a04e09569877e2ee99d2618e1d46c412e240807de2a8b4f94e3aad956dec22b1668080808080808080a04f3d64a611072373222d90a8835ccaf9bd114c0ac0facad0801f1f96e2880555808080808080,
      byteArrayOf 106 0xf8689f3f52c702c40589735c4b038bd94e04268a58c35afad63bb16c071d62d2e23db846f844806ba09875336ba4c9ce1285d49fbea8c0e82830728ae09b8343b8f72975722ea2e791a0a3216dd3ef46a63d518ef54e482cecac68a077f70fca0e5fb900be63f41d54a2]
      = .ok (some (byteArrayOf 70 0xf844806ba09875336ba4c9ce1285d49fbea8c0e82830728ae09b8343b8f72975722ea2e791a0a3216dd3ef46a63d518ef54e482cecac68a077f70fca0e5fb900be63f41d54a2)) :=
  verifyProof_eq_ok_of_kernel (by decide +kernel)

/-- Slot 0 of the account `0x7dcd...7df`, in its storage trie. -/
theorem verifyProof_storage :
    verifyProof keccak256 (hash32 0x9875336ba4c9ce1285d49fbea8c0e82830728ae09b8343b8f72975722ea2e791) true
      (byteArrayOf 32 0) [
      byteArrayOf 500 0xf901f1a0c524ad62e5145b60acc8860eb4ec3e9ec1e9b0e63a883028c93943a77e3e0d88a0e0f863e70b2b109f05e3dbd0813f585fd44e9d5ca08e3f0b6306433c95990c56a09f195a2665d4bf7dc3ed932b5816cbe6a720f2e9cf25fcc3be114ddea3e90937a08a16f80d8ce55056713f959f2063e2b2c50455197491d48e1b407868c3b68158a02c1e1800c1aa4341c58f675e25c73ebe20b5715d00aca9029305566639e198eea06d611e1947247ba6686fac8dfcc9291671fe4d485d06c3967bcda0ab8a050133a0ca1829df66ec0c1e73064b3941ddbe97f2043b1f4f3c0883e2669c28d3ecb70fa0112559961d6092a78880220b26a0e2a91c5a4a8ff0cfc210abdaa9d4b802147ba017c0a52c69772cd5ff70a6025ea9e91b678454643ed867877183989a4b1e4fcca00bedcb4c1329da599d657af2ee16417fd4aede06ed600a293079d590edb08c2aa09a174c20afd335053b1b61777c0475469e342bc98aa8f729125b95efb09c876ca0a594efef7eee34e0783588688a848ec323744be7805126caf79b73c4b5ce8777a016ebd3e54bff3257cbd300eed15f8b896a5634fc29cab01f5f3939e22502735fa0d3da3e5752dd053fc0798b5e4ce8b3b0517fce023e844e6f37b8a83c9ae62019a00987e16792b11e3636800f86b009bfce841b078c9f5b4b67c65d7174c42159c58080,
      byteArrayOf 179 0xf8b1808080a08f7de8a82727a40833bf2db9070e03d4bb0cd3d55dea4ac8beb870d2c3de219180a0251550d4c1f81418d54b764bd8f15bd29c3d4f2d545646047a5204735743c79880a0aef8bbd9f33a5735d1ea2ccc36d4973d597c28cd5a5be31fbf55707766635e1ea09febc6802a5b78026f58a1ebf131ee65b1fc33472f6cc146d76d0af0c9b79d04a03822ab26403807d175522401e184b20b5aa8c7fcd802f4793970a70e810f4ce980808080808080,
      byteArrayOf 35 0xe2a0200decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e56333]
      = .ok (some (byteArrayOf 1 0x33)) :=
  verifyProof_eq_ok_of_kernel (by decide +kernel)

end EthLib.Execution.Trie.KnownAnswers
