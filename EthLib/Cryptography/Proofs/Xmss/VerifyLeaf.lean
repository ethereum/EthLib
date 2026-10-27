import EthLib.Cryptography.Proofs.Xmss.VerifyChains0
import EthLib.Cryptography.Proofs.Xmss.VerifyChains1
import EthLib.Cryptography.Proofs.Xmss.VerifyChains2
import EthLib.Cryptography.Proofs.Hash.Blake2s
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: the encoding and the recovered leaf

These theorems pin the message encoding and the 42 recovered chain ends.

```text
    message, randomness  --encode-->  42 digits
    signature chains     --walk to the end-->  42 chain ends  --hash-->  leaf
```

The values are intermediate states of verifying the reference signature at epoch 7.

They are computed by the verifier itself, so they are not checks on their own.

They split one large kernel evaluation into small steps.

The check is the final known answer: the reference signature verifies.

The leaf hash covers 704 bytes, which is 11 BLAKE2s blocks.

It is checked one block at a time, so each kernel evaluation stays small.

Hashing all 11 blocks in one kernel evaluation needs about 8 GB of memory, more than a CI runner can spare.
-/

namespace EthLib.Cryptography.Xmss
open Constants

theorem katEncodingHash :
    tweakHash examplePublicKey.publicParam .encoding 0 7
      (encodingPayload exampleMessage exampleSignature.randomness) =
    #v[89, 201, 250, 143, 73, 159, 199, 111, 250, 232, 236, 123, 233, 43, 242, 121] := by
  decide +kernel

theorem katEncode :
    wotsEncode examplePublicKey.publicParam exampleMessage exampleSignature.randomness 7 =
      some katDigits := by
  unfold wotsEncode
  rw [katEncodingHash]
  decide +kernel

theorem katRecover :
    otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits =
      katPublic := by
  apply Vector.ext
  intro i hi
  change i < 42 at hi
  interval_cases i
  · exact katChain0
  · exact katChain1
  · exact katChain2
  · exact katChain3
  · exact katChain4
  · exact katChain5
  · exact katChain6
  · exact katChain7
  · exact katChain8
  · exact katChain9
  · exact katChain10
  · exact katChain11
  · exact katChain12
  · exact katChain13
  · exact katChain14
  · exact katChain15
  · exact katChain16
  · exact katChain17
  · exact katChain18
  · exact katChain19
  · exact katChain20
  · exact katChain21
  · exact katChain22
  · exact katChain23
  · exact katChain24
  · exact katChain25
  · exact katChain26
  · exact katChain27
  · exact katChain28
  · exact katChain29
  · exact katChain30
  · exact katChain31
  · exact katChain32
  · exact katChain33
  · exact katChain34
  · exact katChain35
  · exact katChain36
  · exact katChain37
  · exact katChain38
  · exact katChain39
  · exact katChain40
  · exact katChain41

/-! ## The leaf hash, block by block -/

open Hash.Blake2s

/-- The 704 bytes the leaf hash reads: the tweak, the public parameter, then the 42 chain ends. -/
def leafInput : ByteArray :=
  ⟨⟨(makeTweak .leaf 0 7).toList ++ examplePublicKey.publicParam.toList ++
    (katPublic.toList.map Vector.toList).flatten⟩⟩

/-- The chaining value after 0 of the 11 leaf blocks. -/
def leafState0 : Array UInt32 :=
  #[0x6b08e647, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The chaining value after 1 of the 11 leaf blocks. -/
def leafState1 : Array UInt32 :=
  #[0x166761fb, 0x5079a3be, 0xa28ab538, 0x05e7638b,
    0xf92239e2, 0xdac07a1d, 0xeaeca9f2, 0x059db6e3]

/-- The chaining value after 2 of the 11 leaf blocks. -/
def leafState2 : Array UInt32 :=
  #[0x4bf8e83f, 0xa56f974b, 0x265d9aad, 0x771172c4,
    0x31fcc7b7, 0xd164f59f, 0xa2f5943a, 0xd3c93af1]

/-- The chaining value after 3 of the 11 leaf blocks. -/
def leafState3 : Array UInt32 :=
  #[0xaf392729, 0xb0029553, 0xab8183b2, 0x4f59967f,
    0xeba71c99, 0x23b72fdf, 0xc0eeb7f0, 0xd2596f58]

/-- The chaining value after 4 of the 11 leaf blocks. -/
def leafState4 : Array UInt32 :=
  #[0x6df613a1, 0xbaa09f76, 0x6bd5c1e0, 0xb201a9a0,
    0xbdc11a3f, 0xd4bff99a, 0x6eefa5a2, 0x35364651]

/-- The chaining value after 5 of the 11 leaf blocks. -/
def leafState5 : Array UInt32 :=
  #[0x8d8c0d6a, 0xa10f7356, 0xe54c34aa, 0xb6e3a258,
    0xf5218a26, 0xbe513738, 0xc05227cf, 0x151a294d]

/-- The chaining value after 6 of the 11 leaf blocks. -/
def leafState6 : Array UInt32 :=
  #[0x76ab3ab2, 0xda9a6d3e, 0x5dc0541b, 0xa72390fa,
    0x0c67a312, 0x2f6308ac, 0xfa7b1116, 0x5cb94ad3]

/-- The chaining value after 7 of the 11 leaf blocks. -/
def leafState7 : Array UInt32 :=
  #[0x7bc12475, 0x394fd3e1, 0x51a9bac8, 0xcb181cbb,
    0x99052d6d, 0x895cc9cc, 0x9db92725, 0xddc2d70d]

/-- The chaining value after 8 of the 11 leaf blocks. -/
def leafState8 : Array UInt32 :=
  #[0xe6c25223, 0xf59e84bd, 0x29f3e8fb, 0x15c2ae3e,
    0x523a2b64, 0x2bd20147, 0x1b42ba8b, 0xf82278e3]

/-- The chaining value after 9 of the 11 leaf blocks. -/
def leafState9 : Array UInt32 :=
  #[0xcf058fee, 0x46d62425, 0x65647d8c, 0x1aaa6f67,
    0xcb79a7d9, 0xadac95a3, 0x2a1eb904, 0x9b3630c9]

/-- The chaining value after 10 of the 11 leaf blocks. -/
def leafState10 : Array UInt32 :=
  #[0x7eb44610, 0xbc463555, 0x0f2a7b8e, 0x386b1809,
    0x0bfdea3c, 0x68682b0c, 0x500894ef, 0xa92885cf]

/-- The chaining value after 11 of the 11 leaf blocks. -/
def leafState11 : Array UInt32 :=
  #[0x8db38f75, 0x0a43e7de, 0xc88e268d, 0x3a5ca6b6,
    0x22f5b9ee, 0x0823922f, 0x1fb175c1, 0x694bb979]

/-- Compressing leaf block 0. -/
theorem leafStep0 : blockStep leafInput leafState0 0 = leafState1 := by
  decide +kernel

/-- Compressing leaf block 1. -/
theorem leafStep1 : blockStep leafInput leafState1 1 = leafState2 := by
  decide +kernel

/-- Compressing leaf block 2. -/
theorem leafStep2 : blockStep leafInput leafState2 2 = leafState3 := by
  decide +kernel

/-- Compressing leaf block 3. -/
theorem leafStep3 : blockStep leafInput leafState3 3 = leafState4 := by
  decide +kernel

/-- Compressing leaf block 4. -/
theorem leafStep4 : blockStep leafInput leafState4 4 = leafState5 := by
  decide +kernel

/-- Compressing leaf block 5. -/
theorem leafStep5 : blockStep leafInput leafState5 5 = leafState6 := by
  decide +kernel

/-- Compressing leaf block 6. -/
theorem leafStep6 : blockStep leafInput leafState6 6 = leafState7 := by
  decide +kernel

/-- Compressing leaf block 7. -/
theorem leafStep7 : blockStep leafInput leafState7 7 = leafState8 := by
  decide +kernel

/-- Compressing leaf block 8. -/
theorem leafStep8 : blockStep leafInput leafState8 8 = leafState9 := by
  decide +kernel

/-- Compressing leaf block 9. -/
theorem leafStep9 : blockStep leafInput leafState9 9 = leafState10 := by
  decide +kernel

/-- Compressing leaf block 10. -/
theorem leafStep10 : blockStep leafInput leafState10 10 = leafState11 := by
  decide +kernel

/-- 704 bytes are 11 blocks of 64 bytes. -/
theorem leafInput_blockCount : Internal.blockCount leafInput.size = 11 := by
  decide +kernel

/-- The first chaining value is the parameter-block IV. -/
theorem leafInitial : initialState = leafState0 := by
  decide +kernel

/-- The 11 compressions, chained. -/
theorem leafFold :
    (List.range' 0 11).foldl (blockStep leafInput) leafState0 = leafState11 := by
  show List.foldl (blockStep leafInput) leafState0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] = leafState11
  -- Peel one block at a time, replacing each compression by its checked value.
  rw [List.foldl_cons, leafStep0, List.foldl_cons, leafStep1, List.foldl_cons, leafStep2,
    List.foldl_cons, leafStep3, List.foldl_cons, leafStep4, List.foldl_cons, leafStep5,
    List.foldl_cons, leafStep6, List.foldl_cons, leafStep7, List.foldl_cons, leafStep8,
    List.foldl_cons, leafStep9, List.foldl_cons, leafStep10, List.foldl_nil]

/-- The recovered chain ends hash to the reference leaf. -/
theorem katLeaf_eq : otsLeaf examplePublicKey.publicParam 7 katPublic = katLeaf := by
  rw [otsLeaf_eq_tweakHashList]
  -- The list-based tweak hash is the hash of the 704 leaf bytes, truncated to 16.
  show (Hash.Blake2s.hash leafInput).take DIGEST_LEN = katLeaf
  -- Unfold the hash into its 11 compressions, then use the chained values.
  rw [hash_eq_foldl, leafInput_blockCount, leafInitial, leafFold]
  -- Only the final byte serialization is left for the kernel.
  decide +kernel

end EthLib.Cryptography.Xmss
