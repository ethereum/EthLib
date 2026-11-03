module

public import EthLib.Execution.Trie.Root
public import EthLib.Cryptography.Proofs.Hash.KeccakKernel
public import EthLib.Serialization.Proofs.Rlp.Vectors

/-!
# Proofs: known answers for `Trie.Root`

The root of the empty map is `EMPTY_TRIE_ROOT` of execution-specs, secured or not.

Every case of four files of `TrieTests` in `ethereum/tests`, at commit `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`, in each file's order:

- `trietest.json` and `trieanyorder.json`, for the plain trie.
- `trietest_secureTrie.json` and `trieanyorder_secureTrie.json`, for the secured trie.

A case sets its keys one after another, starting from an empty trie, then gives the root.

A `null` value removes its key, as setting the empty byte string does.

A key or a value that starts with `0x` is hex, and any other is ASCII text.

Each claim states the root with Keccak-256.

Its proof evaluates the root with the form of Keccak-256 that `Proofs.Hash.KeccakKernel` proves equal to it.

The cases between the two markers are material from `ethereum/tests`, by the Ethereum Foundation.

They keep its licence, the MIT License, under this notice:

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
-/

@[expose] public section

namespace EthLib.Execution.Trie.KnownAnswers

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Cryptography.Hash.Keccak (keccak256)
open EthLib.Serialization.Rlp.Vectors (byteArrayOf)

/-- The trie that a case builds: each pair set in order, starting from an empty trie. -/
def ofOps (secured : Bool) (ops : List (ByteArray × ByteArray)) : Trie :=
  ops.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured, []⟩

/-- The 32 bytes of `value`, most significant first. -/
def hash32 (value : Nat) : Hash32 :=
  Vector.ofFn fun i => UInt8.ofNat (value / 256 ^ (31 - i.val))

/-- A root that the kernel computes with the fast form of Keccak-256 is the root with Keccak-256. -/
theorem root_eq_ok_of_kernel {trie : Trie} {expected : Hash32}
    (h : (root (fun message => Cryptography.Hash.Keccak.Kernel.keccak256 message) trie).toOption = some expected) :
    root keccak256 trie = .ok expected := by
  -- The two hashes agree on every message.
  have hash_eq : (fun message => Cryptography.Hash.Keccak.Kernel.keccak256 message) = (keccak256 : ByteArray → Hash32) :=
    funext fun message => (Cryptography.Hash.Keccak.Kernel.keccak256_eq message).symm
  rw [hash_eq] at h
  revert h
  cases root keccak256 trie <;> simp [Except.toOption]

/-- `EMPTY_TRIE_ROOT` in [`merkle_patricia_trie.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/merkle_patricia_trie.py#L71) of execution-specs at `2c0c8e7`: the root of the empty map, secured or not. -/
theorem root_empty_keccak256 (secured : Bool) :
    root keccak256 ⟨secured, []⟩
      = .ok (hash32 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421) := by
  cases secured <;> exact root_eq_ok_of_kernel (by decide +kernel)

-- Start of material from `ethereum/tests` (`TrieTests`), by the Ethereum Foundation, under the MIT License.

/-! ### `TrieTests/trietest.json` -/

theorem root_trietest_emptyValues :
    root keccak256 (ofOps false [
      ("do".toByteArray, "verb".toByteArray),
      ("ether".toByteArray, "wookiedoo".toByteArray),
      ("horse".toByteArray, "stallion".toByteArray),
      ("shaman".toByteArray, "horse".toByteArray),
      ("doge".toByteArray, "coin".toByteArray),
      ("ether".toByteArray, .empty),
      ("dog".toByteArray, "puppy".toByteArray),
      ("shaman".toByteArray, .empty)])
      = .ok (hash32 0x5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trietest_branchingTests :
    root keccak256 (ofOps false [
      (byteArrayOf 20 0x04110d816c380812a427968ece99b1c963dfbce6, "something".toByteArray),
      (byteArrayOf 20 0x095e7baea6a6c7c4c2dfeb977efac326af552d87, "something".toByteArray),
      (byteArrayOf 20 0x0a517d755cebbf66312b30fff713666a9cb917e0, "something".toByteArray),
      (byteArrayOf 20 0x24dd378f51adc67a50e339e8031fe9bd4aafab36, "something".toByteArray),
      (byteArrayOf 20 0x293f982d000532a7861ab122bdc4bbfd26bf9030, "something".toByteArray),
      (byteArrayOf 20 0x2cf5732f017b0cf1b1f13a1478e10239716bf6b5, "something".toByteArray),
      (byteArrayOf 20 0x31c640b92c21a1f1465c91070b4b3b4d6854195f, "something".toByteArray),
      (byteArrayOf 20 0x37f998764813b136ddf5a754f34063fd03065e36, "something".toByteArray),
      (byteArrayOf 20 0x37fa399a749c121f8a15ce77e3d9f9bec8020d7a, "something".toByteArray),
      (byteArrayOf 20 0x4f36659fa632310b6ec438dea4085b522a2dd077, "something".toByteArray),
      (byteArrayOf 20 0x62c01474f089b07dae603491675dc5b5748f7049, "something".toByteArray),
      (byteArrayOf 20 0x729af7294be595a0efd7d891c9e51f89c07950c7, "something".toByteArray),
      (byteArrayOf 20 0x83e3e5a16d3b696a0314b30b2534804dd5e11197, "something".toByteArray),
      (byteArrayOf 20 0x8703df2417e0d7c59d063caa9583cb10a4d20532, "something".toByteArray),
      (byteArrayOf 20 0x8dffcd74e5b5923512916c6a64b502689cfa65e1, "something".toByteArray),
      (byteArrayOf 20 0x95a4d7cccb5204733874fa87285a176fe1e9e240, "something".toByteArray),
      (byteArrayOf 20 0x99b2fcba8120bedd048fe79f5262a6690ed38c39, "something".toByteArray),
      (byteArrayOf 20 0xa4202b8b8afd5354e3e40a219bdc17f6001bf2cf, "something".toByteArray),
      (byteArrayOf 20 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b, "something".toByteArray),
      (byteArrayOf 20 0xa9647f4a0a14042d91dc33c0328030a7157c93ae, "something".toByteArray),
      (byteArrayOf 20 0xaa6cffe5185732689c18f37a7f86170cb7304c2a, "something".toByteArray),
      (byteArrayOf 20 0xaae4a2e3c51c04606dcb3723456e58f3ed214f45, "something".toByteArray),
      (byteArrayOf 20 0xc37a43e940dfb5baf581a0b82b351d48305fc885, "something".toByteArray),
      (byteArrayOf 20 0xd2571607e241ecf590ed94b12d87c94babe36db6, "something".toByteArray),
      (byteArrayOf 20 0xf735071cbee190d76b704ce68384fc21e389fbe7, "something".toByteArray),
      (byteArrayOf 20 0x04110d816c380812a427968ece99b1c963dfbce6, .empty),
      (byteArrayOf 20 0x095e7baea6a6c7c4c2dfeb977efac326af552d87, .empty),
      (byteArrayOf 20 0x0a517d755cebbf66312b30fff713666a9cb917e0, .empty),
      (byteArrayOf 20 0x24dd378f51adc67a50e339e8031fe9bd4aafab36, .empty),
      (byteArrayOf 20 0x293f982d000532a7861ab122bdc4bbfd26bf9030, .empty),
      (byteArrayOf 20 0x2cf5732f017b0cf1b1f13a1478e10239716bf6b5, .empty),
      (byteArrayOf 20 0x31c640b92c21a1f1465c91070b4b3b4d6854195f, .empty),
      (byteArrayOf 20 0x37f998764813b136ddf5a754f34063fd03065e36, .empty),
      (byteArrayOf 20 0x37fa399a749c121f8a15ce77e3d9f9bec8020d7a, .empty),
      (byteArrayOf 20 0x4f36659fa632310b6ec438dea4085b522a2dd077, .empty),
      (byteArrayOf 20 0x62c01474f089b07dae603491675dc5b5748f7049, .empty),
      (byteArrayOf 20 0x729af7294be595a0efd7d891c9e51f89c07950c7, .empty),
      (byteArrayOf 20 0x83e3e5a16d3b696a0314b30b2534804dd5e11197, .empty),
      (byteArrayOf 20 0x8703df2417e0d7c59d063caa9583cb10a4d20532, .empty),
      (byteArrayOf 20 0x8dffcd74e5b5923512916c6a64b502689cfa65e1, .empty),
      (byteArrayOf 20 0x95a4d7cccb5204733874fa87285a176fe1e9e240, .empty),
      (byteArrayOf 20 0x99b2fcba8120bedd048fe79f5262a6690ed38c39, .empty),
      (byteArrayOf 20 0xa4202b8b8afd5354e3e40a219bdc17f6001bf2cf, .empty),
      (byteArrayOf 20 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b, .empty),
      (byteArrayOf 20 0xa9647f4a0a14042d91dc33c0328030a7157c93ae, .empty),
      (byteArrayOf 20 0xaa6cffe5185732689c18f37a7f86170cb7304c2a, .empty),
      (byteArrayOf 20 0xaae4a2e3c51c04606dcb3723456e58f3ed214f45, .empty),
      (byteArrayOf 20 0xc37a43e940dfb5baf581a0b82b351d48305fc885, .empty),
      (byteArrayOf 20 0xd2571607e241ecf590ed94b12d87c94babe36db6, .empty),
      (byteArrayOf 20 0xf735071cbee190d76b704ce68384fc21e389fbe7, .empty)])
      = .ok (hash32 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trietest_jeff :
    root keccak256 (ofOps false [
      (byteArrayOf 32 0x0000000000000000000000000000000000000000000000000000000000000045, byteArrayOf 20 0x22b224a1420a802ab51d326e29fa98e34c4f24ea),
      (byteArrayOf 32 0x0000000000000000000000000000000000000000000000000000000000000046, byteArrayOf 32 0x67706c2076330000000000000000000000000000000000000000000000000000),
      (byteArrayOf 32 0x0000000000000000000000000000000000000000000000000000001234567890, byteArrayOf 20 0x697c7b8c961b56f675d570498424ac8de1a918f6),
      (byteArrayOf 32 0x000000000000000000000000697c7b8c961b56f675d570498424ac8de1a918f6, byteArrayOf 5 0x1234567890),
      (byteArrayOf 32 0x0000000000000000000000007ef9e639e2733cb34e4dfc576d4b23f72db776b2, byteArrayOf 32 0x4655474156000000000000000000000000000000000000000000000000000000),
      (byteArrayOf 32 0x000000000000000000000000ec4f34c97e43fbb2816cfd95e388353c7181dab1, byteArrayOf 32 0x4e616d6552656700000000000000000000000000000000000000000000000000),
      (byteArrayOf 32 0x4655474156000000000000000000000000000000000000000000000000000000, byteArrayOf 20 0x7ef9e639e2733cb34e4dfc576d4b23f72db776b2),
      (byteArrayOf 32 0x4e616d6552656700000000000000000000000000000000000000000000000000, byteArrayOf 20 0xec4f34c97e43fbb2816cfd95e388353c7181dab1),
      (byteArrayOf 32 0x0000000000000000000000000000000000000000000000000000001234567890, .empty),
      (byteArrayOf 32 0x000000000000000000000000697c7b8c961b56f675d570498424ac8de1a918f6, byteArrayOf 32 0x6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000),
      (byteArrayOf 32 0x6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000, byteArrayOf 20 0x697c7b8c961b56f675d570498424ac8de1a918f6)])
      = .ok (hash32 0x9f6221ebb8efe7cff60a716ecb886e67dd042014be444669f0159d8e68b42100) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trietest_insertMiddleLeaf :
    root keccak256 (ofOps false [
      ("key1aa".toByteArray, "0123456789012345678901234567890123456789xxx".toByteArray),
      ("key1".toByteArray, "0123456789012345678901234567890123456789Very_Long".toByteArray),
      ("key2bb".toByteArray, "aval3".toByteArray),
      ("key2".toByteArray, "short".toByteArray),
      ("key3cc".toByteArray, "aval3".toByteArray),
      ("key3".toByteArray, "1234567890123456789012345678901".toByteArray)])
      = .ok (hash32 0xcb65032e2f76c48b82b5c24b3db8f670ce73982869d38cd39a624f23d62a9e89) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trietest_branchValueUpdate :
    root keccak256 (ofOps false [
      ("abc".toByteArray, "123".toByteArray),
      ("abcd".toByteArray, "abcd".toByteArray),
      ("abc".toByteArray, "abc".toByteArray)])
      = .ok (hash32 0x7a320748f780ad9ad5b0837302075ce0eeba6c26e3d8562c67ccc0f1b273298a) :=
  root_eq_ok_of_kernel (by decide +kernel)

/-! ### `TrieTests/trieanyorder.json` -/

theorem root_trieanyorder_singleItem :
    root keccak256 (ofOps false [
      ("A".toByteArray, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".toByteArray)])
      = .ok (hash32 0xd23786fb4a010da3ce639d66d5e904a11dbc02746d1ce25029e53290cabf28ab) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorder_dogs :
    root keccak256 (ofOps false [
      ("doe".toByteArray, "reindeer".toByteArray),
      ("dog".toByteArray, "puppy".toByteArray),
      ("dogglesworth".toByteArray, "cat".toByteArray)])
      = .ok (hash32 0x8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorder_puppy :
    root keccak256 (ofOps false [
      ("do".toByteArray, "verb".toByteArray),
      ("horse".toByteArray, "stallion".toByteArray),
      ("doge".toByteArray, "coin".toByteArray),
      ("dog".toByteArray, "puppy".toByteArray)])
      = .ok (hash32 0x5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorder_foo :
    root keccak256 (ofOps false [
      ("foo".toByteArray, "bar".toByteArray),
      ("food".toByteArray, "bass".toByteArray)])
      = .ok (hash32 0x17beaa1648bafa633cda809c90c04af50fc8aed3cb40d16efbddee6fdf63c4c3) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorder_smallValues :
    root keccak256 (ofOps false [
      ("be".toByteArray, "e".toByteArray),
      ("dog".toByteArray, "puppy".toByteArray),
      ("bed".toByteArray, "d".toByteArray)])
      = .ok (hash32 0x3f67c7a47520f79faa29255d2d3c084a7a6df0453116ed7232ff10277a8be68b) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorder_testy :
    root keccak256 (ofOps false [
      ("test".toByteArray, "test".toByteArray),
      ("te".toByteArray, "testy".toByteArray)])
      = .ok (hash32 0x8452568af70d8d140f58d941338542f645fcca50094b20f3c3d8c3df49337928) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorder_hex :
    root keccak256 (ofOps false [
      (byteArrayOf 2 0x0045, byteArrayOf 5 0x0123456789),
      (byteArrayOf 2 0x4500, byteArrayOf 5 0x9876543210)])
      = .ok (hash32 0x285505fcabe84badc8aa310e2aae17eddc7d120aabec8a476902c8184b3a3503) :=
  root_eq_ok_of_kernel (by decide +kernel)

/-! ### `TrieTests/trietest_secureTrie.json` -/

theorem root_trietestSecure_emptyValues :
    root keccak256 (ofOps true [
      ("do".toByteArray, "verb".toByteArray),
      ("ether".toByteArray, "wookiedoo".toByteArray),
      ("horse".toByteArray, "stallion".toByteArray),
      ("shaman".toByteArray, "horse".toByteArray),
      ("doge".toByteArray, "coin".toByteArray),
      ("ether".toByteArray, .empty),
      ("dog".toByteArray, "puppy".toByteArray),
      ("shaman".toByteArray, .empty)])
      = .ok (hash32 0x29b235a58c3c25ab83010c327d5932bcf05324b7d6b1185e650798034783ca9d) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trietestSecure_branchingTests :
    root keccak256 (ofOps true [
      (byteArrayOf 20 0x04110d816c380812a427968ece99b1c963dfbce6, "something".toByteArray),
      (byteArrayOf 20 0x095e7baea6a6c7c4c2dfeb977efac326af552d87, "something".toByteArray),
      (byteArrayOf 20 0x0a517d755cebbf66312b30fff713666a9cb917e0, "something".toByteArray),
      (byteArrayOf 20 0x24dd378f51adc67a50e339e8031fe9bd4aafab36, "something".toByteArray),
      (byteArrayOf 20 0x293f982d000532a7861ab122bdc4bbfd26bf9030, "something".toByteArray),
      (byteArrayOf 20 0x2cf5732f017b0cf1b1f13a1478e10239716bf6b5, "something".toByteArray),
      (byteArrayOf 20 0x31c640b92c21a1f1465c91070b4b3b4d6854195f, "something".toByteArray),
      (byteArrayOf 20 0x37f998764813b136ddf5a754f34063fd03065e36, "something".toByteArray),
      (byteArrayOf 20 0x37fa399a749c121f8a15ce77e3d9f9bec8020d7a, "something".toByteArray),
      (byteArrayOf 20 0x4f36659fa632310b6ec438dea4085b522a2dd077, "something".toByteArray),
      (byteArrayOf 20 0x62c01474f089b07dae603491675dc5b5748f7049, "something".toByteArray),
      (byteArrayOf 20 0x729af7294be595a0efd7d891c9e51f89c07950c7, "something".toByteArray),
      (byteArrayOf 20 0x83e3e5a16d3b696a0314b30b2534804dd5e11197, "something".toByteArray),
      (byteArrayOf 20 0x8703df2417e0d7c59d063caa9583cb10a4d20532, "something".toByteArray),
      (byteArrayOf 20 0x8dffcd74e5b5923512916c6a64b502689cfa65e1, "something".toByteArray),
      (byteArrayOf 20 0x95a4d7cccb5204733874fa87285a176fe1e9e240, "something".toByteArray),
      (byteArrayOf 20 0x99b2fcba8120bedd048fe79f5262a6690ed38c39, "something".toByteArray),
      (byteArrayOf 20 0xa4202b8b8afd5354e3e40a219bdc17f6001bf2cf, "something".toByteArray),
      (byteArrayOf 20 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b, "something".toByteArray),
      (byteArrayOf 20 0xa9647f4a0a14042d91dc33c0328030a7157c93ae, "something".toByteArray),
      (byteArrayOf 20 0xaa6cffe5185732689c18f37a7f86170cb7304c2a, "something".toByteArray),
      (byteArrayOf 20 0xaae4a2e3c51c04606dcb3723456e58f3ed214f45, "something".toByteArray),
      (byteArrayOf 20 0xc37a43e940dfb5baf581a0b82b351d48305fc885, "something".toByteArray),
      (byteArrayOf 20 0xd2571607e241ecf590ed94b12d87c94babe36db6, "something".toByteArray),
      (byteArrayOf 20 0xf735071cbee190d76b704ce68384fc21e389fbe7, "something".toByteArray),
      (byteArrayOf 20 0x04110d816c380812a427968ece99b1c963dfbce6, .empty),
      (byteArrayOf 20 0x095e7baea6a6c7c4c2dfeb977efac326af552d87, .empty),
      (byteArrayOf 20 0x0a517d755cebbf66312b30fff713666a9cb917e0, .empty),
      (byteArrayOf 20 0x24dd378f51adc67a50e339e8031fe9bd4aafab36, .empty),
      (byteArrayOf 20 0x293f982d000532a7861ab122bdc4bbfd26bf9030, .empty),
      (byteArrayOf 20 0x2cf5732f017b0cf1b1f13a1478e10239716bf6b5, .empty),
      (byteArrayOf 20 0x31c640b92c21a1f1465c91070b4b3b4d6854195f, .empty),
      (byteArrayOf 20 0x37f998764813b136ddf5a754f34063fd03065e36, .empty),
      (byteArrayOf 20 0x37fa399a749c121f8a15ce77e3d9f9bec8020d7a, .empty),
      (byteArrayOf 20 0x4f36659fa632310b6ec438dea4085b522a2dd077, .empty),
      (byteArrayOf 20 0x62c01474f089b07dae603491675dc5b5748f7049, .empty),
      (byteArrayOf 20 0x729af7294be595a0efd7d891c9e51f89c07950c7, .empty),
      (byteArrayOf 20 0x83e3e5a16d3b696a0314b30b2534804dd5e11197, .empty),
      (byteArrayOf 20 0x8703df2417e0d7c59d063caa9583cb10a4d20532, .empty),
      (byteArrayOf 20 0x8dffcd74e5b5923512916c6a64b502689cfa65e1, .empty),
      (byteArrayOf 20 0x95a4d7cccb5204733874fa87285a176fe1e9e240, .empty),
      (byteArrayOf 20 0x99b2fcba8120bedd048fe79f5262a6690ed38c39, .empty),
      (byteArrayOf 20 0xa4202b8b8afd5354e3e40a219bdc17f6001bf2cf, .empty),
      (byteArrayOf 20 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b, .empty),
      (byteArrayOf 20 0xa9647f4a0a14042d91dc33c0328030a7157c93ae, .empty),
      (byteArrayOf 20 0xaa6cffe5185732689c18f37a7f86170cb7304c2a, .empty),
      (byteArrayOf 20 0xaae4a2e3c51c04606dcb3723456e58f3ed214f45, .empty),
      (byteArrayOf 20 0xc37a43e940dfb5baf581a0b82b351d48305fc885, .empty),
      (byteArrayOf 20 0xd2571607e241ecf590ed94b12d87c94babe36db6, .empty),
      (byteArrayOf 20 0xf735071cbee190d76b704ce68384fc21e389fbe7, .empty)])
      = .ok (hash32 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trietestSecure_jeff :
    root keccak256 (ofOps true [
      (byteArrayOf 32 0x0000000000000000000000000000000000000000000000000000000000000045, byteArrayOf 20 0x22b224a1420a802ab51d326e29fa98e34c4f24ea),
      (byteArrayOf 32 0x0000000000000000000000000000000000000000000000000000000000000046, byteArrayOf 32 0x67706c2076330000000000000000000000000000000000000000000000000000),
      (byteArrayOf 32 0x0000000000000000000000000000000000000000000000000000001234567890, byteArrayOf 20 0x697c7b8c961b56f675d570498424ac8de1a918f6),
      (byteArrayOf 32 0x000000000000000000000000697c7b8c961b56f675d570498424ac8de1a918f6, byteArrayOf 5 0x1234567890),
      (byteArrayOf 32 0x0000000000000000000000007ef9e639e2733cb34e4dfc576d4b23f72db776b2, byteArrayOf 32 0x4655474156000000000000000000000000000000000000000000000000000000),
      (byteArrayOf 32 0x000000000000000000000000ec4f34c97e43fbb2816cfd95e388353c7181dab1, byteArrayOf 32 0x4e616d6552656700000000000000000000000000000000000000000000000000),
      (byteArrayOf 32 0x4655474156000000000000000000000000000000000000000000000000000000, byteArrayOf 20 0x7ef9e639e2733cb34e4dfc576d4b23f72db776b2),
      (byteArrayOf 32 0x4e616d6552656700000000000000000000000000000000000000000000000000, byteArrayOf 20 0xec4f34c97e43fbb2816cfd95e388353c7181dab1),
      (byteArrayOf 32 0x0000000000000000000000000000000000000000000000000000001234567890, .empty),
      (byteArrayOf 32 0x000000000000000000000000697c7b8c961b56f675d570498424ac8de1a918f6, byteArrayOf 32 0x6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000),
      (byteArrayOf 32 0x6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000, byteArrayOf 20 0x697c7b8c961b56f675d570498424ac8de1a918f6)])
      = .ok (hash32 0x72adb52e9d9428f808e3e8045be18d3baa77881d0cfab89a17a2bcbacee2f320) :=
  root_eq_ok_of_kernel (by decide +kernel)

/-! ### `TrieTests/trieanyorder_secureTrie.json` -/

theorem root_trieanyorderSecure_singleItem :
    root keccak256 (ofOps true [
      ("A".toByteArray, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".toByteArray)])
      = .ok (hash32 0xe9e2935138352776cad724d31c9fa5266a5c593bb97726dd2a908fe6d53284df) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorderSecure_dogs :
    root keccak256 (ofOps true [
      ("doe".toByteArray, "reindeer".toByteArray),
      ("dog".toByteArray, "puppy".toByteArray),
      ("dogglesworth".toByteArray, "cat".toByteArray)])
      = .ok (hash32 0xd4cd937e4a4368d7931a9cf51686b7e10abb3dce38a39000fd7902a092b64585) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorderSecure_puppy :
    root keccak256 (ofOps true [
      ("do".toByteArray, "verb".toByteArray),
      ("horse".toByteArray, "stallion".toByteArray),
      ("doge".toByteArray, "coin".toByteArray),
      ("dog".toByteArray, "puppy".toByteArray)])
      = .ok (hash32 0x29b235a58c3c25ab83010c327d5932bcf05324b7d6b1185e650798034783ca9d) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorderSecure_foo :
    root keccak256 (ofOps true [
      ("foo".toByteArray, "bar".toByteArray),
      ("food".toByteArray, "bass".toByteArray)])
      = .ok (hash32 0x1385f23a33021025d9e87cca5c66c00de06178807b96a9acc92b7d651ccde842) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorderSecure_smallValues :
    root keccak256 (ofOps true [
      ("be".toByteArray, "e".toByteArray),
      ("dog".toByteArray, "puppy".toByteArray),
      ("bed".toByteArray, "d".toByteArray)])
      = .ok (hash32 0x826a4f9f9054a3e980e54b20da992c24fa20467f1ca635115ef4917be66e746f) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorderSecure_testy :
    root keccak256 (ofOps true [
      ("test".toByteArray, "test".toByteArray),
      ("te".toByteArray, "testy".toByteArray)])
      = .ok (hash32 0xaea54fb6c80499674248a462864c420c9d9f3b3d38c879c12425bade1ad76552) :=
  root_eq_ok_of_kernel (by decide +kernel)

theorem root_trieanyorderSecure_hex :
    root keccak256 (ofOps true [
      (byteArrayOf 2 0x0045, byteArrayOf 5 0x0123456789),
      (byteArrayOf 2 0x4500, byteArrayOf 5 0x9876543210)])
      = .ok (hash32 0xbc11c02c8ab456db0c4d2728b6a2a6210d06f26a2ace4f7d8bdfc72ddf2630ab) :=
  root_eq_ok_of_kernel (by decide +kernel)

-- End of material from `ethereum/tests`.

end EthLib.Execution.Trie.KnownAnswers
