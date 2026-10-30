import EthLib.Serialization.Rlp.Encode
import EthLib.Serialization.Proofs.Rlp.Item
import EthLib.Serialization.Proofs.Rlp.Vectors

/-!
# `Serialization.Proofs.Rlp.Encode`

The bound on a length, and known answers for the RLP encoding.

A claim `output r = some b` says that `r` succeeds, with exactly the bytes `b`.

`decide +kernel` has the kernel itself evaluate each such claim.

It adds no axiom, unlike `native_decide`.
-/

namespace EthLib.Serialization.Rlp

open Vectors

/-- The bytes of a success, as a list, or `none` for a failure.

The kernel compares two lists of bytes in linear time.

With `decide +kernel`, comparing two `ByteArray`s of a kilobyte takes more than 6 GB of memory instead. -/
private def output (result : Except RlpError ByteArray) : Option (List UInt8) :=
  result.toOption.map (·.data.toList)

/-! ## The bound of a length

A length must be below `2^64`.

No test vector comes near it: no byte string that long fits in memory.

So the prefix of the largest length is checked on `lengthPrefix` directly.

Every longer payload is proved to make `encode` fail. -/

/-- Below `2^64`, the first byte of a long prefix is at most `offset + 63`.

That is `0xbf` for a byte string, below every list, and `0xff` for a list, still a byte.

So the first byte of a prefix never wraps around 256. -/
theorem lengthPrefix_first_byte_le (kind : PayloadKind) (length : Nat) (h : length < 2 ^ 64) :
    kind.offset + 55 + (bigEndian length).size ≤ kind.offset + 63 := by
  -- `2^64 = 256^8`, so the length has at most 8 digits in base 256.
  have := bigEndian_size_le length 8 (by simpa using h)
  omega

/-- The largest length, `2^64 - 1`, for a byte string: the prefix `bf`, then the length on 8 bytes. -/
theorem lengthPrefix_bytes_max :
    output (lengthPrefix .bytes (2 ^ 64 - 1)) = some (bytesOf 9 0xbfffffffffffffffff) := by
  decide +kernel

/-- The same length for a list: the prefix `ff`, then the length on 8 bytes. -/
theorem lengthPrefix_list_max :
    output (lengthPrefix .list (2 ^ 64 - 1)) = some (bytesOf 9 0xffffffffffffffffff) := by
  decide +kernel

/-- `lengthPrefix` refuses every length from `2^64` on, for a byte string or a list. -/
theorem lengthPrefix_too_long (kind : PayloadKind) (length : Nat) (h : 2 ^ 64 ≤ length) :
    lengthPrefix kind length = .error (.payloadTooLong length) := by
  -- `length` is below neither bound of `lengthPrefix`, 56 or `2^64`.
  have notShort : ¬ length < 56 := Nat.not_lt.mpr (Nat.le_trans (by decide) h)
  have notLong : ¬ length < 2 ^ 64 := Nat.not_lt.mpr h
  rw [lengthPrefix, ite_eq_right notShort, ite_eq_right notLong]

/-- `encode` refuses a byte string of `2^64` bytes or more. -/
theorem encode_bytes_too_long (data : ByteArray) (h : 2 ^ 64 ≤ data.size) :
    encode (.bytes data) = .error (.payloadTooLong data.size) := by
  -- More than one byte, so the byte string is not its own encoding and takes a prefix.
  have notOne : data.size ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h)
  have notSingle : isSingleLowByte data = false := by simp [isSingleLowByte, notOne]
  rw [encode, encodeBytes, notSingle]
  -- The prefix fails, so the encoding fails with it.
  show (fun prefixBytes => prefixBytes ++ data) <$> lengthPrefix .bytes data.size = _
  rw [lengthPrefix_too_long .bytes data.size h]
  rfl

/-- `encode` refuses a list whose items encode to a payload of `2^64` bytes or more. -/
theorem encode_list_too_long (items : List Item) (payload : ByteArray)
    (hp : joinEncodings items = .ok payload) (h : 2 ^ 64 ≤ payload.size) :
    encode (.list items) = .error (.payloadTooLong payload.size) := by
  rw [encode, hp]
  -- The prefix of the payload fails, so the encoding fails with it.
  show (fun prefixBytes => prefixBytes ++ payload) <$> lengthPrefix .list payload.size = _
  rw [lengthPrefix_too_long .list payload.size h]
  rfl

/-! ## `RLPTests/rlptest.json`

Every case of `RLPTests/rlptest.json` in `ethereum/tests`, at commit `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`, in the file's order.

Each claim is named after its case.

An input is read by its JSON type:

- an array is a list;
- a number is a scalar;
- a string is a byte string, one byte per character, all of them ASCII here.

`docs/test_types/rlp_tests.rst` in the same repository sets two exceptions for strings.

A string that starts with `#` is a decimal number, so it is a scalar too.

A string that starts with `0x` is hex bytes, but no input of this file starts with `0x`.

A list of more than two copies of one list is written with `List.replicate`.

A string longer than 64 characters is cut after a space into pieces, written with `strPieces`.

The file writes each output in hex, and the same hex follows its byte count below.

The cases between the two markers are material from `ethereum/tests`, by the Ethereum Foundation.

They keep its licence, the MIT License, under this notice:

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
-/

-- Start of material from `ethereum/tests` (`RLPTests/rlptest.json`), by the Ethereum Foundation, under the MIT License.

theorem encode_emptystring :
    output (encode (str "")) = some (bytesOf 1 0x80) := by
  decide +kernel

theorem encode_bytestring00 :
    output (encode (str "\u0000")) = some (bytesOf 1 0x00) := by
  decide +kernel

theorem encode_bytestring01 :
    output (encode (str "\u0001")) = some (bytesOf 1 0x01) := by
  decide +kernel

theorem encode_bytestring7F :
    output (encode (str "\u007F")) = some (bytesOf 1 0x7f) := by
  decide +kernel

theorem encode_shortstring :
    output (encode (str "dog")) = some (bytesOf 4 0x83646f67) := by
  decide +kernel

theorem encode_shortstring2 :
    output (encode (str "Lorem ipsum dolor sit amet, consectetur adipisicing eli")) = some (bytesOf 56 0xb74c6f72656d20697073756d20646f6c6f722073697420616d65742c20636f6e7365637465747572206164697069736963696e6720656c69) := by
  decide +kernel

theorem encode_longstring :
    output (encode (str "Lorem ipsum dolor sit amet, consectetur adipisicing elit")) = some (bytesOf 58 0xb8384c6f72656d20697073756d20646f6c6f722073697420616d65742c20636f6e7365637465747572206164697069736963696e6720656c6974) := by
  decide +kernel

theorem encode_longstring2 :
    output (encode (strPieces [
      "Lorem ipsum dolor sit amet, consectetur adipiscing elit. ",
      "Curabitur mauris magna, suscipit sed vehicula non, iaculis ",
      "faucibus tortor. Proin suscipit ultricies malesuada. Duis ",
      "tortor elit, dictum quis tristique eu, ultrices at risus. Morbi ",
      "a est imperdiet mi ullamcorper aliquet suscipit nec lorem. ",
      "Aenean quis leo mollis, vulputate elit varius, consequat enim. ",
      "Nulla ultrices turpis justo, et posuere urna consectetur nec. ",
      "Proin non convallis metus. Donec tempor ipsum in mauris congue ",
      "sollicitudin. Vestibulum ante ipsum primis in faucibus orci ",
      "luctus et ultrices posuere cubilia Curae; Suspendisse convallis ",
      "sem vel massa faucibus, eget lacinia lacus tempor. Nulla quis ",
      "ultricies purus. Proin auctor rhoncus nibh condimentum mollis. ",
      "Aliquam consequat enim at metus luctus, a eleifend purus ",
      "egestas. Curabitur at nibh metus. Nam bibendum, neque at auctor ",
      "tristique, lorem libero aliquet arcu, non interdum tellus ",
      "lectus sit amet eros. Cras rhoncus, metus ac ornare cursus, ",
      "dolor justo ultrices metus, at ullamcorper volutpat"])) = some (bytesOf 1027 0xb904004c6f72656d20697073756d20646f6c6f722073697420616d65742c20636f6e73656374657475722061646970697363696e6720656c69742e20437572616269747572206d6175726973206d61676e612c20737573636970697420736564207665686963756c61206e6f6e2c20696163756c697320666175636962757320746f72746f722e2050726f696e20737573636970697420756c74726963696573206d616c6573756164612e204475697320746f72746f7220656c69742c2064696374756d2071756973207472697374697175652065752c20756c7472696365732061742072697375732e204d6f72626920612065737420696d70657264696574206d6920756c6c616d636f7270657220616c6971756574207375736369706974206e6563206c6f72656d2e2041656e65616e2071756973206c656f206d6f6c6c69732c2076756c70757461746520656c6974207661726975732c20636f6e73657175617420656e696d2e204e756c6c6120756c74726963657320747572706973206a7573746f2c20657420706f73756572652075726e6120636f6e7365637465747572206e65632e2050726f696e206e6f6e20636f6e76616c6c6973206d657475732e20446f6e65632074656d706f7220697073756d20696e206d617572697320636f6e67756520736f6c6c696369747564696e2e20566573746962756c756d20616e746520697073756d207072696d697320696e206661756369627573206f726369206c756374757320657420756c74726963657320706f737565726520637562696c69612043757261653b2053757370656e646973736520636f6e76616c6c69732073656d2076656c206d617373612066617563696275732c2065676574206c6163696e6961206c616375732074656d706f722e204e756c6c61207175697320756c747269636965732070757275732e2050726f696e20617563746f722072686f6e637573206e69626820636f6e64696d656e74756d206d6f6c6c69732e20416c697175616d20636f6e73657175617420656e696d206174206d65747573206c75637475732c206120656c656966656e6420707572757320656765737461732e20437572616269747572206174206e696268206d657475732e204e616d20626962656e64756d2c206e6571756520617420617563746f72207472697374697175652c206c6f72656d206c696265726f20616c697175657420617263752c206e6f6e20696e74657264756d2074656c6c7573206c65637475732073697420616d65742065726f732e20437261732072686f6e6375732c206d65747573206163206f726e617265206375727375732c20646f6c6f72206a7573746f20756c747269636573206d657475732c20617420756c6c616d636f7270657220766f6c7574706174) := by
  decide +kernel

theorem encode_zero :
    output (encode (.scalar 0)) = some (bytesOf 1 0x80) := by
  decide +kernel

theorem encode_smallint :
    output (encode (.scalar 1)) = some (bytesOf 1 0x01) := by
  decide +kernel

theorem encode_smallint2 :
    output (encode (.scalar 16)) = some (bytesOf 1 0x10) := by
  decide +kernel

theorem encode_smallint3 :
    output (encode (.scalar 79)) = some (bytesOf 1 0x4f) := by
  decide +kernel

theorem encode_smallint4 :
    output (encode (.scalar 127)) = some (bytesOf 1 0x7f) := by
  decide +kernel

theorem encode_mediumint1 :
    output (encode (.scalar 128)) = some (bytesOf 2 0x8180) := by
  decide +kernel

theorem encode_mediumint2 :
    output (encode (.scalar 1000)) = some (bytesOf 3 0x8203e8) := by
  decide +kernel

theorem encode_mediumint3 :
    output (encode (.scalar 100000)) = some (bytesOf 4 0x830186a0) := by
  decide +kernel

theorem encode_mediumint4 :
    output (encode (.scalar 83729609699884896815286331701780722)) = some (bytesOf 16 0x8f102030405060708090a0b0c0d0e0f2) := by
  decide +kernel

theorem encode_mediumint5 :
    output (encode (.scalar 105315505618206987246253880190783558935785933862974822347068935681)) = some (bytesOf 29 0x9c0100020003000400050006000700080009000a000b000c000d000e01) := by
  decide +kernel

theorem encode_emptylist :
    output (encode (.list [])) = some (bytesOf 1 0xc0) := by
  decide +kernel

theorem encode_stringlist :
    output (encode (.list [str "dog", str "god", str "cat"])) = some (bytesOf 13 0xcc83646f6783676f6483636174) := by
  decide +kernel

theorem encode_multilist :
    output (encode (.list [str "zw", .list [.scalar 4], .scalar 1])) = some (bytesOf 7 0xc6827a77c10401) := by
  decide +kernel

theorem encode_shortListMax1 :
    output (encode (.list [str "asdf", str "qwer", str "zxcv", str "asdf", str "qwer", str "zxcv", str "asdf", str "qwer", str "zxcv", str "asdf", str "qwer"])) = some (bytesOf 56 0xf784617364668471776572847a78637684617364668471776572847a78637684617364668471776572847a78637684617364668471776572) := by
  decide +kernel

theorem encode_longList1 :
    output (encode (.list (List.replicate 4 (.list [str "asdf", str "qwer", str "zxcv"])))) = some (bytesOf 66 0xf840cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376) := by
  decide +kernel

theorem encode_longList2 :
    output (encode (.list (List.replicate 32 (.list [str "asdf", str "qwer", str "zxcv"])))) = some (bytesOf 515 0xf90200cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376) := by
  decide +kernel

theorem encode_listsoflists :
    output (encode (.list [.list [.list [], .list []], .list []])) = some (bytesOf 5 0xc4c2c0c0c0) := by
  decide +kernel

theorem encode_listsoflists2 :
    output (encode (.list [.list [], .list [.list []], .list [.list [], .list [.list []]]])) = some (bytesOf 8 0xc7c0c1c0c3c0c1c0) := by
  decide +kernel

theorem encode_dictTest1 :
    output (encode (.list [.list [str "key1", str "val1"], .list [str "key2", str "val2"], .list [str "key3", str "val3"], .list [str "key4", str "val4"]])) = some (bytesOf 45 0xecca846b6579318476616c31ca846b6579328476616c32ca846b6579338476616c33ca846b6579348476616c34) := by
  decide +kernel

theorem encode_bigint :
    output (encode (.scalar 115792089237316195423570985008687907853269984665640564039457584007913129639936)) = some (bytesOf 34 0xa1010000000000000000000000000000000000000000000000000000000000000000) := by
  decide +kernel

-- End of material from `ethereum/tests`.

end EthLib.Serialization.Rlp
