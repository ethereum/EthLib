import EthLib.Serialization.Rlp.Decode
import EthLib.Serialization.Proofs.Rlp.Vectors

/-!
# `Serialization.Proofs.Rlp.Decode`

Known answers for the strict RLP decoding.

- Every case of `RLPTests/rlptest.json` decodes to its item.
- Every case of `RLPTests/invalidRLPTest.json` is rejected, with the error that names its fault.

`decide +kernel` has the kernel itself evaluate each claim.
-/

namespace EthLib.Serialization.Rlp

open Vectors

/-- The error of a failure, or `none` for a success. -/
private def errorOf (result : Except RlpError Item) : Option RlpError :=
  match result with
  | .error e => some e
  | .ok _ => none

/-! ## The cases of `ethereum/tests`

The cases come from `RLPTests/rlptest.json` and `RLPTests/invalidRLPTest.json` in `ethereum/tests`, at commit `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`, in each file's order.

Each claim is named after its case.

An input of `rlptest.json` is read as `Proofs/Rlp/Encode` reads it, and its output is the input here.

`invalidRLPTest.json` gives each case as hex bytes and marks it invalid.

The expected error is the fault that the name of the case describes:

- `bytesShouldBeSingleByte`: a byte below `0x80` written with a prefix.
- `nonOptimalLongLength` and `wrongSizeList`: a length below 56 written in the long form.
- `leadingZerosInLongLength` and `incorrectLengthInArray`: a length with a leading zero byte.
- `lessThan`, `int32Overflow` and `emptyEncoding`: an input that ends before the bytes its prefix announces.

`randomRLP` is a list, inside which a byte string writes its length with a leading zero byte.

The cases between the two markers are material from `ethereum/tests`, by the Ethereum Foundation.

They keep its licence, the MIT License, under this notice:

```text
Copyright 2014-2025 Ethereum Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
-/

-- Start of material from `ethereum/tests` (`RLPTests/rlptest.json` and `RLPTests/invalidRLPTest.json`), by the Ethereum Foundation, under the MIT License.

theorem decode_emptystring :
    (decode (byteArrayOf 1 0x80)).toOption = some (str "") := by
  decide +kernel

theorem decode_bytestring00 :
    (decode (byteArrayOf 1 0x00)).toOption = some (str "\u0000") := by
  decide +kernel

theorem decode_bytestring01 :
    (decode (byteArrayOf 1 0x01)).toOption = some (str "\u0001") := by
  decide +kernel

theorem decode_bytestring7F :
    (decode (byteArrayOf 1 0x7f)).toOption = some (str "\u007F") := by
  decide +kernel

theorem decode_shortstring :
    (decode (byteArrayOf 4 0x83646f67)).toOption = some (str "dog") := by
  decide +kernel

theorem decode_shortstring2 :
    (decode (byteArrayOf 56 0xb74c6f72656d20697073756d20646f6c6f722073697420616d65742c20636f6e7365637465747572206164697069736963696e6720656c69)).toOption = some (str "Lorem ipsum dolor sit amet, consectetur adipisicing eli") := by
  decide +kernel

theorem decode_longstring :
    (decode (byteArrayOf 58 0xb8384c6f72656d20697073756d20646f6c6f722073697420616d65742c20636f6e7365637465747572206164697069736963696e6720656c6974)).toOption = some (str "Lorem ipsum dolor sit amet, consectetur adipisicing elit") := by
  decide +kernel

theorem decode_longstring2 :
    (decode (byteArrayOf 1027 0xb904004c6f72656d20697073756d20646f6c6f722073697420616d65742c20636f6e73656374657475722061646970697363696e6720656c69742e20437572616269747572206d6175726973206d61676e612c20737573636970697420736564207665686963756c61206e6f6e2c20696163756c697320666175636962757320746f72746f722e2050726f696e20737573636970697420756c74726963696573206d616c6573756164612e204475697320746f72746f7220656c69742c2064696374756d2071756973207472697374697175652065752c20756c7472696365732061742072697375732e204d6f72626920612065737420696d70657264696574206d6920756c6c616d636f7270657220616c6971756574207375736369706974206e6563206c6f72656d2e2041656e65616e2071756973206c656f206d6f6c6c69732c2076756c70757461746520656c6974207661726975732c20636f6e73657175617420656e696d2e204e756c6c6120756c74726963657320747572706973206a7573746f2c20657420706f73756572652075726e6120636f6e7365637465747572206e65632e2050726f696e206e6f6e20636f6e76616c6c6973206d657475732e20446f6e65632074656d706f7220697073756d20696e206d617572697320636f6e67756520736f6c6c696369747564696e2e20566573746962756c756d20616e746520697073756d207072696d697320696e206661756369627573206f726369206c756374757320657420756c74726963657320706f737565726520637562696c69612043757261653b2053757370656e646973736520636f6e76616c6c69732073656d2076656c206d617373612066617563696275732c2065676574206c6163696e6961206c616375732074656d706f722e204e756c6c61207175697320756c747269636965732070757275732e2050726f696e20617563746f722072686f6e637573206e69626820636f6e64696d656e74756d206d6f6c6c69732e20416c697175616d20636f6e73657175617420656e696d206174206d65747573206c75637475732c206120656c656966656e6420707572757320656765737461732e20437572616269747572206174206e696268206d657475732e204e616d20626962656e64756d2c206e6571756520617420617563746f72207472697374697175652c206c6f72656d206c696265726f20616c697175657420617263752c206e6f6e20696e74657264756d2074656c6c7573206c65637475732073697420616d65742065726f732e20437261732072686f6e6375732c206d65747573206163206f726e617265206375727375732c20646f6c6f72206a7573746f20756c747269636573206d657475732c20617420756c6c616d636f7270657220766f6c7574706174)).toOption = some (strPieces [
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
      "dolor justo ultrices metus, at ullamcorper volutpat"]) := by
  decide +kernel

theorem decode_zero :
    (decode (byteArrayOf 1 0x80)).toOption = some (.scalar 0) := by
  decide +kernel

theorem decode_smallint :
    (decode (byteArrayOf 1 0x01)).toOption = some (.scalar 1) := by
  decide +kernel

theorem decode_smallint2 :
    (decode (byteArrayOf 1 0x10)).toOption = some (.scalar 16) := by
  decide +kernel

theorem decode_smallint3 :
    (decode (byteArrayOf 1 0x4f)).toOption = some (.scalar 79) := by
  decide +kernel

theorem decode_smallint4 :
    (decode (byteArrayOf 1 0x7f)).toOption = some (.scalar 127) := by
  decide +kernel

theorem decode_mediumint1 :
    (decode (byteArrayOf 2 0x8180)).toOption = some (.scalar 128) := by
  decide +kernel

theorem decode_mediumint2 :
    (decode (byteArrayOf 3 0x8203e8)).toOption = some (.scalar 1000) := by
  decide +kernel

theorem decode_mediumint3 :
    (decode (byteArrayOf 4 0x830186a0)).toOption = some (.scalar 100000) := by
  decide +kernel

theorem decode_mediumint4 :
    (decode (byteArrayOf 16 0x8f102030405060708090a0b0c0d0e0f2)).toOption = some (.scalar 83729609699884896815286331701780722) := by
  decide +kernel

theorem decode_mediumint5 :
    (decode (byteArrayOf 29 0x9c0100020003000400050006000700080009000a000b000c000d000e01)).toOption = some (.scalar 105315505618206987246253880190783558935785933862974822347068935681) := by
  decide +kernel

theorem decode_emptylist :
    (decode (byteArrayOf 1 0xc0)).toOption = some (.list []) := by
  decide +kernel

theorem decode_stringlist :
    (decode (byteArrayOf 13 0xcc83646f6783676f6483636174)).toOption = some (.list [str "dog", str "god", str "cat"]) := by
  decide +kernel

theorem decode_multilist :
    (decode (byteArrayOf 7 0xc6827a77c10401)).toOption = some (.list [str "zw", .list [.scalar 4], .scalar 1]) := by
  decide +kernel

theorem decode_shortListMax1 :
    (decode (byteArrayOf 56 0xf784617364668471776572847a78637684617364668471776572847a78637684617364668471776572847a78637684617364668471776572)).toOption = some (.list [str "asdf", str "qwer", str "zxcv", str "asdf", str "qwer", str "zxcv", str "asdf", str "qwer", str "zxcv", str "asdf", str "qwer"]) := by
  decide +kernel

theorem decode_longList1 :
    (decode (byteArrayOf 66 0xf840cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376)).toOption = some (.list (List.replicate 4 (.list [str "asdf", str "qwer", str "zxcv"]))) := by
  decide +kernel

theorem decode_longList2 :
    (decode (byteArrayOf 515 0xf90200cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376cf84617364668471776572847a786376)).toOption = some (.list (List.replicate 32 (.list [str "asdf", str "qwer", str "zxcv"]))) := by
  decide +kernel

theorem decode_listsoflists :
    (decode (byteArrayOf 5 0xc4c2c0c0c0)).toOption = some (.list [.list [.list [], .list []], .list []]) := by
  decide +kernel

theorem decode_listsoflists2 :
    (decode (byteArrayOf 8 0xc7c0c1c0c3c0c1c0)).toOption = some (.list [.list [], .list [.list []], .list [.list [], .list [.list []]]]) := by
  decide +kernel

theorem decode_dictTest1 :
    (decode (byteArrayOf 45 0xecca846b6579318476616c31ca846b6579328476616c32ca846b6579338476616c33ca846b6579348476616c34)).toOption = some (.list [.list [str "key1", str "val1"], .list [str "key2", str "val2"], .list [str "key3", str "val3"], .list [str "key4", str "val4"]]) := by
  decide +kernel

theorem decode_bigint :
    (decode (byteArrayOf 34 0xa1010000000000000000000000000000000000000000000000000000000000000000)).toOption = some (.scalar 115792089237316195423570985008687907853269984665640564039457584007913129639936) := by
  decide +kernel

theorem decode_int32Overflow :
    errorOf (decode (byteArrayOf 11 0xbf0f000000000000021111)) = some (.inputTooShort 1080863910568919042 2) := by
  decide +kernel

theorem decode_int32Overflow2 :
    errorOf (decode (byteArrayOf 11 0xff0f000000000000021111)) = some (.inputTooShort 1080863910568919042 2) := by
  decide +kernel

theorem decode_wrongSizeList :
    errorOf (decode (byteArrayOf 3 0xf80180)) = some (.longFormForShortLength 1) := by
  decide +kernel

theorem decode_wrongSizeList2 :
    errorOf (decode (byteArrayOf 3 0xf80100)) = some (.longFormForShortLength 1) := by
  decide +kernel

theorem decode_incorrectLengthInArray :
    errorOf (decode (byteArrayOf 36 0xb9002100dc2b275d0f74e8a53e6f4ec61b27f24278820be3f82ea2110e582081b0565df0)) = some .leadingZeroInLength := by
  decide +kernel

theorem decode_randomRLP :
    errorOf (decode (byteArrayOf 99 0xf861f83eb9002100dc2b275d0f74e8a53e6f4ec61b27f24278820be3f82ea2110e582081b0565df027b90015002d5ef8325ae4d034df55d4b58d0dfba64d61ddd17be00000b9001a00dae30907045a2f66fa36f2bb8aa9029cbb0b8a7b3b5c435ab331)) = some .leadingZeroInLength := by
  decide +kernel

theorem decode_bytesShouldBeSingleByte00 :
    errorOf (decode (byteArrayOf 2 0x8100)) = some (.singleByteWithPrefix 0) := by
  decide +kernel

theorem decode_bytesShouldBeSingleByte01 :
    errorOf (decode (byteArrayOf 2 0x8101)) = some (.singleByteWithPrefix 1) := by
  decide +kernel

theorem decode_bytesShouldBeSingleByte7F :
    errorOf (decode (byteArrayOf 2 0x817f)) = some (.singleByteWithPrefix 127) := by
  decide +kernel

theorem decode_leadingZerosInLongLengthArray1 :
    errorOf (decode (byteArrayOf 67 0xb90040000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f)) = some .leadingZeroInLength := by
  decide +kernel

theorem decode_leadingZerosInLongLengthArray2 :
    errorOf (decode (byteArrayOf 2 0xb800)) = some .leadingZeroInLength := by
  decide +kernel

theorem decode_leadingZerosInLongLengthList1 :
    errorOf (decode (byteArrayOf 69 0xfb00000040000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f)) = some .leadingZeroInLength := by
  decide +kernel

theorem decode_leadingZerosInLongLengthList2 :
    errorOf (decode (byteArrayOf 2 0xf800)) = some .leadingZeroInLength := by
  decide +kernel

theorem decode_nonOptimalLongLengthArray1 :
    errorOf (decode (byteArrayOf 18 0xb81000112233445566778899aabbccddeeff)) = some (.longFormForShortLength 16) := by
  decide +kernel

theorem decode_nonOptimalLongLengthArray2 :
    errorOf (decode (byteArrayOf 3 0xb801ff)) = some (.longFormForShortLength 1) := by
  decide +kernel

theorem decode_nonOptimalLongLengthList1 :
    errorOf (decode (byteArrayOf 18 0xf810000102030405060708090a0b0c0d0e0f)) = some (.longFormForShortLength 16) := by
  decide +kernel

theorem decode_nonOptimalLongLengthList2 :
    errorOf (decode (byteArrayOf 5 0xf803112233)) = some (.longFormForShortLength 3) := by
  decide +kernel

theorem decode_emptyEncoding :
    errorOf (decode .empty) = some (.inputTooShort 1 0) := by
  decide +kernel

theorem decode_lessThanShortLengthArray1 :
    errorOf (decode (byteArrayOf 1 0x81)) = some (.inputTooShort 1 0) := by
  decide +kernel

theorem decode_lessThanShortLengthArray2 :
    errorOf (decode (byteArrayOf 32 0xa0000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e)) = some (.inputTooShort 32 31) := by
  decide +kernel

theorem decode_lessThanShortLengthList1 :
    errorOf (decode (byteArrayOf 4 0xc5010203)) = some (.inputTooShort 5 3) := by
  decide +kernel

theorem decode_lessThanShortLengthList2 :
    errorOf (decode (byteArrayOf 8 0xe201020304050607)) = some (.inputTooShort 34 7) := by
  decide +kernel

theorem decode_lessThanLongLengthArray1 :
    errorOf (decode (byteArrayOf 10 0xba010000aabbccddeeff)) = some (.inputTooShort 65536 6) := by
  decide +kernel

theorem decode_lessThanLongLengthArray2 :
    errorOf (decode (byteArrayOf 18 0xb840ffeeddccbbaa99887766554433221100)) = some (.inputTooShort 64 16) := by
  decide +kernel

theorem decode_lessThanLongLengthList1 :
    errorOf (decode (byteArrayOf 3 0xf90180)) = some (.inputTooShort 384 0) := by
  decide +kernel

theorem decode_lessThanLongLengthList2 :
    errorOf (decode (byteArrayOf 17 0xffffffffffffffffff0001020304050607)) = some (.inputTooShort 18446744073709551615 8) := by
  decide +kernel

-- End of material from `ethereum/tests`.

end EthLib.Serialization.Rlp
