import EthLib.Cryptography.Proofs.Hash.KeccakKernel

/-!
# Proofs: Keccak-256

Keccak-256 agrees with the Keccak team's reference values, and its digest is always 32 bytes.
-/

namespace EthLib.Cryptography.Hash.Keccak

/-! ## Keccak-256 known answers

All but `abc` come from the Keccak team's KAT files for Keccak[r = 1088, c = 512], with no suffix.

They are `ShortMsgKAT_256.txt` and `LongMsgKAT_256.txt`, in `KeccakKAT-3.zip` of the third round of the SHA-3 competition.

Those files list messages by their length in bits.

The cases below are the byte-aligned ones that reach every way a message can end against the 136-byte rate:

```text
    bytes   blocks   padding
      0       1      136 bytes, a whole block
      1       1      135 bytes
    135       1        1 byte, 0x81
    136       2      136 bytes, a whole second block
    137       2      135 bytes
    256       2       16 bytes
    319       3       89 bytes
```

Messages and digests are written in hex, as in the files, and read by the kernel.

Each check runs the sponge over the record form of Keccak-f, which is proved equal to the specification's. -/

/-- The value of one hex digit, upper or lower case. -/
def hexDigit (c : Char) : Nat :=
  -- '0' is 48, 'A' is 65 and 'a' is 97 in ASCII.
  if c.toNat < 58 then c.toNat - 48 else if c.toNat < 71 then c.toNat - 55 else c.toNat - 87

/-- The bytes a hex string spells, two digits per byte, the high digit first. -/
def hexBytes (s : String) : ByteArray :=
  ⟨(go s.toList).toArray⟩
where
  /-- Read the digits two at a time. -/
  go : List Char → List UInt8
    | hi :: lo :: rest => UInt8.ofNat (16 * hexDigit hi + hexDigit lo) :: go rest
    | _ => []

/-- `Len = 0` of `ShortMsgKAT_256.txt`: the empty message, padded to one whole block. -/
theorem keccak256_empty :
    (keccak256 ByteArray.empty).toArray
      = (hexBytes "C5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470").data := by
  rw [Kernel.keccak256_eq]
  decide +kernel

/-- The three ASCII bytes `abc`.

The Keccak team's files hold no such message, so this digest is not theirs.

Issue #64 asks for it, because SHA3-256 gives `abc` another digest. -/
theorem keccak256_abc :
    (keccak256 "abc".toUTF8).toArray
      = (hexBytes "4E03657AEA45A94FC7D47BA826C8D667C0D1E6E33A64A036EC44F58FA12D6C45").data := by
  rw [Kernel.keccak256_eq]
  decide +kernel

/-- `Len = 8` of `ShortMsgKAT_256.txt`: one byte, the smallest nonempty message. -/
theorem keccak256_len8 :
    (keccak256 (hexBytes "CC")).toArray
      = (hexBytes "EEAD6DBFC7340A56CAEDC044696A168870549A6A7F6F56961E84A54BD9970B8A").data := by
  rw [Kernel.keccak256_eq]
  decide +kernel

/-- `Len = 24` of `ShortMsgKAT_256.txt`: three bytes. -/
theorem keccak256_len24 :
    (keccak256 (hexBytes "1F877C")).toArray
      = (hexBytes "627D7BC1491B2AB127282827B8DE2D276B13D7D70FB4C5957FDF20655BC7AC30").data := by
  rw [Kernel.keccak256_eq]
  decide +kernel

/-- `Len = 1080` of `ShortMsgKAT_256.txt`: 135 bytes: one byte of padding, `0x81`. -/
theorem keccak256_len1080 :
    (keccak256 (hexBytes (
      "B771D5CEF5D1A41A93D15643D7181D2A2EF0A8E84D91812F20ED21F147BEF732" ++
      "BF3A60EF4067C3734B85BC8CD471780F10DC9E8291B58339A677B960218F71E7" ++
      "93F2797AEA349406512829065D37BB55EA796FA4F56FD8896B49B2CD19B43215" ++
      "AD967C712B24E5032D065232E02C127409D2ED4146B9D75D763D52DB98D949D3" ++
      "B0FED6A8052FBB"
    ))).toArray
      = (hexBytes "BD6F5492582A7C1B116304DE28314DF9FFFE95B0DA11AF52FE9440A717A34859").data := by
  rw [Kernel.keccak256_eq]
  decide +kernel

/-- `Len = 1088` of `ShortMsgKAT_256.txt`: 136 bytes: a whole block, so the padding is a second block. -/
theorem keccak256_len1088 :
    (keccak256 (hexBytes (
      "B32D95B0B9AAD2A8816DE6D06D1F86008505BD8C14124F6E9A163B5A2ADE55F8" ++
      "35D0EC3880EF50700D3B25E42CC0AF050CCD1BE5E555B23087E04D7BF9813622" ++
      "780C7313A1954F8740B6EE2D3F71F768DD417F520482BD3A08D4F222B4EE9DBD" ++
      "015447B33507DD50F3AB4247C5DE9A8ABD62A8DECEA01E3B87C8B927F5B08BEB" ++
      "37674C6F8E380C04"
    ))).toArray
      = (hexBytes "E717A7769448ABBE5FEF8187954A88AC56DED1D22E63940AB80D029585A21921").data := by
  rw [Kernel.keccak256_eq]
  decide +kernel

/-- `Len = 1096` of `ShortMsgKAT_256.txt`: 137 bytes: one byte into the second block. -/
theorem keccak256_len1096 :
    (keccak256 (hexBytes (
      "04410E31082A47584B406F051398A6ABE74E4DA59BB6F85E6B49E8A1F7F2CA00" ++
      "DFBA5462C2CD2BFDE8B64FB21D70C083F11318B56A52D03B81CAC5EEC29EB31B" ++
      "D0078B6156786DA3D6D8C33098C5C47BB67AC64DB14165AF65B44544D806DDE5" ++
      "F487D5373C7F9792C299E9686B7E5821E7C8E2458315B996B5677D926DAC57B3" ++
      "F22DA873C601016A0D"
    ))).toArray
      = (hexBytes "A95D50B50B4545F0947441DF74A1E9D74622EB3BAA49C1BBFC3A0CCE6619C1AA").data := by
  rw [Kernel.keccak256_eq]
  decide +kernel

/-- `Len = 2048` of `LongMsgKAT_256.txt`: 256 bytes: two blocks. -/
theorem keccak256_len2048 :
    (keccak256 (hexBytes (
      "724627916C50338643E6996F07877EAFD96BDF01DA7E991D4155B9BE1295EA7D" ++
      "21C9391F4C4A41C75F77E5D27389253393725F1427F57914B273AB862B9E31DA" ++
      "BCE506E558720520D33352D119F699E784F9E548FF91BC35CA14704212870982" ++
      "0D69A8287EA3257857615EB0321270E94B84F446942765CE882B191FAEE7E1C8" ++
      "7E0F0BD4E0CD8A927703524B559B769CA4ECE1F6DBF313FDCF67C572EC4185C1" ++
      "A88E86EC11B6454B371980020F19633B6B95BD280E4FBCB0161E1A82470320CE" ++
      "C6ECFA25AC73D09F1536F286D3F9DACAFB2CD1D0CE72D64D197F5C7520B3CCB2" ++
      "FD74EB72664BA93853EF41EABF52F015DD591500D018DD162815CC993595B195"
    ))).toArray
      = (hexBytes "EA0E416C0F7B4F11E3F00479FDDF954F2539E5E557753BD546F69EE375A5DE29").data := by
  rw [Kernel.keccak256_eq]
  decide +kernel

/-- `Len = 2552` of `LongMsgKAT_256.txt`: 319 bytes: three blocks. -/
theorem keccak256_len2552 :
    (keccak256 (hexBytes (
      "3139840B8AD4BCD39092916FD9D01798FF5AA1E48F34702C72DFE74B12E98A11" ++
      "4E318CDD2D47A9C320FFF908A8DBC2A5B1D87267C8E983829861A567558B37B2" ++
      "92D4575E200DE9F1DE45755FAFF9EFAE34964E4336C259F1E66599A7C904EC02" ++
      "539F1A8EAB8706E0B4F48F72FEC2794909EE4A7B092D6061C74481C9E21B9332" ++
      "DC7C6E482D7F9CC3210B38A6F88F7918C2D8C55E64A428CE2B68FD07AB572A8B" ++
      "0A2388664F99489F04EB54DF1376271810E0E7BCE396F52807710E0DEA94EB49" ++
      "F4B367271260C3456B9818FC7A72234E6BF2205FF6A36546205015EBD7D8C252" ++
      "7AA430F58E0E8AC97A7B6B793CD403D517D66295F37A34D0B7D2FA7BC345AC04" ++
      "CA1E266480DEEC39F5C88641C9DC0BD1358158FDECDD96685BBBB5C1FE5EA89D" ++
      "2CB4A9D5D12BB8C893281FF38E87D6B4841F0650092D447E013F20EA934E18"
    ))).toArray
      = (hexBytes "59E904B2AA0CCBF2A9D127446F113B7CC3D07B970E07A322325ECEE66AE0C9CA").data := by
  rw [Kernel.keccak256_eq]
  decide +kernel

/-! ## The digest length -/

/-- Every digest is 32 bytes, whatever the message. -/
theorem size_keccak256 (msg : ByteArray) : (keccak256 msg).toArray.size = DIGEST_LEN :=
  (keccak256 msg).size_toArray

end EthLib.Cryptography.Hash.Keccak
