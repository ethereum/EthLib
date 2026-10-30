import EthLib.Cryptography.Hash.Crc32c

/-!
# Proofs: CRC-32C

CRC-32C agrees with the examples of RFC 3720 Appendix B.4, the remainder that §12.1 states, and the check value of the CRC catalogue.

The empty message gets the catalogue's CRC, 0.

The CRC catalogue is Greg Cook's [Catalogue of parametrised CRC algorithms](https://reveng.sourceforge.io/crc-catalogue/17plus.htm#crc.cat.crc-32-iscsi), last updated 11 December 2024.
-/

namespace EthLib.Cryptography.Hash.Crc32c

/-! ## The examples of RFC 3720 Appendix B.4

The appendix gives five messages and the digest word of each, as its bytes are stored.

RFC 7143 Appendix A.4 repeats them unchanged.

Each message is built as the appendix describes it, and each digest is copied byte for byte. -/

/-- 32 bytes of zeroes. -/
theorem digest_zeroes : digest ⟨Array.replicate 32 0x00⟩ = #v[0xaa, 0x36, 0x91, 0x8a] := by
  decide +kernel

/-- 32 bytes of ones, each `ff`. -/
theorem digest_ones : digest ⟨Array.replicate 32 0xff⟩ = #v[0x43, 0xab, 0xa8, 0x62] := by
  decide +kernel

/-- 32 bytes incrementing from `00` to `1f`. -/
theorem digest_incrementing :
    digest ⟨⟨(List.range 32).map Nat.toUInt8⟩⟩ = #v[0x4e, 0x79, 0xdd, 0x46] := by
  decide +kernel

/-- 32 bytes decrementing from `1f` to `00`. -/
theorem digest_decrementing :
    digest ⟨⟨(List.range 32).reverse.map Nat.toUInt8⟩⟩ = #v[0x5c, 0xdb, 0x3f, 0x11] := by
  decide +kernel

/-- The iSCSI SCSI Read (10) Command PDU of the appendix, four bytes per row as it prints them. -/
def scsiRead10 : ByteArray := ⟨#[
  0x01, 0xc0, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x14, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x04, 0x00,
  0x00, 0x00, 0x00, 0x14,
  0x00, 0x00, 0x00, 0x18,
  0x28, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x02, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00]⟩

/-- The 48 bytes of the SCSI Read (10) Command PDU. -/
theorem digest_scsiRead10 : digest scsiRead10 = #v[0x56, 0x3a, 0x96, 0xd9] := by
  decide +kernel

/-! ## The remainder of a message followed by its digest

The last bullet of RFC 3720 §12.1: a message extended with its digest always leaves the remainder `0x1c2d19ed`.

The RFC gives that value in its polynomial form, which is the form `remainder` returns.

The digest below is the one Appendix B.4 prints, so the statement does not go through `digest`. -/

/-- The SCSI Read (10) Command PDU, followed by its digest from Appendix B.4. -/
theorem remainder_scsiRead10_digest :
    remainder (scsiRead10 ++ ⟨#[0x56, 0x3a, 0x96, 0xd9]⟩) = 0x1c2d19ed := by
  decide +kernel

/-! ## The empty message

No coefficient enters the division, so `remainder` stays at `0xffffffff`, and the CRC, its complement, is 0.

The catalogue's CRC-32/ISCSI gives 0 as well, since its initial value and its final XOR are both `0xffffffff`. -/

/-- The empty message. -/
theorem crc32c_empty : crc32c ByteArray.empty = 0 := by
  decide +kernel

/-! ## The check value

A check value is the CRC of the nine ASCII bytes `123456789`.

The CRC-32/ISCSI entry of the CRC catalogue gives `0xe3069283`, a value RFC 3720 does not give. -/

/-- The nine ASCII bytes `123456789`. -/
theorem crc32c_check : crc32c "123456789".toUTF8 = 0xe3069283 := by
  decide +kernel

end EthLib.Cryptography.Hash.Crc32c
