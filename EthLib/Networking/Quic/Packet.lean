module

public import EthLib.Networking.Quic.Wire

/-!
# QUIC packet headers

RFC 9000 §17 defines the QUIC version 1 headers and the version-independent negotiation packet.

For protected packets, remove header protection (RFC 9001 §5.4) and authenticate the payload first.

In particular, reserved-bit errors must not be exposed before authentication (RFC 9000 §17.2).

Retry and Version Negotiation consume the rest of the datagram, since neither has a Length field.

The caller checks a long header's Length against the bytes that follow it (§12.2).
-/

@[expose] public section

namespace EthLib.Networking.Quic.Packet

open Wire

/-- The two-bit packet-number length, read as one through four bytes (§§17.2, 17.3.1). -/
abbrev PacketNumberLength := Fin 4

/-- The packet-number length bits of an unprotected first byte (§§17.2, 17.3.1). -/
def widthOfFirst (first : UInt8) : PacketNumberLength :=
  -- Packet Number Length: the bits with the mask 0x03 of byte 0.
  ⟨first.toNat % 4, Nat.mod_lt _ (by decide)⟩

/-- The number of bytes selected by the packet-number length bits. -/
def numberLength (width : PacketNumberLength) : Nat :=
  -- The length of the Packet Number field is the value of Packet Number Length plus one.
  width.val + 1

/-- Reasons a sender cannot select a packet-number width under RFC 9000 §17.1. -/
inductive WidthError where
  /-- The largest acknowledged number is not earlier than the number being sent. -/
  | acknowledgedNotEarlier (number largestAcked : Nat)
  /-- The full number or twice the acknowledged gap needs more than four bytes.

  The fields retain the full number and the optional largest acknowledged number. -/
  | rangeTooLarge (number : Nat) (largestAcked : Option Nat)
  deriving Repr, DecidableEq

/-- The stable local code of a width-selection failure, after those of the wire errors. -/
def WidthError.code : WidthError → UInt32
  | .acknowledgedNotEarlier .. => 10
  | .rangeTooLarge .. => 11

/-- Select the shortest packet-number width permitted by [RFC 9000 §17.1][encoding].

Any acknowledgement must be for this sender in the same connection and packet-number space.

An acknowledged number at or above the new number, or a range needing more than four bytes, fails.

The width meets the strict bound of §17.1, to which [verified erratum 9281][erratum] corrects A.2.

Before any acknowledgement, it can be shorter than the width of [Appendix A.2][sample].

[encoding]: https://www.rfc-editor.org/rfc/rfc9000#section-17.1
[erratum]: https://www.rfc-editor.org/errata/eid9281
[sample]: https://www.rfc-editor.org/rfc/rfc9000#appendix-A.2
-/
def packetNumberWidth (number : Varint) (largestAcked : Option Varint) :
    Except WidthError PacketNumberLength := do
  -- Not in §17.1: an acknowledged number at or above the number being sent fails.
  --
  -- The difference that §17.1 counts is then not positive.
  if let some ack := largestAcked then
    if number.val ≤ ack.val then throw (.acknowledgedNotEarlier number.val ack.val)
  let range := match largestAcked with
    -- §17.1: prior to receiving an acknowledgment, the full packet number MUST be included.
    --
    -- Appendix A.2 takes `num_unacked = full_pn + 1` here, and doubles it as below.
    --
    -- So A.2 may choose a longer field, while §17.1 asks only for the full number.
    --
    -- EthLib takes the §17.1 bound, and leaves headroom for reordering to the caller.
    | none => number.val
    -- §17.1: after an acknowledgment, a size able to represent more than twice the difference.
    --
    -- That difference is `num_unacked = full_pn - largest_acked` of Appendix A.2.
    | some ack => 2 * (number.val - ack.val)
  -- The fewest bytes `k` with the range below `256^k`: twice the difference, or the full number.
  --
  -- The field value is `k - 1`.
  --
  -- After an acknowledgment, that is `num_bytes = floor(min_bits / 8) + 1` of erratum 9281.
  if range < 256 then return 0
  else if range < 256 ^ 2 then return 1
  else if range < 256 ^ 3 then return 2
  else if range < 256 ^ 4 then return 3
  -- A Packet Number field has at most 4 bytes (§17.1).
  else throw (.rangeTooLarge number.val (largestAcked.map (·.val)))

/-- Keep the low packet-number bytes of the chosen width (§17.1).

The sender selects the width from the largest acknowledged number, if any. -/
def encodePacketNumberList (width : PacketNumberLength) (number : Varint) : List UInt8 :=
  -- §17.1: only the least significant bytes of the packet number, in network byte order.
  --
  -- Appendix A.2: `encode(full_pn, num_bytes)`, truncated to its least significant bytes.
  (Base.ByteOrder.toBE (numberLength width) number.val).toList

/-- Reconstruct a packet number using RFC 9000 Appendix A.3.

`expected` is one greater than the largest authenticated number, or zero before any packet arrives.

A result of `2^62` or more is rejected, which can happen only when the expected number is `2^62`.
-/
def decodePacketNumber (width : PacketNumberLength) (truncated : Nat) (expected : Nat) :
    Except Error Nat := do
  -- `pn_win = 1 << pn_nbits`, with 8 bits for each byte of the field.
  let window := 256 ^ numberLength width
  -- Not in Appendix A.3: the truncated number is below the window, else the call fails.
  --
  -- An expected number above `2^62` fails too, since it is one more than a packet number.
  if truncated ≥ window ∨ expected > 2 ^ 62 then
    throw (.packetNumber truncated (numberLength width) expected)
  -- `candidate_pn = (expected_pn & ~pn_mask) | truncated_pn`, with `pn_mask = pn_win - 1`.
  --
  -- The quotient form has its low bits 0, and `truncated_pn < pn_win`, so `|` is `+` here.
  let candidate := expected / window * window + truncated
  let result :=
    -- `candidate_pn <= expected_pn - pn_hwin and candidate_pn < (1 << 62) - pn_win`.
    --
    -- `pn_hwin = pn_win / 2` moves to the left side, so no natural number goes below zero.
    if candidate + window / 2 ≤ expected ∧ candidate < 2 ^ 62 - window then
      -- `return candidate_pn + pn_win`.
      candidate + window
    -- `candidate_pn > expected_pn + pn_hwin and candidate_pn >= pn_win`.
    else if candidate > expected + window / 2 ∧ candidate ≥ window then
      -- `return candidate_pn - pn_win`.
      candidate - window
    -- `return candidate_pn`.
    else candidate
  -- Not in Appendix A.3: a result of `2^62` or more is not a packet number (§12.3), and fails.
  if result < 2 ^ 62 then return result
  else throw (.packetNumber truncated (numberLength width) expected)

/-- Packet types that carry frames, RFC 9000 §12.4, Table 3. -/
inductive PacketType where
  | initial
  | zeroRtt
  | handshake
  | oneRtt
  deriving Repr, DecidableEq

/-- Headers through the packet-number field, or a whole Retry or Version Negotiation packet.

The encoder checks the bounds on connection IDs and byte strings, and the decoder checks each field.

The Length field of a long header counts the packet-number bytes and the encrypted payload (§17.2).

Version Negotiation permits connection IDs through 255 bytes, independently of version 1 (§17.2.1).
-/
inductive Header where
  | initial (destination source token : ByteArray) (width : PacketNumberLength)
      (length : Varint) (number : Nat)
  | zeroRtt (destination source : ByteArray) (width : PacketNumberLength)
      (length : Varint) (number : Nat)
  | handshake (destination source : ByteArray) (width : PacketNumberLength)
      (length : Varint) (number : Nat)
  | oneRtt (destination : ByteArray) (spin keyPhase : Bool)
      (width : PacketNumberLength) (number : Nat)
  | retry (destination source token : ByteArray) (tag : Vector UInt8 16) (unused : Fin 16)
  | versionNegotiation (destination source : ByteArray) (unused : Fin 128)
      (versions : List UInt32)
  deriving Repr, DecidableEq

/-- Conditions that prevent an encoder from truncating fields or emitting malformed headers. -/
def Header.Valid : Header → Prop
  | .initial d s t w l n => d.size ≤ 20 ∧ s.size ≤ 20 ∧ t.size < 2 ^ 62 ∧
      numberLength w ≤ l.val ∧ n < 256 ^ numberLength w
  | .zeroRtt d s w l n | .handshake d s w l n =>
      d.size ≤ 20 ∧ s.size ≤ 20 ∧ numberLength w ≤ l.val ∧
      n < 256 ^ numberLength w
  | .oneRtt d _ _ w n => d.size ≤ 20 ∧ n < 256 ^ numberLength w
  | .retry d s t _ _ => d.size ≤ 20 ∧ s.size ≤ 20 ∧ t ≠ ByteArray.empty
  | .versionNegotiation d s _ _ => d.size ≤ 255 ∧ s.size ≤ 255

instance (header : Header) : Decidable header.Valid := by
  cases header <;> unfold Header.Valid <;> infer_instance

/-- The version-independent connection-ID prefix of a long header (§17.2). -/
def longPrefixList (first : UInt8) (version : Nat) (destination source : ByteArray) :
    List UInt8 :=
  -- Figure 13: byte 0, Version (32), Destination Connection ID Length (8).
  [first] ++ (Base.ByteOrder.toBE 4 version).toList ++ [UInt8.ofNat destination.size] ++
    -- Destination Connection ID, Source Connection ID Length (8), Source Connection ID.
    destination.data.toList ++ [UInt8.ofNat source.size] ++ source.data.toList

/-- Encode a header after checking all field bounds (§§17.2–17.3).

The version 1 encoder sets the reserved bits to zero.
-/
def encodeList (header : Header) : Except Error (List UInt8) := do
  -- Each field meets its bound, so none is truncated on the wire.
  if ¬header.Valid then throw .packetLength
  match header with
  | .initial d s t w l n =>
    let tlen ← checkedVarint t.size
    -- Figure 15: Header Form 1, Fixed Bit 1, Long Packet Type 0 and Reserved Bits 0.
    --
    -- So byte 0 is 0xc0 plus the Packet Number Length, and the Version is 1.
    return longPrefixList (UInt8.ofNat (192 + w.val)) 1 d s ++
      -- Token Length (i), Token (..), Length (i), Packet Number (8..32).
      Varint.encodeList tlen ++ t.data.toList ++ Varint.encodeList l ++
        (Base.ByteOrder.toBE (numberLength w) n).toList
  | .zeroRtt d s w l n =>
    -- Figure 16: Long Packet Type 1, so byte 0 is 0xd0 plus the Packet Number Length.
    return longPrefixList (UInt8.ofNat (208 + w.val)) 1 d s ++
      -- Length (i), Packet Number (8..32).
      Varint.encodeList l ++ (Base.ByteOrder.toBE (numberLength w) n).toList
  | .handshake d s w l n =>
    -- Figure 17: Long Packet Type 2, so byte 0 is 0xe0 plus the Packet Number Length.
    return longPrefixList (UInt8.ofNat (224 + w.val)) 1 d s ++
      -- Length (i), Packet Number (8..32).
      Varint.encodeList l ++ (Base.ByteOrder.toBE (numberLength w) n).toList
  | .oneRtt d spin keyPhase w n =>
    -- Figure 19: Header Form 0, Fixed Bit 1 (0x40), Spin Bit (0x20) and Reserved Bits 0.
    --
    -- Then Key Phase (0x04), Packet Number Length (0x03), the connection ID and Packet Number.
    return [UInt8.ofNat (64 + (if spin then 32 else 0) +
      (if keyPhase then 4 else 0) + w.val)] ++ d.data.toList
        ++ (Base.ByteOrder.toBE (numberLength w) n).toList
  | .retry d s t tag unused =>
    -- Figure 18: Long Packet Type 3, so byte 0 is 0xf0 plus Unused (4).
    --
    -- Then Retry Token (..) and Retry Integrity Tag (128).
    return longPrefixList (UInt8.ofNat (240 + unused.val)) 1 d s ++ t.data.toList ++ tag.toList
  | .versionNegotiation d s unused versions =>
    -- Figure 14: Header Form 1, then Unused (7), which the caller chooses, and Version 0.
    --
    -- The caller may set the bit 0x40, which servers SHOULD set where QUIC might be multiplexed.
    return longPrefixList (UInt8.ofNat (128 + unused.val)) 0 d s ++
      -- Supported Version (32) ..., each in network byte order.
      versions.flatMap fun v => (Base.ByteOrder.toBE 4 v.toNat).toList

/-- Read a connection ID with its one-byte length (§17.2). -/
def connectionId (maximum : Nat) : Reader ByteArray := do
  -- Connection ID Length (8), an 8-bit unsigned integer.
  let n ← byte
  -- At most the bound of the version: in version 1, a length above 20 MUST drop the packet.
  require (n.toNat ≤ maximum) (.connectionIdLength n.toNat maximum)
  -- Then the Connection ID, of that many bytes.
  return (← bytes n.toNat).toByteArray

/-- Read the Length and truncated Packet Number fields (§17.2). -/
def lengthAndNumber (width : PacketNumberLength) : Reader (Varint × Nat) := do
  -- Length (i): the bytes of the Packet Number and Payload fields.
  let length ← varint
  -- Implied by §17.2, not stated there: the Length is at least that of the Packet Number.
  require (numberLength width ≤ length.val) .packetLength
  -- Packet Number (8..32): as many bytes as its length says, in network byte order.
  let number ← uint (numberLength width)
  return (length, number)

/-- Read the 32-bit versions of a Version Negotiation packet, zero or more (§17.2.1). -/
def versions : List UInt8 → Except Error (List UInt32)
  -- The list ends with the datagram.
  | [] => .ok []
  -- Supported Version (32): four bytes in network byte order, then the rest of the list.
  | a :: b :: c :: d :: rest => do
    let next ← versions rest
    return (UInt32.ofNat (Base.ByteOrder.ofBE [a, b, c, d])) :: next
  -- Fewer than four bytes left are not a version.
  | rest => .error (.truncated 4 rest.length)

/-- Decode one authenticated header, returning bytes after its packet-number field.

The short-header connection-ID length comes from the connection, not from the wire (§17.3.1).

Retry and Version Negotiation consume the remaining datagram.
-/
def decodeList (shortConnectionIdLength : Nat) : Reader Header := do
  -- Byte 0, with header protection removed.
  let first ← byte
  -- Packet Number Length, the bits 0x03, in the packet types that have it.
  let width := widthOfFirst first
  -- Header Form, the bit 0x80, is 0: a short header, the 1-RTT packet of §17.3.1.
  if first.toNat < 128 then
    -- Fixed Bit, 0x40, is 1, else the packet is not valid in this version and is discarded.
    require (first.toNat / 64 = 1) (.fixedBit first)
    -- Reserved Bits, mask 0x18, are 0 in an authenticated header.
    require (first.toNat / 8 % 4 = 0) (.reservedBits first)
    -- Destination Connection ID (0..160): at most 20 bytes, of a length the connection knows.
    require (shortConnectionIdLength ≤ 20) (.connectionIdLength shortConnectionIdLength 20)
    let destination := (← bytes shortConnectionIdLength).toByteArray
    -- Packet Number (8..32): as many bytes as its length says, in network byte order.
    let number ← uint (numberLength width)
    -- Spin Bit, 0x20, and Key Phase, 0x04.
    return .oneRtt destination (first.toNat / 32 % 2 = 1)
      (first.toNat / 4 % 2 = 1) width number
  -- Header Form is 1: a long header of §17.2.
  else
    -- Version (32).
    let version ← uint 4
    -- Version 1 bounds each connection ID by 20 bytes, and a packet with a longer one is dropped.
    --
    -- Other versions may have longer ones, up to 255, the most a length byte holds.
    let maximum := if version = 1 then 20 else 255
    -- The Destination, then the Source Connection ID, each after its length.
    let destination ← connectionId maximum
    let source ← connectionId maximum
    -- Version 0 is a Version Negotiation packet (§17.2.1).
    if version = 0 then
      -- Supported Version (32) ..., up to the end of the datagram, since it has no Length field.
      let rest ← remainder
      let vs ← StateT.lift (versions rest)
      -- Unused (7), which a client MUST ignore, is kept, unchecked.
      return .versionNegotiation destination source
        ⟨first.toNat % 128, Nat.mod_lt _ (by decide)⟩ vs
    else
      -- Only version 1 is read: the fields after the connection IDs are version-specific.
      require (version = 1) (.version version)
      -- Fixed Bit, 0x40, is 1, else the packet is not valid in this version and is discarded.
      require (first.toNat / 64 % 2 = 1) (.fixedBit first)
      -- Long Packet Type, mask 0x30, is 3: a Retry packet (§17.2.5).
      if first.toNat / 16 % 4 = 3 then
        let rest ← remainder
        -- Retry Token (..), then Retry Integrity Tag (128), up to the end of the datagram.
        --
        -- A client MUST discard a Retry packet with a zero-length Retry Token (§17.2.5.2).
        require (16 < rest.length) .packetLength
        let token := rest.take (rest.length - 16)
        let tag ← StateT.lift
          (Base.exactArray 16 (rest.drop (rest.length - 16)).toArray (.truncated 16))
        -- Unused (4), which a client MUST ignore, is kept, unchecked.
        return .retry destination source token.toByteArray tag
          ⟨first.toNat % 16, Nat.mod_lt _ (by decide)⟩
      else
        -- Reserved Bits, mask 0x0c, are 0 in an authenticated header.
        require (first.toNat / 4 % 4 = 0) (.reservedBits first)
        -- Long Packet Type 0: an Initial packet (§17.2.2).
        if first.toNat / 16 % 4 = 0 then
          -- Token Length (i), Token (..).
          let token ← blob
          -- Length (i), Packet Number (8..32).
          let (length, number) ← lengthAndNumber width
          return .initial destination source token.toByteArray width length number
        else
          -- Length (i), Packet Number (8..32).
          let (length, number) ← lengthAndNumber width
          -- Long Packet Type 1: a 0-RTT packet (§17.2.3).
          if first.toNat / 16 % 4 = 1 then
            return .zeroRtt destination source width length number
          -- Long Packet Type 2: a Handshake packet (§17.2.4).
          else return .handshake destination source width length number


/-- Keep the low packet-number bytes in their packed representation. -/
def encodePacketNumber (width : PacketNumberLength) (number : Varint) : ByteArray :=
  (encodePacketNumberList width number).toByteArray

/-- Encode a header as packed bytes without changing its wire format. -/
def encode (header : Header) : Except Error ByteArray :=
  (encodeList header).map List.toByteArray

/-- Read one authenticated header and preserve the packed trailing bytes. -/
def decode (shortConnectionIdLength : Nat) (input : ByteArray) :
    Except Error (Header × ByteArray) :=
  (decodeList shortConnectionIdLength input.data.toList).map fun (header, rest) =>
    (header, rest.toByteArray)

end EthLib.Networking.Quic.Packet
