module

public import EthLib.Networking.Quic.Wire

/-!
# QUIC packet headers

RFC 9000 §17 defines the QUIC version 1 headers and the version-independent negotiation packet.

The decoder reads headers after both header and payload authentication.

In particular, reserved-bit errors must not be exposed before authentication (RFC 9000 §17.2).

Retry and Version Negotiation consume the whole packet, since neither has a Length field.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Packet

open Wire

/-- The two-bit packet-number length, interpreted as one through four bytes (§17.1). -/
abbrev PacketNumberLength := Fin 4

/-- The number of bytes selected by the packet-number length bits. -/
def numberLength (width : PacketNumberLength) : Nat := width.val + 1

/-- Encode the low packet-number bytes, as RFC 9000 §17.1 requires. -/
def encodePacketNumber (width : PacketNumberLength) (number : Varint) : List UInt8 :=
  Base.natToBytes (numberLength width) number.val

/-- Reconstruct a packet number using RFC 9000 Appendix A.3.

`expected` is one greater than the largest authenticated number, or zero before any packet arrives.

The addition form of the first comparison avoids natural-number subtraction below zero.
-/
def decodePacketNumber (width : PacketNumberLength) (truncated : Nat) (expected : Nat) :
    Except Error Nat := do
  let window := 256 ^ numberLength width
  if truncated ≥ window ∨ expected > 2 ^ 62 then throw .packetNumber
  let candidate := expected / window * window + truncated
  let result :=
    if candidate + window / 2 ≤ expected ∧ candidate < 2 ^ 62 - window then
      candidate + window
    else if candidate > expected + window / 2 ∧ candidate ≥ window then
      candidate - window
    else candidate
  if result < 2 ^ 62 then return result else throw .packetNumber

/-- Packet types that carry frames, RFC 9000 §12.4, Table 3. -/
inductive PacketType where
  | initial
  | zeroRtt
  | handshake
  | oneRtt
  deriving Repr, DecidableEq

/-- Headers through the packet-number field, or the whole unprotected special packet.

Connection IDs and variable byte strings are checked by `Header.Valid` at encoding and decoding.

A long header's `length` counts the packet-number bytes and the encrypted payload (§17.2).

Version Negotiation permits connection IDs through 255 bytes, independently of version 1 (§17.2.1).
-/
inductive Header where
  | initial (destination source token : List UInt8) (width : PacketNumberLength)
      (length : Varint) (number : Nat)
  | zeroRtt (destination source : List UInt8) (width : PacketNumberLength)
      (length : Varint) (number : Nat)
  | handshake (destination source : List UInt8) (width : PacketNumberLength)
      (length : Varint) (number : Nat)
  | oneRtt (destination : List UInt8) (spin keyPhase : Bool)
      (width : PacketNumberLength) (number : Nat)
  | retry (destination source token : List UInt8) (tag : Vector UInt8 16) (unused : Fin 16)
  | versionNegotiation (destination source : List UInt8) (unused : Fin 128)
      (versions : List UInt32)
  deriving Repr, DecidableEq

/-- Conditions that prevent an encoder from truncating fields or emitting malformed headers. -/
def Header.Valid : Header → Prop
  | .initial d s t w l n => d.length ≤ 20 ∧ s.length ≤ 20 ∧ t.length < 2 ^ 62 ∧
      numberLength w ≤ l.val ∧ n < 256 ^ numberLength w
  | .zeroRtt d s w l n | .handshake d s w l n =>
      d.length ≤ 20 ∧ s.length ≤ 20 ∧ numberLength w ≤ l.val ∧
      n < 256 ^ numberLength w
  | .oneRtt d _ _ w n => d.length ≤ 20 ∧ n < 256 ^ numberLength w
  | .retry d s t _ _ => d.length ≤ 20 ∧ s.length ≤ 20 ∧ t ≠ []
  | .versionNegotiation d s _ vs => d.length ≤ 255 ∧ s.length ≤ 255 ∧ vs ≠ []

instance (header : Header) : Decidable header.Valid := by
  cases header <;> unfold Header.Valid <;> infer_instance

/-- The version-independent connection-ID prefix of a long header (§17.2). -/
def longPrefix (first : UInt8) (version : Nat) (destination source : List UInt8) :
    List UInt8 :=
  [first] ++ Base.natToBytes 4 version ++ [UInt8.ofNat destination.length] ++
    destination ++ [UInt8.ofNat source.length] ++ source

/-- Encode a header after checking all field bounds (§§17.2–17.3).

The version 1 encoder sets the reserved bits to zero.
-/
def encode (header : Header) : Except Error (List UInt8) := do
  if ¬header.Valid then throw .packetLength
  match header with
  | .initial d s t w l n =>
    let tlen ← checkedVarint t.length
    return longPrefix (UInt8.ofNat (192 + w.val)) 1 d s ++
      Varint.encode tlen ++ t ++ Varint.encode l ++ Base.natToBytes (numberLength w) n
  | .zeroRtt d s w l n =>
    return longPrefix (UInt8.ofNat (208 + w.val)) 1 d s ++
      Varint.encode l ++ Base.natToBytes (numberLength w) n
  | .handshake d s w l n =>
    return longPrefix (UInt8.ofNat (224 + w.val)) 1 d s ++
      Varint.encode l ++ Base.natToBytes (numberLength w) n
  | .oneRtt d spin keyPhase w n =>
    return [UInt8.ofNat (64 + (if spin then 32 else 0) +
      (if keyPhase then 4 else 0) + w.val)] ++ d ++ Base.natToBytes (numberLength w) n
  | .retry d s t tag unused =>
    return longPrefix (UInt8.ofNat (240 + unused.val)) 1 d s ++ t ++ tag.toList
  | .versionNegotiation d s unused versions =>
    return longPrefix (UInt8.ofNat (128 + unused.val)) 0 d s ++
      versions.flatMap fun v => Base.natToBytes 4 v.toNat

/-- Read a connection ID with its one-byte length (§17.2). -/
def connectionId (maximum : Nat) : Reader (List UInt8) := do
  let n ← byte
  require (n.toNat ≤ maximum) .connectionIdLength
  bytes n.toNat

/-- Read the Length and truncated Packet Number fields (§17.2). -/
def lengthAndNumber (width : PacketNumberLength) : Reader (Varint × Nat) := do
  let length ← varint
  require (numberLength width ≤ length.val) .packetLength
  let number ← uint (numberLength width)
  return (length, number)

/-- Read a Version Negotiation packet's nonempty sequence of 32-bit versions (§17.2.1). -/
def versions : List UInt8 → Except Error (List UInt32)
  | [] => .ok []
  | a :: b :: c :: d :: rest => do
    let next ← versions rest
    return (UInt32.ofNat (Base.bytesToNat [a, b, c, d])) :: next
  | _ => .error .truncated

/-- Decode one authenticated header, returning bytes after its packet-number field.

The short-header connection-ID length comes from the connection, not from the wire (§17.3.1).

Retry and Version Negotiation consume the remaining datagram.
-/
def decode (shortConnectionIdLength : Nat) : Reader Header := do
  let first ← byte
  let width : PacketNumberLength := ⟨first.toNat % 4, Nat.mod_lt _ (by decide)⟩
  if first.toNat < 128 then
    require (first.toNat / 64 = 1) .fixedBit
    require (first.toNat / 8 % 4 = 0) .reservedBits
    require (shortConnectionIdLength ≤ 20) .connectionIdLength
    let destination ← bytes shortConnectionIdLength
    let number ← uint (numberLength width)
    return .oneRtt destination (first.toNat / 32 % 2 = 1)
      (first.toNat / 4 % 2 = 1) width number
  else
    let version ← uint 4
    let maximum := if version = 0 then 255 else 20
    let destination ← connectionId maximum
    let source ← connectionId maximum
    if version = 0 then
      let rest ← remainder
      let vs ← StateT.lift (versions rest)
      require (vs ≠ []) .packetLength
      return .versionNegotiation destination source
        ⟨first.toNat % 128, Nat.mod_lt _ (by decide)⟩ vs
    else
      require (version = 1) .version
      require (first.toNat / 64 % 2 = 1) .fixedBit
      if first.toNat / 16 % 4 = 3 then
        let rest ← remainder
        require (16 < rest.length) .packetLength
        let token := rest.take (rest.length - 16)
        let tag := rest.drop (rest.length - 16)
        if h : tag.length = 16 then
          return .retry destination source token
            ⟨tag.toArray, by simpa using h⟩
            ⟨first.toNat % 16, Nat.mod_lt _ (by decide)⟩
        else throw .truncated
      else
        require (first.toNat / 4 % 4 = 0) .reservedBits
        if first.toNat / 16 % 4 = 0 then
          let token ← blob
          let (length, number) ← lengthAndNumber width
          return .initial destination source token width length number
        else
          let (length, number) ← lengthAndNumber width
          if first.toNat / 16 % 4 = 1 then
            return .zeroRtt destination source width length number
          else return .handshake destination source width length number

end EthLib.Networking.Quic.Packet
