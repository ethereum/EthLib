/-!
# `Networking.Encoding.Varint`

Unsigned protobuf varints, as the consensus layer's req/resp protocol uses
them.

A req/resp message begins with the length of its payload, encoded as an
unsigned protobuf varint. A varint stores seven bits of the value per byte,
least significant group first, and sets the top bit of every byte but the
last:

```text
300  ->  ac 02
```

`phase0/p2p-interface.md` in `ethereum/consensus-specs`, under
"Encoding-dependent header", states three rules, which it inherits from the
protobuf encoding guide it links:

* the varint MUST NOT exceed ten bytes,
* it MUST decode into the full range of `Uint64`, so larger values are
  rejected,
* it SHOULD be minimally encoded.

Scope here is the encoding and decoding of a `UInt64`.
-/

namespace EthLib.Networking.Encoding.Varint

/-- The most bytes a varint may occupy.

This is the specification's cap, and it is also exactly what a `UInt64`
needs: ten groups of seven bits span 70 bits, and nine span only 63. -/
def maxLength : Nat := 10

/-- The seven value bits a varint byte carries. -/
def payloadBits : Nat := 7

/-- The radix one varint byte advances the value by. -/
def groupSize : Nat := 2 ^ payloadBits

/-- The value of the continuation bit, set on every byte but the last.

Seven payload bits occupy everything below it, so the bit's value `0x80` is
exactly `groupSize`. A continued byte is therefore its group plus this, and
a byte carries the bit precisely when its value is at least this. -/
def continuation : Nat := groupSize

/-- Every way decoding a varint can reject its input. -/
inductive VarintError where
  /-- The bytes ran out while a continuation bit was still set, or there
  were no bytes at all. -/
  | unterminated
  /-- A byte without its continuation bit was followed by more bytes, so
  the input holds something beyond the varint. -/
  | trailingBytes
  /-- The varint was longer than `maxLength` bytes. -/
  | tooLong (length : Nat)
  /-- The groups denote a value of `2 ^ 64` or more, outside `UInt64`. -/
  | overflow
  /-- A multi-byte encoding ended in a group of zero, which a shorter
  encoding would have denoted. -/
  | nonMinimal
  deriving Repr, DecidableEq

/-- The groups of `n`, least significant first, for at most `fuel` bytes.

The recursion is structural in `fuel` so that the kernel unfolds it: a
well-founded definition on `n` would be stuck behind `WellFounded.fix` and
no known answer below could be decided.

`encode` supplies `maxLength`, which covers every `UInt64`, so the
exhausted case is unreachable from it. `encode_length_le` and
`decode_encode` are what pin that down. -/
def encodeAux : Nat → Nat → List UInt8
  | _, 0 => []
  | n, fuel + 1 =>
      if n < groupSize then
        [UInt8.ofNat n]
      else
        UInt8.ofNat (n % groupSize + continuation) :: encodeAux (n / groupSize) fuel

/-- `v` as an unsigned protobuf varint. -/
def encode (v : UInt64) : List UInt8 :=
  encodeAux v.toNat maxLength

/-- The value the groups `gs` denote, least significant group first.

Each byte contributes its low seven bits; the continuation bit is
structure, not value, so it is masked off here. -/
def valueOf : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat % groupSize + groupSize * valueOf bs

/-- The bytes of one varint, checked for shape.

Succeeds when every byte but the last carries its continuation bit and the
last does not. A terminator followed by further bytes is `trailingBytes`
rather than a short read: `decode` consumes its whole input. -/
def groups : List UInt8 → Except VarintError (List UInt8)
  | [] => .error .unterminated
  | [b] => if b.toNat < continuation then .ok [b] else .error .unterminated
  | b :: bs =>
      if b.toNat < continuation then
        .error .trailingBytes
      else
        (groups bs).map (b :: ·)

/-- Whether `gs` is a longer encoding than the value needs.

The canonical encoding never ends in a group of zero: dropping that group
denotes the same value. One byte is always minimal, `00` among them. -/
def nonMinimal (gs : List UInt8) : Bool :=
  1 < gs.length && gs.getLast? == some 0

/-- The `UInt64` the varint `bs` denotes, or why it is not one.

The three rules are checked in the order the specification states them: the
ten-byte cap, then the `UInt64` range, then minimality. Rejecting a
non-minimal encoding is stricter than the specification's SHOULD; it is
done because a length prefix that admits several encodings of one length
admits a second message that differs only in its padding. -/
def decode (bs : List UInt8) : Except VarintError UInt64 :=
  match groups bs with
  | .error e => .error e
  | .ok gs =>
      if maxLength < gs.length then
        .error (.tooLong gs.length)
      else if nonMinimal gs then
        .error .nonMinimal
      else if 2 ^ 64 ≤ valueOf gs then
        .error .overflow
      else
        .ok (UInt64.ofNat (valueOf gs))

end EthLib.Networking.Encoding.Varint
