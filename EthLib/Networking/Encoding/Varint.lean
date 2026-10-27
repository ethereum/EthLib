/-!
# `Networking.Encoding.Varint`

Unsigned protobuf varints, as the req/resp protocol of the consensus layer uses them.

A req/resp message starts with the length of its payload, written as a varint.

A varint splits a number into groups of seven bits, least significant group first.

Each group takes one byte.

The top bit of a byte is the continuation bit: it is set on every byte but the last.

```text
    300 = 0b10_0101100

    group 0 = 0101100 = 0x2c   ->  byte 0x2c | 0x80 = 0xac   (more bytes follow)
    group 1 = 0000010 = 0x02   ->  byte 0x02                 (last byte)

    300  ->  [ 0xac, 0x02 ]
```

The specification is `phase0/p2p-interface.md` in `ethereum/consensus-specs`, under "Encoding-dependent header".

It states three rules for the length prefix:

- It SHOULD be minimally encoded.
- It MUST NOT exceed 10 bytes.
- It MUST decode into a type that holds every `Uint64` value.

The byte format itself is the "Base 128 Varints" section of the protobuf encoding guide that the specification links.
-/

namespace EthLib.Networking.Encoding.Varint

/-- The most bytes a varint may occupy.

The specification sets this cap.

It is also exactly what a 64-bit value needs.

Ten groups of seven bits hold 70 bits, while nine hold only 63.
-/
def maxLength : Nat := 10

/-- The number of value bits in one varint byte. -/
def payloadBits : Nat := 7

/-- The radix of a varint: each byte is worth 2^7 = 128 times the byte before it. -/
def groupSize : Nat := 2 ^ payloadBits

/-- The value of the continuation bit, `0x80`.

The seven value bits sit below it, so `0x80` equals the radix.

So a continued byte is its group plus 128.

A byte carries the bit exactly when its value is at least 128.
-/
def continuation : Nat := groupSize

/-- Every way decoding a varint can reject its input. -/
inductive VarintError where
  /-- The input ended while a continuation bit was still set, or the input was empty. -/
  | unterminated
  /-- A last byte was followed by more bytes. -/
  | trailingBytes
  /-- More than ten bytes carry the continuation bit. -/
  | tooLong
  /-- The value is 2^64 or more, outside the 64-bit range. -/
  | overflow
  /-- The encoding ends in a zero group that a shorter encoding would not need. -/
  | nonMinimal
  deriving Repr, DecidableEq

/-- The varint bytes of `n`, using at most `fuel` bytes.

# Why fuel

The recursion counts down a byte budget instead of shrinking `n`.

The kernel unfolds such a definition directly, so every known answer is checked by `rfl`.

Encoding passes the ten-byte cap, which covers every 64-bit value.

So the budget never runs out on that path.
-/
def encodeAux : Nat → Nat → List UInt8
  -- Out of budget: write nothing.
  | _, 0 => []
  | n, fuel + 1 =>
      -- The value fits in one group: this is the last byte.
      if n < groupSize then
        [UInt8.ofNat n]
      -- Otherwise write the low group with the continuation bit, then the rest.
      else
        UInt8.ofNat (n % groupSize + continuation) :: encodeAux (n / groupSize) fuel

/-- A 64-bit value as an unsigned protobuf varint. -/
def encode (v : UInt64) : List UInt8 :=
  encodeAux v.toNat maxLength

/-- The number that a list of varint bytes denotes, least significant group first.

Each byte contributes its low seven bits.

The continuation bit marks structure, not value, so it is dropped.

```text
    [ b_0, b_1, ..., b_k ]  ->  (b_0 mod 128) + 128 * ((b_1 mod 128) + 128 * (...))
```
-/
def valueOf : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat % groupSize + groupSize * valueOf bs

/-- The bytes of one varint that fills the whole input, read at most `fuel` bytes deep.

Succeeds when every byte but the last carries the continuation bit, and the last does not.

# Why a budget

Input comes from a peer and can be megabytes long.

Reading stops once the budget is spent, so the work is bounded by the cap, not by the input.

A long run of continuation bytes is rejected at byte eleven.
-/
def groups : Nat → List UInt8 → Except VarintError (List UInt8)
  -- The input ran out before a last byte.
  | _, [] => .error .unterminated
  -- Every allowed byte carried the continuation bit, and more bytes follow.
  | 0, _ :: _ => .error .tooLong
  | fuel + 1, b :: bs =>
      if b.toNat < continuation then
        -- A last byte must also be the last byte of the input.
        match bs with
        | [] => .ok [b]
        | _ :: _ => .error .trailingBytes
      else
        -- A continued byte: keep it, and read the rest with one byte less of budget.
        (groups fuel bs).map (b :: ·)

/-- Whether a varint is longer than its value needs.

The shortest encoding never ends in a zero group.

Dropping that group would denote the same value.

A single byte is always minimal, the byte `0x00` included.
-/
def nonMinimal (gs : List UInt8) : Bool :=
  1 < gs.length && gs.getLast? == some 0

/-- The 64-bit value a varint denotes, or why it is not a valid varint.

The rules are checked in this order:

1. The ten-byte cap, while reading, so the work stays bounded.
2. Minimal encoding.
3. The 64-bit range.

# Why minimality is enforced

The specification only says SHOULD.

Rejecting padding means each length has exactly one encoding.

So a message cannot be re-sent with a different prefix that differs only in padding.
-/
def decode (bs : List UInt8) : Except VarintError UInt64 :=
  match groups maxLength bs with
  | .error e => .error e
  | .ok gs =>
      if nonMinimal gs then
        .error .nonMinimal
      else if 2 ^ 64 ≤ valueOf gs then
        .error .overflow
      else
        .ok (UInt64.ofNat (valueOf gs))

end EthLib.Networking.Encoding.Varint
