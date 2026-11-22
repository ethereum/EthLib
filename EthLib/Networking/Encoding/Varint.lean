module

/-!
# `Networking.Encoding.Varint`

Unsigned protobuf varints, as the req/resp protocol of the consensus layer uses them.

A req/resp message starts with the length of its payload, written as a varint.

A varint splits a number into groups of seven bits, least significant group first.

Each group takes one byte.

The top bit of a byte is the continuation bit: it is set on every byte but the last.

For example, 300 has the groups `0x2c` and `0x02`, so its bytes are `0xac 0x02`.

The consensus layer sets three rules for the length prefix:

- It SHOULD be minimally encoded.
- It MUST NOT exceed 10 bytes.
- It MUST decode into a type that holds every `Uint64` value.

The byte format is Base 128 Varints of the protobuf encoding guide:
<https://github.com/protocolbuffers/protocolbuffers.github.io/blob/bc2f346991e20631ed0a884e345110738228bfae/content/programming-guides/encoding.md#base-128-varints-varints>
-/

@[expose] public section

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
  /-- A last byte was followed by `count` more bytes. -/
  | trailingBytes (count : Nat)
  /-- Ten bytes carry the continuation bit, and another byte follows. -/
  | tooLong
  /-- The encoding denotes `value`, which is 2^64 or more, outside the 64-bit range. -/
  | overflow (value : Nat)
  /-- The encoding of `length` bytes ends in a zero group that a shorter one would not need. -/
  | nonMinimal (length : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def VarintError.code : VarintError → UInt32
  | .unterminated => 1
  | .trailingBytes _ => 2
  | .tooLong => 3
  | .overflow _ => 4
  | .nonMinimal _ => 5

/-- The varint bytes of `n`, using at most `fuel` bytes.

# Why fuel

The recursion counts down a byte budget instead of shrinking `n`.

The kernel unfolds such a definition directly, so proofs can compute with it.

Encoding passes the ten-byte cap, which covers every 64-bit value.

So the budget never runs out on that path.
-/
def encodeAux : Nat → Nat → List UInt8
  -- Out of budget: write nothing.
  | _, 0 => []
  | n, fuel + 1 =>
      -- Base 128 Varints: if `n < 2^7`, one byte holds the 7-bit payload `n`, with its MSB clear.
      --
      -- The MSB is the continuation bit, so a clear MSB makes this the last byte.
      if n < groupSize then
        [UInt8.ofNat n]
      -- Otherwise the payload `n mod 2^7` comes first, with the MSB set, since a byte follows.
      --
      -- The payloads are in little-endian order, so the next bytes encode `floor(n / 2^7)`.
      else
        UInt8.ofNat (n % groupSize + continuation) :: encodeAux (n / groupSize) fuel

/-- A 64-bit value as an unsigned protobuf varint. -/
def encode (v : UInt64) : List UInt8 :=
  -- Base 128 Varints: an unsigned 64-bit integer takes one to ten bytes, so the budget suffices.
  encodeAux v.toNat maxLength

/-- The number that a list of varint bytes denotes, least significant group first. -/
def valueOf : List UInt8 → Nat
  | [] => 0
  -- Base 128 Varints: the MSB of each byte is dropped, as it only marks the end of the number.
  --
  -- The payloads are little-endian: `b_0 ... b_k` denotes the sum of `(b_i mod 2^7) * 2^(7 i)`.
  --
  -- That sum is the guide's reverse-and-concatenate of the payloads, written as arithmetic.
  --
  -- It is `(b_0 mod 2^7) + 2^7 * v`, for the value `v` of `b_1 ... b_k`.
  | b :: bs => b.toNat % groupSize + groupSize * valueOf bs

/-- The bytes of one varint that fills the whole input, read at most `fuel` bytes deep.

Succeeds when every byte but the last carries the continuation bit, and the last does not.

# Why a budget

Input comes from a peer and can be megabytes long.

Reading stops once the budget is spent, so the work is bounded by the cap, not by the input.

A long run of continuation bytes is rejected at byte eleven.
-/
def groups : Nat → List UInt8 → Except VarintError (List UInt8)
  -- The input ran out while the last MSB read said a byte follows, or before any byte.
  | _, [] => .error .unterminated
  -- At most ten bytes, the cap of the consensus layer, and ten bytes had their MSB set.
  | 0, _ :: _ => .error .tooLong
  | fuel + 1, b :: bs =>
      -- Base 128 Varints: a clear MSB says no byte of the varint follows.
      if b.toNat < continuation then
        -- The varint fills the whole input, so this byte must also end the input.
        match bs with
        | [] => .ok [b]
        | more@(_ :: _) => .error (.trailingBytes more.length)
      else
        -- A set MSB says the next byte is part of the varint, with one byte less of budget.
        (groups fuel bs).map (b :: ·)

/-- The bytes of a varint at the start of the input, and the bytes after them.

A varint ends at its first byte below `0x80`.

The prefix holds at most eleven bytes, so the decoder still sees an overlong prefix.
-/
def split (bs : List UInt8) : List UInt8 × List UInt8 :=
  -- The varint ends at the first byte with a clear MSB, searched among the first ten bytes.
  --
  -- With no such byte there, the prefix takes an eleventh byte, which decoding rejects as too long.
  --
  -- An input that ends first is the whole prefix, which decoding rejects as unterminated.
  let k := (bs.take maxLength).findIdx (·.toNat < continuation) + 1
  (bs.take k, bs.drop k)

/-- Whether a varint is longer than its value needs.

The shortest encoding never ends in a zero group.

Dropping that group would denote the same value.

A single byte is always minimal, the byte `0x00` included.
-/
def nonMinimal (gs : List UInt8) : Bool :=
  -- More than one byte, and the last payload is zero: the last byte is exactly `0x00`.
  1 < gs.length && gs.getLast? == some 0

/-- The 64-bit value a varint denotes, or why it is not a valid varint. -/
def decode (bs : List UInt8) : Except VarintError UInt64 :=
  -- The ten-byte cap is checked first, while reading, so the work stays bounded.
  match groups maxLength bs with
  | .error e => .error e
  | .ok gs =>
      -- Next, minimality: the consensus layer only says the length prefix SHOULD be minimal.
      --
      -- EthLib rejects padding anyway, so that each length has exactly one encoding.
      --
      -- So a message cannot be re-sent with a prefix that differs only in padding.
      if nonMinimal gs then
        .error (.nonMinimal gs.length)
      -- Last, the range: Base 128 Varints encodes unsigned 64-bit integers, below `2^64`.
      --
      -- The guide leaves a larger sum unspecified, and the consensus layer needs a 64-bit value.
      else if 2 ^ 64 ≤ valueOf gs then
        .error (.overflow (valueOf gs))
      else
        .ok (UInt64.ofNat (valueOf gs))

end EthLib.Networking.Encoding.Varint
