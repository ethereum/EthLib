module

public import EthLib.Networking.Enr.Base64
public import EthLib.Serialization.Rlp.Codec

/-!
# `Networking.Enr.Record`

Ethereum Node Records, from the sections "RLP Encoding" and "Text Encoding" of EIP-778.

Source: [EIP-778][eip-778].

A record is a signed list of key and value pairs that says how to reach a node.

It is the RLP list `[signature, seq, k1, v1, k2, v2, ...]`, at most 300 bytes long.

The keys are byte strings, sorted and unique.

Every record has the key `id`, which names its identity scheme.

All other keys are optional.

The EIP does not name the order, so the keys here increase in lexicographic byte order.

A value is any RLP item.

The text form is `enr:`, then the URL-safe base64 of the RLP bytes, without padding.

[eip-778]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-778.md
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Serialization.Rlp

/-- The largest size of an encoded record, in bytes. -/
def MAX_RECORD_SIZE : Nat := 300

/-- A node record: the signature, the sequence number and the key and value pairs.

The identity scheme defines the signature, so its size is not fixed here.

A node increases the sequence number when the record changes. -/
structure Enr where
  /-- The signature of the content, made by the identity scheme. -/
  signature : ByteArray
  /-- The sequence number, a 64-bit unsigned integer. -/
  seq : UInt64
  /-- The key and value pairs, in record order. -/
  pairs : List (ByteArray × Item)
  deriving DecidableEq

/-- Why a record was refused. -/
inductive EnrError where
  /-- The encoded record has `size` bytes, more than 300. -/
  | tooLarge (size : Nat)
  /-- The bytes are not the RLP encoding of one item. -/
  | rlp (e : RlpError)
  /-- The item is a byte string, not a list. -/
  | notAList
  /-- The list has no signature or no sequence number. -/
  | tooFewItems
  /-- The signature is a list, not a byte string. -/
  | signatureNotBytes
  /-- The sequence number is not an RLP scalar below `2^64`. -/
  | invalidSeq (e : RlpError)
  /-- A key is a list, not a byte string. -/
  | keyNotBytes
  /-- The last key has no value. -/
  | missingValue
  /-- A key follows a key equal to it. -/
  | repeatedKey (key : ByteArray)
  /-- A key follows a larger key. -/
  | unsortedKeys (key next : ByteArray)
  /-- The text does not start with `enr:`. -/
  | missingPrefix
  /-- The text after `enr:` is not base64. -/
  | base64 (e : Base64.Base64Error)
  /-- The record has no `id` pair, which names its identity scheme. -/
  | missingId
  /-- The identity scheme is not "v4". -/
  | unknownScheme
  /-- The `secp256k1` value is missing, or it is not a compressed point of the curve. -/
  | invalidPublicKey
  /-- The signature could not be made.

  This happens for the private key zero, and with negligible probability when no nonce is usable. -/
  | signing
  deriving DecidableEq

/-- The key `id`, in ASCII. -/
def KEY_ID : ByteArray := ⟨#[0x69, 0x64]⟩

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def EnrError.code : EnrError → UInt32
  | .tooLarge _ => 1
  | .rlp _ => 2
  | .notAList => 3
  | .tooFewItems => 4
  | .signatureNotBytes => 5
  | .invalidSeq _ => 6
  | .keyNotBytes => 7
  | .missingValue => 8
  | .repeatedKey _ => 9
  | .unsortedKeys .. => 10
  | .missingPrefix => 11
  | .base64 _ => 12
  | .missingId => 13
  | .unknownScheme => 14
  | .invalidPublicKey => 15
  | .signing => 16

/-- Whether the key `a` comes before the key `b`, in lexicographic byte order. -/
def keyLt (a b : ByteArray) : Prop := a.data.toList < b.data.toList

instance (a b : ByteArray) : Decidable (keyLt a b) :=
  inferInstanceAs (Decidable (a.data.toList < b.data.toList))

/-- The pairs as RLP items: each key, then its value. -/
def flatten : List (ByteArray × Item) → List Item
  | [] => []
  | (key, value) :: rest => .bytes key :: value :: flatten rest

/-- The content that the identity scheme signs: the RLP list `[seq, k1, v1, ...]`. -/
def Enr.content (r : Enr) : Item :=
  .list (Codec.toItem r.seq :: flatten r.pairs)

/-- The RLP encoding of a record, `[signature, seq, k1, v1, ...]`.

It does not check the size or the order of the keys. -/
def Enr.encode (r : Enr) : Except RlpError ByteArray :=
  Serialization.Rlp.encode (.list (.bytes r.signature :: Codec.toItem r.seq :: flatten r.pairs))

/-- The pairs of the items after the sequence number, two items each. -/
def readPairs : List Item → Except EnrError (List (ByteArray × Item))
  | [] => return []
  | .bytes key :: value :: rest => return (key, value) :: (← readPairs rest)
  | .list _ :: _ :: _ => throw .keyNotBytes
  | [_] => throw .missingValue

/-- Succeeds when each key comes before the next, so the keys are sorted and unique. -/
def checkKeys : List (ByteArray × Item) → Except EnrError Unit
  | p :: q :: rest =>
    if keyLt p.1 q.1 then checkKeys (q :: rest)
    else if p.1 = q.1 then throw (.repeatedKey q.1)
    else throw (.unsortedKeys p.1 q.1)
  | _ => return ()

/-- The record that `bytes` encodes.

It fails on more than 300 bytes, which the EIP says implementations should reject.

It fails on bytes that are not one RLP item, and on keys that do not strictly increase.

It fails on a record without the key `id`, the one key that the EIP requires.

It does not check the signature, which is the work of the identity scheme. -/
def decode (bytes : ByteArray) : Except EnrError Enr := do
  if MAX_RECORD_SIZE < bytes.size then throw (.tooLarge bytes.size)
  let item ← (Serialization.Rlp.decode bytes).mapError .rlp
  match item with
  | .list (.bytes signature :: seqItem :: rest) =>
    let seq ← (Codec.ofItem seqItem : Except RlpError UInt64).mapError .invalidSeq
    let pairs ← readPairs rest
    checkKeys pairs
    unless pairs.any (·.1 = KEY_ID) do throw .missingId
    return ⟨signature, seq, pairs⟩
  | .list (.list _ :: _ :: _) => throw .signatureNotBytes
  | .list _ => throw .tooFewItems
  | .bytes _ => throw .notAList

/-- The prefix of the text form, `enr:`. -/
def TEXT_PREFIX : List Char := ['e', 'n', 'r', ':']

/-- The text form of a record: `enr:`, then the base64 of its RLP encoding. -/
def Enr.toText (r : Enr) : Except RlpError String := do
  return String.ofList TEXT_PREFIX ++ Base64.encode (← r.encode)

/-- The record of a text form.

It fails unless the text is `enr:`, then the base64 of bytes that the decoder accepts. -/
def fromText (text : String) : Except EnrError Enr :=
  match text.toList with
  | 'e' :: 'n' :: 'r' :: ':' :: rest => do
    let bytes ← (Base64.decodeList rest).mapError .base64
    decode ⟨bytes.toArray⟩
  | _ => throw .missingPrefix

end EthLib.Networking.Enr
