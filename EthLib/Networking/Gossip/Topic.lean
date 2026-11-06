module

public import EthLib.Base.Hex

/-!
# `Networking.Gossip.Topic`

A gossip topic is the string `/eth2/D/N/ssz_snappy`.

`D` is the fork digest, four bytes in lowercase hex, with no `0x` prefix.

`N` is the name of the topic, and it contains no `/`.

`ssz_snappy` names the encoding of the messages, and it is the only encoding.

The topic of one subnet is named by a base name, `_` and the subnet ID in decimal.

The fork digest is an input here, since the consensus layer computes it.

Which names a fork uses is not part of this module.
-/

@[expose] public section

namespace EthLib.Networking.Gossip

/-- The number of a gossip subnet. -/
abbrev SubnetID := UInt64

/-- The characters of a fork digest: two lowercase hex digits per byte, high digit first. -/
def forkDigestChars (digest : Vector UInt8 4) : List Char :=
  digest.toList.flatMap Base.byteHexDigits

/-- The topic string of a fork digest and a name. -/
def topicString (digest : Vector UInt8 4) (name : String) : String :=
  "/eth2/" ++ String.ofList (forkDigestChars digest) ++ "/" ++ name ++ "/ssz_snappy"

/-- The name of the topic of one subnet.

The subnet ID is in decimal, with no leading zero. -/
def subnetTopicName (base : String) (subnetId : SubnetID) : String :=
  base ++ "_" ++ Nat.repr subnetId.toNat

/-- Every way a string can fail to be a topic. -/
inductive TopicError where
  /-- The string does not start with `/eth2/`. -/
  | notEth2
  /-- The fork digest is not eight lowercase hex digits followed by `/`. -/
  | forkDigest
  /-- The string does not end with `/ssz_snappy`. -/
  | encoding
  /-- The name contains `/`. -/
  | name
  deriving Repr, DecidableEq

/-- The rest of a list after a prefix, if the list starts with it. -/
def dropPrefix? (pre cs : List Char) : Option (List Char) :=
  if pre.isPrefixOf cs then some (cs.drop pre.length) else none

/-- The start of a list before a suffix, if the list ends with it. -/
def dropSuffix? (suf cs : List Char) : Option (List Char) :=
  if suf.isSuffixOf cs then some (cs.take (cs.length - suf.length)) else none

/-- The value of a lowercase hex digit. -/
def hexDigit? (c : Char) : Option Nat :=
  ((List.finRange 16).find? (Base.hexDigitChar · == c)).map Fin.val

/-- The byte that two lowercase hex digits write, high digit first. -/
def hexByte? (hi lo : Char) : Option UInt8 := do
  return UInt8.ofNat (16 * (← hexDigit? hi) + (← hexDigit? lo))

/-- The fork digest that eight lowercase hex digits write. -/
def parseForkDigest : List Char → Option (Vector UInt8 4)
  | [a, b, c, d, e, f, g, h] => do
    return #v[← hexByte? a b, ← hexByte? c d, ← hexByte? e f, ← hexByte? g h]
  | _ => none

/-- The fork digest and the name of a topic string. -/
def parseTopic (topic : String) : Except TopicError (Vector UInt8 4 × String) := do
  let some rest := dropPrefix? "/eth2/".toList topic.toList | throw .notEth2
  let some digest := parseForkDigest (rest.take 8) | throw .forkDigest
  let some body := dropPrefix? ['/'] (rest.drop 8) | throw .forkDigest
  let some name := dropSuffix? "/ssz_snappy".toList body | throw .encoding
  if '/' ∈ name then throw .name
  return (digest, String.ofList name)

/-- The subnet ID that a decimal string writes.

A number has one decimal form with no leading zero.

So the parser accepts a string only if printing its value gives the string back.

That rejects an empty string, a leading zero, a character that is not a digit, and 2^64 or more. -/
def parseSubnetId (digits : List Char) : Option SubnetID :=
  let value := digits.foldl (fun acc c => 10 * acc + (c.toNat - '0'.toNat)) 0
  if value < 2 ^ 64 ∧ Nat.toDigits 10 value = digits then some value.toUInt64 else none

/-- The subnet ID in the name of a subnet topic, given the base name the caller expects. -/
def parseSubnetTopicName (base name : String) : Option SubnetID :=
  (dropPrefix? (base ++ "_").toList name.toList).bind parseSubnetId

end EthLib.Networking.Gossip
