module

public import EthLib.Base.Bytes
public import EthLib.Base.Hex

/-!
# `Consensus.BuilderApi.AuthData`

From Gloas, a proposer signs data that it agreed with a builder in each request to it.

By default that data is the host of the builder's URL, lowercased and ASCII.

An IPv6 host is compressed and in brackets, so each of its spellings gives the same bytes.

The rule is in the [validator document], and the compressed form in [RFC 5952] section 4.

The URL is read by a part of the grammar of [RFC 3986] section 3, which SOUNDNESS.md lists.

[validator document]: https://github.com/ethereum/builder-specs/blob/ea92eff73ad77c33d3b59a2033ffa02dfae5ee05/specs/gloas/validator.md#default-auth-data
[RFC 5952]: https://www.rfc-editor.org/rfc/rfc5952#section-4
[RFC 3986]: https://www.rfc-editor.org/rfc/rfc3986#section-3
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

/-- Why a URL gives no default data. -/
inductive AuthDataError where
  /-- The URL does not start with a scheme, a colon and two slashes. -/
  | noAuthority
  /-- The host is empty. -/
  | noHost
  /-- The text after the host is neither empty nor a colon followed by decimal digits. -/
  | badPort
  /-- A host that opens a bracket is not an IPv6 address followed by a closing bracket. -/
  | badIpv6
  /-- The host holds a character that is not ASCII. -/
  | nonAscii
  /-- The host holds an ASCII character that a registered name may not hold. -/
  | badName
  deriving DecidableEq, Repr

/-- Stable error codes for the bindings. -/
def AuthDataError.code : AuthDataError → UInt32
  | .noAuthority => 1
  | .noHost => 2
  | .badPort => 3
  | .badIpv6 => 4
  | .nonAscii => 5
  | .badName => 6

/-! ## IPv6 text -/

/-- A group of one to four hexadecimal digits, by RFC 4291 section 2.2. -/
def parseHexGroup (cs : List Char) : Option UInt16 :=
  -- Each x is one to four hexadecimal digits of a 16-bit piece.
  if cs = [] ∨ 4 < cs.length then none
  else (cs.foldlM (fun acc c => (acc * 16 + ·.toNat) <$> Base.hexValue? c) 0).map Nat.toUInt16

/-- A decimal number from 0 to 255 without a leading zero, by RFC 3986 section 3.2.2. -/
def parseDecOctet (cs : List Char) : Option Nat :=
  -- dec-octet = DIGIT / %x31-39 DIGIT / "1" 2DIGIT / "2" %x30-34 DIGIT / "25" %x30-35.
  --
  -- EthLib reads the same set as one to three digits without a leading zero, at most 255.
  if cs = [] ∨ 3 < cs.length ∨ (1 < cs.length ∧ cs.head? = some '0') then none
  else if cs.all Char.isDigit then
    let value := cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    if value ≤ 255 then some value else none
  else none

/-- An IPv4 address in dotted decimal, as the two groups that it fills. -/
def parseIpv4Groups (cs : List Char) : Option (List UInt16) :=
  -- IPv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet.
  match cs.splitOn '.' with
  | [a, b, c, d] => do
    let a ← parseDecOctet a
    let b ← parseDecOctet b
    let c ← parseDecOctet c
    let d ← parseDecOctet d
    -- RFC 4291 section 2.2, form 3: the four 8-bit pieces fill the two low-order 16-bit pieces.
    return [(a * 256 + b).toUInt16, (c * 256 + d).toUInt16]
  | _ => none

/-- A field between colons, which may be an IPv4 address when it ends the address. -/
def parseField (last : Bool) (cs : List Char) : Option (List UInt16) :=
  -- Only the last field may be d.d.d.d, in the form x:x:x:x:x:x:d.d.d.d of RFC 4291.
  if last ∧ '.' ∈ cs then parseIpv4Groups cs else (fun group => [group]) <$> parseHexGroup cs

/-- The groups of fields between colons, the last of which may be an IPv4 address. -/
def parseFields (ipv4Tail : Bool) : List (List Char) → Option (List UInt16)
  | [] => some []
  | [field] => parseField ipv4Tail field
  | field :: fields => do
    let group ← parseHexGroup field
    return group :: (← parseFields ipv4Tail fields)

/-- The groups of a text of fields between colons; the empty text has none. -/
def parseGroups (ipv4Tail : Bool) (cs : List Char) : Option (List UInt16) :=
  if cs = [] then some [] else parseFields ipv4Tail (cs.splitOn ':')

/-- The text before and after the first double colon, if any. -/
def splitDoubleColon : List Char → Option (List Char × List Char)
  | ':' :: ':' :: rest => some ([], rest)
  | c :: rest => (fun (left, right) => (c :: left, right)) <$> splitDoubleColon rest
  | [] => none

/-- The eight groups of an IPv6 address, from text without brackets.

The text follows RFC 4291 section 2.2: hexadecimal groups and at most one double colon.

The last two groups may be written as an IPv4 address. -/
def parseIpv6 (text : String) : Except AuthDataError (Vector UInt16 8) :=
  let groups : Option (List UInt16) :=
    match splitDoubleColon text.toList with
    -- The `::` stands for one or more groups of 16 bits of zeros, and appears at most once.
    | some (left, right) => do
      -- An IPv4 address can only end the address, so only the right part may hold one.
      let left ← parseGroups false left
      let right ← parseGroups true right
      -- At most seven groups around the `::`, since it stands for at least one.
      if left.length + right.length ≤ 7 then
        return left ++ List.replicate (8 - (left.length + right.length)) 0 ++ right
      else none
    -- Without `::`, the text writes every group.
    | none => parseGroups true text.toList
  match groups with
  -- Exactly eight groups of 16 bits, so 128 bits.
  | some groups => Base.exactArray 8 groups.toArray fun _ => .badIpv6
  | none => .error .badIpv6

/-- A group in lowercase hexadecimal, without leading zeros, by RFC 5952 sections 4.1 and 4.3. -/
def hexGroup (group : UInt16) : List Char := Nat.toDigits 16 group.toNat

/-- Groups in hexadecimal, separated by colons. -/
def joinGroups (groups : List UInt16) : List Char := [':'].intercalate (groups.map hexGroup)

/-- The start and the length of the first longest run of two or more zero groups, if any. -/
def zeroRun (groups : List UInt16) : Option (Nat × Nat) :=
  (List.range groups.length).foldl (fun best start =>
    let length := ((groups.drop start).takeWhile (· = 0)).length
    -- RFC 5952 section 4.2.2: a single zero group is no run.
    --
    -- Section 4.2.3: the longest run, and the first of runs of equal length.
    if 2 ≤ length ∧ best.all (·.2 < length) then some (start, length) else best) none

/-- The compressed text of an IPv6 address, by RFC 5952 section 4.

An IPv4 tail is written as two groups, as the validator document requires.

So the form departs from RFC 5952 section 5, which writes such a tail in dotted decimal. -/
def compressIpv6 (address : Vector UInt16 8) : String :=
  let groups := address.toList
  String.ofList <| match zeroRun groups with
    -- RFC 5952 section 4.2.2: without a run of two or more zero groups, no `::`.
    | none => joinGroups groups
    -- Sections 4.2.1 and 4.2.3: the whole of the first longest run becomes `::`.
    | some (start, length) =>
      joinGroups (groups.take start) ++ [':', ':'] ++ joinGroups (groups.drop (start + length))

/-! ## The host of a URL -/

/-- The host of a URL: a name or an IPv4 address in text, or an IPv6 address. -/
inductive UrlHost where
  /-- A host that is not in brackets, lowercased. -/
  | name (text : String)
  /-- A host in brackets, as the IPv6 address that it names. -/
  | ipv6 (address : Vector UInt16 8)
  deriving DecidableEq, Repr

/-- Whether a character may follow the first letter of a scheme, by RFC 3986 section 3.1. -/
def isSchemeChar (c : Char) : Bool :=
  c.isAlphanum || c = '+' || c = '-' || c = '.'

/-- The text after the scheme and the two slashes of a URL. -/
def afterScheme (cs : List Char) : Option (List Char) :=
  match cs.span (· ≠ ':') with
  -- RFC 3986 section 3.1: scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." ), then `://`.
  | (c :: scheme, ':' :: '/' :: '/' :: rest) =>
    if c.isAlpha && scheme.all isSchemeChar then some rest else none
  | _ => none

/-- Whether a character may be in a registered name, by RFC 3986 section 3.2.2.

These are the unreserved characters and the sub-delimiters, without percent-encoding.

A character that is not ASCII is allowed here, and refused later as such. -/
def isNameChar (c : Char) : Bool :=
  -- unreserved = ALPHA / DIGIT / "-" / "." / "_" / "~".
  --
  -- sub-delims = "!" / "$" / "&" / "'" / "(" / ")" / "*" / "+" / "," / ";" / "=".
  128 ≤ c.toNat || c.isAlphanum || "-._~!$&'()*+,;=".toList.contains c

/-- Whether a port is absent, or a colon and decimal digits, by RFC 3986 section 3.2.3. -/
def isPort : List Char → Bool
  | [] => true
  -- port = *DIGIT, after the colon of the authority.
  | ':' :: digits => digits.all Char.isDigit
  | _ => false

/-- The host of a URL, without its userinfo and port. -/
def urlHost (url : String) : Except AuthDataError UrlHost := do
  -- RFC 3986 section 3: a scheme, then two slashes and an authority.
  let some rest := afterScheme url.toList | throw .noAuthority
  -- Section 3.2: the authority ends at the first `/`, `?` or `#`.
  let authority := rest.takeWhile fun c => c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#'
  -- authority = [ userinfo "@" ] host [ ":" port ], and a host holds no `@`.
  --
  -- So the userinfo ends at the last `@`, and the default data drops it.
  let hostPort := (authority.reverse.takeWhile (· ≠ '@')).reverse
  match hostPort with
  -- Section 3.2.2: IP-literal = "[" ( IPv6address / IPvFuture ) "]".
  --
  -- EthLib reads an IPv6 address only.
  | '[' :: bracketed =>
    match bracketed.span (· ≠ ']') with
    | (inside, ']' :: port) =>
      unless isPort port do throw .badPort
      return .ipv6 (← parseIpv6 (String.ofList inside))
    | _ => throw .badIpv6
  -- A registered name or an IPv4 address, up to the colon of the port.
  | _ =>
    let (host, port) := hostPort.span (· ≠ ':')
    unless isPort port do throw .badPort
    -- The default data needs a host.
    if host = [] then throw .noHost
    -- reg-name = *( unreserved / pct-encoded / sub-delims ), here without percent-encoding.
    unless host.all isNameChar do throw .badName
    -- The validator document: the host, lowercased.
    return .name (String.ofList (host.map Char.toLower))

/-- The bytes of ASCII characters. -/
def asciiBytes (cs : List Char) : ByteArray := ⟨(cs.map fun c => c.toNat.toUInt8).toArray⟩

/-- The default data that a proposer and a builder agree, from the builder's URL.

It is the host as ASCII bytes, with an IPv6 address compressed and in brackets.

A host that is not ASCII gives an error, so an internationalized name must be in punycode. -/
def defaultAuthData (url : String) : Except AuthDataError ByteArray := do
  let text := match ← urlHost url with
    -- A name or an IPv4 address, as it is written.
    | .name text => text.toList
    -- An IPv6 literal in its compressed form, inside brackets.
    | .ipv6 address => '[' :: (compressIpv6 address).toList ++ [']']
  -- The host is ASCII, so an internationalized name must be given in punycode.
  unless text.all (·.toNat < 128) do throw .nonAscii
  -- The ASCII encoding of the host.
  return asciiBytes text

end EthLib.Consensus.BuilderApi
