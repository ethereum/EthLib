module

public import EthLib.Networking.Encoding.Base32
public import EthLib.Networking.Enr.V4
public import EthLib.Networking.Rlpx.Handshake

/-!
# `Networking.DnsDisc`

The node lists of [EIP-1459], published as DNS TXT records, from its maintained text [dnsdisc].

A list is a Merkle tree of entries, each the text of one TXT record.

- The root, `enrtree-root:v1 e=<enr-root> l=<link-root> seq=<seq> sig=<signature>`.
- A branch, `enrtree-branch:<h1>,<h2>,...`, the hashes of the entries below it.
- A link to another list, `enrtree://<key>@<domain>`, which is also the URL of a list.
- A node record, `enr:<record>`, in the text form of EIP-778.

A client verifies the root, then walks the tree and checks each entry against its hash.

An entry other than the root sits at the subdomain named by the hash of its text.

That hash is "the base32 encoding of the (abbreviated) keccak256 hash of its text content".

The source does not say how much is kept, so the hash is the first 16 bytes, as in its examples.

So a hash name has 26 characters of the base32 of RFC 4648 §6, without padding.

The key of a URL is the base32 of the 33 bytes of a compressed secp256k1 public key.

The root signs the Keccak-256 hash of its text before ` sig=`, with 65 bytes `r || s || v`.

The signature is in the URL-safe base64 of RFC 4648 §5, without padding.

The sequence number is a decimal integer, written here with no leading zero.

Each text has one value, and each value one text.

A signature with `n - s` and the other recovery id verifies too: the source has no low-s rule.

[EIP-1459]: https://eips.ethereum.org/EIPS/eip-1459
[dnsdisc]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/dnsdisc.md#L20-L102
-/

@[expose] public section

namespace EthLib.Networking.DnsDisc

open EthLib.Base
open EthLib.Networking.Encoding
open EthLib.Cryptography.Secp256k1

/-- The number of bytes of the hash that names an entry. -/
def HASH_SIZE : Nat := 16

/-- The number of characters of a hash name: the base32 of 16 bytes. -/
def HASH_TEXT_SIZE : Nat := 26

/-- The number of characters of a key: the base32 of a compressed public key of 33 bytes. -/
def KEY_TEXT_SIZE : Nat := 53

/-- The number of characters of a signature: the base64 of 65 bytes. -/
def SIGNATURE_TEXT_SIZE : Nat := 87

/-- Why a text is not an entry of a node list. -/
inductive DnsError where
  /-- The text starts with none of the prefixes of an entry. -/
  | unknownEntry
  /-- The root text does not have its fields `e=`, `l=`, `seq=` and `sig=`, in that order. -/
  | rootFields
  /-- The sequence number is not a decimal integer with no leading zero. -/
  | seq
  /-- A hash, a key or a signature is not base32 or base64 of the right size. -/
  | encoding
  /-- The hashes of a branch are not separated by commas. -/
  | branchHashes
  /-- A link has no `@` after its key. -/
  | linkFields
  /-- The key of a link is not a point of the curve. -/
  | publicKey
  /-- The record of an `enr:` entry is refused. -/
  | enr (e : Enr.EnrError)
  /-- The root could not be signed. -/
  | signing
  /-- No TXT record was found at a name. -/
  | missing (name : String)
  /-- The text at the name of a hash does not have that hash. -/
  | hashMismatch (name : String)
  /-- A link sits under the records, a record under the links, or a root inside a subtree. -/
  | wrongSubtree (name : String)
  /-- The text at the domain of the list is not a root. -/
  | notRoot
  /-- The root is not signed by the key of the list. -/
  | badSignature
  /-- The sequence number of the root is below the one seen last. -/
  | staleSeq (seq seen : Nat)
  /-- The walk took more hashes than its budget. -/
  | tooManyEntries
  /-- The node record at a name does not verify under its own "v4" key. -/
  | badRecord (name : String)
  deriving DecidableEq

/-- The stable code of an error, one per constructor, for the C exports. -/
def DnsError.code : DnsError → UInt32
  | .unknownEntry => 1
  | .rootFields => 2
  | .seq => 3
  | .encoding => 4
  | .branchHashes => 5
  | .linkFields => 6
  | .publicKey => 7
  | .enr _ => 8
  | .signing => 9
  | .missing _ => 10
  | .hashMismatch _ => 11
  | .wrongSubtree _ => 12
  | .notRoot => 13
  | .badSignature => 14
  | .staleSeq .. => 15
  | .tooManyEntries => 16
  | .badRecord _ => 17

/-- The hash that names an entry: the first 16 bytes of a Keccak-256 hash. -/
abbrev Hash := Vector UInt8 HASH_SIZE

/-- The rest of a list of characters after a prefix, if it starts with the prefix. -/
def dropPrefix : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | p :: ps, c :: cs => if p = c then dropPrefix ps cs else none
  | _ :: _, [] => none

/-- The base32 name of a hash. -/
def Hash.toText (h : Hash) : List Char :=
  Base32.encodeList h.toList

/-- The hash of a base32 name of 16 bytes. -/
def Hash.ofText (cs : List Char) : Except DnsError Hash := do
  let bytes ← (Base32.decodeList 0 cs).mapError fun _ => .encoding
  exactBytes HASH_SIZE ⟨bytes.toArray⟩ fun _ => .encoding

/-- The hash that names an entry: the first 16 bytes of the Keccak-256 hash of its text. -/
def hashOf (text : String) : Hash :=
  let digest := Cryptography.Hash.Keccak.keccak256 text.toUTF8
  Vector.ofFn fun i => digest[i.val]

/-- The subdomain at which an entry sits: the name of the hash of its text, 26 characters. -/
def subdomain (text : String) : String :=
  String.ofList (hashOf text).toText

/-! ## The root -/

/-- The root of a node list: the two subtrees, the sequence number and the signature. -/
structure Root where
  /-- The hash of the root entry of the subtree of node records. -/
  enrRoot : Hash
  /-- The hash of the root entry of the subtree of links. -/
  linkRoot : Hash
  /-- The sequence number, which grows when the list changes. -/
  seq : Nat
  /-- The signature `r || s || v` of the text before ` sig=`. -/
  signature : Vector UInt8 65
  deriving DecidableEq

/-- The prefix of a root, up to its first hash. -/
def ROOT_PREFIX : List Char := "enrtree-root:v1 e=".toList

/-- The text that a root signs: everything before ` sig=`. -/
def signedText (enrRoot linkRoot : Hash) (seq : Nat) : List Char :=
  ROOT_PREFIX ++ enrRoot.toText ++ " l=".toList ++ linkRoot.toText ++ " seq=".toList ++
    (Nat.repr seq).toList

/-- The text of a root. -/
def Root.toText (r : Root) : List Char :=
  signedText r.enrRoot r.linkRoot r.seq ++ " sig=".toList ++
    Base64.encodeList r.signature.toList

/-- The sequence number of a decimal text with no leading zero and no separator.

Any other text, such as one with a sign, a space or a letter, is rejected. -/
def seqOf (cs : List Char) : Except DnsError Nat :=
  let n := Nat.ofDigitChars 10 cs 0
  if (Nat.repr n).toList = cs then return n else throw .seq

/-- The signature of a base64 text of 65 bytes. -/
def signatureOf (cs : List Char) : Except DnsError (Vector UInt8 65) := do
  let bytes ← (Base64.decodeList 0 cs).mapError fun _ => .encoding
  exactBytes 65 ⟨bytes.toArray⟩ fun _ => .encoding

/-- The root in the text after its prefix.

The hashes have 26 characters and the signature 87, so the sequence number is what lies between. -/
def Root.parseFields (rest : List Char) : Except DnsError Root := do
  let enrRoot ← Hash.ofText (rest.take HASH_TEXT_SIZE)
  let some rest := dropPrefix " l=".toList (rest.drop HASH_TEXT_SIZE) | throw .rootFields
  let linkRoot ← Hash.ofText (rest.take HASH_TEXT_SIZE)
  let some rest := dropPrefix " seq=".toList (rest.drop HASH_TEXT_SIZE) | throw .rootFields
  let tail := rest.length - (5 + SIGNATURE_TEXT_SIZE)
  let some sig := dropPrefix " sig=".toList (rest.drop tail) | throw .rootFields
  return ⟨enrRoot, linkRoot, ← seqOf (rest.take tail), ← signatureOf sig⟩

/-- The Keccak-256 hash that a root signs. -/
def signingHash (enrRoot linkRoot : Hash) (seq : Nat) : Vector UInt8 32 :=
  Cryptography.Hash.Keccak.keccak256 (String.ofList (signedText enrRoot linkRoot seq)).toUTF8

/-- Whether a root is signed by a public key, given as its 33 compressed bytes.

The signature must recover a public key from the hash of the signed text, and that key. -/
def Root.verify (key : Vector UInt8 33) (r : Root) : Bool :=
  match Rlpx.recoverSigner (signingHash r.enrRoot r.linkRoot r.seq) r.signature with
  | .ok q => q.encodeCompressed == ⟨key.toArray⟩
  | .error _ => false

/-- The root of two subtrees and a sequence number, signed with a private key.

The nonce is that of RFC 6979, and `s` is low. -/
def Root.sign (sk : Fn) (enrRoot linkRoot : Hash) (seq : Nat) : Except DnsError Root := do
  let sig ← (Ecdsa.sign sk (signingHash enrRoot linkRoot seq)).mapError fun _ => .signing
  return ⟨enrRoot, linkRoot, seq, Rlpx.signatureBytes sig⟩

/-! ## Links and URLs -/

/-- A node list: the public key that signs it, and the domain where it is published. -/
structure Url where
  /-- The compressed public key, 33 bytes. -/
  key : Vector UInt8 33
  /-- The domain of the root of the list.

  It is not checked as a DNS name, and it may be empty. -/
  domain : String
  deriving DecidableEq

/-- The prefix of a URL and of a link entry. -/
def URL_PREFIX : List Char := "enrtree://".toList

/-- The text of a URL, which is also the text of a link entry. -/
def Url.toText (u : Url) : List Char :=
  URL_PREFIX ++ Base32.encodeList u.key.toList ++ '@' :: u.domain.toList

/-- The URL in the text after its prefix.

The key has 53 characters, then comes `@`, and the domain is the rest. -/
def Url.parseFields (rest : List Char) : Except DnsError Url := do
  let bytes ← (Base32.decodeList 0 (rest.take KEY_TEXT_SIZE)).mapError fun _ => .encoding
  let key ← exactBytes 33 ⟨bytes.toArray⟩ fun _ => .encoding
  unless (Point.decode ⟨key.toArray⟩).toBool do throw .publicKey
  let '@' :: domain := rest.drop KEY_TEXT_SIZE | throw .linkFields
  return ⟨key, String.ofList domain⟩

/-! ## Branches -/

/-- The prefix of a branch. -/
def BRANCH_PREFIX : List Char := "enrtree-branch:".toList

/-- The hashes of a branch, separated by commas. -/
def hashesText : List Hash → List Char
  | [] => []
  | [h] => h.toText
  | h :: rest => h.toText ++ ',' :: hashesText rest

/-- The hashes of a non-empty text, each 26 characters, separated by commas. -/
def hashesOf (cs : List Char) : Except DnsError (List Hash) := do
  let h ← Hash.ofText (cs.take HASH_TEXT_SIZE)
  match hrest : cs.drop HASH_TEXT_SIZE with
  | [] => return [h]
  | ',' :: rest =>
    have : rest.length < cs.length := by
      have := congrArg List.length hrest
      simp only [List.length_drop, List.length_cons] at this
      omega
    return h :: (← hashesOf rest)
  | _ => throw .branchHashes
termination_by cs.length

/-- The hashes of a branch, in the text after its prefix; an empty text has none. -/
def branchOf (rest : List Char) : Except DnsError (List Hash) :=
  if rest = [] then return [] else hashesOf rest

/-! ## Entries -/

/-- An entry of a node list. -/
inductive Entry where
  /-- The root of the list. -/
  | root (r : Root)
  /-- A branch, with the hashes of the entries below it. -/
  | branch (hashes : List Hash)
  /-- A link to another list. -/
  | link (url : Url)
  /-- A node record. -/
  | enr (record : Enr.Enr)

/-- The text of an entry.

It fails only for a record that has no RLP encoding. -/
def Entry.toText : Entry → Except DnsError String
  | .root r => return String.ofList r.toText
  | .branch hashes => return String.ofList (BRANCH_PREFIX ++ hashesText hashes)
  | .link url => return String.ofList url.toText
  | .enr record => record.toText.mapError (.enr ∘ .rlp)

/-- The entry of a text, by its prefix. -/
def Entry.parse (text : String) : Except DnsError Entry :=
  match dropPrefix ROOT_PREFIX text.toList with
  | some rest => .root <$> Root.parseFields rest
  | none =>
    match dropPrefix BRANCH_PREFIX text.toList with
    | some rest => .branch <$> branchOf rest
    | none =>
      match dropPrefix URL_PREFIX text.toList with
      | some rest => .link <$> Url.parseFields rest
      | none =>
        match dropPrefix Enr.TEXT_PREFIX text.toList with
        | some _ => .enr <$> (Enr.fromText text).mapError .enr
        | none => throw .unknownEntry

/-- The URL of a text. -/
def Url.parse (text : String) : Except DnsError Url :=
  match dropPrefix URL_PREFIX text.toList with
  | some rest => Url.parseFields rest
  | none => throw .unknownEntry

/-! ## Resolving a list -/

/-- The subtree that an entry belongs to: the node records, or the links. -/
inductive Subtree where
  /-- The subtree under the root of node records. -/
  | records
  /-- The subtree under the root of links. -/
  | links
  deriving DecidableEq

/-- What a walk of a list has found so far: its node records and its links, in order. -/
structure Found where
  /-- The node records. -/
  records : List Enr.Enr
  /-- The links to other lists. -/
  links : List Url

/-- The name at which the entry of a hash sits, under the domain of the list. -/
def nameOf (hash : Hash) (domain : String) : String :=
  String.ofList hash.toText ++ "." ++ domain

/-- The walk of the subtrees of a list, with the hashes still to read and those already read.

The lookup is the DNS: any function from a name to the text of its TXT record.

Each text must have the hash of its name, so a resolver cannot change it unseen.

A link may sit only under the root of links, and a record only under the root of records.

A record must verify under its own key, as the client must "verify the node record".

A hash met again is skipped, as the client "must track hashes ... already resolved".

The budget bounds the number of hashes taken, since a lookup can make a tree without end. -/
def walk (lookup : String → Option String) (domain : String) :
    Nat → List (Subtree × Hash) → List Hash → Found → Except DnsError Found
  | _, [], _, found => return found
  | 0, _ :: _, _, _ => throw .tooManyEntries
  | budget + 1, (tree, hash) :: pending, visited, found =>
    if hash ∈ visited then walk lookup domain budget pending visited found
    else do
      let name := nameOf hash domain
      let some text := lookup name | throw (.missing name)
      unless hashOf text = hash do throw (.hashMismatch name)
      match tree, ← Entry.parse text with
      | _, .branch hashes =>
        walk lookup domain budget (hashes.map (tree, ·) ++ pending) (hash :: visited) found
      | .records, .enr record =>
        -- The client must "decode, verify the node record".
        unless Enr.verifyV4 record do throw (.badRecord name)
        walk lookup domain budget pending (hash :: visited)
          { found with records := found.records ++ [record] }
      | .links, .link url =>
        walk lookup domain budget pending (hash :: visited)
          { found with links := found.links ++ [url] }
      | _, _ => throw (.wrongSubtree name)

/-- The node list at a domain, under a known key: its sequence number, records and links.

The root must be signed by the key, and its sequence number at least the one seen last.

Then the walk reads both subtrees, within the budget. -/
def resolve (lookup : String → Option String) (key : Vector UInt8 33) (seenSeq : Nat)
    (domain : String) (budget : Nat) : Except DnsError (Nat × Found) := do
  let some text := lookup domain | throw (.missing domain)
  let .root root ← Entry.parse text | throw .notRoot
  unless root.verify key do throw .badSignature
  unless seenSeq ≤ root.seq do throw (.staleSeq root.seq seenSeq)
  let found ← walk lookup domain budget [(.records, root.enrRoot), (.links, root.linkRoot)] []
    ⟨[], []⟩
  return (root.seq, found)

/-! ## Two lookups that disagree -/

/-- Two texts that differ and have one hash: a collision of the truncated Keccak-256. -/
def IsCollision (pair : String × String) : Prop :=
  pair.1 ≠ pair.2 ∧ hashOf pair.1 = hashOf pair.2

/-- The first place where two lookups give two different texts with one hash, at the name of a hash.

It follows the first lookup where they agree.

It finds nothing when they never disagree, when a lookup has no text, or when the budget ends.

It also finds nothing when the first two texts that differ have different hashes. -/
def walkCollision (lookup1 lookup2 : String → Option String) (domain : String) :
    Nat → List (Subtree × Hash) → List Hash → Option (String × String)
  | _, [], _ => none
  | 0, _ :: _, _ => none
  | budget + 1, (tree, hash) :: pending, visited =>
    if hash ∈ visited then walkCollision lookup1 lookup2 domain budget pending visited
    else
      match lookup1 (nameOf hash domain), lookup2 (nameOf hash domain) with
      | some text1, some text2 =>
        if text1 = text2 then
          match Entry.parse text1 with
          | .ok (.branch hashes) =>
            walkCollision lookup1 lookup2 domain budget (hashes.map (tree, ·) ++ pending)
              (hash :: visited)
          | _ => walkCollision lookup1 lookup2 domain budget pending (hash :: visited)
        else if hashOf text1 = hashOf text2 then some (text1, text2) else none
      | _, _ => none

/-- The two subtree hashes and the sequence number of the root that a lookup gives at a domain.

They are what a resolve takes from the root, leaving out the text of its signature. -/
def rootFields (lookup : String → Option String) (domain : String) : Option (Hash × Hash × Nat) :=
  match lookup domain with
  | some text =>
    match Entry.parse text with
    | .ok (.root root) => some (root.enrRoot, root.linkRoot, root.seq)
    | _ => none
  | none => none

/-- The first place where two lookups of one list give two texts with one hash.

It starts from the subtrees of the root that the first lookup gives at the domain. -/
def findCollision (lookup1 lookup2 : String → Option String) (domain : String) (budget : Nat) :
    Option (String × String) :=
  match rootFields lookup1 domain with
  | some (enrRoot, linkRoot, _) =>
    walkCollision lookup1 lookup2 domain budget [(.records, enrRoot), (.links, linkRoot)] []
  | none => none

end EthLib.Networking.DnsDisc
