module

public import EthLib.Base.Exports.PyValue
public import EthLib.Cryptography.Exports.Secp256k1
public import EthLib.Networking.DnsDisc

/-!
# `Exports.DnsDisc`

C-ABI exports for the node lists of EIP-1459, callable from the Python C extension.

An entry crosses the boundary as its text, and comes back as a `dict` of its type and fields.

A hash is its 16 bytes, a key its 33 compressed bytes, and a record its RLP bytes.

A rejected text comes back with the code of its error.
-/

public section

namespace EthLib.Networking.DnsDisc.Exports

open EthLib.Exports (ExportError Result PyValue UnreadArgument toPy pyExport rejectArgument
  toResult)

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : DnsError → String
  | .unknownEntry => "text is not a root, a branch, a link or a node record"
  | .rootFields => "root does not have the fields e=, l=, seq= and sig=, in that order"
  | .seq => "sequence number is not a decimal integer without leading zeros"
  | .encoding => "a hash, a key or a signature is not base32 or base64 of its size"
  | .branchHashes => "the hashes of a branch are not separated by commas"
  | .linkFields => "link has no @ after its key"
  | .publicKey => "key is not a point of secp256k1"
  | .enr _ => "node record is refused"
  | .signing => "the root could not be signed"
  | .missing name => s!"no TXT record at {name}"
  | .hashMismatch name => s!"the text at {name} does not have the hash of its name"
  | .wrongSubtree name => s!"the entry at {name} is in the wrong subtree"
  | .notRoot => "the text at the domain is not a root"
  | .badSignature => "the root is not signed by the key of the list"
  | .staleSeq seq seen => s!"sequence number {seq} is below {seen}, the one seen last"
  | .tooManyEntries => "the walk took more hashes than its budget"
  | .badRecord name => s!"the node record at {name} does not verify"

/-- A rejection reaches Python with its code, and its message names the fault. -/
instance : ExportError DnsError where
  code := DnsError.code
  message := message

/-- The fields of an entry, as Python values. -/
def entryFields : Entry → Result (List (String × PyValue))
  | .root r => return [("type", toPy "root"), ("enr_root", toPy r.enrRoot),
      ("link_root", toPy r.linkRoot), ("seq", toPy r.seq), ("signature", toPy r.signature)]
  | .branch hashes => return [("type", toPy "branch"), ("hashes", toPy hashes)]
  | .link url => return [("type", toPy "link"), ("key", toPy url.key),
      ("domain", toPy url.domain)]
  | .enr record =>
    match record.encode with
    | .ok bytes => return [("type", toPy "enr"), ("record", toPy bytes)]
    | .error _ => rejectArgument none "record has no RLP encoding"

/-- The type and the fields of an entry text. -/
def parseEntryOf (text : String) : Result PyValue := do
  return .dict (← entryFields (← toResult none (Entry.parse text))).toArray

/-- The type and the fields of an entry text, as a `dict`.

The type is `root`, `branch`, `link` or `enr`. -/
@[export eth_dnsdisc_parse_entry]
def parseEntryExport (args : PyValue) : Result PyValue :=
  pyExport parseEntryOf args

/-- The subdomain of an entry text: the base32 of the first 16 bytes of its Keccak-256 hash. -/
def subdomainOf (text : String) : Result String :=
  return subdomain text

/-- The subdomain of an entry text: the base32 of the first 16 bytes of its Keccak-256 hash. -/
@[export eth_dnsdisc_subdomain]
def subdomainExport (args : PyValue) : Result PyValue :=
  pyExport subdomainOf args

/-- Whether a root text is signed by a compressed public key of 33 bytes. -/
def verifyRootOf (args : Vector UInt8 33 × String) : Result Bool := do
  let (key, text) := args
  match ← toResult none (Entry.parse text) with
  | .root r => return r.verify key
  | _ => throw ((DnsError.rootFields).code, "text is not a root")

/-- Whether a root text is signed by a compressed public key of 33 bytes.

A text that is no root comes back with the code of a root error. -/
@[export eth_dnsdisc_verify_root]
def verifyRootExport (args : PyValue) : Result PyValue :=
  pyExport verifyRootOf args

/-- The compressed public key and the domain of a URL. -/
def parseUrlOf (text : String) : Result (Vector UInt8 33 × String) := do
  let url ← toResult none (Url.parse text)
  return (url.key, url.domain)

/-- The compressed public key and the domain of a URL `enrtree://<key>@<domain>`. -/
@[export eth_dnsdisc_parse_url]
def parseUrlExport (args : PyValue) : Result PyValue :=
  pyExport parseUrlOf args

/-- The node list at a domain, with the TXT records of a table as the DNS. -/
def resolveOf (args : Vector UInt8 33 × Nat × String × Nat × List (String × String)) :
    Result (Nat × List ByteArray × List String) := do
  let (key, seenSeq, domain, budget, table) := args
  -- The first record of the table at a name is its text.
  let lookup := fun name => (table.find? (·.1 = name)).map (·.2)
  let (seq, found) ← toResult none (resolve lookup key seenSeq domain budget)
  let records ← found.records.mapM fun record =>
    toResult none (record.encode.mapError fun _ => UnreadArgument.mk "record has no RLP encoding")
  return (seq, records, found.links.map fun url => String.ofList url.toText)

/-- The node list at a domain, under a compressed public key, with a table as the DNS.

The arguments are the key, the sequence number seen last, the domain and a budget of entries.

Last come the TXT records of the table, each a name and its text.

The result is the sequence number of the root, the RLP bytes of the records and the links. -/
@[export eth_dnsdisc_resolve]
def resolveExport (args : PyValue) : Result PyValue :=
  pyExport resolveOf args

/-- The text of a root of two hashes and a sequence number, signed with a private key. -/
def signRootOf (args : ByteArray × Hash × Hash × Nat) : Result String := do
  let (secretKey, enrRoot, linkRoot, seq) := args
  let sk ← toResult none
    (Cryptography.Secp256k1.Exports.readPrivateKey secretKey (fun _ => bad) bad)
  let root ← toResult none (Root.sign sk enrRoot linkRoot seq)
  return String.ofList root.toText
where
  /-- The error of a private key that is not 32 bytes below the group order. -/
  bad : UnreadArgument := ⟨"private key is not 32 bytes below the group order"⟩

/-- The text of a root of two hashes of 16 bytes and a sequence number, signed with a private key.

The private key is 32 big-endian bytes, and a bad one comes back with code 0. -/
@[export eth_dnsdisc_sign_root]
def signRootExport (args : PyValue) : Result PyValue :=
  pyExport signRootOf args

end EthLib.Networking.DnsDisc.Exports
