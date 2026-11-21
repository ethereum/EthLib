module

public import EthLib.Base.Exports.PyValue
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

open EthLib.Exports (Result PyValue toPy pyExport)

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

/-- Run a fallible computation, with its error as a code and a message. -/
def runDns {α : Type} (act : Except DnsError α) : Result α :=
  act.mapError fun e => (e.code, message e)

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
    | .error _ => throw (0, "record has no RLP encoding")

/-- The type and the fields of an entry text. -/
def parseEntryOf (text : String) : Result PyValue := do
  return .dict (← entryFields (← runDns (Entry.parse text))).toArray

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
  match ← runDns (Entry.parse text) with
  | .root r => return r.verify key
  | _ => throw ((DnsError.rootFields).code, "text is not a root")

/-- Whether a root text is signed by a compressed public key of 33 bytes.

A text that is no root comes back with the code of a root error. -/
@[export eth_dnsdisc_verify_root]
def verifyRootExport (args : PyValue) : Result PyValue :=
  pyExport verifyRootOf args

/-- The compressed public key and the domain of a URL. -/
def parseUrlOf (text : String) : Result (Vector UInt8 33 × String) := do
  let url ← runDns (Url.parse text)
  return (url.key, url.domain)

/-- The compressed public key and the domain of a URL `enrtree://<key>@<domain>`. -/
@[export eth_dnsdisc_parse_url]
def parseUrlExport (args : PyValue) : Result PyValue :=
  pyExport parseUrlOf args

end EthLib.Networking.DnsDisc.Exports
