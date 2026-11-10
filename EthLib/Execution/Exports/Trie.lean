module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Trie.HexPrefix
public import EthLib.Execution.Trie.Proof
public import EthLib.Execution.Trie.Range
public import EthLib.Serialization.Rlp.Codec

/-!
# Exports: the Merkle Patricia trie

The C exports of the trie root, of proof verification and of the hex-prefix encoding.

Both hash with Keccak-256.

The Engine exports check an answer of `eth_getProof`, whose fields are JSON.

The pairs of a trie and the nodes of a proof cross the boundary as RLP lists.

The hex-prefix encoding takes typed Python values: a list of nibbles and a bool.

A trie or proof error comes back with its code and a message.

A malformed RLP input has code 0, since no error type of the specification covers that format.
-/

public section

namespace EthLib.Execution.Trie.Exports

open EthLib.Exports (Result PyValue pyExport)

open EthLib.Base
open EthLib.Serialization.Rlp

/-- A key and a value: a list of exactly two byte strings. -/
def ofPairItem (item : Item) : Except RlpError (ByteArray × ByteArray) := do
  match ← item.fields 2 with
  | [key, value] => return (← key.toBytes, ← value.toBytes)
  | items => .error (.wrongFieldCount 2 items.length)

/-- The items of the RLP list that `input` encodes, or an error naming `what`. -/
def readList (input : ByteArray) (what : String) : Result (List Item) := do
  let .ok item := decode input | throw (0, s!"{what} is not one RLP item")
  let .ok items := item.toItems | throw (0, s!"{what} is not an RLP list")
  return items

/-- The root of the trie that sets the pairs of `input` in order, from an empty trie.

The input is an RLP list of pairs, each a list of a key and a value.

An empty value removes its key.

A `secured` other than 0 hashes each key before it becomes a path. -/
@[export eth_trie_root]
def rootExport (secured : UInt8) (input : ByteArray) : Result ByteArray := do
  let .ok pairs := (← readList input "pairs").mapM ofPairItem
    | throw (0, "a pair is not a list of a key and a value")
  let trie := pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured != 0, []⟩
  match root Cryptography.Hash.Keccak.keccak256 trie with
  | .ok hash => return ⟨hash.toArray⟩
  | .error e => throw (e.code, s!"trie has no root: {repr e}")

/-- The value of `key` in the trie of `root`, as the nodes of `proof` show.

The proof is an RLP list of byte strings, the encodings of the nodes.

No bytes means that `key` is not set, since no value is empty.

A root of another length than 32 bytes, or a proof that does not verify, is an error. -/
@[export eth_trie_verify_proof]
def verifyProofExport (root : ByteArray) (secured : UInt8) (key proof : ByteArray) :
    Result ByteArray := do
  if h : root.size = 32 then
    let .ok nodes := (← readList proof "proof").mapM Item.toBytes
      | throw (0, "a node of the proof is not a byte string")
    match verifyProof Cryptography.Hash.Keccak.keccak256 ⟨root.data, h⟩ (secured != 0) key nodes with
    | .ok (some value) => return value
    | .ok none => return .empty
    | .error e => throw (e.code, s!"proof does not verify: {repr e}")
  else
    throw (0, s!"bad root size: {root.size}, expected 32")

/-- Check a range of the trie of a 32-byte root from a 32-byte start, with Keccak-256.

It returns whether the trie holds a key after the last entry. -/
def verifyRangeOf (args : Hash32 × Hash32 × List (Hash32 × ByteArray) × List ByteArray) :
    Result Bool := do
  let (root, start, entries, proof) := args
  (verifyRange Cryptography.Hash.Keccak.keccak256 root start entries proof).mapError fun e =>
    (e.code, s!"range does not verify: {repr e}")

/-- Check a range of the trie of a 32-byte root from a 32-byte start, with Keccak-256.

The arguments are the root, the start, the entries and the encodings of the proof nodes.

Each entry is a pair of a 32-byte key and its value.

It returns whether the trie holds a key after the last entry.

An argument of the wrong shape has code 0.

A range that does not verify has the code of its fault. -/
@[export eth_trie_verify_range]
def verifyRangeExport (args : PyValue) : Result PyValue :=
  pyExport verifyRangeOf args

/-- The hex-prefix encoding of a path of nibbles, for a leaf or an extension.

A value of 16 or more is not a nibble, and fails with code 0. -/
def hexPrefixOf (args : List Nat × Bool) : Result ByteArray := do
  let (nibbles, isLeaf) := args
  let path ← nibbles.mapM fun n =>
    if h : n < 16 then pure (⟨n, h⟩ : Nibble)
    else throw (0, s!"{n} is not a nibble")
  return nibbleListToCompact path isLeaf

/-- The hex-prefix encoding of a path of nibbles, for a leaf or an extension.

The arguments are the list of the nibbles and whether the path ends at a leaf.

A value of 16 or more is not a nibble, and fails with code 0. -/
@[export eth_trie_hex_prefix]
def hexPrefixExport (args : PyValue) : Result PyValue :=
  pyExport hexPrefixOf args

end EthLib.Execution.Trie.Exports
