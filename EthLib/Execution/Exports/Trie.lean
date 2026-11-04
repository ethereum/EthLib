module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Trie.HexPrefix
public import EthLib.Execution.Trie.Proof
public import EthLib.Serialization.Rlp.Codec

/-!
# Exports: the Merkle Patricia trie

The C exports of the trie root, of proof verification and of the hex-prefix encoding.

Both hash with Keccak-256.

The pairs of a trie and the nodes of a proof cross the boundary as RLP lists.

A trie or proof error comes back with its code and a message.

A malformed RLP input has code 0, since no error type of the specification covers that format.
-/

public section

namespace EthLib.Execution.Trie.Exports

open EthLib.Exports (Result)

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

/-- The hex-prefix encoding of a path, with one nibble in each input byte.

A byte of 16 or more is not a nibble, and fails with code 0. -/
@[export eth_trie_hex_prefix]
def hexPrefixExport (nibbles : ByteArray) (isLeaf : UInt8) : Result ByteArray := do
  let path ← nibbles.toList.mapM fun b =>
    if h : b.toNat < 16 then pure (⟨b.toNat, h⟩ : Nibble)
    else throw (0, s!"{b} is not a nibble")
  return nibbleListToCompact path (isLeaf != 0)

end EthLib.Execution.Trie.Exports
