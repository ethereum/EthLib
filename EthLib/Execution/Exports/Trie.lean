module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.State.AccountProof
public import EthLib.Execution.Trie.HexPrefix
public import EthLib.Execution.Trie.Proof
public import EthLib.Serialization.Rlp.Codec

/-!
# Exports: the Merkle Patricia trie

The C exports of the trie root, of proof verification and of the hex-prefix encoding.

A fourth export checks an answer of `eth_getProof` against a state root.

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

/-- The nodes of a proof, from a list of byte strings. -/
def nodesOfItem (item : Item) : Except RlpError (List ByteArray) := do
  (← item.toItems).mapM Item.toBytes

/-- One slot of an answer, from a list of the slot on 32 bytes, the word and the nodes. -/
def storageProofOfItem (item : Item) : Except RlpError State.StorageProof := do
  match ← item.fields 3 with
  | [key, value, proof] =>
    return ⟨← Codec.ofItem key, ← Codec.ofItem value, ← nodesOfItem proof⟩
  | items => .error (.wrongFieldCount 3 items.length)

/-- An answer of `eth_getProof`, from a list of its seven fields in the order of the structure. -/
def accountProofOfItem (item : Item) : Except RlpError State.AccountProof := do
  match ← item.fields 7 with
  | [address, nonce, balance, codeHash, storageHash, accountProof, storageProof] =>
    return {
      address := ← Codec.ofItem address
      nonce := ← Codec.ofItem nonce
      balance := ← Codec.ofItem balance
      codeHash := ← Codec.ofItem codeHash
      storageHash := ← Codec.ofItem storageHash
      accountProof := ← nodesOfItem accountProof
      storageProof := ← (← storageProof.toItems).mapM storageProofOfItem }
  | items => .error (.wrongFieldCount 7 items.length)

/-- Check an answer of `eth_getProof` against a state root, with Keccak-256.

The answer is the RLP list of the address, the nonce, the balance, the code hash and storage root.

The list goes on with the nodes of the account proof, then the slots.

Each slot is the list of the slot on 32 bytes, the word, and the nodes of its proof.

No bytes means that the address has no account: the nonce, the balance and each slot word are `0`.

Otherwise the byte 1 comes first, then one byte for each slot: 1 if it is set, 0 if it is not.

A root of another length than 32 bytes, or an answer that does not decode, has code 0. -/
@[export eth_trie_verify_account_proof]
def verifyAccountProofExport (root answer : ByteArray) : Result ByteArray := do
  if h : root.size = 32 then
    let .ok item := decode answer | throw (0, "answer is not one RLP item")
    let .ok p := accountProofOfItem item
      | throw (0, "answer is not an RLP list of the fields of an account proof")
    match p.verify Cryptography.Hash.Keccak.keccak256 ⟨root.data, h⟩ with
    | .ok .absent => return .empty
    | .ok (.present slots) =>
      return ⟨(#[1] : Array UInt8) ++ (slots.map fun
        | .set => (1 : UInt8)
        | .absent => 0).toArray⟩
    | .error e => throw (e.code, s!"answer does not hold: {repr e}")
  else
    throw (0, s!"bad root size: {root.size}, expected 32")

end EthLib.Execution.Trie.Exports
