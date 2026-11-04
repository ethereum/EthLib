module

public import EthLib.Execution.Trie.Root
public import EthLib.Serialization.Rlp.Decode

/-!
# `Trie.Proof`

A Merkle proof for one key: the nodes on the path of the key.

A client checks the value of the key against a root alone.

Source: the account and storage proofs of EIP-1186, at
<https://github.com/ethereum/EIPs/blob/7622abc1c6569b7e7ade9ed957dde4ed2271cc40/EIPS/eip-1186.md>.

The EIP describes a proof as the RLP-serialized nodes from the root, along the path of the key.

A parent holds a short child inside its own encoding, and a long child by the hash of its encoding.

So the proof lists the root node, then each node on the path that its parent holds by hash.

A child held inside its parent is read from the parent, not from the proof.

A proof shows either the value of the key or its absence:

- The path ends at a leaf with the rest of the key, or at a branch with a value: the key is set.
- The path leaves the trie: the key is not set.

The module checks a proof, and builds the proof of a key from a trie.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-- Why a Merkle proof is rejected. -/
inductive ProofError where
  /-- The path needs a node that the proof does not hold. -/
  | missingNode
  /-- A node of the proof does not hash to the reference that points to it. -/
  | hashMismatch
  /-- A node of the proof is not the RLP encoding of an item. -/
  | rlp (error : RlpError)
  /-- The path of a leaf or an extension is not a hex-prefix encoding. -/
  | hexPrefix (error : HexPrefixError)
  /-- An item is not a node.

  A node is a list of two items with a path first, or a list of 17 items with a value last. -/
  | invalidNode
  /-- A reference is a byte string of neither 0 nor 32 bytes. -/
  | invalidReference
  /-- An extension consumes no nibble, which `patricialize` never builds. -/
  | emptyExtension
  /-- The proof holds nodes that the path does not reach. -/
  | unusedNodes
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

The codes start at 101, above every code of a trie error, so that the two never meet.

A new constructor takes a new code, so that each code keeps its meaning. -/
def ProofError.code : ProofError → UInt32
  | .missingNode => 101
  | .hashMismatch => 102
  | .rlp _ => 103
  | .hexPrefix _ => 104
  | .invalidNode => 105
  | .invalidReference => 106
  | .emptyExtension => 107
  | .unusedNodes => 108

/-- The node that an item writes: the inverse of `unencoded` on a node. -/
def decodeNode : Item → Except ProofError InternalNode
  -- A leaf or an extension: its path in hex-prefix encoding, then its value or its child.
  | .list [.bytes compact, second] =>
    match compactToNibbleList compact, second with
    | .error error, _ => .error (.hexPrefix error)
    | .ok (path, true), .bytes value => .ok (.leaf path value)
    | .ok (_, true), .list _ => .error .invalidNode
    | .ok ([], false), _ => .error .emptyExtension
    | .ok (path, false), child => .ok (.extension path child)
  -- A branch: 16 children, then its value.
  | .list items =>
    if h : items.length = 17 then
      match items[16] with
      | .bytes value => .ok (.branch ⟨(items.take 16).toArray, by simp [h]⟩ value)
      | .list _ => .error .invalidNode
    else
      .error .invalidNode
  | .bytes _ => .error .invalidNode

/-- The item that a reference points to, and the proof nodes left after it.

- The empty byte string points to no node.
- A 32-byte string is the hash of the next proof node, which is decoded.
- A list is a node held inside its parent, and takes no proof node. -/
def resolve (hash : ByteArray → Hash32) (reference : Item) (proof : List ByteArray) :
    Except ProofError (Item × List ByteArray) :=
  match reference with
  | .list _ => .ok (reference, proof)
  | .bytes digest =>
    if digest.size = 0 then
      .ok (reference, proof)
    else if digest.size = 32 then
      match proof with
      | [] => .error .missingNode
      | encoded :: rest =>
        if (hash encoded).toList = digest.data.toList then do
          let item ← (decode encoded).mapError .rlp
          return (item, rest)
        else
          .error .hashMismatch
    else
      .error .invalidReference

/-- The value that the item `node` gives to the rest `path` of a key, and the proof nodes left.

`none` means that the key is not set.

# Why fuel

Each call either returns or consumes at least one nibble of `path`.

So a budget of one more than the length of `path` never runs out. -/
def walk (hash : ByteArray → Hash32) :
    Nat → Item → List Nibble → List ByteArray → Except ProofError (Option ByteArray × List ByteArray)
  | 0, _, _, _ => .error .missingNode
  | fuel + 1, node, path, proof =>
    match node with
    -- The empty byte string is no node: the key is not set.
    | .bytes data => if data.size = 0 then .ok (none, proof) else .error .invalidNode
    | .list _ => do
      match ← decodeNode node with
      | .leaf restOfKey value => return (if restOfKey = path then some value else none, proof)
      | .extension keySegment subnode =>
        if keySegment = path.take keySegment.length then
          let (child, rest) ← resolve hash subnode proof
          walk hash fuel child (path.drop keySegment.length) rest
        else
          -- The path leaves the run of nibbles that every key below shares.
          return (none, proof)
      | .branch subnodes value =>
        match path with
        | [] => return (if value.size = 0 then none else some value, proof)
        | nibble :: restOfPath =>
          let (child, rest) ← resolve hash subnodes[nibble] proof
          walk hash fuel child restOfPath rest

/-- The value of `key` in the trie of `root`, or `none` when `key` is not set, as `proof` shows.

`secured` says whether the trie hashes its keys, as the state and storage tries do.

The root is always the hash of the root node's encoding, so the proof starts with that encoding. -/
def verifyProof (hash : ByteArray → Hash32) (root : Hash32) (secured : Bool) (key : ByteArray)
    (proof : List ByteArray) : Except ProofError (Option ByteArray) := do
  let path := keyPath hash secured key
  let (rootNode, rest) ← resolve hash (.bytes ⟨root.toArray⟩) proof
  let (value, unused) ← walk hash (path.length + 1) rootNode path rest
  if unused.isEmpty then
    return value
  else
    .error .unusedNodes

/-- The proof below the node of `obj` at `level`, for the rest `path` of a key.

It lists the encoding of each node on the path that its parent holds by hash.

The budget counts the nodes on the path, and one more than the length of `path` is enough. -/
def proofBelow (hash : ByteArray → Hash32) :
    Nat → List (List Nibble × ByteArray) → Nat → List Nibble → Except RlpError (List ByteArray)
  | 0, _, _, _ => .ok []
  | fuel + 1, obj, level, path => do
    -- The proof of the child that the path enters, the keys `sub` at `deeper`.
    let child (sub : List (List Nibble × ByteArray)) (deeper : Nat) (restOfPath : List Nibble) := do
      let encoded ← encode (unencoded (← patricialize hash sub deeper))
      let below ← proofBelow hash fuel sub deeper restOfPath
      return (if encoded.size < 32 then [] else [encoded]) ++ below
    match ← patricialize hash obj level with
    | some (.extension keySegment _) =>
      if keySegment = path.take keySegment.length then
        child obj (level + keySegment.length) (path.drop keySegment.length)
      else
        return []
    | some (.branch _ _) =>
      match path with
      | [] => return []
      | nibble :: restOfPath => child (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1) restOfPath
    -- No node or a leaf: the path ends here.
    | _ => return []

/-- The proof of one key of a trie: the encoding of the root node, then the proof below it. -/
def getProof (hash : ByteArray → Hash32) (trie : Trie) (key : ByteArray) : Except TrieError (List ByteArray) := do
  let obj ← prepareData hash trie.data trie.secured
  let path := keyPath hash trie.secured key
  let encoded ← (encode (unencoded (← (patricialize hash obj 0).mapError .rlp))).mapError .rlp
  let below ← (proofBelow hash (path.length + 1) obj 0 path).mapError .rlp
  return encoded :: below

end EthLib.Execution.Trie
