module

public import EthLib.Base.Hash32
public import EthLib.Execution.Trie.HexPrefix
public import EthLib.Serialization.Rlp.Encode

/-!
# `Trie.Root`

The root of the Merkle Patricia Trie: one 32-byte hash that commits to a map from byte keys to byte values.

Source: [`merkle_patricia_trie.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/merkle_patricia_trie.py) of execution-specs at `2c0c8e7`.

Every fork from Frontier to Bogota imports the trie from that one file.

The trie reads each key as a path of nibbles, and it has three kinds of node:

- A leaf holds the rest of one key's path and that key's value.
- An extension holds a run of nibbles that every path below it shares, then one child.
- A branch holds 16 children, one for each next nibble, and the value of a key whose path ends there.

A parent holds a child by its RLP structure when the child's encoding has fewer than 32 bytes.

Otherwise the parent holds the hash of the child's encoding.

The root is always the hash of the root node's encoding.

So the empty map has a fixed root, the hash of `0x80`, which is the RLP encoding of the empty byte string.

Ethereum hashes with Keccak-256.

The hash is an argument here.

So a known answer can pass a faster form of Keccak-256 for the kernel, which is proved equal to it.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-- `InternalNode`: a leaf, an extension or a branch, with its children already encoded. -/
inductive InternalNode where
  /-- `LeafNode`: the nibbles of the key that the nodes above leave, and its value. -/
  | leaf (restOfKey : List Nibble) (value : ByteArray)
  /-- `ExtensionNode`: the nibbles that every key below shares, and the encoded child after them. -/
  | extension (keySegment : List Nibble) (subnode : Item)
  /-- `BranchNode`: one encoded child for each next nibble, and the value of a key that ends here.

  An absent child is the empty byte string, and so is the value when no key ends here. -/
  | branch (subnodes : Vector Item 16) (value : ByteArray)

/-- Why the trie has no root. -/
inductive TrieError where
  /-- A value is the empty byte string.

  The trie stores an absent key as no entry at all, so the source asserts that no value is empty. -/
  | emptyValue
  /-- The RLP encoding of a node failed, because a payload has `2^64` bytes or more. -/
  | rlp (error : RlpError)
  deriving Repr, DecidableEq

/-- The RLP structure of a node before it is encoded: `unencoded` in `encode_internal_node`.

No node is the empty byte string. -/
def unencoded : Option InternalNode → Item
  | none => .bytes .empty
  | some (.leaf restOfKey value) => .list [.bytes (nibbleListToCompact restOfKey true), .bytes value]
  | some (.extension keySegment subnode) => .list [.bytes (nibbleListToCompact keySegment false), subnode]
  -- The 16 children, then the value.
  | some (.branch subnodes value) => .list (subnodes.toList ++ [.bytes value])

/-- `encode_internal_node`: how a parent holds a node.

- An encoding shorter than 32 bytes is held as the node's RLP structure, inside the parent.
- A longer encoding is held as its hash. -/
def encodeInternalNode (hash : ByteArray → Hash32) (node : Option InternalNode) : Except RlpError Item := do
  let encoded ← encode (unencoded node)
  if encoded.size < 32 then
    return unencoded node
  else
    return .bytes ⟨(hash encoded).toArray⟩

/-- `f` on each entry of `xs` in order, or the first error, with the length of `xs` kept in the type.

The kernel can unfold this definition, so it evaluates a branch's 16 children in the known answers. -/
def mapMVector {α β ε : Type} (f : α → Except ε β) : (xs : List α) → Except ε (Vector β xs.length)
  | [] => .ok ⟨#[], rfl⟩
  | x :: rest => do
    let y ← f x
    let ys ← mapMVector f rest
    return ⟨⟨y :: ys.toList⟩, by simp⟩

/-- `common_prefix_length`: the number of leading nibbles that two paths share. -/
def commonPrefixLength : List Nibble → List Nibble → Nat
  | a :: restA, b :: restB => if a = b then commonPrefixLength restA restB + 1 else 0
  | _, _ => 0

/-- One call of `patricialize`, with each nested call made through `recurse`.

`obj` lists each key's full path with its value, and `level` nibbles of every path are already consumed.

- With no key, there is no node.
- With one key, the node is a leaf.
- When every path shares a run of nibbles after `level`, the node is an extension.
- Otherwise the node is a branch, with one child for each next nibble. -/
def patricializeStep (hash : ByteArray → Hash32)
    (recurse : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode)) :
    List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode)
  | [], _ => .ok none
  -- The rest of the one path, and its value.
  | [(key, value)], level => .ok (some (.leaf (key.drop level) value))
  | obj@((arbitraryKey, _) :: _ :: _), level => do
    let substring := arbitraryKey.drop level
    -- The longest run of nibbles after `level` that every path shares.
    let prefixLength :=
      obj.foldl (fun length (key, _) => min length (commonPrefixLength substring (key.drop level))) substring.length
    if 0 < prefixLength then
      -- Every path shares the run, so an extension consumes it.
      let subnode ← encodeInternalNode hash (← recurse obj (level + prefixLength))
      return some (.extension (substring.take prefixLength) subnode)
    else
      -- The value of the key whose path ends here, or the empty byte string.
      let value := obj.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value) .empty
      -- The child of each next nibble holds the keys whose path continues with it, in their order.
      let subnodes ← mapMVector (fun nibble => do
          encodeInternalNode hash (← recurse (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1)))
        (List.finRange 16)
      return some (.branch (subnodes.cast (by simp)) value)

/-- `patricialize`, with a budget of `fuel` levels of nested calls.

# Why fuel

The kernel cannot unfold well-founded recursion, so it could not evaluate the known answers.

This definition recurses on a budget instead.

When the budget runs out, a nested call gives no node.

Each level of nested calls on two keys or more consumes more nibbles of the paths.

So a budget of one more than the longest path never runs out, which `Proofs.Trie.Root` proves. -/
def patricializeAux (hash : ByteArray → Hash32) :
    Nat → List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode)
  | 0 => patricializeStep hash fun _ _ => .ok none
  | fuel + 1 => patricializeStep hash (patricializeAux hash fuel)

/-- The longest path among the keys of `obj`. -/
def longestPath (obj : List (List Nibble × ByteArray)) : Nat :=
  obj.foldl (fun longest (key, _) => max longest key.length) 0

/-- `patricialize`: the node for the keys of `obj`, `level` nibbles into their paths. -/
def patricialize (hash : ByteArray → Hash32) (obj : List (List Nibble × ByteArray)) (level : Nat) :
    Except RlpError (Option InternalNode) :=
  patricializeAux hash (longestPath obj + 1) obj level

/-- `Trie`, for byte values whose default is the empty byte string.

- `secured` says whether each key is hashed before it becomes a path.
- `data` lists the keys and their values, in the order they were first set.

The source keeps the entries in a Python dictionary, which keeps that order too. -/
structure Trie where
  /-- Whether each key is hashed before it becomes a path. -/
  secured : Bool
  /-- The keys and their values, in the order they were first set. -/
  data : List (ByteArray × ByteArray)

/-- Whether two byte strings are equal, compared as lists of bytes, which the kernel does in linear time. -/
def sameBytes (a b : ByteArray) : Bool :=
  decide (a.data.toList = b.data.toList)

/-- `trie_set`: set `key` to `value`, or remove `key` when `value` is the default, the empty byte string.

A key already present keeps its place, and a new key goes last. -/
def trieSet (trie : Trie) (key value : ByteArray) : Trie :=
  if value.size = 0 then
    { trie with data := trie.data.filter fun (k, _) => !sameBytes k key }
  else if trie.data.any fun (k, _) => sameBytes k key then
    { trie with data := trie.data.map fun (k, v) => if sameBytes k key then (k, value) else (k, v) }
  else
    { trie with data := trie.data ++ [(key, value)] }

/-- `trie_get`: the value of `key`, or the default, the empty byte string, when `key` is not set. -/
def trieGet (trie : Trie) (key : ByteArray) : ByteArray :=
  ((trie.data.find? fun (k, _) => sameBytes k key).map Prod.snd).getD .empty

/-- The path of a key: its nibbles, after hashing it in a secured trie. -/
def keyPath (hash : ByteArray → Hash32) (secured : Bool) (key : ByteArray) : List Nibble :=
  bytesToNibbleList (if secured then ⟨(hash key).toArray⟩ else key)

/-- `_prepare_data`, for values that are already bytes: each key as its path, after hashing it in a secured trie.

The source encodes each value first, and leaves a byte string unchanged. -/
def prepareData (hash : ByteArray → Hash32) (data : List (ByteArray × ByteArray)) (secured : Bool) :
    Except TrieError (List (List Nibble × ByteArray)) :=
  data.mapM fun (preimage, value) =>
    if value.size = 0 then
      .error .emptyValue
    else
      .ok (keyPath hash secured preimage, value)

/-- `root`: the hash of the encoding of the root node.

The source returns the root node as its parent would hold it, then hashes its encoding when that is short.

Both cases give the hash of the root node's encoding:

- A short encoding is hashed by `root` itself.
- A long encoding is replaced by its hash already, and `root` returns that hash. -/
def root (hash : ByteArray → Hash32) (trie : Trie) : Except TrieError Hash32 := do
  let obj ← prepareData hash trie.data trie.secured
  let rootNode ← (patricialize hash obj 0).mapError .rlp
  let encoded ← (encode (unencoded rootNode)).mapError .rlp
  return hash encoded

end EthLib.Execution.Trie
