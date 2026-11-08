module

public import EthLib.Base.Hash32
public import EthLib.Execution.Trie.HexPrefix
public import EthLib.Serialization.Rlp.Encode

/-!
# `Trie.Root`

The root of the Merkle Patricia Trie.

It is one 32-byte hash that commits to a map from byte keys to byte values.

Source: `TRIE` in Appendix D of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>.

Every fork since Frontier uses this trie.

The trie reads each key as a path of nibbles, and it has three kinds of node:

- A leaf holds the rest of one key's path and that key's value.
- An extension holds a run of nibbles that every path below it shares, then one child.
- A branch holds 16 children, one for each next nibble.
  It also holds the value of a key whose path ends there.

A parent holds a child by its RLP structure when the child's encoding has fewer than 32 bytes.

Otherwise the parent holds the hash of the child's encoding.

The root is always the hash of the root node's encoding.

So the empty map has a fixed root, the hash of `0x80`.

`0x80` is the RLP encoding of the empty byte string.

Ethereum hashes with Keccak-256.

The hash is an argument here, and it may answer inside a monad.

The specification is the identity monad with a plain hash.

So a random-oracle model can run the same definitions with a hash that queries an oracle.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-- A leaf, an extension or a branch, with its children already encoded. -/
inductive InternalNode where
  /-- A leaf: the nibbles of the key that the nodes above leave, and its value. -/
  | leaf (restOfKey : List Nibble) (value : ByteArray)
  /-- An extension: the nibbles that every key below shares, and the encoded child after them. -/
  | extension (keySegment : List Nibble) (subnode : Item)
  /-- A branch: one encoded child for each next nibble, and the value of a key that ends here.

  An absent child is the empty byte string, and so is the value when no key ends here. -/
  | branch (subnodes : Vector Item 16) (value : ByteArray)

/-- Why the trie has no root. -/
inductive TrieError where
  /-- A value is the empty byte string.

  The trie stores an absent key as no entry at all, so no value is empty. -/
  | emptyValue
  /-- The RLP encoding of a node failed, because a payload has `2^64` bytes or more. -/
  | rlp (error : RlpError)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def TrieError.code : TrieError → UInt32
  | .emptyValue => 1
  | .rlp _ => 2

/-- The RLP structure of a node before it is encoded: `c` of the Yellow Paper.

No node is the empty byte string. -/
def unencoded : Option InternalNode → Item
  | none => .bytes .empty
  | some (.leaf restOfKey value) => .list [.bytes (nibbleListToCompact restOfKey true), .bytes value]
  | some (.extension keySegment subnode) => .list [.bytes (nibbleListToCompact keySegment false), subnode]
  -- The 16 children, then the value.
  | some (.branch subnodes value) => .list (subnodes.toList ++ [.bytes value])

/-- How a parent holds a node: `n` of the Yellow Paper, with a hash that may answer in a monad.

- An encoding shorter than 32 bytes is held as the node's RLP structure, inside the parent.
- A longer encoding is held as its hash. -/
def encodeInternalNodeM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32)
    (node : Option InternalNode) : ExceptT RlpError m Item := do
  let encoded ← encode (unencoded node)
  if encoded.size < 32 then
    return unencoded node
  else
    return .bytes ⟨(← hash encoded).toArray⟩

/-- How a parent holds a node: `n` of the Yellow Paper, with a plain hash. -/
def encodeInternalNode (hash : ByteArray → Hash32) (node : Option InternalNode) :
    Except RlpError Item :=
  (encodeInternalNodeM (m := Id) hash node).run

/-- `f` on each entry of `xs` in order, in the monad `m`.

The length of `xs` stays in the type.

The kernel can unfold this definition, so it evaluates the 16 children of a branch. -/
def mapMVector {m : Type → Type} [Monad m] {α β : Type} (f : α → m β) :
    (xs : List α) → m (Vector β xs.length)
  | [] => pure ⟨#[], rfl⟩
  | x :: rest => do
    let y ← f x
    let ys ← mapMVector f rest
    return ⟨⟨y :: ys.toList⟩, by simp⟩

/-- The number of leading nibbles that two paths share. -/
def commonPrefixLength : List Nibble → List Nibble → Nat
  | a :: restA, b :: restB => if a = b then commonPrefixLength restA restB + 1 else 0
  | _, _ => 0

/-- One step of the node composition, with each nested step made through `recurse`.

`obj` lists the full path of each key with its value.

The first `level` nibbles of every path are already consumed.

- With no key, there is no node.
- With one key, the node is a leaf.
- When every path shares a run of nibbles after `level`, the node is an extension.
- Otherwise the node is a branch, with one child for each next nibble. -/
def patricializeStepM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32)
    (recurse : List (List Nibble × ByteArray) → Nat → ExceptT RlpError m (Option InternalNode)) :
    List (List Nibble × ByteArray) → Nat → ExceptT RlpError m (Option InternalNode)
  | [], _ => pure none
  -- The rest of the one path, and its value.
  | [(key, value)], level => pure (some (.leaf (key.drop level) value))
  | obj@((arbitraryKey, _) :: _ :: _), level => do
    let substring := arbitraryKey.drop level
    -- The longest run of nibbles after `level` that every path shares.
    let prefixLength :=
      obj.foldl (fun length (key, _) => min length (commonPrefixLength substring (key.drop level)))
        substring.length
    if 0 < prefixLength then
      -- Every path shares the run, so an extension consumes it.
      let subnode ← encodeInternalNodeM hash (← recurse obj (level + prefixLength))
      return some (.extension (substring.take prefixLength) subnode)
    else
      -- The value of the key whose path ends here, or the empty byte string.
      let value :=
        obj.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value)
          .empty
      -- The child of each next nibble holds the keys whose path continues with it, in order.
      let subnodes ← mapMVector (fun nibble => do
          encodeInternalNodeM hash
            (← recurse (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1)))
        (List.finRange 16)
      return some (.branch (subnodes.cast (by simp)) value)

/-- One step of the node composition, with a plain hash. -/
def patricializeStep (hash : ByteArray → Hash32)
    (recurse : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode))
    (obj : List (List Nibble × ByteArray)) (level : Nat) : Except RlpError (Option InternalNode) :=
  (patricializeStepM (m := Id) hash recurse obj level).run

/-- The node composition, with a budget of `fuel` levels of nested calls.

# Why fuel

The kernel cannot unfold well-founded recursion, so it could not evaluate a concrete root.

This definition recurses on a budget instead.

When the budget runs out, a nested call gives no node.

Each level of nested calls on two keys or more consumes more nibbles of the paths.

So a budget of one more than the longest path never runs out, as the proofs show. -/
def patricializeAuxM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32) :
    Nat → List (List Nibble × ByteArray) → Nat → ExceptT RlpError m (Option InternalNode)
  | 0 => patricializeStepM hash fun _ _ => pure none
  | fuel + 1 => patricializeStepM hash (patricializeAuxM hash fuel)

/-- The node composition with a budget, with a plain hash. -/
def patricializeAux (hash : ByteArray → Hash32) (fuel : Nat) (obj : List (List Nibble × ByteArray))
    (level : Nat) : Except RlpError (Option InternalNode) :=
  (patricializeAuxM (m := Id) hash fuel obj level).run

/-- The longest path among the keys of `obj`. -/
def longestPath (obj : List (List Nibble × ByteArray)) : Nat :=
  obj.foldl (fun longest (key, _) => max longest key.length) 0

/-- `c` of the Yellow Paper: the node for the keys of `obj`, `level` nibbles into their paths. -/
def patricializeM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32)
    (obj : List (List Nibble × ByteArray)) (level : Nat) :
    ExceptT RlpError m (Option InternalNode) :=
  patricializeAuxM hash (longestPath obj + 1) obj level

/-- `c` of the Yellow Paper, with a plain hash. -/
def patricialize (hash : ByteArray → Hash32) (obj : List (List Nibble × ByteArray)) (level : Nat) :
    Except RlpError (Option InternalNode) :=
  (patricializeM (m := Id) hash obj level).run

/-- A trie of byte values whose default is the empty byte string.

It records whether each key is hashed before it becomes a path.

It lists the keys and their values, in the order they were first set. -/
structure Trie where
  /-- Whether each key is hashed before it becomes a path. -/
  secured : Bool
  /-- The keys and their values, in the order they were first set. -/
  data : List (ByteArray × ByteArray)

/-- Whether two byte strings are equal, compared byte by byte in place. -/
def sameBytes (a b : ByteArray) : Bool :=
  a.data == b.data

/-- Set `key` to `value`, or remove `key` when `value` is the empty byte string.

A key already present keeps its place, and a new key goes last. -/
def trieSet (trie : Trie) (key value : ByteArray) : Trie :=
  if value.size = 0 then
    { trie with data := trie.data.filter fun (k, _) => !sameBytes k key }
  else if trie.data.any fun (k, _) => sameBytes k key then
    { trie with data := trie.data.map fun (k, v) => if sameBytes k key then (k, value) else (k, v) }
  else
    { trie with data := trie.data ++ [(key, value)] }

/-- The value of `key`, or the empty byte string when `key` is not set. -/
def trieGet (trie : Trie) (key : ByteArray) : ByteArray :=
  ((trie.data.find? fun (k, _) => sameBytes k key).map Prod.snd).getD .empty

/-- The path of a key: its nibbles, after hashing it in a secured trie. -/
def keyPathM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32) (secured : Bool)
    (key : ByteArray) : m (List Nibble) := do
  let bytes ← if secured then do pure ⟨(← hash key).toArray⟩ else pure key
  return bytesToNibbleList bytes

/-- The path of a key, with a plain hash. -/
def keyPath (hash : ByteArray → Hash32) (secured : Bool) (key : ByteArray) : List Nibble :=
  (keyPathM (m := Id) hash secured key).run

/-- Each key as its path, after hashing it in a secured trie.

The values are already bytes, so they stay as they are. -/
def prepareDataM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32)
    (data : List (ByteArray × ByteArray)) (secured : Bool) :
    ExceptT TrieError m (List (List Nibble × ByteArray)) :=
  data.mapM fun (preimage, value) =>
    if value.size = 0 then
      throw .emptyValue
    else do
      return (← ExceptT.lift (keyPathM hash secured preimage), value)

/-- Each key as its path, with a plain hash. -/
def prepareData (hash : ByteArray → Hash32) (data : List (ByteArray × ByteArray)) (secured : Bool) :
    Except TrieError (List (List Nibble × ByteArray)) :=
  (prepareDataM (m := Id) hash data secured).run

/-- `TRIE` of the Yellow Paper: the hash of the encoding of the root node.

The root node is first held as a parent would hold it, and then hashed if its encoding is short.

Both cases give the hash of the encoding of the root node:

- A short encoding is hashed here.
- A long encoding is replaced by its hash already, and that hash is the root. -/
def rootM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32) (trie : Trie) :
    ExceptT TrieError m Hash32 := do
  let obj ← prepareDataM hash trie.data trie.secured
  let rootNode ← (patricializeM hash obj 0).adapt .rlp
  let encoded ← ((encode (unencoded rootNode)).mapError .rlp : Except TrieError ByteArray)
  ExceptT.lift (hash encoded)

/-- `TRIE` of the Yellow Paper, with a plain hash: Keccak-256 in Ethereum. -/
def root (hash : ByteArray → Hash32) (trie : Trie) : Except TrieError Hash32 :=
  (rootM (m := Id) hash trie).run

end EthLib.Execution.Trie
