module

public import EthLib.Base.Hash32
public import EthLib.Execution.Trie.HexPrefix
public import EthLib.Serialization.Rlp.Encode
public import Std.Data.TreeMap.Basic

/-!
# `Trie.Root`

The root of the Merkle Patricia Trie.

It is one 32-byte hash that commits to a map from byte keys to byte values.

Source: `TRIE` in Appendix D of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>.

Every fork since Frontier uses this trie.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-- A leaf, an extension or a branch, with its children already encoded.

The trie reads each key as a path of nibbles, and these are its three kinds of node. -/
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
  -- Not in Appendix D: `c(∅, i)` is undefined, so here it is `()`, as `n(∅, i)` is.
  | none => .bytes .empty
  -- A leaf: `(HP(I_0[i .. (||I_0|| - 1)], 1), I_1)`, for the one pair `I` of `𝔍`.
  | some (.leaf restOfKey value) => .list [.bytes (nibbleListToCompact restOfKey true), .bytes value]
  -- An extension: `(HP(I_0[i .. (j - 1)], 0), n(𝔍, j))`.
  | some (.extension keySegment subnode) => .list [.bytes (nibbleListToCompact keySegment false), subnode]
  -- A branch: `(u(0), u(1), ..., u(15), v)`, the 16 children, then the value.
  | some (.branch subnodes value) => .list (subnodes.toList ++ [.bytes value])

/-- How a parent holds a node: `n` of the Yellow Paper, with a hash that may answer in a monad.

- An encoding shorter than 32 bytes is held as the node's RLP structure, inside the parent.
- A longer encoding is held as its hash. -/
def encodeInternalNodeM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32)
    (node : Option InternalNode) : ExceptT RlpError m Item := do
  let encoded ← encode (unencoded node)
  -- `n(𝔍, i) = c(𝔍, i)` if `||RLP(c(𝔍, i))|| < 32`.
  --
  -- The case `n(∅, i) = ()` falls here, since `RLP(()) = 0x80` has one byte.
  if encoded.size < 32 then
    return unencoded node
  -- `n(𝔍, i) = KEC(RLP(c(𝔍, i)))` otherwise.
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

The first `level` nibbles of every path are already consumed. -/
def patricializeStepM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32)
    (recurse : List (List Nibble × ByteArray) → Nat → ExceptT RlpError m (Option InternalNode)) :
    List (List Nibble × ByteArray) → Nat → ExceptT RlpError m (Option InternalNode)
  -- With no key, there is no node.
  --
  -- No key: no node, held by a parent as `n(∅, i) = ()`, and so `TRIE(∅) = KEC(RLP(()))`.
  | [], _ => pure none
  -- With one key, the node is a leaf.
  --
  -- `||𝔍|| = 1`: a leaf with the rest of the one path, and its value.
  | [(key, value)], level => pure (some (.leaf (key.drop level) value))
  | obj@((arbitraryKey, _) :: _ :: _), level => do
    let substring := arbitraryKey.drop level
    -- `j - i`: the length of the longest run of nibbles after `i = level` that every path shares.
    let prefixLength :=
      obj.foldl (fun length (key, _) => min length (commonPrefixLength substring (key.drop level)))
        substring.length
    -- When every path shares a run of nibbles after `level`, the node is an extension.
    --
    -- `i ≠ j`, since `j - i > 0`: an extension consumes the run, and holds `n(𝔍, j)`.
    if 0 < prefixLength then
      let subnode ← encodeInternalNodeM hash (← recurse obj (level + prefixLength))
      return some (.extension (substring.take prefixLength) subnode)
    -- Otherwise the node is a branch, with one child for each next nibble.
    else
      -- `v = I_1` for the key with `||I_0|| = i`, or `()` when no key ends here.
      let value :=
        obj.foldl (fun value (key, keyValue) => if key.length = level then keyValue else value)
          .empty
      -- `u(j) = n({I ∈ 𝔍 : I_0[i] = j}, i + 1)` for each nibble `j`, in order.
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

When the budget runs out, a nested call gives no node. -/
def patricializeAuxM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32) :
    Nat → List (List Nibble × ByteArray) → Nat → ExceptT RlpError m (Option InternalNode)
  -- Why fuel: the kernel cannot unfold well-founded recursion.
  --
  -- So it could not evaluate a concrete root.
  --
  -- This definition recurses on a budget instead.
  --
  -- Each level of nested calls on two keys or more consumes more nibbles of the paths.
  --
  -- So a budget of one more than the longest path never runs out, as the proofs show.
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

It lists the keys and their values, in the order they were last added. -/
structure Trie where
  /-- Whether each key is hashed before it becomes a path. -/
  secured : Bool
  /-- The keys and their values, in the order they were last added. -/
  data : List (ByteArray × ByteArray)

/-- Whether two byte strings are equal, compared byte by byte in place. -/
def sameBytes (a b : ByteArray) : Bool :=
  a.data == b.data

/-- Set one pair in a log of keys and a table from each key to its place in the log and its value.
-/
def setPairStep (state : Array ByteArray × Std.TreeMap ByteArray (Nat × ByteArray))
    (pair : ByteArray × ByteArray) : Array ByteArray × Std.TreeMap ByteArray (Nat × ByteArray) :=
  let (log, table) := state
  let (key, value) := pair
  -- An empty value removes its key.
  if value.size = 0 then (log, table.erase key)
  else match table[key]? with
    -- A key already set keeps its place, with the new value.
    | some (place, _) => (log, table.insert key (place, value))
    -- A new key goes last.
    --
    -- Its place is read before the push, so the push updates the log in place.
    | none =>
      let place := log.size
      (log.push key, table.insert key (place, value))

/-- The keys of a log with their values in a table, at the places that the table gives them. -/
def logEntries (log : Array ByteArray) (table : Std.TreeMap ByteArray (Nat × ByteArray)) :
    List (ByteArray × ByteArray) :=
  -- A place of the log holds its key's value when the table still puts the key there.
  --
  -- A key removed and set again is in the log twice, and only its last place holds its value.
  log.toList.zipIdx.filterMap fun (key, place) =>
    match table[key]? with
    | some (p, value) => if p = place then some (key, value) else none
    | none => none

/-- The entries of a trie that sets the pairs in order from no entries. -/
def setPairs (pairs : List (ByteArray × ByteArray)) : List (ByteArray × ByteArray) :=
  -- An empty value removes its key, a key already set keeps its place, and a new key goes last.
  --
  -- So a key set again after its removal goes last.
  --
  -- The table is a search tree of the keys, in byte order.
  --
  -- So each pair costs a count of comparisons logarithmic in the count of keys.
  --
  -- A search of the entries would walk them all.
  let (log, table) := pairs.foldl setPairStep (#[], ∅)
  logEntries log table

/-- The value of `key`, or the empty byte string when `key` is not set. -/
def trieGet (trie : Trie) (key : ByteArray) : ByteArray :=
  ((trie.data.find? fun (k, _) => sameBytes k key).map Prod.snd).getD .empty

/-- The path of a key: its nibbles, after hashing it in a secured trie. -/
def keyPathM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32) (secured : Bool)
    (key : ByteArray) : m (List Nibble) := do
  -- A secured trie keys each value by `KEC(k)`, as `L_I` and `p(a)` of Yellow Paper §4.1 do.
  let bytes ← if secured then do pure ⟨(← hash key).toArray⟩ else pure key
  -- `y`: each byte as its high nibble, then its low nibble.
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
    -- A key set to the empty byte string is no key, so an empty value here is an error.
    if value.size = 0 then
      throw .emptyValue
    else do
      return (← ExceptT.lift (keyPathM hash secured preimage), value)

/-- Each key as its path, with a plain hash. -/
def prepareData (hash : ByteArray → Hash32) (data : List (ByteArray × ByteArray)) (secured : Bool) :
    Except TrieError (List (List Nibble × ByteArray)) :=
  (prepareDataM (m := Id) hash data secured).run

/-- `TRIE` of the Yellow Paper: the hash of the encoding of the root node, whatever its size.

The hash is an argument, and it may answer inside a monad.

So a random-oracle model can run the same definitions with a hash that queries an oracle. -/
def rootM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32) (trie : Trie) :
    ExceptT TrieError m Hash32 := do
  -- `y(𝔍)`: each key as a path of nibbles, after `KEC` in a secured trie.
  let obj ← prepareDataM hash trie.data trie.secured
  -- `c(𝔍, 0)`.
  let rootNode ← (patricializeM hash obj 0).adapt .rlp
  -- `TRIE(𝔍) = KEC(RLP(c(𝔍, 0)))`, whatever the size of the encoding.
  --
  -- So the empty map has a fixed root, the hash of `0x80`.
  --
  -- `0x80` is the RLP encoding of the empty byte string.
  let encoded ← ((encode (unencoded rootNode)).mapError .rlp : Except TrieError ByteArray)
  ExceptT.lift (hash encoded)

/-- `TRIE` of the Yellow Paper, with a plain hash: Keccak-256 in Ethereum.

The specification is the monadic form in the identity monad, with a plain hash. -/
def root (hash : ByteArray → Hash32) (trie : Trie) : Except TrieError Hash32 :=
  (rootM (m := Id) hash trie).run

end EthLib.Execution.Trie
