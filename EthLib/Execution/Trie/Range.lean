module

public import EthLib.Execution.Trie.Proof

/-!
# `Trie.Range`

A range proof: consecutive keys of a trie, with the nodes on the paths of its two ends.

A client checks against a root alone that the range holds every key between its two ends.

That holds when the hash resists collisions, as Keccak-256 is assumed to.

The snap capability of devp2p sends such ranges, as [`caps/snap.md`][snap] says.

Its sections "AccountRange (0x01)" and "StorageRanges (0x03)" describe the proofs.

[snap]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md

The first end is a starting key, which the trie may not hold.

The last end is the last key of the range.

The check needs no node off the two paths: their parents hold each such subtree by reference.

The check walks the trie of the root along the two paths, with nodes from the proof.

Each subtree between the two paths must be the subtree that the entries under it build.

Each subtree before the first end must hold no entry, and so must each after the last end.

A range with no proof must be the whole trie: its entries must build the root.

The check returns whether some key lies after the last entry, as the proof shows.

Each key is a 32-byte hash, so each path in the trie has 64 nibbles.

So no key ends at a branch, and a branch on the two paths holds no value.

The proof may hold nodes that the check never reaches, and the check ignores them.

The two paths share their upper nodes, so a sender may list those nodes twice.

The check accepts a node listed twice.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-- Why a range of a trie is rejected. -/
inductive RangeError where
  /-- The keys are not in strictly increasing order. -/
  | unsorted
  /-- The first key is below the starting key. -/
  | beforeStart
  /-- A value is the empty byte string, which the trie never stores. -/
  | emptyValue
  /-- A node that the check needs is missing from the proof, or a node or reference is malformed. -/
  | proof (error : ProofError)
  /-- The RLP encoding of a node failed, because a payload has `2^64` bytes or more. -/
  | rlp (error : RlpError)
  /-- A branch on one of the two paths holds a value, but every key has 64 nibbles. -/
  | branchValue
  /-- The entries do not build the trie of the root that the proof shows. -/
  | mismatch
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor, which the message carries.

The codes start at 201, above every code of a trie error and of a proof error.

A new constructor takes a new code, so that each code keeps its meaning. -/
def RangeError.code : RangeError → UInt32
  | .unsorted => 201
  | .beforeStart => 202
  | .emptyValue => 203
  | .proof _ => 204
  | .rlp _ => 205
  | .branchValue => 206
  | .mismatch => 207

/-- Where the keys of a subtree lie, against a range. -/
inductive RangePlace where
  /-- On the path of one end of the range: the subtree may hold keys on both sides of that end. -/
  | boundary
  /-- Every key of the subtree is below the first end of the range. -/
  | before
  /-- Every key of the subtree is inside the range. -/
  | inside
  /-- Every key of the subtree is above the last end of the range. -/
  | after
  deriving Repr, DecidableEq

/-- Where the keys whose paths start with `pre` lie, against the range from `left` to `right`.

No last end means that the range runs to the end of the trie.

A path that is no prefix of an end compares with every extension of itself as it does alone.

So it falls wholly before, inside or after the range. -/
def rangePlace (left : List Nibble) (right : Option (List Nibble)) (pre : List Nibble) :
    RangePlace :=
  if pre.isPrefixOf left || right.any pre.isPrefixOf then .boundary
  else if pre < left then .before
  else if right.any (· < pre) then .after
  else .inside

/-- The item that a reference points to, with the proof nodes indexed by their hashes.

- The empty byte string points to no node.
- A 32-byte string is the hash of a proof node, which is decoded.
- A list is a node held inside its parent.

Unlike a proof of one key, a range proof is a set of nodes, so the nodes come in any order. -/
def lookupNode (nodes : List (Hash32 × ByteArray)) (reference : Item) : Except ProofError Item :=
  match reference with
  | .list _ => .ok reference
  | .bytes digest =>
    if digest.size = 0 then
      .ok reference
    else if digest.size = 32 then
      match nodes.find? fun (hash, _) => hash.toList == digest.data.toList with
      | some (_, encoded) => (decode encoded).mapError .rlp
      | none => .error .missingNode
    else
      .error .invalidReference

/-- Check the subtree that `reference` holds at the path `pre`, against `entries`.

The entries are those whose paths start with `pre`, as full paths with their values.

It returns whether the subtree holds a key after the range.

# Why fuel

A call that goes deeper has a path that is a prefix of an end.

The range check passes two ends of 64 nibbles, as long as `left`.

Each such call is at least one nibble deeper than its caller.

So at most one more than the length of `left` such calls nest, and one last call leaves the paths.

So with ends of one length, a budget of two more than that length never runs out. -/
def checkSubtree (hash : ByteArray → Hash32) (nodes : List (Hash32 × ByteArray))
    (left : List Nibble) (right : Option (List Nibble)) :
    Nat → Item → List Nibble → List (List Nibble × ByteArray) → Except RangeError Bool
  -- The budget never runs out, so this error never occurs.
  | 0, _, _, _ => .error (.proof .missingNode)
  | fuel + 1, reference, pre, entries =>
    match rangePlace left right pre with
    | .before => if entries.isEmpty then .ok false else .error .mismatch
    -- Any node after the range holds a key there.
    | .after => if entries.isEmpty then .ok (reference != .bytes .empty) else .error .mismatch
    -- The parent must hold the node that the entries build, as the parent of a trie does.
    | .inside => do
      let node ← (patricialize hash entries pre.length).mapError .rlp
      let held ← (encodeInternalNode hash node).mapError .rlp
      if held = reference then .ok false else .error .mismatch
    | .boundary => do
      let item ← (lookupNode nodes reference).mapError .proof
      if item = .bytes .empty then
        if entries.isEmpty then return false else throw .mismatch
      match ← (decodeNode item).mapError .proof with
      | .leaf restOfKey value =>
        let key := pre ++ restOfKey
        if left ≤ key && right.all (key ≤ ·) then
          -- The key is inside the range, so it is the one entry here.
          if entries = [(key, value)] then return false else throw .mismatch
        else if entries.isEmpty then
          return right.any (· < key)
        else
          throw .mismatch
      | .extension keySegment subnode =>
        let deeper := pre ++ keySegment
        if entries.all fun (key, _) => deeper.isPrefixOf key then
          checkSubtree hash nodes left right fuel subnode deeper entries
        else
          throw .mismatch
      | .branch subnodes value =>
        if value.size ≠ 0 then throw .branchValue
        -- Each entry goes on below the branch, to the child of its next nibble.
        unless entries.all fun (key, _) => pre.length < key.length do throw .mismatch
        let afterRange ← (List.finRange 16).mapM fun nibble =>
          checkSubtree hash nodes left right fuel subnodes[nibble] (pre ++ [nibble])
            (entries.filter fun (key, _) => key[pre.length]? = some nibble)
        return afterRange.any id

/-- Whether the keys are in strictly increasing order. -/
def strictlyIncreasing (keys : List (List Nibble)) : Bool :=
  (keys.zip keys.tail).all fun (a, b) => a < b

/-- Check a range of the trie of `root` from `start`, against its proof.

Each entry is a key and its value in the trie, whose keys are not hashed again.

It returns whether the trie holds a key after the last entry.

With no proof, the entries must be the whole trie.

With no entry, the range runs from the start to the end of the trie.

It then returns false, since the trie holds no key from the start on. -/
def verifyRange (hash : ByteArray → Hash32) (root start : Hash32)
    (entries : List (Hash32 × ByteArray)) (proof : List ByteArray) : Except RangeError Bool := do
  let obj := entries.map fun (key, value) => (bytesToNibbleList ⟨key.toArray⟩, value)
  let left := bytesToNibbleList ⟨start.toArray⟩
  unless strictlyIncreasing (obj.map Prod.fst) do throw .unsorted
  if obj.any fun (key, _) => key < left then throw .beforeStart
  if obj.any fun (_, value) => value.size = 0 then throw .emptyValue
  if proof.isEmpty then
    -- The whole trie: the entries must build the root.
    let trie : Trie := ⟨false, entries.map fun (key, value) => (⟨key.toArray⟩, value)⟩
    match Trie.root hash trie with
    | .ok built => if built = root then return false else throw .mismatch
    | .error (.rlp error) => throw (.rlp error)
    | .error .emptyValue => throw .emptyValue
  else
    let nodes := proof.map fun encoded => (hash encoded, encoded)
    checkSubtree hash nodes left (obj.getLast?.map Prod.fst) (left.length + 2)
      (.bytes ⟨root.toArray⟩) [] obj

end EthLib.Execution.Trie
