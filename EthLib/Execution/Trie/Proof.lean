module

public import EthLib.Execution.Trie.Root
public import EthLib.Serialization.Rlp.Decode

/-!
# `Trie.Proof`

A Merkle proof for one key: the nodes on the path of the key.

A client checks the value of the key against a root alone.

Source: the account and storage proofs of [EIP-1186][eip-1186].

The module checks a proof, and builds the proof of a key from a trie.

The step comments write the trie in the notation of Appendix D of the [Yellow Paper][yp].

[eip-1186]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-1186.md
[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-- Why a Merkle proof is rejected. -/
inductive ProofError where
  /-- The path needs the node of the hash `hash`, which the proof does not hold.

  The hash is none only when a walk runs out of its budget, which no walk does. -/
  | missingNode (hash : Option ByteArray)
  /-- A node of the proof hashes to `actual`, not to the reference `expected` that points to it. -/
  | hashMismatch (expected : ByteArray) (actual : Hash32)
  /-- A node of the proof is not the RLP encoding of an item. -/
  | rlp (error : RlpError)
  /-- The path of a leaf or an extension is not a hex-prefix encoding. -/
  | hexPrefix (error : HexPrefixError)
  /-- An item is not a node.

  A node is a list of two items with a path first, or a list of 17 items with a value last. -/
  | invalidNode
  /-- A reference is a byte string of `size` bytes, neither 0 nor 32. -/
  | invalidReference (size : Nat)
  /-- An extension consumes no nibble, which the composition `c` of Appendix D never builds. -/
  | emptyExtension
  /-- The proof holds `count` nodes that the path does not reach. -/
  | unusedNodes (count : Nat)
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def proofErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Trie.ProofError." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named and each hash in hex. -/
def ProofError.reprPrec : ProofError → Nat → Std.Format
  | .missingNode hash, p => proofErrorFormat "missingNode" [namedArg "hash" hash] p
  | .hashMismatch expected actual, p =>
    proofErrorFormat "hashMismatch" [namedArg "expected" expected, namedArg "actual" actual] p
  | .rlp error, p => proofErrorFormat "rlp" [reprArg error] p
  | .hexPrefix error, p => proofErrorFormat "hexPrefix" [reprArg error] p
  | .invalidNode, p => proofErrorFormat "invalidNode" [] p
  | .invalidReference size, p => proofErrorFormat "invalidReference" [namedArg "size" size] p
  | .emptyExtension, p => proofErrorFormat "emptyExtension" [] p
  | .unusedNodes count, p => proofErrorFormat "unusedNodes" [namedArg "count" count] p

instance : Repr ProofError := ⟨ProofError.reprPrec⟩

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

The codes start at 101, above every code of a trie error, so that the two never meet.

A new constructor takes a new code, so that each code keeps its meaning. -/
def ProofError.code : ProofError → UInt32
  | .missingNode _ => 101
  | .hashMismatch .. => 102
  | .rlp _ => 103
  | .hexPrefix _ => 104
  | .invalidNode => 105
  | .invalidReference _ => 106
  | .emptyExtension => 107
  | .unusedNodes _ => 108

/-- The node that an item writes, read back as a case of the composition `c` of Appendix D. -/
def decodeNode : Item → Except ProofError InternalNode
  -- A leaf or an extension: its path in hex-prefix encoding, then its value or its child.
  | .list [.bytes compact, second] =>
    match compactToNibbleList compact, second with
    | .error error, _ => .error (.hexPrefix error)
    -- `(HP(x, 1), I_1)`: a leaf, whose value is bytes.
    | .ok (path, true), .bytes value => .ok (.leaf path value)
    | .ok (_, true), .list _ => .error .invalidNode
    -- `(HP(x, 0), n(I, j))` with `i ≠ j`: an extension consumes at least one nibble.
    | .ok ([], false), _ => .error .emptyExtension
    | .ok (path, false), child => .ok (.extension path child)
  -- A branch: 16 children, then its value.
  | .list items =>
    -- `(u(0), ..., u(15), v)`: 17 items, with the value `v` as bytes.
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
  -- `n(I, i) = c(I, i)` when `||RLP(c(I, i))|| < 32`: a node held inside its parent.
  --
  -- A child held inside its parent is read from the parent, not from the proof.
  --
  -- EthLib does not check that size, here or for a node held by hash: the root hash binds the node.
  | .list _ => .ok (reference, proof)
  | .bytes digest =>
    -- `n(∅, i) = ()`, no node.
    if digest.size = 0 then
      .ok (reference, proof)
    -- `n(I, i) = KEC(RLP(c(I, i)))`: the next node of the proof must hash to it.
    else if digest.size = 32 then
      match proof with
      | [] => .error (.missingNode (some digest))
      | encoded :: rest =>
        if (hash encoded).toList = digest.data.toList then do
          let item ← (decode encoded).mapError .rlp
          return (item, rest)
        else
          .error (.hashMismatch digest (hash encoded))
    else
      .error (.invalidReference digest.size)

/-- The value that the item `node` gives to the rest `path` of a key, and the proof nodes left.

`none` means that the key is not set. -/
def walk (hash : ByteArray → Hash32) :
    Nat → Item → List Nibble → List ByteArray → Except ProofError (Option ByteArray × List ByteArray)
  -- Why fuel: each call either returns or consumes at least one nibble of `path`.
  --
  -- So a budget of one more than the length of `path` never runs out.
  | 0, _, _, _ => .error (.missingNode none)
  | fuel + 1, node, path, proof =>
    match node with
    -- The empty byte string is no node: the path leaves the trie, and the key is not set.
    | .bytes data => if data.size = 0 then .ok (none, proof) else .error .invalidNode
    | .list _ => do
      match ← decodeNode node with
      -- The path ends at a leaf with the rest of the key: the key is set.
      --
      -- A leaf holds only the key whose rest of path it stores.
      --
      -- A leaf with another rest shows the key not set, as EIP-1186 says.
      | .leaf restOfKey value => return (if restOfKey = path then some value else none, proof)
      | .extension keySegment subnode =>
        -- The path follows the extension when it starts with its run of nibbles.
        if keySegment = path.take keySegment.length then
          let (child, rest) ← resolve hash subnode proof
          walk hash fuel child (path.drop keySegment.length) rest
        else
          -- The path leaves the run of nibbles that every key below shares.
          --
          -- So the path leaves the trie: the key is not set.
          return (none, proof)
      | .branch subnodes value =>
        match path with
        -- The path ends at a branch with a value: the key is set.
        --
        -- The path ends here: `v`, where `()` means that no key ends here.
        | [] => return (if value.size = 0 then none else some value, proof)
        -- Else the child `u(j)` of the next nibble `j`.
        | nibble :: restOfPath =>
          let (child, rest) ← resolve hash subnodes[nibble] proof
          walk hash fuel child restOfPath rest

/-- The root of the empty trie: the hash of `0x80`, the encoding of the empty string. -/
def emptyTrieRoot (hash : ByteArray → Hash32) : Hash32 := hash ⟨#[0x80]⟩

/-- The nodes that the check of a proof against `root` reads.

The empty trie has no node, so a proof of no nodes shows that it holds no key.

Against the root of the empty trie, that proof reads as the encoding of its root node, `0x80`.

Any other proof reads as it is. -/
def readNodes (hash : ByteArray → Hash32) (root : Hash32) : List ByteArray → List ByteArray
  -- A choice of EthLib, which EIP-1186 leaves open.
  --
  -- EIP-1186 says nothing of the empty trie, whose root is the hash of `0x80`, the RLP of no bytes.
  --
  -- EthLib decides that two proofs show any key not set against that root.
  --
  -- One is the proof `[0x80]`, which starts with the encoding of the root, as the EIP describes.
  --
  -- The other is the proof of no nodes, since the empty trie has no node to list.
  --
  -- Against the empty root, a proof of no nodes reads as `[0x80]`.
  | [] => if root = emptyTrieRoot hash then [⟨#[0x80]⟩] else []
  | node :: rest => node :: rest

/-- The value of `key` in the trie of `root`, or `none` when `key` is not set, as `proof` shows.

`secured` says whether the trie hashes its keys, as the state and storage tries do.

The root is always the hash of the root node's encoding, so the proof starts with that encoding.

Against the root of the empty trie, a proof of no nodes also shows that no key is set. -/
def verifyProof (hash : ByteArray → Hash32) (root : Hash32) (secured : Bool) (key : ByteArray)
    (proof : List ByteArray) : Except ProofError (Option ByteArray) := do
  -- The path of the key: `KEC(k)` in nibbles in a secured trie, else `k` in nibbles.
  --
  -- The state and storage tries are secured.
  let path := keyPath hash secured key
  -- EIP-1186 describes a proof as the RLP-serialized nodes from the root, along the key's path.
  --
  -- EIP-1186: the proof starts with the root node, whose hash is the root.
  let (rootNode, rest) ← resolve hash (.bytes ⟨root.toArray⟩) (readNodes hash root proof)
  -- A parent holds a short child inside its own encoding.
  --
  -- It holds a long child by the hash of its encoding.
  --
  -- So the proof lists the root node, then each node on the path that its parent holds by hash.
  let (value, unused) ← walk hash (path.length + 1) rootNode path rest
  -- EIP-1186 lists only the nodes along the path, so EthLib rejects a proof with any other node.
  if unused.isEmpty then
    return value
  else
    .error (.unusedNodes unused.length)

/-- The proof below the node of `obj` at `level`, for the rest `path` of a key.

It lists the encoding of each node on the path that its parent holds by hash.

The budget counts the nodes on the path, and one more than the length of `path` is enough. -/
def proofBelowM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32) :
    Nat → List (List Nibble × ByteArray) → Nat → List Nibble → ExceptT RlpError m (List ByteArray)
  | 0, _, _, _ => pure []
  | fuel + 1, obj, level, path => do
    -- The proof of the child that the path enters, the keys `sub` at `deeper`.
    let child (sub : List (List Nibble × ByteArray)) (deeper : Nat) (restOfPath : List Nibble) := do
      let encoded ← encode (unencoded (← patricializeM hash sub deeper))
      let below ← proofBelowM hash fuel sub deeper restOfPath
      -- A child with `||RLP(c(I, i))|| < 32` sits inside its parent, so the proof lists no node.
      return (if encoded.size < 32 then [] else [encoded]) ++ below
    match ← patricializeM hash obj level with
    -- An extension that the path follows, then its child.
    | some (.extension keySegment _) =>
      if keySegment = path.take keySegment.length then
        child obj (level + keySegment.length) (path.drop keySegment.length)
      else
        return []
    -- A branch, then the child `u(j)` of the next nibble `j`.
    | some (.branch _ _) =>
      match path with
      | [] => return []
      | nibble :: restOfPath =>
        child (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1) restOfPath
    -- No node or a leaf: the path ends here.
    | _ => return []

/-- The proof below a node, with a plain hash. -/
def proofBelow (hash : ByteArray → Hash32) (fuel : Nat) (obj : List (List Nibble × ByteArray))
    (level : Nat) (path : List Nibble) : Except RlpError (List ByteArray) :=
  (proofBelowM (m := Id) hash fuel obj level path).run

/-- The proof of one key of a trie: the encoding of the root node, then the proof below it. -/
def getProofM {m : Type → Type} [Monad m] (hash : ByteArray → m Hash32) (trie : Trie)
    (key : ByteArray) : ExceptT TrieError m (List ByteArray) := do
  let obj ← prepareDataM hash trie.data trie.secured
  let path ← ExceptT.lift (keyPathM hash trie.secured key)
  -- EIP-1186: the proof starts with `RLP(c(I, 0))`, the root node.
  let rootNode ← (patricializeM hash obj 0).adapt .rlp
  let encoded ← ((encode (unencoded rootNode)).mapError .rlp : Except TrieError ByteArray)
  -- Then each node on the path of the key that its parent holds by hash.
  let below ← (proofBelowM hash (path.length + 1) obj 0 path).adapt .rlp
  return encoded :: below

/-- The proof of one key of a trie, with a plain hash. -/
def getProof (hash : ByteArray → Hash32) (trie : Trie) (key : ByteArray) :
    Except TrieError (List ByteArray) :=
  (getProofM (m := Id) hash trie key).run

end EthLib.Execution.Trie
