module

public import EthLib.Execution.State.Account
public import EthLib.Execution.State.Root
public import EthLib.Execution.Trie.Proof

/-!
# `State.AccountProof`

The check of an account proof, the answer of `eth_getProof`.

A light client holds a state root, and asks a node for one account and some of its storage slots.

The node answers with the fields of the account and the proof of the account in the state trie.

It adds a proof of each slot in the storage trie of the account.

The client then checks every claim against the state root alone.

[EIP-1186][eip-1186] defines the answer.

The [`AccountProof` schema][schema] of execution-apis gives its fields.

The account proof is a proof in the secured state trie, under the bytes of the address.

Its value is the RLP form of the account: nonce, balance, storage root and code hash.

Each slot proof is a proof in the secured storage trie, under the slot on 32 bytes.

Its value is the RLP form of the word.

An account with no storage has the root of the empty trie, which has no node.

So the proof of a slot of it may hold no node, and it shows the slot not set.

Likewise, against the empty state, an account proof with no node shows the address has no account.

A proof can also show that the address has no account, or that the slot is not set.

The word of a slot that is not set is the storage value `0`, so the answer must give `0`.

The [text of the method][method] fixes the answer for an address without an account.

Its code hash and storage root are zero, and each slot has the word `0` and no proof node.

Its [fixture][missing] of execution-apis also gives such an address a balance and a nonce of `0`.

A node builds its answer from a state, with the proofs that the tries of the state give.

For an address with no account, it reads no storage and gives that answer.

The [Yellow Paper][yp], §4.1, gives the value under an address, `p(a)`, and under a slot, `L_I`.

[eip-1186]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-1186.md
[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[schema]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/schemas/state.yaml#L1-L62
[method]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/eth/state.yaml#L161-L200
[missing]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/tests/eth_getProof/get-account-proof-missing-account.io
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Serialization.Rlp

/-- A storage key of a request, with the form in which the answer gives it back.

A key of 63 or 64 hex digits comes back as 32 bytes, and any other key as a number. -/
structure StorageKey where
  /-- The slot, as 32 big-endian bytes. -/
  slot : Bytes32
  /-- Whether the answer gives the key back as 32 bytes, rather than as a number. -/
  asBytes : Bool
  deriving DecidableEq

/-- One slot of the answer: the key as the request gave it, the word of the answer, and its proof.
-/
structure StorageProof where
  /-- The key, as the request gave it. -/
  key : StorageKey
  /-- The word that the answer gives for the slot. -/
  value : U256
  /-- The encodings of the nodes on the path of the slot, from the storage root down. -/
  proof : List ByteArray

/-- The answer of `eth_getProof`: the fields of one account, and the proofs of it and of some slots.
-/
structure AccountProof where
  /-- The address of the account. -/
  address : Address
  /-- The nonce that the answer gives. -/
  nonce : Nat
  /-- The balance that the answer gives. -/
  balance : U256
  /-- The code hash that the answer gives. -/
  codeHash : Hash32
  /-- The storage root that the answer gives. -/
  storageHash : Hash32
  /-- The encodings of the nodes on the path of the address, from the state root down. -/
  accountProof : List ByteArray
  /-- The slots, in the order of the answer. -/
  storageProof : List StorageProof

/-- Why an answer of `eth_getProof` does not hold against a state root. -/
inductive AccountProofError where
  /-- The account proof does not verify against the state root. -/
  | account (error : ProofError)
  /-- The value under the address is not the RLP form of an account. -/
  | accountEncoding
  /-- The fields of the answer are not those that the account proof shows.

  For an absent account, a number is not `0`, or a hash is not zero. -/
  | accountMismatch
  /-- The proof of the slot at an index, from 0, does not verify against the storage root. -/
  | slot (index : Nat) (error : ProofError)
  /-- The value under the slot at an index is not the RLP form of a word. -/
  | slotEncoding (index : Nat)
  /-- The slot at `index` has the word `actual` in the answer, not `expected` of its proof.

  A slot that is not set, by its proof or since the account has no storage, has the word `0`.
  -/
  | slotMismatch (index : Nat) (expected actual : U256)
  /-- The slot at an index, from 0, of an absent account has a proof node. -/
  | absentSlotProof (index : Nat)
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def accountProofErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.State.AccountProofError." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named and each word in decimal. -/
def AccountProofError.reprPrec : AccountProofError → Nat → Std.Format
  | .account error, p => accountProofErrorFormat "account" [reprArg error] p
  | .accountEncoding, p => accountProofErrorFormat "accountEncoding" [] p
  | .accountMismatch, p => accountProofErrorFormat "accountMismatch" [] p
  | .slot index error, p =>
    accountProofErrorFormat "slot" [namedArg "index" index, reprArg error] p
  | .slotEncoding index, p => accountProofErrorFormat "slotEncoding" [namedArg "index" index] p
  | .slotMismatch index expected actual, p =>
    accountProofErrorFormat "slotMismatch"
      [namedArg "index" index, namedArg "expected" expected, namedArg "actual" actual] p
  | .absentSlotProof index, p =>
    accountProofErrorFormat "absentSlotProof" [namedArg "index" index] p

instance : Repr AccountProofError := ⟨AccountProofError.reprPrec⟩

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 501, above the codes of the errors of a proof.

A new constructor takes a new code, so that each code keeps its meaning. -/
def AccountProofError.code : AccountProofError → UInt32
  | .account _ => 501
  | .accountEncoding => 502
  | .accountMismatch => 503
  | .slot .. => 504
  | .slotEncoding _ => 505
  | .slotMismatch .. => 506
  | .absentSlotProof _ => 507

/-- What the proof of a slot shows: the slot is set, or it is not. -/
inductive SlotOutcome where
  /-- The slot is set, and holds the word that the answer gives. -/
  | set
  /-- The slot is not set, and the answer gives it the word `0`. -/
  | absent
  deriving DecidableEq, Repr

/-- What the proofs of an answer show. -/
inductive AccountOutcome where
  /-- The account exists with the fields of the answer, and each slot is as the outcome says. -/
  | present (slots : List SlotOutcome)
  /-- No account at the address: zero fields, and each slot the word `0` with no proof node. -/
  | absent
  deriving DecidableEq, Repr

namespace AccountProof

/-- The account that an answer gives, without its storage. -/
def account (p : AccountProof) : Account := ⟨p.nonce, p.balance, p.codeHash⟩

/-- Whether the fields of an answer are those of an address with no account.

The nonce and the balance are `0`, and the code hash and the storage root are zero. -/
def absentFields (p : AccountProof) : Bool :=
  -- The method of execution-apis: a code hash and a storage root of zero for a missing account.
  --
  -- Its fixture for a missing account also gives a balance and a nonce of 0.
  p.nonce == 0 && p.balance == 0 && p.codeHash == Vector.replicate 32 0 &&
    p.storageHash == Vector.replicate 32 0

/-- Check the account of an answer against the state root.

It is `true` when the proof shows the account.

The fields and the storage root of the account must then be those of the answer.

It is `false` when the proof shows that the address has no account.

The fields of the answer must then be those of an address with no account. -/
def verifyAccount (hash : ByteArray → Hash32) (stateRoot : Hash32) (p : AccountProof) :
    Except AccountProofError Bool := do
  -- EIP-1186: the account proof is a proof in the state trie, under `KEC(a)`.
  let value ← (verifyProof hash stateRoot true ⟨p.address.toArray⟩ p.accountProof).mapError
    .account
  match value with
  -- The value is `RLP((sigma[a]_n, sigma[a]_b, sigma[a]_s, sigma[a]_c))`, Yellow Paper §4.1.
  | some bytes =>
    let (account, storageRoot) ← (decodeAccount bytes).mapError fun _ => .accountEncoding
    -- Each of the four fields must equal the one that the answer gives.
    unless account = p.account ∧ storageRoot = p.storageHash do throw .accountMismatch
    return true
  -- The proof shows no account: the answer must give the fields of a missing account.
  | none =>
    unless p.absentFields do throw .accountMismatch
    return false

/-- Check the slot at an index against the storage root.

A set slot must hold the word of the answer.

A slot that is not set is absent, and the answer must give it the word `0`. -/
def verifySlot (hash : ByteArray → Hash32) (storageRoot : Hash32) (index : Nat)
    (s : StorageProof) : Except AccountProofError SlotOutcome := do
  -- EIP-1186: a storage proof is a proof in the storage trie, under `KEC(k)` of the 32-byte slot.
  let value ← (verifyProof hash storageRoot true ⟨s.key.slot.toArray⟩ s.proof).mapError
    (.slot index)
  match value with
  -- The value is `RLP(v)`, `L_I` of Yellow Paper §4.1, and `v` must be the word of the answer.
  | some bytes =>
    let word ← (Codec.decode bytes : Except RlpError U256).mapError fun _ => .slotEncoding index
    unless word = s.value do throw (.slotMismatch index word s.value)
    return .set
  -- A slot that is not set reads 0, so the answer must give 0.
  | none =>
    unless s.value = 0 do throw (.slotMismatch index 0 s.value)
    return .absent

/-- Check each slot of the answer against its storage root, in order. -/
def verifySlots (hash : ByteArray → Hash32) (storageRoot : Hash32) :
    Nat → List StorageProof → Except AccountProofError (List SlotOutcome)
  | _, [] => pure []
  | index, s :: rest => do
    let outcome ← verifySlot hash storageRoot index s
    return outcome :: (← verifySlots hash storageRoot (index + 1) rest)

/-- Check that each slot of an absent account gives the word `0` and no proof node, in order. -/
def verifyAbsentSlots : Nat → List StorageProof → Except AccountProofError Unit
  | _, [] => pure ()
  | index, s :: rest => do
    -- The method of execution-apis: the word 0 and no proof node, for a missing account.
    unless s.value = 0 do throw (.slotMismatch index 0 s.value)
    unless s.proof.isEmpty do throw (.absentSlotProof index)
    verifyAbsentSlots (index + 1) rest

/-- Check a whole answer of `eth_getProof` against a state root: the account, then each slot.

The slots of an existing account are checked against its storage root.

Those of an absent account must each give the word `0` and no proof node. -/
def verify (hash : ByteArray → Hash32) (stateRoot : Hash32) (p : AccountProof) :
    Except AccountProofError AccountOutcome := do
  -- The account against the state root first.
  if ← p.verifyAccount hash stateRoot then
    -- Then each slot against the storage root that the account proof has shown.
    return .present (← verifySlots hash p.storageHash 0 p.storageProof)
  else
    verifyAbsentSlots 0 p.storageProof
    return .absent

/-- The answer of `eth_getProof` that a state gives for an address and some slots.

The account proof is the proof of the address in the state trie.

For an account, each slot gives its word in the storage, and its proof in the storage trie.

An address with no account has zero fields, and each slot the word `0` with no proof node.

It fails when a trie of the state cannot be encoded. -/
def ofState (hash : ByteArray → Hash32) (state : State) (address : Address)
    (keys : List StorageKey) : Except TrieError AccountProof := do
  -- The proof of the address in the state trie, which shows the account or its absence.
  let accountProof ← getProof hash ⟨true, ← stateEntries hash state⟩ ⟨address.toArray⟩
  match state.accounts[address]? with
  -- An account: its fields, its storage root, and the proof of each slot in its storage trie.
  | some account =>
    let storage := state.storage.getD address ∅
    let storageTrie : Trie := ⟨true, ← (storageEntries storage).mapError .rlp⟩
    let storageHash ← root hash storageTrie
    let storageProof ← keys.mapM fun key => do
      let proof ← getProof hash storageTrie ⟨key.slot.toArray⟩
      return (⟨key, storage.getD key.slot 0, proof⟩ : StorageProof)
    return ⟨address, account.nonce, account.balance, account.codeHash, storageHash, accountProof,
      storageProof⟩
  -- No account: the fields of a missing account, and the word 0 with no proof node for each slot.
  | none =>
    return ⟨address, 0, 0, Vector.replicate 32 0, Vector.replicate 32 0, accountProof,
      keys.map fun key => ⟨key, 0, []⟩⟩

end AccountProof

end EthLib.Execution.State
