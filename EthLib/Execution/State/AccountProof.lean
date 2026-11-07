module

public import EthLib.Execution.State.Account
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

A proof can also show that the address has no account, or that the slot is not set.

The word of a slot that is not set is the storage value `0`, so the answer must give `0`.

EIP-1186 does not say which fields the answer holds for an address without an account.

So the check judges no field of an absent account, and checks no slot of it.

It reports the absence instead, and leaves the meaning of those fields to the caller.

[eip-1186]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-1186.md
[schema]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/state.yaml
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Serialization.Rlp

/-- One slot of the answer: the slot on 32 bytes, the word that the answer gives, and its proof. -/
structure StorageProof where
  /-- The slot, as 32 big-endian bytes. -/
  key : Bytes32
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
  /-- The fields of the answer are not those that the account proof shows. -/
  | accountMismatch
  /-- The proof of the slot at an index, from 0, does not verify against the storage root. -/
  | slot (index : Nat) (error : ProofError)
  /-- The value under the slot at an index is not the RLP form of a word. -/
  | slotEncoding (index : Nat)
  /-- The word that the answer gives for the slot at an index is not the one its proof shows. -/
  | slotMismatch (index : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 501, above the codes of the errors of a proof.

A new constructor takes a new code, so that each code keeps its meaning. -/
def AccountProofError.code : AccountProofError → UInt32
  | .account _ => 501
  | .accountEncoding => 502
  | .accountMismatch => 503
  | .slot .. => 504
  | .slotEncoding _ => 505
  | .slotMismatch _ => 506

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
  /-- The address has no account; the check judges no field and no slot. -/
  | absent
  deriving DecidableEq, Repr

namespace AccountProof

/-- The account that an answer gives, without its storage. -/
def account (p : AccountProof) : Account := ⟨p.nonce, p.balance, p.codeHash⟩

/-- Check the account of an answer against the state root.

It is `true` when the proof shows the account.

The fields and the storage root of the account must then be those of the answer.

It is `false` when the proof shows that the address has no account. -/
def verifyAccount (hash : ByteArray → Hash32) (stateRoot : Hash32) (p : AccountProof) :
    Except AccountProofError Bool := do
  let value ← (verifyProof hash stateRoot true ⟨p.address.toArray⟩ p.accountProof).mapError
    .account
  match value with
  | some bytes =>
    let (account, storageRoot) ← (decodeAccount bytes).mapError fun _ => .accountEncoding
    unless account = p.account ∧ storageRoot = p.storageHash do throw .accountMismatch
    return true
  | none => return false

/-- Check the slot at an index against the storage root.

A set slot must hold the word of the answer.

A slot that is not set is absent, and the answer must give it the word `0`. -/
def verifySlot (hash : ByteArray → Hash32) (storageRoot : Hash32) (index : Nat)
    (s : StorageProof) : Except AccountProofError SlotOutcome := do
  let value ← (verifyProof hash storageRoot true ⟨s.key.toArray⟩ s.proof).mapError
    (.slot index)
  match value with
  | some bytes =>
    let word ← (Codec.decode bytes : Except RlpError U256).mapError fun _ => .slotEncoding index
    unless word = s.value do throw (.slotMismatch index)
    return .set
  | none =>
    unless s.value = 0 do throw (.slotMismatch index)
    return .absent

/-- Check each slot of the answer against its storage root, in order. -/
def verifySlots (hash : ByteArray → Hash32) (storageRoot : Hash32) :
    Nat → List StorageProof → Except AccountProofError (List SlotOutcome)
  | _, [] => pure []
  | index, s :: rest => do
    let outcome ← verifySlot hash storageRoot index s
    return outcome :: (← verifySlots hash storageRoot (index + 1) rest)

/-- Check a whole answer of `eth_getProof` against a state root: the account, then each slot.

The slots are checked only when the account exists. -/
def verify (hash : ByteArray → Hash32) (stateRoot : Hash32) (p : AccountProof) :
    Except AccountProofError AccountOutcome := do
  if ← p.verifyAccount hash stateRoot then
    return .present (← verifySlots hash p.storageHash 0 p.storageProof)
  else
    return .absent

end AccountProof

end EthLib.Execution.State
