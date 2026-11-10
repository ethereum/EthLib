module

public import EthLib.Execution.Network.Snap
public import EthLib.Execution.Trie.Range

/-!
# `Execution.Network.SnapRange`

When an AccountRange or StorageRanges answer of a snap peer is valid.

The source is [`caps/snap.md`][snap] of the devp2p specifications.

[snap]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md

Each range must pass the range check of the trie against its proof.

A range with no proof must be the whole trie, as "GetStorageRanges (0x02)" says.

No signal says that a range reaches the end of its trie, as "GetAccountRange (0x00)" says.

The proof shows it instead.

A peer without the state of the root sends an empty reply, as the two requests say.

A peer without the storage of a requested account does the same, as "GetStorageRanges (0x02)" says.

The checks read no entry and no proof as that reply, never as an empty range.

The checks do not read the limit hash.

A peer may answer past it, as "GetAccountRange (0x00)" says.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Execution.Trie

/-- Why an AccountRange or StorageRanges answer is rejected. -/
inductive SnapRangeError where
  /-- A range fails the range check of its trie. -/
  | range (error : RangeError)
  /-- An account body is not the slim form of an account, byte for byte. -/
  | slimAccount
  /-- A StorageRanges answer holds more ranges than the request names accounts. -/
  | tooManyRanges
  deriving Repr, DecidableEq

/-- The stable code of an error.

A failed range check keeps the code of its own error, from 201 on.

The two other codes follow the codes of a snap message error, so the two kinds never meet.

A new constructor takes a new code, so that each code keeps its meaning. -/
def SnapRangeError.code : SnapRangeError → UInt32
  | .range error => error.code
  | .slimAccount => 3
  | .tooManyRanges => 4

/-- What a valid AccountRange or StorageRanges answer says. -/
inductive RangeAnswer where
  /-- The empty reply of a peer without the state of the root, or of a requested account. -/
  | noState
  /-- The range reaches the end of its trie. -/
  | toEnd
  /-- The trie holds keys after the range. -/
  | more
  deriving Repr, DecidableEq

/-- The answer of a valid range, from whether its trie holds keys after it. -/
def RangeAnswer.ofMore (more : Bool) : RangeAnswer :=
  if more then .more else .toEnd

/-- Check the accounts of an AccountRange answer from `start`, in the state trie of `root`.

Each account is a hash of an address and the account in slim form.

The account must be the slim form itself, and its value in the trie is its full form.

No account and no proof is the empty reply of a peer without the state. -/
def verifyAccountRange (root start : Hash32) (accounts : List RangeEntry)
    (proof : List ByteArray) : Except SnapRangeError RangeAnswer := do
  if accounts.isEmpty && proof.isEmpty then return .noState
  let entries ← accounts.mapM fun entry => do
    let some value := fullAccount entry.data | throw .slimAccount
    return (entry.hash, value)
  let more ← (verifyRange Cryptography.Hash.Keccak.keccak256 root start entries proof).mapError
    .range
  return .ofMore more

/-- Check the ranges of a StorageRanges answer, one for each account from the first.

`roots` holds the storage root of each requested account, in the order of the request.

The data of a slot is its value in the storage trie.

The starting hash crosses the wire with no fixed length.

The caller passes it on 32 bytes, and an empty one as the zero hash.

Each range but the last must be the whole storage of its account, so it takes no proof.

The proof is that of the last range, as "GetStorageRanges (0x02)" says.

That section starts at the starting hash for one account, and asks for whole ranges for several.

So with several accounts, each range starts at the zero hash.

No range and no proof is the empty reply of a peer without the state.

A proof with no range shows that the first account holds no slot from the start on.

Otherwise the answer is that of the last range. -/
def verifyStorageRanges (roots : List Hash32) (start : Hash32) (slots : List (List RangeEntry))
    (proof : List ByteArray) : Except SnapRangeError RangeAnswer := do
  if slots.isEmpty && proof.isEmpty then return .noState
  -- A proof with no range proves an empty range of the first account.
  let slots := if slots.isEmpty then [[]] else slots
  if roots.length < slots.length then throw .tooManyRanges
  let first := if roots.length = 1 then start else Vector.replicate 32 0
  let check (root : Hash32) (range : List RangeEntry) (proof : List ByteArray) :=
    (verifyRange Cryptography.Hash.Keccak.keccak256 root first
      (range.map fun entry => (entry.hash, entry.data)) proof).mapError .range
  let ranges := roots.zip slots
  -- Each range but the last is a whole trie.
  for (root, range) in ranges.dropLast do
    discard <| check root range []
  match ranges.getLast? with
  | some (root, range) => return .ofMore (← check root range proof)
  -- The answer holds a range, so this case never occurs.
  | none => return .noState

end EthLib.Execution.Network
