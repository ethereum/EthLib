module

public import EthLib.Base.U256
public import EthLib.Consensus.Config
public import EthLib.Consensus.Preset
public import EthLib.Cryptography.Hash.Sha256

/-!
# `Consensus.DataAvailability.Custody`

From Fulu, each node stores the columns of a few custody groups, chosen by its node ID.

[EIP-7594](https://eips.ethereum.org/EIPS/eip-7594), "Specification", sets that rule.

The node hashes its ID, then the next IDs, until it has hit enough distinct groups.

A group holds the columns that are congruent to it modulo the number of groups.
-/

@[expose] public section

namespace EthLib.Consensus.DataAvailability

open Base

/-- The ID of a node on the network, a 256-bit integer. -/
abbrev NodeID := U256

/-- The index of a custody group. -/
abbrev CustodyIndex := UInt64

/-- The index of a column of the extended blob matrix. -/
abbrev ColumnIndex := UInt64

/-- Why a custody selection fails. -/
inductive CustodyError where
  /-- The node asks for more groups than exist. -/
  | tooManyGroups (count : UInt64)
  /-- The group index is not below the number of groups. -/
  | groupOutOfRange (group : CustodyIndex)
  /-- The search for distinct groups ran out of steps. -/
  | outOfFuel
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def CustodyError.code : CustodyError → UInt32
  | .tooManyGroups _ => 1
  | .groupOutOfRange _ => 2
  | .outOfFuel => 3

/-- The integer of the first eight bytes, least significant first. -/
def firstUInt64 (bytes : ByteArray) : UInt64 :=
  (List.range 8).foldr (fun i acc => acc <<< 8 ||| (bytes.data.getD i 0).toUInt64) 0

/-- The group that one ID hashes to.

It hashes the 32 bytes of the ID, least significant first, with SHA-256.

Its first eight bytes, least significant first, give an integer modulo the number of groups. -/
def groupOfId (config : Config) (id : NodeID) : CustodyIndex :=
  firstUInt64 (Cryptography.Hash.Sha256.hash ⟨(U256.toBeBytes id).toArray.reverse⟩) %
    config.NUMBER_OF_CUSTODY_GROUPS

/-- The groups of `groups`, then those of the IDs from `id` upward, until `count` are found.

Each new ID takes one step of `fuel`, and the ID after `2^256 - 1` is `0`. -/
def collectGroups (config : Config) (count : Nat) :
    Nat → NodeID → List CustodyIndex → Except CustodyError (List CustodyIndex)
  | fuel, id, groups =>
    if count ≤ groups.length then .ok groups
    else match fuel with
      | 0 => .error .outOfFuel
      | fuel + 1 =>
        let group := groupOfId config id
        collectGroups config count fuel (id + 1)
          (if group ∈ groups then groups else groups ++ [group])

/-- The `count` custody groups of a node, sorted.

No bound on the search is proved: it ends only if the hashes hit `count` distinct groups.

So it takes at most `fuel` steps, and fails when they run out. -/
def getCustodyGroups (config : Config) (nodeId : NodeID) (count : UInt64) (fuel : Nat) :
    Except CustodyError (List CustodyIndex) :=
  if config.NUMBER_OF_CUSTODY_GROUPS < count then .error (.tooManyGroups count)
  else if count = config.NUMBER_OF_CUSTODY_GROUPS then
    .ok ((List.range config.NUMBER_OF_CUSTODY_GROUPS.toNat).map UInt64.ofNat)
  else (collectGroups config count.toNat fuel nodeId []).map List.mergeSort

/-- The columns of one custody group: those congruent to it modulo the number of groups. -/
def computeColumnsForCustodyGroup (config : Config) (preset : Preset) (group : CustodyIndex) :
    Except CustodyError (List ColumnIndex) :=
  let groups := config.NUMBER_OF_CUSTODY_GROUPS
  if group < groups then
    .ok ((List.range (preset.NUMBER_OF_COLUMNS / groups).toNat).map
      fun i => groups * UInt64.ofNat i + group)
  else .error (.groupOutOfRange group)

end EthLib.Consensus.DataAvailability
