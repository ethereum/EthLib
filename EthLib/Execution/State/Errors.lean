module

public import EthLib.Execution.Trie.Root
public import EthLib.Serialization.Rlp.Item

/-!
# `State.Errors`

Typed errors for a state given as RLP bytes: a list of accounts.

The C exports pass the code and the message of an error to the bindings.
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Serialization.Rlp

/-- Every way a state given as RLP bytes can be rejected. -/
inductive StateInputError where
  /-- The input is not one RLP item. -/
  | notAnItem (e : RlpError)
  /-- The input is not an RLP list. -/
  | notAList (e : RlpError)
  /-- An account is not a list of address, nonce, balance, code and storage. -/
  | badAccount (e : RlpError)
  /-- An address is given twice. -/
  | repeatedAddress
  /-- The trie of the state has no root. -/
  | noRoot (e : Trie.TrieError)

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def StateInputError.message : StateInputError → String
  | .notAnItem _ => "state is not one RLP item"
  | .notAList _ => "state is not an RLP list"
  | .badAccount _ => "an account is not a list of address, nonce, balance, code and storage"
  | .repeatedAddress => "an address is given twice"
  | .noRoot _ => "state has no root"

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def StateInputError.code : StateInputError → UInt32
  | .notAnItem _ => 1
  | .notAList _ => 2
  | .badAccount _ => 3
  | .repeatedAddress => 4
  | .noRoot _ => 5

end EthLib.Execution.State
