module

public import EthLib.Engine.Json

/-!
# `Engine.TransitionConfiguration`

The method `engine_exchangeTransitionConfigurationV1` of Paris.

Both layers must agree on where proof of work ends.

The method exchanges three of the four values that EIP-3675 makes part of a client's configuration.

They are the terminal total difficulty, the terminal block hash and the terminal block number.

With this method a consensus node sends its own values, and reads those of its execution node.

The execution node answers its configured values, whatever configuration the request holds.

The request holds one parameter, the configuration of the consensus node.

Any other parameters are invalid parameters.

The source leaves the rest to clients, so no definition models it:

- each side should report a mismatch to its user, the execution node ignoring the block number;
- the consensus node should poll the method every 60 seconds;
- the execution node should report a request missing for 120 seconds.

The consensus node may send `0` as the terminal block number, and the decoder accepts it.

While the terminal total difficulty is not decided, both layers must send `2^256 - 2^10`.

From Cancun, the consensus layer must not call the method, and either layer may drop it.

Whether the method still answers after Cancun is a client choice, so the method takes no fork.

EIP-3675 fixes the terminal total difficulty of mainnet, but not its block hash or number.

So EthLib gives no mainnet value of the whole configuration.

The sources, at commit `3284ee8` of execution-apis and `46976b2` of EIPs:

- the structure [`TransitionConfigurationV1`][tc] and the method [itself][method]
- its deprecation in [`cancun.md`][deprecate]
- the [configuration][config] and the [definitions][defs] of EIP-3675

[tc]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#transitionconfigurationv1
[method]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_exchangetransitionconfigurationv1
[deprecate]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#deprecate-engine_exchangetransitionconfigurationv1
[config]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#client-software-configuration
[defs]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#definitions
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc

/-- The settings of the transition to proof of stake, as the method exchanges them. -/
structure TransitionConfiguration where
  /-- The total difficulty at which proof of work ends. -/
  terminalTotalDifficulty : U256
  /-- The hash of the terminal block of proof of work, or zero when none is set. -/
  terminalBlockHash : Hash32
  /-- The number of the block of that hash, which has no effect when the hash is zero. -/
  terminalBlockNumber : UInt64
  deriving DecidableEq, Repr

/-- The terminal total difficulty that both layers send while it is not decided: `2^256 - 2^10`.

Step 7 of the method sets it. -/
def UNDECIDED_TERMINAL_TOTAL_DIFFICULTY : U256 := BitVec.ofNat 256 (2 ^ 256 - 2 ^ 10)

/-- Whether a block of proof of work is terminal: the definition of [EIP-3675].

Its total difficulty reaches the terminal total difficulty, and that of its parent does not.

The totals are natural numbers, since the execution layer puts no bound on them.

The terminal block hash plays no part: EIP-3675 uses it only in the fork choice of proof of work.

[EIP-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#definitions
-/
def isTerminalPowBlock (config : TransitionConfiguration)
    (totalDifficulty parentTotalDifficulty : Nat) : Bool :=
  decide (config.terminalTotalDifficulty.toNat ≤ totalDifficulty) &&
    decide (parentTotalDifficulty < config.terminalTotalDifficulty.toNat)

/-- The three fields of the structure. -/
def transitionConfigurationFields : List String :=
  ["terminalTotalDifficulty", "terminalBlockHash", "terminalBlockNumber"]

/-- The configuration as JSON: two quantities and a 32-byte hash. -/
def transitionConfigurationJson (c : TransitionConfiguration) : Json :=
  Json.mkObj [
    ("terminalTotalDifficulty", quantityJson c.terminalTotalDifficulty.toNat),
    ("terminalBlockHash", dataJson c.terminalBlockHash.toList),
    ("terminalBlockNumber", quantityJson c.terminalBlockNumber.toNat)]

/-- A configuration: an object with exactly the three fields.

The total difficulty is a quantity of 256 bits, and the block number one of 64 bits. -/
def transitionConfigurationOfJson (j : Json) : Decode TransitionConfiguration := do
  let fs ← fields "transitionConfiguration" j
  unless hasExactly fs transitionConfigurationFields do
    invalid "transitionConfiguration: not the fields of the structure"
  let get := field "transitionConfiguration" fs
  return {
    terminalTotalDifficulty := BitVec.ofNat 256
      (← quantity "terminalTotalDifficulty" 256 (← get "terminalTotalDifficulty"))
    terminalBlockHash := ← fixed "terminalBlockHash" 32 (← get "terminalBlockHash")
    terminalBlockNumber := ← uint64 "terminalBlockNumber" (← get "terminalBlockNumber") }

/-- The parameters of the request as JSON: the configuration of the consensus node alone. -/
def exchangeTransitionConfigurationParamsJson (c : TransitionConfiguration) : Json :=
  .arr #[transitionConfigurationJson c]

/-- The method at an execution node with a configuration: decode the request, answer its own.

Step 1 says that the node responds with its configured values, so the answer ignores the request.
-/
def exchangeTransitionConfiguration (own : TransitionConfiguration) (params : Json) :
    Except EngineError TransitionConfiguration := do
  let params ← paramsArray params
  match params with
  | [c] =>
    let _ ← transitionConfigurationOfJson c
    return own
  | _ => invalid s!"params: got {params.length}, expected 1"

end EthLib.Engine
