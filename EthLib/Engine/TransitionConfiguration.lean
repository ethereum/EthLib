module

public import EthLib.Engine.Json

/-!
# `Engine.TransitionConfiguration`

The method `engine_exchangeTransitionConfigurationV1` of Paris.

A consensus node sends its settings of the transition, and reads those of its execution node.

A step comment names the step of the method, as in step 6.

Sources, at commit `1ca0818` of execution-apis and `46976b2` of EIPs:

- the structure [`TransitionConfigurationV1`][tc] and the method [itself][method]
- its deprecation in [`cancun.md`][deprecate]
- the [configuration][config] and the [definitions][defs] of EIP-3675
- the table of [errors][errors] in `common.md`

[tc]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#transitionconfigurationv1
[method]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#engine_exchangetransitionconfigurationv1
[deprecate]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#deprecate-engine_exchangetransitionconfigurationv1
[errors]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/common.md#errors
[config]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#client-software-configuration
[defs]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#definitions
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc

/-- The settings of the transition to proof of stake, as the method exchanges them.

Both layers must agree on where proof of work ends.

Its three fields are three of the four values that EIP-3675 makes part of a client's configuration.

EIP-3675 fixes the terminal total difficulty of mainnet, but not its block hash or number.

So EthLib gives no mainnet value of the whole configuration. -/
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

The totals are natural numbers, since the execution layer puts no bound on them.

The terminal block hash plays no part: EIP-3675 uses it only in the fork choice of proof of work.

[EIP-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#definitions
-/
def isTerminalPowBlock (config : TransitionConfiguration)
    (totalDifficulty parentTotalDifficulty : Nat) : Bool :=
  -- EIP-3675, terminal PoW block: its total difficulty is at least `TERMINAL_TOTAL_DIFFICULTY`.
  --
  -- And the total difficulty of its parent is below `TERMINAL_TOTAL_DIFFICULTY`.
  decide (config.terminalTotalDifficulty.toNat ≤ totalDifficulty) &&
    decide (parentTotalDifficulty < config.terminalTotalDifficulty.toNat)

/-- The three fields of the structure. -/
def transitionConfigurationFields : List String :=
  ["terminalTotalDifficulty", "terminalBlockHash", "terminalBlockNumber"]

/-- The configuration as JSON: two quantities and a 32-byte hash. -/
def transitionConfigurationJson (c : TransitionConfiguration) : Json :=
  Json.mkObj [
    -- `TransitionConfigurationV1`: `terminalTotalDifficulty`, a `QUANTITY` of 256 bits.
    ("terminalTotalDifficulty", quantityJson c.terminalTotalDifficulty.toNat),
    -- `terminalBlockHash`, `DATA` of 32 bytes.
    ("terminalBlockHash", dataJson c.terminalBlockHash.toList),
    -- `terminalBlockNumber`, a `QUANTITY` of 64 bits.
    ("terminalBlockNumber", quantityJson c.terminalBlockNumber.toNat)]

/-- A configuration: an object with exactly the three fields. -/
def transitionConfigurationOfJson (j : Json) : Decode TransitionConfiguration := do
  let fs ← fields "transitionConfiguration" j
  -- `TransitionConfigurationV1`: the three fields.
  --
  -- Not in this method: EthLib rejects any other field, as `engine_newPayloadV3`, step 1, does.
  unless hasExactly fs transitionConfigurationFields do
    invalid "transitionConfiguration: not the fields of the structure"
  let get := field "transitionConfiguration" fs
  return {
    -- `terminalTotalDifficulty`, a `QUANTITY` of 256 bits.
    --
    -- Step 7: while it is not decided, both layers send `2^256 - 2^10`, below `2^256`.
    terminalTotalDifficulty := BitVec.ofNat 256
      (← quantity "terminalTotalDifficulty" 256 (← get "terminalTotalDifficulty"))
    -- `terminalBlockHash`, `DATA` of 32 bytes.
    terminalBlockHash := ← fixed "terminalBlockHash" 32 (← get "terminalBlockHash")
    -- `terminalBlockNumber`, a `QUANTITY` of 64 bits.
    --
    -- Step 6: the consensus node may send `0`, and the decoder accepts it.
    terminalBlockNumber := ← uint64 "terminalBlockNumber" (← get "terminalBlockNumber") }

/-- The parameters of the request as JSON: the configuration of the consensus node alone. -/
def exchangeTransitionConfigurationParamsJson (c : TransitionConfiguration) : Json :=
  -- Request: one parameter, the configuration of the consensus node.
  .arr #[transitionConfigurationJson c]

/-- The method at an execution node with a configuration: decode the request, answer its own. -/
def exchangeTransitionConfiguration (own : TransitionConfiguration) (params : Json) :
    Except EngineError TransitionConfiguration := do
  -- From Cancun, the consensus layer must not call the method, and either layer may drop it.
  --
  -- Whether the method still answers after Cancun is a client choice, so the method takes no fork.
  --
  -- The source leaves steps 2 to 5 to clients, so no definition models them:
  --
  -- - each side should report a mismatch to its user, the execution node ignoring the block number
  -- - the consensus node should poll the method every 60 seconds
  -- - the execution node should report a request missing for 120 seconds
  let params ← paramsArray params
  match params with
  -- Request: one parameter, `transitionConfiguration`, a `TransitionConfigurationV1` object.
  | [c] =>
    let _ ← transitionConfigurationOfJson c
    -- Step 1: the node responds with its configured values of EIP-3675.
    --
    -- So the answer ignores the configuration of the request, once it decodes.
    return own
  -- Any other parameters are `-32602`, invalid params, by the table of errors.
  | _ => invalid s!"params: got {params.length}, expected 1"

end EthLib.Engine
