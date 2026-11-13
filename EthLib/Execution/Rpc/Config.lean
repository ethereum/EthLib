module

public import EthLib.Execution.Rpc.View
public import EthLib.Execution.Blocks.SystemCall
public import EthLib.Networking.Devp2p.ForkId

/-!
# `Execution.Rpc.Config`

The configuration report of [EIP-7910][eip], from the configuration and head of a chain view.

Each configuration has the parameters at its activation, rather than at the head's timestamp.

The configurations are those of the forks by timestamp, the named BPO forks included.

A chain blob schedule that starts at no fork time makes the method fail.

The fork ID is the `FORK_HASH` of [EIP-6122][eip-6122] that the node announces at that activation.

The method requires the genesis hash and timestamp.

It supports Dencun (Cancun) through Glamsterdam (Amsterdam), for the head and every future fork.

Before Cancun, EIP-7910 [permits nonstandard reports][compat]; this definition gives none.

[eip]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7910.md#specification
[compat]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7910.md#backwards-compatibility
[eip-6122]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-6122.md#specification
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Networking.Devp2p (Schedule activationValue)
open EthLib.Serialization.JsonRpc (RpcError quantityJson dataJson optionJson)
open EthLib.Execution.Blocks
open EthLib.Execution.Fees.BlobBaseFee (chainBlobSchedule)

/-- The name that EIP-7910 gives the precompile at an address of the precompile table.

EIP-7910 names every precompile through Osaka.

Any other address has the empty name, and no report uses it. -/
def precompileName : Nat → String
  | 0x01 => "ECREC"
  | 0x02 => "SHA256"
  | 0x03 => "RIPEMD160"
  | 0x04 => "ID"
  | 0x05 => "MODEXP"
  | 0x06 => "BN254_ADD"
  | 0x07 => "BN254_MUL"
  | 0x08 => "BN254_PAIRING"
  | 0x09 => "BLAKE2F"
  | 0x0a => "KZG_POINT_EVALUATION"
  | 0x0b => "BLS12_G1ADD"
  | 0x0c => "BLS12_G1MSM"
  | 0x0d => "BLS12_G2ADD"
  | 0x0e => "BLS12_G2MSM"
  | 0x0f => "BLS12_PAIRING_CHECK"
  | 0x10 => "BLS12_MAP_FP_TO_G1"
  | 0x11 => "BLS12_MAP_FP2_TO_G2"
  | 0x100 => "P256VERIFY"
  | _ => ""

/-- The names of the active precompiles, paired with their addresses. -/
def configPrecompiles (fork : Fork) : List (String × Address) :=
  (Evm.Precompiles.ADDRESSES.filter (Evm.Precompiles.isPrecompile fork)).map
    fun address => (precompileName address, toAddressMasked (BitVec.ofNat 256 address))

/-- The system contracts, using the deposit contract of the configured chain.

EIP-7910 lists them through Prague, and no meta-EIP at the pinned commit lists them after Prague.

From Amsterdam they also hold the builder contracts named by [EIP-8282][builders].

[EIP-7773][eip-7773] schedules EIP-8282 for Amsterdam.

[builders]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8282.md#constants
[eip-7773]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7773.md
-/
def configSystemContracts (config : ChainConfig) (fork : Fork) : List (String × Address) :=
  (if .dencun ≤ fork then [("BEACON_ROOTS_ADDRESS", BEACON_ROOTS_ADDRESS)] else []) ++
  (if .glamsterdam ≤ fork then
    [("BUILDER_DEPOSIT_CONTRACT_ADDRESS", BUILDER_DEPOSIT_CONTRACT_ADDRESS),
      ("BUILDER_EXIT_CONTRACT_ADDRESS", BUILDER_EXIT_CONTRACT_ADDRESS)] else []) ++
  (if .pectra ≤ fork then
    [("CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS", CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS),
      ("DEPOSIT_CONTRACT_ADDRESS", config.depositContractAddress),
      ("HISTORY_STORAGE_ADDRESS", HISTORY_STORAGE_ADDRESS),
      ("WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS", WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS)] else [])

/-- Every fork from Dencun on and every chain blob schedule activate by timestamp or at block 0.

EIP-7910 omits a fork whose activation time is unknown, and assumes a post-Merge chain.

This definition refuses such a chain instead, so that a report never silently drops a fork. -/
def configHasTimestamps (config : ChainConfig) : Bool :=
  (config.activations.all fun (fork, activation) =>
    match activation with
    | .block n => fork < .dencun || n == 0
    | .time _ => true) &&
  config.blobSchedules.all fun (activation, _) =>
    match activation with
    | .block n => n == 0
    | .time _ => true

/-- Every chain blob schedule by timestamp starts at genesis or at the time of a fork.

[EIP-7892][eip-7892] ties each blob schedule to the time of a fork.

[eip-7892]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7892.md#execution-layer-configuration
-/
def configBlobsAtForks (s : Schedule) : Bool :=
  s.config.blobSchedules.all fun (activation, _) =>
    match activation with
    | .block _ => true
    | .time t => t ≤ s.genesisTime || s.times.contains t

/-- The activation time of the configuration at a head: the last fork time it has reached.

It is zero when the head has reached no fork time after genesis. -/
def configCurrentTime (s : Schedule) (timestamp : Nat) : Nat :=
  (0 :: s.times.filter (· ≤ timestamp)).getLast (by simp)

/-- The parameters of one reported configuration.

The fork and its lower bound are internal, and are not members of the JSON object. -/
structure ConfigObject where
  /-- The execution rules at this activation. -/
  fork : Fork
  /-- The fork is Dencun or later, from where EIP-7910 requires standard reports. -/
  sinceDencun : .dencun ≤ fork
  /-- The activation timestamp, or zero for a configuration active at genesis. -/
  activationTime : Nat
  /-- The blob parameters of this configuration. -/
  blobSchedule : BlobSchedule
  /-- The chain's replay-protection identifier. -/
  chainId : UInt64
  /-- The four-byte fork checksum. -/
  forkId : Vector UInt8 4
  /-- The named active precompiles. -/
  precompiles : List (String × Address)
  /-- The named system contracts. -/
  systemContracts : List (String × Address)

/-- A configuration at its activation, using the block number of a post-Merge head.

An activation time of zero stands for genesis, whose timestamp can be nonzero.

No active fork, a zero chain ID or a fork outside Dencun to Glamsterdam gives an error.

So does a passed fork whose block or time is not below 2^64, which a fork ID cannot encode.

The block number stays fixed for future timestamp forks.

The fork ID is then the one of that activation when the head has passed every fork block. -/
def configObject (s : Schedule) (number activationTime : Nat) : Except RpcError ConfigObject := do
  let timestamp := max s.genesisTime activationTime
  let some fork := s.config.activeFork number timestamp
    | throw (resourceNotFound.toRpcError (some (.str "eth_config: no active fork")))
  if h : .dencun ≤ fork then
    unless fork ≤ .glamsterdam do
      throw (methodNotSupported.toRpcError (some (.str "eth_config: unsupported fork")))
    unless s.config.chainId ≠ 0 do
      throw (internalError.toRpcError (some (.str "eth_config: zero chain ID")))
    unless (s.passed number timestamp).all (fun a => activationValue a < 2 ^ 64) do
      throw (internalError.toRpcError (some (.str "eth_config: activation is not below 2^64")))
    return {
      fork := fork
      sinceDencun := h
      activationTime := activationTime
      blobSchedule := chainBlobSchedule s.config fork number timestamp h
      chainId := s.config.chainId
      forkId := (s.forkId number timestamp).hash
      precompiles := configPrecompiles fork
      systemContracts := configSystemContracts s.config fork }
  else
    throw (methodNotSupported.toRpcError (some (.str "eth_config: before Cancun")))

/-- A named address table as a JSON object, which orders its names alphabetically. -/
def configAddressesJson (entries : List (String × Address)) : Json :=
  Json.mkObj (entries.map fun (name, address) => (name, dataJson address.toList))

/-- The configuration object, with the six members required by EIP-7910. -/
def ConfigObject.toJson (c : ConfigObject) : Json :=
  Json.mkObj [
    ("activationTime", Lean.toJson c.activationTime),
    ("blobSchedule", Json.mkObj [
      ("baseFeeUpdateFraction", Lean.toJson c.blobSchedule.baseFeeUpdateFraction),
      ("max", Lean.toJson c.blobSchedule.max), ("target", Lean.toJson c.blobSchedule.target)]),
    ("chainId", quantityJson c.chainId.toNat),
    ("forkId", dataJson c.forkId.toList),
    ("precompiles", configAddressesJson c.precompiles),
    ("systemContracts", configAddressesJson c.systemContracts)]

/-- The current configuration and the next and last future configurations, if any. -/
structure ConfigReport where
  /-- The configuration in effect at the head. -/
  current : ConfigObject
  /-- The next scheduled configuration. -/
  next : Option ConfigObject
  /-- The last scheduled configuration, or none when no future configuration is scheduled. -/
  last : Option ConfigObject

/-- The three members of an EIP-7910 response, with absent future configurations written as null. -/
def ConfigReport.toJson (r : ConfigReport) : Json :=
  Json.mkObj [("current", r.current.toJson), ("next", optionJson ConfigObject.toJson r.next),
    ("last", optionJson ConfigObject.toJson r.last)]

namespace ChainView

/-- The fork-ID schedule of the view, when the view knows its genesis hash and timestamp. -/
def schedule? (v : ChainView) : Option Schedule :=
  v.genesis.map fun (genesisHash, genesisTime) =>
    ⟨genesisHash, genesisTime, v.config, v.mergeForkBlock⟩

/-- The configuration report at the head, which EIP-7910 requires to reflect the latest header.

The genesis context is required even when the node has pruned its genesis block.

The head must have passed every fork block, the Merge fork-ID block included.

The current activation is the last fork time reached by the head, or zero for genesis.

The next and last configurations are those of the first and last fork times after the head. -/
def configReport (v : ChainView) : Except RpcError ConfigReport := do
  let some s := v.schedule?
    | throw (internalError.toRpcError (some (.str "eth_config: genesis context unavailable")))
  unless configHasTimestamps s.config do
    throw (internalError.toRpcError (some (.str "eth_config: activation time is unknown")))
  unless configBlobsAtForks s do
    throw (internalError.toRpcError (some (.str "eth_config: blob schedule without a fork")))
  unless s.blocks.all (· ≤ v.head.block.header.number) do
    throw (internalError.toRpcError (some (.str "eth_config: fork block not reached")))
  let number := v.head.block.header.number
  let timestamp := v.head.block.header.timestamp.toNat
  let current ← configObject s number (configCurrentTime s timestamp)
  match s.times.filter (timestamp < ·) with
  | [] => return ⟨current, none, none⟩
  | first :: rest =>
    let next ← configObject s number first
    let last ← configObject s number ((first :: rest).getLast (by simp))
    return ⟨current, some next, some last⟩

/-- The JSON result of `eth_config`. -/
def ethConfig (v : ChainView) : Except RpcError Json :=
  ConfigReport.toJson <$> v.configReport

end ChainView

end EthLib.Execution.Rpc
