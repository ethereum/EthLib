module

public import EthLib.Execution.Rpc.View
public import EthLib.Execution.Blocks.SystemCall
public import EthLib.Networking.Devp2p.ForkId

/-!
# `Execution.Rpc.Config`

The configuration report of [EIP-7910][eip], from the configuration and head of a chain view.

Each configuration has the parameters at its activation, rather than at the head's timestamp.

Blob-only activations include the chain's own blob schedules, as well as the named BPO forks.

The checksum uses the Merge fork-ID block, not the block where Paris actually activated.

The method requires the genesis hash and timestamp, and supports Dencun through Glamsterdam.

Before Cancun, EIP-7910 permits nonstandard reports; this definition declines to report one.

EIP-7910 names every precompile through Osaka and the system contracts through Prague.

No meta-EIP at the pin lists the system contracts after Prague.

The Amsterdam report also lists the builder contracts named by [EIP-8282][builders].

[eip]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7910.md#specification
[builders]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8282.md#constants
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Networking.Devp2p (Schedule activationValue)
open EthLib.Serialization.JsonRpc (RpcError quantityJson dataJson optionJson)
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions (precompileAddresses)
open EthLib.Execution.Fees.BlobBaseFee (chainBlobSchedule)

/-- Names and numeric addresses, from EIP-7910, in the order of the precompile table. -/
def precompileNames : List (String × Nat) :=
  [("ECREC", 1), ("SHA256", 2), ("RIPEMD160", 3), ("ID", 4), ("MODEXP", 5),
    ("BN254_ADD", 6), ("BN254_MUL", 7), ("BN254_PAIRING", 8), ("BLAKE2F", 9),
    ("KZG_POINT_EVALUATION", 10), ("BLS12_G1ADD", 11), ("BLS12_G1MSM", 12),
    ("BLS12_G2ADD", 13), ("BLS12_G2MSM", 14), ("BLS12_PAIRING_CHECK", 15),
    ("BLS12_MAP_FP_TO_G1", 16), ("BLS12_MAP_FP2_TO_G2", 17), ("P256VERIFY", 256)]

/-- The names of the active precompiles, paired with their addresses. -/
def configPrecompiles (fork : Fork) : List (String × Address) :=
  (precompileNames.filter fun entry => Evm.Precompiles.isPrecompile fork entry.2).map
    fun (name, address) => (name, toAddressMasked (BitVec.ofNat 256 address))

/-- The system contracts, using the deposit contract of the configured chain. -/
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

/-- Configured fork times after genesis, including changes of only the blob schedule.

Sorting and removing duplicates makes a simultaneous fork and blob change one activation. -/
def configTimes (s : Schedule) : List Nat :=
  let blobTimes := s.config.blobSchedules.filterMap fun (activation, _) =>
    match activation with
    | .time t => if s.genesisTime < t then some t else none
    | .block _ => none
  (s.times ++ blobTimes).mergeSort.eraseDups

/-- Every reported activation has a timestamp, except a rule already active at genesis.

EIP-7910 omits unknown activation times and makes no accommodation for proof of work. -/
def configHasTimestamps (config : ChainConfig) : Bool :=
  (config.activations.all fun (fork, activation) =>
    match activation with
    | .block n => fork < .dencun || n == 0
    | .time _ => true) &&
  config.blobSchedules.all fun (activation, _) =>
    match activation with
    | .block n => n == 0
    | .time _ => true

/-- The activations included in a post-Merge configuration's checksum.

Every configured fork block precedes the timestamp forks, as EIP-6122 requires. -/
def configForks (s : Schedule) (timestamp : Nat) : List Activation :=
  s.blocks.map .block ++ ((configTimes s).takeWhile (· ≤ timestamp)).map .time

/-- The parameters of one reported configuration.

The fork and its lower bound are internal, and are not members of the JSON object. -/
structure ConfigObject where
  /-- The execution rules at this activation. -/
  fork : Fork
  /-- EIP-7910 requires standard reports from Cancun on. -/
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

Zero denotes genesis, whose actual timestamp can be nonzero.

A chain ID of zero, missing activation, or rules outside the supported range gives an error.

The block number stays fixed for future timestamp forks, which do not depend on a future block. -/
def configObject (s : Schedule) (number activationTime : Nat) : Except RpcError ConfigObject := do
  let timestamp := max s.genesisTime activationTime
  let some fork := s.config.activeFork number timestamp
    | throw (resourceNotFound.toRpcError (some (.str "eth_config: no active fork")))
  if h : .dencun ≤ fork then
    unless fork ≤ .glamsterdam do
      throw (⟨-32004, "Method not supported",
        some (.str "eth_config: unsupported fork")⟩ : RpcError)
    unless s.config.chainId ≠ 0 do
      throw (internalError.toRpcError (some (.str "eth_config: zero chain ID")))
    unless (configForks s timestamp).all (fun a => activationValue a < 2 ^ 64) do
      throw (internalError.toRpcError (some (.str "eth_config: activation is not below 2^64")))
    return {
      fork := fork
      sinceDencun := h
      activationTime := activationTime
      blobSchedule := chainBlobSchedule s.config fork number timestamp h
      chainId := s.config.chainId
      forkId := Schedule.checksum s.genesisHash (configForks s timestamp)
      precompiles := configPrecompiles fork
      systemContracts := configSystemContracts s.config fork }
  else
    throw (⟨-32004, "Method not supported", some (.str "eth_config: before Cancun")⟩ : RpcError)

/-- A named address table as JSON, with the names sorted alphabetically. -/
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

/-- The configuration report at the head, computed afresh for each request.

The genesis context is required even when the node has pruned its genesis block.

The current activation is the last configured time reached by the head, or zero for genesis. -/
def configReport (v : ChainView) : Except RpcError ConfigReport := do
  let some (genesisHash, genesisTime) := v.genesis
    | throw (internalError.toRpcError (some (.str "eth_config: genesis context unavailable")))
  unless configHasTimestamps v.config do
    throw (internalError.toRpcError (some (.str "eth_config: activation time is unknown")))
  let s : Schedule := ⟨genesisHash, genesisTime, v.config, v.mergeForkBlock⟩
  let timestamp := v.head.block.header.timestamp.toNat
  let times := configTimes s
  let reached := 0 :: times.filter (· ≤ timestamp)
  let current ← configObject s v.head.block.header.number (reached.getLast (by simp [reached]))
  match times.filter (timestamp < ·) with
  | [] => return ⟨current, none, none⟩
  | first :: rest =>
    let next ← configObject s v.head.block.header.number first
    let last ← configObject s v.head.block.header.number
      ((first :: rest).getLast (by simp))
    return ⟨current, some next, some last⟩

/-- The JSON result of `eth_config`. -/
def ethConfig (v : ChainView) : Except RpcError Json :=
  ConfigReport.toJson <$> v.configReport

end ChainView

end EthLib.Execution.Rpc
