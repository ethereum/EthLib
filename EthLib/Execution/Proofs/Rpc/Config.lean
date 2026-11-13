module

public import EthLib.Execution.Rpc.Config
public import EthLib.Base.Except
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonLaws

/-!
# Proofs: the configuration report

The precompile names cover exactly the addresses that transaction execution warms.

A reported configuration uses the checksum and blob schedule of its activation.

The BPO forks keep Osaka's precompiles and system contracts.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc (RpcError)
open EthLib.Networking.Devp2p (Schedule activationValue)
open EthLib.Execution.Fees.BlobBaseFee (chainBlobSchedule)
open EthLib.Serialization.JsonRpc (dataJson)

/-- The named precompiles have exactly the addresses that transaction processing uses. -/
theorem configPrecompiles_addresses (fork : Fork) :
    (configPrecompiles fork).map Prod.snd = Transactions.precompileAddresses fork := by
  cases fork <;> rfl

/-- No active precompile name can overwrite another name in the JSON object. -/
theorem configPrecompiles_distinct (fork : Fork) :
    (configPrecompiles fork).Pairwise (fun a b => a.1 ≠ b.1) := by
  cases fork <;> decide

/-- A configured supported fork with an encodable checksum always has a report. -/
theorem configObject_exists {s : Schedule} {number time : Nat} {fork : Fork}
    (active : s.config.activeFork number (max s.genesisTime time) = some fork)
    (since : .dencun ≤ fork) (supported : fork ≤ .glamsterdam)
    (nonzero : s.config.chainId ≠ 0)
    (bounded : (s.passed number (max s.genesisTime time)).all
      (fun a => activationValue a < 2 ^ 64) = true) :
    ∃ c, configObject s number time = .ok c ∧ c.fork = fork := by
  simp [configObject, active, since, supported, nonzero, bounded, pure, Except.pure]

/-- A successful configuration fixes its fork, activation, checksum, blob schedule and addresses. -/
theorem configObject_eq_ok {s : Schedule} {number time : Nat} {c : ConfigObject}
    (made : configObject s number time = .ok c) :
    s.config.activeFork number (max s.genesisTime time) = some c.fork ∧
      c.activationTime = time ∧ c.chainId = s.config.chainId ∧
      c.forkId = (s.forkId number (max s.genesisTime time)).hash ∧
      c.blobSchedule =
        chainBlobSchedule s.config c.fork number (max s.genesisTime time) c.sinceDencun ∧
      c.precompiles = configPrecompiles c.fork ∧
      c.systemContracts = configSystemContracts s.config c.fork := by
  cases active : s.config.activeFork number (max s.genesisTime time) with
  | none =>
    simp [configObject, active, throw, throwThe, MonadExceptOf.throw] at made
  | some fork =>
    by_cases since : .dencun ≤ fork
    · by_cases supported : fork ≤ .glamsterdam
      · by_cases nonzero : s.config.chainId ≠ 0
        · by_cases bounded : (s.passed number (max s.genesisTime time)).all
              (fun a => activationValue a < 2 ^ 64) = true
          · simp [configObject, active, since, supported, nonzero, bounded,
              pure, Except.pure] at made
            cases made
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · simp [configObject, active, since, supported, nonzero, bounded, bind, Except.bind,
              throw, throwThe, MonadExceptOf.throw] at made
        · simp [configObject, active, since, supported, nonzero, bind, Except.bind,
            throw, throwThe, MonadExceptOf.throw] at made
      · simp [configObject, active, since, supported, bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw] at made
    · simp [configObject, active, since, throw, throwThe, MonadExceptOf.throw] at made

/-- The report's fork ID is the `FORK_HASH` that the node announces at the activation. -/
theorem configObject_forkId {s : Schedule} {number time : Nat} {c : ConfigObject}
    (made : configObject s number time = .ok c) :
    c.forkId = (s.forkId number (max s.genesisTime time)).hash :=
  (configObject_eq_ok made).2.2.2.1

/-- A reported precompile list contains every active address and no other address. -/
theorem configObject_precompiles {s : Schedule} {number time : Nat} {c : ConfigObject}
    (made : configObject s number time = .ok c) :
    c.precompiles.map Prod.snd = Transactions.precompileAddresses c.fork := by
  rw [(configObject_eq_ok made).2.2.2.2.2.1]
  exact configPrecompiles_addresses c.fork

/-- The reported blob schedule is the chain's schedule at this configuration's activation. -/
theorem configObject_blobSchedule {s : Schedule} {number time : Nat} {c : ConfigObject}
    (made : configObject s number time = .ok c) :
    c.blobSchedule =
      chainBlobSchedule s.config c.fork number (max s.genesisTime time) c.sinceDencun :=
  (configObject_eq_ok made).2.2.2.2.1

/-- The JSON fork ID is the four-byte `FORK_HASH` that the node announces at the activation. -/
theorem getObjVal_configObject_forkId {s : Schedule} {number time : Nat} {c : ConfigObject}
    (made : configObject s number time = .ok c) :
    c.toJson.getObjVal? "forkId" =
      .ok (dataJson (s.forkId number (max s.genesisTime time)).hash.toList) := by
  have field : c.toJson.getObjVal? "forkId" = .ok (dataJson c.forkId.toList) := by
    unfold ConfigObject.toJson
    exact EthLib.Serialization.Ssz.getObjVal?_mkObj (by simp) (by simp)
  rw [field, configObject_forkId made]

/-- The JSON blob schedule has the three numbers that the reported chain schedule gives. -/
theorem getObjVal_configObject_blobSchedule (c : ConfigObject) :
    c.toJson.getObjVal? "blobSchedule" = .ok (Lean.Json.mkObj [
      ("baseFeeUpdateFraction", Lean.toJson c.blobSchedule.baseFeeUpdateFraction),
      ("max", Lean.toJson c.blobSchedule.max), ("target", Lean.toJson c.blobSchedule.target)]) := by
  unfold ConfigObject.toJson
  exact EthLib.Serialization.Ssz.getObjVal?_mkObj (by simp) (by simp)

/-- Every named active precompile is present with its address in the JSON report. -/
theorem getObjVal_configObject_precompile {s : Schedule} {number time : Nat} {c : ConfigObject}
    (made : configObject s number time = .ok c) {name : String} {address : Address}
    (member : (name, address) ∈ c.precompiles) :
    (c.toJson.getObjVal? "precompiles").bind (·.getObjVal? name) =
      .ok (dataJson address.toList) := by
  have field : c.toJson.getObjVal? "precompiles" = .ok (configAddressesJson c.precompiles) := by
    unfold ConfigObject.toJson
    exact EthLib.Serialization.Ssz.getObjVal?_mkObj (by simp) (by simp)
  rw [field]
  change (configAddressesJson c.precompiles).getObjVal? name = _
  unfold configAddressesJson
  apply EthLib.Serialization.Ssz.getObjVal?_mkObj
  · have distinct := configPrecompiles_distinct c.fork
    rw [← (configObject_eq_ok made).2.2.2.2.2.1] at distinct
    simpa only [List.pairwise_map] using distinct
  · exact List.mem_map.mpr ⟨(name, address), member, rfl⟩

/-- Every named BPO fork keeps Osaka's precompile addresses and names. -/
theorem configPrecompiles_bpo {fork : Fork} (lower : .bpo1 ≤ fork) (upper : fork ≤ .bpo5) :
    configPrecompiles fork = configPrecompiles .fusaka := by
  cases fork <;> first | rfl | contradiction

/-- Every named BPO fork keeps Osaka's system contracts. -/
theorem configSystemContracts_bpo (config : ChainConfig) {fork : Fork}
    (lower : .bpo1 ≤ fork) (upper : fork ≤ .bpo5) :
    configSystemContracts config fork = configSystemContracts config .fusaka := by
  cases fork <;> first | rfl | contradiction

/-- A view without genesis context cannot invent a configuration checksum. -/
theorem ChainView.configReport_no_genesis (v : ChainView) (absent : v.genesis = none) :
    v.configReport = .error
      (internalError.toRpcError (some (.str "eth_config: genesis context unavailable"))) := by
  simp [ChainView.configReport, absent, throw, throwThe, MonadExceptOf.throw]

end EthLib.Execution.Rpc
