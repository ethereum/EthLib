module

public import EthLib.Execution.Rpc.Config
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonLaws

/-!
# Proofs: the configuration report

The precompile names cover exactly the addresses that transaction execution warms.

A reported configuration uses the checksum and blob schedule of its activation.

The BPO forks keep Osaka's precompiles and system contracts.

The current configuration is the last the head reached, and the next and last come after it.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Networking.Devp2p (Schedule activationValue)
open EthLib.Execution.Fees.BlobBaseFee (chainBlobSchedule)
open EthLib.Serialization.JsonRpc (dataJson)

/-- The named precompiles have exactly the addresses that transaction processing uses. -/
theorem configPrecompiles_addresses (fork : Fork) :
    (configPrecompiles fork).map Prod.snd = Transactions.precompileAddresses fork := by
  simp [configPrecompiles, Transactions.precompileAddresses, Function.comp_def]

/-- The precompiles of the table have pairwise different names. -/
theorem precompileName_pairwise :
    Evm.Precompiles.ADDRESSES.Pairwise (fun a b => precompileName a ≠ precompileName b) := by
  decide

/-- No active precompile name can overwrite another name in the JSON object. -/
theorem configPrecompiles_distinct (fork : Fork) :
    (configPrecompiles fork).Pairwise (fun a b => a.1 ≠ b.1) := by
  unfold configPrecompiles
  rw [List.pairwise_map]
  exact precompileName_pairwise.filter _

/-- A supported fork with a nonzero chain ID and activations below 2^64 always has a report. -/
theorem configObject_exists {s : Schedule} {number time : Nat} {fork : Fork}
    (active : s.config.activeFork number (max s.genesisTime time) = some fork)
    (since : .dencun ≤ fork) (supported : fork ≤ .glamsterdam)
    (nonzero : s.config.chainId ≠ 0)
    (bounded : (s.passed number (max s.genesisTime time)).all
      (fun a => activationValue a < 2 ^ 64) = true) :
    ∃ c, configObject s number time = .ok c ∧ c.fork = fork := by
  simp [configObject, active, since, supported, nonzero, bounded, pure, Except.pure]

/-- A successful report fixes its fork, activation, chain ID, checksum, blob schedule and addresses.
-/
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

/-- The JSON blob schedule has the three numbers of the object's blob schedule. -/
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

/-- A view without the genesis hash and timestamp answers with an internal error. -/
theorem ChainView.configReport_no_genesis (v : ChainView) (absent : v.genesis = none) :
    v.configReport = .error
      (internalError.toRpcError (some (.str "eth_config: genesis context unavailable"))) := by
  simp [ChainView.configReport, ChainView.schedule?, absent, throw, throwThe,
    MonadExceptOf.throw]

/-- A successful report comes from the view's schedule, with the configurations it selects.

The schedule has blob schedules at forks, and the head has passed its fork blocks.

The current one is at the last fork time the head has reached, and its fork has a known time.

The next and last ones are at the first and last supported fork times after the head.

They are both absent when no such time exists. -/
theorem ChainView.configReport_eq_ok {v : ChainView} {r : ConfigReport}
    (made : v.configReport = .ok r) :
    ∃ s, v.schedule? = some s ∧ configBlobsAtForks s = true ∧
      s.blocks.all (· ≤ v.head.block.header.number) = true ∧
      configObject s v.head.block.header.number
        (configCurrentTime s v.head.block.header.timestamp.toNat) = .ok r.current ∧
      configTimeKnown s.config r.current.fork = true ∧
      ((configFutureTimes s v.head.block.header.number v.head.block.header.timestamp.toNat = [] ∧
          r.next = none ∧ r.last = none) ∨
        ∃ first rest c c',
          configFutureTimes s v.head.block.header.number v.head.block.header.timestamp.toNat =
            first :: rest ∧
          configObject s v.head.block.header.number first = .ok c ∧
          configObject s v.head.block.header.number ((first :: rest).getLast (by simp)) =
            .ok c' ∧
          r.next = some c ∧ r.last = some c') := by
  unfold ChainView.configReport at made
  rcases hs : v.schedule? with _ | s
  · simp [hs, throw, throwThe, MonadExceptOf.throw] at made
  · rw [hs] at made
    by_cases hb : configBlobsAtForks s = true
    · by_cases hp : s.blocks.all (· ≤ v.head.block.header.number) = true
      case neg =>
        simp [hb, hp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at made
      refine ⟨s, rfl, hb, hp, ?_⟩
      simp only [hb, hp, ite_true] at made
      cases hc : configObject s v.head.block.header.number
          (configCurrentTime s v.head.block.header.timestamp.toNat) with
      | error e => simp [hc, bind, Except.bind] at made
      | ok cur =>
        simp only [hc, bind, Except.bind] at made
        by_cases hk : configTimeKnown s.config cur.fork = true
        case neg =>
          simp [hk, throw, throwThe, MonadExceptOf.throw] at made
        simp only [hk, ite_true] at made
        split at made
        · next heq =>
          simp only [pure, Except.pure, Except.ok.injEq] at made
          subst made
          exact ⟨rfl, hk, .inl ⟨heq, rfl, rfl⟩⟩
        · next first rest heq =>
          cases hn : configObject s v.head.block.header.number first with
          | error e => simp [hn] at made
          | ok c =>
            cases hl : configObject s v.head.block.header.number
                ((first :: rest).getLast (by simp)) with
            | error e => simp [hn, hl] at made
            | ok c' =>
              simp only [hn, hl, pure, Except.pure, Except.ok.injEq] at made
              subst made
              exact ⟨rfl, hk, .inr ⟨first, rest, c, c', heq, hn, hl, rfl, rfl⟩⟩
    · simp [hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at made

/-- A future fork time of the report is exactly a fork time after the head that the node supports. -/
theorem mem_configFutureTimes {s : Schedule} {number timestamp time : Nat} :
    time ∈ configFutureTimes s number timestamp ↔
      time ∈ s.times ∧ timestamp < time ∧ configSupported s number time = true := by
  simp [configFutureTimes]

/-- The next and last configurations are both present or both absent. -/
theorem ChainView.configReport_next_eq_none_iff {v : ChainView} {r : ConfigReport}
    (made : v.configReport = .ok r) : r.next = none ↔ r.last = none := by
  obtain ⟨s, -, -, -, -, -, h | ⟨_, _, c, c', -, -, -, hn, hl⟩⟩ :=
    ChainView.configReport_eq_ok made
  · simp [h.2.1, h.2.2]
  · simp [hn, hl]

/-- The activation time of the current configuration is at most the head's timestamp. -/
theorem configCurrentTime_le (s : Schedule) (timestamp : Nat) :
    configCurrentTime s timestamp ≤ timestamp := by
  unfold configCurrentTime
  have mem := List.getLast_mem (l := 0 :: s.times.filter (· ≤ timestamp)) (by simp)
  rcases List.mem_cons.1 mem with h | h
  · rw [h]
    exact Nat.zero_le _
  · simpa using (List.mem_filter.1 h).2

/-- The current configuration activates no later than the head. -/
theorem ChainView.configReport_current_le {v : ChainView} {r : ConfigReport}
    (made : v.configReport = .ok r) :
    r.current.activationTime ≤ v.head.block.header.timestamp.toNat := by
  obtain ⟨s, -, -, -, hc, -, -⟩ := ChainView.configReport_eq_ok made
  rw [(configObject_eq_ok hc).2.1]
  exact configCurrentTime_le s _

/-- The next configuration activates after the head. -/
theorem ChainView.configReport_next_after {v : ChainView} {r : ConfigReport} {c : ConfigObject}
    (made : v.configReport = .ok r) (next : r.next = some c) :
    v.head.block.header.timestamp.toNat < c.activationTime := by
  obtain ⟨s, -, -, -, -, -, h | ⟨first, rest, c₁, c₂, hf, hn, -, hnext, -⟩⟩ :=
    ChainView.configReport_eq_ok made
  · rw [h.2.1] at next
    cases next
  · rw [hnext, Option.some.injEq] at next
    subst next
    rw [(configObject_eq_ok hn).2.1]
    have mem : first ∈ configFutureTimes s v.head.block.header.number
        v.head.block.header.timestamp.toNat := by
      rw [hf]
      exact List.mem_cons_self
    exact (mem_configFutureTimes.1 mem).2.1

/-- The last configuration activates after the head. -/
theorem ChainView.configReport_last_after {v : ChainView} {r : ConfigReport} {c : ConfigObject}
    (made : v.configReport = .ok r) (last : r.last = some c) :
    v.head.block.header.timestamp.toNat < c.activationTime := by
  obtain ⟨s, -, -, -, -, -, h | ⟨first, rest, c₁, c₂, hf, -, hl, -, hlast⟩⟩ :=
    ChainView.configReport_eq_ok made
  · rw [h.2.2] at last
    cases last
  · rw [hlast, Option.some.injEq] at last
    subst last
    rw [(configObject_eq_ok hl).2.1]
    have mem : (first :: rest).getLast (by simp) ∈
        configFutureTimes s v.head.block.header.number v.head.block.header.timestamp.toNat := by
      rw [hf]
      exact List.getLast_mem _
    exact (mem_configFutureTimes.1 mem).2.1

end EthLib.Execution.Rpc
