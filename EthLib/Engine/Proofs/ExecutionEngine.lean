module

public import EthLib.Consensus.Proofs.Transition.Execution
public import EthLib.Engine.ExecutionEngine
public import EthLib.Engine.Proofs.Block

/-!
# Proofs: the execution layer of the beacon chain

The execution layer built from the checks of `engine_newPayload` answers from the payload's block.

It accepts a request exactly when the payload has a block at the active fork of the chain.

That block must carry the versioned hashes of the request from Deneb, and pass the state transition.

A payload whose block decodes holds no transaction of no bytes.

The beacon chain calls a version of the method at each fork from Bellatrix to Fulu.

A field from a fork decodes exactly when it is present from that fork on and absent before.

A field decodes from an option exactly when reading the field back gives that option.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Block BlockChain stateTransition)
open EthLib.Execution.Transactions (Transaction decodeTransaction)

variable {preset : Consensus.Preset} {fork : Fork}

/-- Each byte array of a list whose transactions decode has at least one byte. -/
theorem size_pos_of_decodeTransactions {f : Fork} {index : Nat} {bytes : List ByteArray}
    {txs : List Transaction} (h : decodeTransactions f index bytes = .ok txs) :
    ∀ b ∈ bytes, 0 < b.size := by
  induction bytes generalizing index txs with
  | nil => simp
  | cons bytes rest ih =>
    simp only [decodeTransactions, bind_ok_iff, mapError_ok_iff] at h
    obtain ⟨tx, decoded, txs', rest_ok, -⟩ := h
    intro b mem
    rcases List.mem_cons.mp mem with rfl | mem
    · unfold decodeTransaction at decoded
      split at decoded
      · assumption
      · cases decoded
    · exact ih rest_ok b mem

/-- The transactions of the block of a payload are those of the payload, decoded at its fork. -/
theorem decodeTransactions_of_toBlock {f : Fork}
    {p : ExecutionPayload f} {beacon : Since .dencun f Hash32}
    {requests : Since .pectra f (List ByteArray)} {accessList : Since .glamsterdam f ByteArray}
    {slot : Since .glamsterdam f UInt64} {b : Block f Transaction}
    (h : p.toBlock beacon requests accessList slot = .ok b) :
    decodeTransactions f 0 p.transactions = .ok b.transactions := by
  simp only [ExecutionPayload.toBlock, ExecutionPayload.toBlockUnchecked, bind_ok_iff] at h
  obtain ⟨_, ⟨txs, decoded, _, _, _, _, _, _, built⟩, _, _, result⟩ := h
  cases built
  cases result
  exact decoded

private theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α}
    (h : x.toOption = some a) : x = .ok a := by
  cases x <;> simp_all [Except.toOption]

/-- A payload at a fork keeps the transactions of the structure that it comes from. -/
theorem atFork_transactions {any : Json.AnyPayload} {f : Fork} {q : ExecutionPayload f}
    (h : any.atFork f = .ok q) : q.transactions = any.common.transactions := by
  simp only [Json.AnyPayload.atFork, bind_ok_iff] at h
  obtain ⟨_, _, _, _, _, _, result⟩ := h
  cases result
  rfl

/-- The structure of a payload of the beacon chain holds its transactions. -/
theorem common_transactions {p : Consensus.ExecutionPayload preset fork} {any : Json.AnyPayload}
    (h : anyPayloadOf p = some any) : any.common.transactions = beaconTransactions p := by
  unfold anyPayloadOf at h
  split at h
  · cases h
    rfl
  · cases h

/-- The transactions of the block of a payload of the beacon chain are those of the payload. -/
theorem decodeTransactions_of_payloadBlock {config : ChainConfig}
    {p : Consensus.ExecutionPayload preset fork} {root : Since .dencun fork Consensus.Root}
    {requests : Since .pectra fork (List ByteArray)} {f : Fork} {b : Block f Transaction}
    (h : payloadBlock config p root requests = some ⟨f, b⟩) :
    decodeTransactions f 0 (beaconTransactions p) = .ok b.transactions := by
  unfold payloadBlock at h
  cases hAny : anyPayloadOf p with
  | none => simp [hAny] at h
  | some any =>
  cases hActive : config.activeFork p.blockNumber.toNat p.timestamp.toNat with
  | none => simp [hAny, hActive] at h
  | some active =>
  simp only [hAny, hActive, Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨payload, hPayload, beacon, -, lists, -, block, hBlock, result⟩ := h
    cases result
    have decoded := decodeTransactions_of_toBlock (toOption_eq_some hBlock)
    rwa [atFork_transactions (toOption_eq_some hPayload), common_transactions hAny] at decoded
  · cases h

/-- A payload of the beacon chain with a block holds no transaction of no bytes. -/
theorem hasEmptyTransaction_of_payloadBlock {config : ChainConfig}
    {p : Consensus.ExecutionPayload preset fork} {root : Since .dencun fork Consensus.Root}
    {requests : Since .pectra fork (List ByteArray)} {f : Fork} {b : Block f Transaction}
    (h : payloadBlock config p root requests = some ⟨f, b⟩) :
    p.hasEmptyTransaction = false := by
  have pos := size_pos_of_decodeTransactions (decodeTransactions_of_payloadBlock h)
  simp only [beaconTransactions, List.mem_map, Array.mem_toList_iff] at pos
  simp only [Consensus.ExecutionPayload.hasEmptyTransaction, Array.any_eq_false']
  intro tx mem empty
  have := pos _ ⟨tx, mem, rfl⟩
  simp only [ByteArray.size] at this
  simp only [Array.isEmpty_iff_size_eq_zero] at empty
  omega

/-- The execution layer accepts a payload request exactly when the payload has a block.

The request lists must be well formed, and the block of the payload must exist.

From Deneb, the blob transactions of the block must carry the versioned hashes of the request.

The block must pass the state transition of the chain. -/
theorem executionEngine_accepts_iff {chain : BlockChain}
    {request : Consensus.NewPayloadRequest preset fork} :
    (executionEngine chain).verifyAndNotifyNewPayload request = .ok true ↔
      ∃ requests, request.requestsList = .ok requests ∧ ∃ f b,
        payloadBlock chain.config request.executionPayload request.parentBeaconBlockRoot
          requests = some ⟨f, b⟩ ∧
        (∀ deneb : .dencun ≤ fork, ExecutionPayload.blobVersionedHashes b.transactions =
          (request.versionedHashes deneb).data.toList) ∧
        ∃ post, stateTransition chain b (checkSeal := false) = .ok post := by
  unfold executionEngine
  rw [Consensus.ExecutionEngine.verifyAndNotifyNewPayload_default,
    Consensus.verifyAndNotify_ok_true_iff]
  constructor
  · rintro ⟨requests, found, -, -, hashes, notified⟩
    cases hBlock : payloadBlock chain.config request.executionPayload
        request.parentBeaconBlockRoot requests with
    | none => simp [hBlock] at notified
    | some block =>
      obtain ⟨f, b⟩ := block
      simp only [hBlock] at notified
      refine ⟨requests, found, f, b, hBlock, fun deneb => ?_, ?_⟩
      · simpa [found, hBlock, sinceValue, deneb] using hashes deneb
      · cases transition : stateTransition chain b (checkSeal := false) with
        | error => simp [transition, Except.toBool] at notified
        | ok post => exact ⟨post, rfl⟩
  · rintro ⟨requests, found, f, b, hBlock, hashes, post, transition⟩
    refine ⟨requests, found, hasEmptyTransaction_of_payloadBlock hBlock, ?_, fun deneb => ?_, ?_⟩
    · simp [hBlock]
    · simp [found, hBlock, sinceValue, deneb, hashes deneb]
    · simp [hBlock, transition, Except.toBool]

/-- From Bellatrix to Fulu, the version of the method at a fork takes some fork. -/
theorem exists_acceptsFork_newPayloadVersion (h : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    ∃ f, acceptsFork (newPayloadVersion fork) f = true := by
  obtain ⟨low, high⟩ := h
  cases fork <;> first
    | exact absurd low (by decide)
    | exact absurd high (by decide)
    | exact ⟨.paris, by decide⟩
    | exact ⟨.shapella, by decide⟩
    | exact ⟨.dencun, by decide⟩
    | exact ⟨.pectra, by decide⟩

/-- From Gloas, no payload of the beacon chain has a block here. -/
theorem payloadBlock_of_glamsterdam (h : .glamsterdam ≤ fork) {config : ChainConfig}
    {p : Consensus.ExecutionPayload preset fork} {root : Since .dencun fork Consensus.Root}
    {requests : Since .pectra fork (List ByteArray)} :
    payloadBlock config p root requests = none := by
  have zero : newPayloadVersion fork = 0 := by simp [newPayloadVersion, h]
  unfold payloadBlock
  cases anyPayloadOf p <;> cases config.activeFork p.blockNumber.toNat p.timestamp.toNat <;>
    simp [zero, acceptsFork]

/-! ## A field from a fork -/

/-- A field from fork `f` decodes exactly when its presence agrees with `f ≤ fork`. -/
theorem exists_since_iff {α : Type} {f : Fork} {what : String} {o : Option α} :
    (∃ x : Since f fork α, Json.since what o = .ok x) ↔ (o.isSome ↔ f ≤ fork) := by
  -- Each of the four cases either succeeds or fails with an invalid parameter.
  cases o <;> unfold Json.since <;> by_cases h : f ≤ fork <;>
    simp [h, Json.invalid, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] <;>
    exact ⟨_, rfl⟩

/-- Reading back a decoded field from a fork gives the option it was decoded from. -/
theorem sinceValue_of_since {α : Type} {f : Fork} {what : String} {o : Option α}
    {x : Since f fork α} (h : Json.since what o = .ok x) : sinceValue x = o := by
  -- The two cases that fail cannot give the field, and the other two give back the option.
  cases o <;> unfold Json.since at h <;> by_cases hf : f ≤ fork <;>
    simp [hf, Json.invalid, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
  · simp [sinceValue, hf]
  · cases h
    simp [sinceValue, hf]

/-- Decoding the value of a field from a fork gives back the field. -/
theorem since_sinceValue {α : Type} {f : Fork} {what : String} (x : Since f fork α) :
    Json.since what (sinceValue x) = .ok x := by
  unfold sinceValue Json.since
  by_cases hf : f ≤ fork
  · simp only [hf, dite_true, ite_true]
    rfl
  · simp only [hf, dite_false]
    exact congrArg Except.ok (funext fun h => absurd h hf)

/-- A field from a fork decodes from an option exactly when reading it back gives that option. -/
theorem since_eq_ok_iff {α : Type} {f : Fork} {what : String} {o : Option α}
    {x : Since f fork α} : Json.since what o = .ok x ↔ sinceValue x = o :=
  ⟨sinceValue_of_since, fun h => h ▸ since_sinceValue x⟩

end EthLib.Engine
