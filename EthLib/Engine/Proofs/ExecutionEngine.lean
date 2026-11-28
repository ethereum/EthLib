module

public import EthLib.Consensus.Proofs.Transition.Execution
public import EthLib.Engine.ExecutionEngine
public import EthLib.Engine.Proofs.Block
public import EthLib.Engine.Proofs.Json

/-!
# Proofs: the execution layer of the beacon chain

The execution layer built from the checks of `engine_newPayload` answers from the payload's block.

It accepts a request exactly when the payload has a block at the active fork of the chain.

The beacon chain calls a version of the method at each fork from Bellatrix to Gloas.
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

/-- A payload of the beacon chain has a block exactly when each of its steps succeeds.

The structure of the payload gives a payload at the active fork, which the version must take.

The root, the requests, the access list and the slot decode at that fork.

The block of that payload, with them, must then decode. -/
theorem payloadBlock_eq_some_iff {config : ChainConfig}
    {p : Consensus.ExecutionPayload preset fork} {root : Since .dencun fork Consensus.Root}
    {requests : Since .pectra fork (List ByteArray)} {f : Fork}
    {b : Execution.Blocks.Block f Execution.Transactions.Transaction} :
    payloadBlock config p root requests = some ⟨f, b⟩ ↔
      ∃ any, anyPayloadOf p = some any ∧
        config.activeFork p.blockNumber.toNat p.timestamp.toNat = some f ∧
        acceptsFork (newPayloadVersion fork) f = true ∧
        ∃ (payload : ExecutionPayload f) (beacon : Since .dencun f Hash32)
          (lists : Since .pectra f (List ByteArray)) (accessList : Since .glamsterdam f ByteArray)
          (slot : Since .glamsterdam f UInt64),
          any.atFork f = .ok payload ∧
          Json.since "parentBeaconBlockRoot" (sinceValue root) = .ok beacon ∧
          Json.since "executionRequests" (sinceValue requests) = .ok lists ∧
          Json.since "blockAccessList"
            ((sinceValue p.blockAccessList).map fun list => ⟨list.data⟩) = .ok accessList ∧
          Json.since "slotNumber" (sinceValue p.slotNumber) = .ok slot ∧
          payload.toBlock beacon lists accessList slot = .ok b := by
  unfold payloadBlock
  constructor
  · intro h
    cases hAny : anyPayloadOf p with
    | none => simp [hAny] at h
    | some any =>
    cases hActive : config.activeFork p.blockNumber.toNat p.timestamp.toNat with
    | none => simp [hAny, hActive] at h
    | some active =>
    simp only [hAny, hActive, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hAccepted
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨payload, hPayload, beacon, hBeacon, lists, hLists, accessList, hAccess, slot, hSlot,
        block, hBlock, result⟩ := h
      cases result
      exact ⟨any, rfl, rfl, hAccepted, payload, beacon, lists, accessList, slot,
        toOption_eq_some hPayload, toOption_eq_some hBeacon, toOption_eq_some hLists,
        toOption_eq_some hAccess, toOption_eq_some hSlot, toOption_eq_some hBlock⟩
    · cases h
  · rintro ⟨any, hAny, hActive, hAccepted, payload, beacon, lists, accessList, slot, hPayload,
      hBeacon, hLists, hAccess, hSlot, hBlock⟩
    simp [hAny, hActive, hAccepted, hPayload, hBeacon, hLists, hAccess, hSlot, hBlock,
      Except.toOption]

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
    obtain ⟨payload, hPayload, beacon, -, lists, -, accessList, -, slot, -, block, hBlock,
      result⟩ := h
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
        (∀ deneb : .dencun ≤ fork, b.blobVersionedHashes =
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

/-- From Bellatrix to Fulu, the execution layer of a chain accepts a block's request as follows.

From Electra, the request lists of the requests of the block must be well formed.

The payload of the block must have a block at the active fork of the chain.

From Deneb, that block reads the parent root of the latest block header of the state.

From Deneb, its blob transactions carry the versioned hashes of the commitments of the block.

They are the hashes of those commitments, in the order of the commitments.

The block must pass the state transition of the chain. -/
theorem executionEngine_accepts_newPayloadRequest_iff {chain : BlockChain}
    {state : Consensus.BeaconState preset fork} {body : Consensus.BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} :
    (executionEngine chain).verifyAndNotifyNewPayload (body.newPayloadRequest state bellatrix) =
        .ok true ↔
      ∃ requests : Since .pectra fork (List ByteArray),
        (∀ electra : .pectra ≤ fork,
          Consensus.getExecutionRequestsList (body.executionRequests ⟨electra, bellatrix.2⟩) =
            .ok (requests electra)) ∧
        ∃ f b, payloadBlock chain.config (body.executionPayload bellatrix)
            (fun _ => state.latestBlockHeader.parentRoot) requests = some ⟨f, b⟩ ∧
          (∀ deneb : .dencun ≤ fork, b.blobVersionedHashes =
            (body.blobKzgCommitments ⟨deneb, bellatrix.2⟩).data.toList.map
              Consensus.commitmentVersionedHash) ∧
          ∃ post, stateTransition chain b (checkSeal := false) = .ok post := by
  rw [executionEngine_accepts_iff]
  simp only [Consensus.NewPayloadRequest.requestsList_eq_ok_iff]
  refine exists_congr fun requests => and_congr Iff.rfl <| exists_congr fun f =>
    exists_congr fun b => and_congr Iff.rfl <| and_congr ?_ Iff.rfl
  exact forall_congr' fun deneb => by
    simp [Consensus.BeaconBlockBody.newPayloadRequest]

/-- From Bellatrix on, the version of the method at a fork takes some fork. -/
theorem exists_acceptsFork_newPayloadVersion (h : .bellatrix ≤ fork) :
    ∃ f, acceptsFork (newPayloadVersion fork) f = true := by
  cases fork <;> first
    | exact absurd h (by decide)
    | exact ⟨.paris, by decide⟩
    | exact ⟨.shapella, by decide⟩
    | exact ⟨.dencun, by decide⟩
    | exact ⟨.pectra, by decide⟩
    | exact ⟨.glamsterdam, by decide⟩
    | exact ⟨.hegota, by decide⟩

/-- A payload with a block has it at a fork that the version of the method takes. -/
theorem acceptsFork_of_payloadBlock {config : ChainConfig}
    {p : Consensus.ExecutionPayload preset fork} {root : Since .dencun fork Consensus.Root}
    {requests : Since .pectra fork (List ByteArray)} {f : Fork} {b : Block f Transaction}
    (h : payloadBlock config p root requests = some ⟨f, b⟩) :
    acceptsFork (newPayloadVersion fork) f = true :=
  let ⟨_, _, _, accepted, _⟩ := payloadBlock_eq_some_iff.mp h
  accepted

/-- From Heze, a payload with a block has a block of Bogota. -/
theorem fork_of_payloadBlock_of_heze (heze : .hegota ≤ fork) {config : ChainConfig}
    {p : Consensus.ExecutionPayload preset fork}
    {root : Since .dencun fork Consensus.Root} {requests : Since .pectra fork (List ByteArray)}
    {f : Fork} {b : Block f Transaction} (h : payloadBlock config p root requests = some ⟨f, b⟩) :
    f = .hegota := by
  have version : newPayloadVersion fork = 6 := by simp [newPayloadVersion, heze]
  have accepted := acceptsFork_of_payloadBlock h
  rw [version] at accepted
  simpa [acceptsFork] using accepted

/-- At Gloas, a payload with a block has a block of Amsterdam. -/
theorem fork_of_payloadBlock_of_gloas (gloas : .glamsterdam ≤ fork) (before : fork < .hegota)
    {config : ChainConfig}
    {p : Consensus.ExecutionPayload preset fork}
    {root : Since .dencun fork Consensus.Root} {requests : Since .pectra fork (List ByteArray)}
    {f : Fork} {b : Block f Transaction} (h : payloadBlock config p root requests = some ⟨f, b⟩) :
    f = .glamsterdam := by
  -- Before Heze the fork is Gloas, which calls version 5.
  have heze : ¬.hegota ≤ fork := Nat.not_le.mpr before
  have version : newPayloadVersion fork = 5 := by simp [newPayloadVersion, heze, gloas]
  have accepted := acceptsFork_of_payloadBlock h
  rw [version] at accepted
  simpa [acceptsFork] using accepted

/-- The block of a payload of the beacon chain has the parent hash of the payload.

Its header hashes to the block hash of the payload. -/
theorem header_of_payloadBlock {config : ChainConfig}
    {p : Consensus.ExecutionPayload preset fork} {root : Since .dencun fork Consensus.Root}
    {requests : Since .pectra fork (List ByteArray)} {f : Fork}
    {b : Execution.Blocks.Block f Execution.Transactions.Transaction}
    (h : payloadBlock config p root requests = some ⟨f, b⟩) :
    b.header.parentHash = p.parentHash ∧ b.header.hash = .ok p.blockHash := by
  obtain ⟨any, hAny, -, -, payload, _, _, _, _, hPayload, -, -, -, -, hBlock⟩ :=
    payloadBlock_eq_some_iff.mp h
  -- The structure of the payload, and the payload at the fork, keep both hashes.
  have hp : payload.parentHash = p.parentHash ∧ payload.blockHash = p.blockHash := by
    unfold anyPayloadOf at hAny
    split at hAny
    · cases hAny
      simp only [Json.AnyPayload.atFork, bind_ok_iff] at hPayload
      obtain ⟨_, _, _, _, _, _, result⟩ := hPayload
      cases result
      exact ⟨rfl, rfl⟩
    · cases hAny
  -- The header of the block takes the parent hash of the payload.
  have hParent : b.header.parentHash = payload.parentHash := by
    have h' := hBlock
    simp only [ExecutionPayload.toBlock, ExecutionPayload.toBlockUnchecked,
      ExecutionPayload.toHeader, bind_ok_iff] at h'
    obtain ⟨_, ⟨_, -, _, -, _, -, _, ⟨_, -, built⟩, result⟩, _, -, final⟩ := h'
    cases final
    cases result
    cases built
    rfl
  -- The block hash check makes the hash of the header the block hash of the payload.
  exact ⟨hParent.trans hp.1, (ExecutionPayload.toBlock_shape hBlock).1.trans (by rw [hp.2])⟩

/-- From Gloas, the header of the block of a payload holds the slot number of the payload.

It also holds the Keccak-256 hash of the block access list of the payload. -/
theorem header_of_payloadBlock_of_gloas (gloas : .glamsterdam ≤ fork) {config : ChainConfig}
    {p : Consensus.ExecutionPayload preset fork} {root : Since .dencun fork Consensus.Root}
    {requests : Since .pectra fork (List ByteArray)} {b : Block .glamsterdam Transaction}
    (h : payloadBlock config p root requests = some ⟨.glamsterdam, b⟩) :
    b.header.slotNumber (Nat.le_refl _) = p.slotNumber gloas ∧
      b.header.blockAccessListHash (Nat.le_refl _) =
        Cryptography.Hash.Keccak.keccak256 ⟨(p.blockAccessList gloas).data⟩ := by
  obtain ⟨-, -, -, -, payload, beacon, lists, accessList, slot, -, -, -, hAcc, hSlot, hBlock⟩ :=
    payloadBlock_eq_some_iff.mp h
  have acc := Json.sinceValue_of_since hAcc
  have sl := Json.sinceValue_of_since hSlot
  have pa : sinceValue p.blockAccessList = some (p.blockAccessList gloas) := by
    simp [sinceValue, gloas]
  have ps : sinceValue p.slotNumber = some (p.slotNumber gloas) := by simp [sinceValue, gloas]
  rw [pa] at acc
  rw [ps] at sl
  have acc' : accessList (Nat.le_refl _) = ⟨(p.blockAccessList gloas).data⟩ := by
    simpa [sinceValue] using acc
  have sl' : slot (Nat.le_refl _) = p.slotNumber gloas := by simpa [sinceValue] using sl
  exact ⟨(ExecutionPayload.toBlock_slotNumber hBlock (Nat.le_refl _)).trans sl',
    (ExecutionPayload.toBlock_accessList hBlock (Nat.le_refl _)).2.trans (congrArg _ acc')⟩

/-- At Gloas, the execution layer accepts exactly the requests whose Amsterdam block passes.

The request lists must be well formed, and the block of the payload must exist.

The blob transactions of that block must carry the versioned hashes of the request, in order.

The block must pass the state transition of the chain. -/
theorem executionEngine_accepts_iff_of_gloas (gloas : .glamsterdam ≤ fork)
    (before : fork < .hegota) {chain : BlockChain}
    {request : Consensus.NewPayloadRequest preset fork} :
    (executionEngine chain).verifyAndNotifyNewPayload request = .ok true ↔
      ∃ requests, request.requestsList = .ok requests ∧ ∃ b : Block .glamsterdam Transaction,
        payloadBlock chain.config request.executionPayload request.parentBeaconBlockRoot
          requests = some ⟨.glamsterdam, b⟩ ∧
        b.blobVersionedHashes =
          (request.versionedHashes (Nat.le_trans (by decide) gloas)).data.toList ∧
        ∃ post, stateTransition chain b (checkSeal := false) = .ok post := by
  rw [executionEngine_accepts_iff]
  constructor
  · rintro ⟨requests, found, f, b, hBlock, hashes, post, transition⟩
    obtain rfl := fork_of_payloadBlock_of_gloas gloas before hBlock
    exact ⟨requests, found, b, hBlock, hashes _, post, transition⟩
  · rintro ⟨requests, found, b, hBlock, hashes, post, transition⟩
    exact ⟨requests, found, _, b, hBlock, fun _ => hashes, post, transition⟩

/-! ## A payload at a fork -/

/-- A payload takes a fork exactly when its optional fields are present from their forks on.

The withdrawals must be present exactly from Shapella.

The two blob gas fields must be present exactly from Dencun.

The block access list and the slot number of version 4 are not part of the payload here.

The fork is not checked to be from Paris on. -/
theorem exists_atFork_iff {p : Json.AnyPayload} :
    (∃ q : ExecutionPayload fork, p.atFork fork = .ok q) ↔
      (p.withdrawals.isSome ↔ .shapella ≤ fork) ∧ (p.blobGasUsed.isSome ↔ .dencun ≤ fork) ∧
        (p.excessBlobGas.isSome ↔ .dencun ≤ fork) := by
  constructor
  · rintro ⟨q, h⟩
    simp only [Json.AnyPayload.atFork, bind_ok_iff] at h
    obtain ⟨w, hw, b, hb, e, he, -⟩ := h
    exact ⟨Json.exists_since_iff.mp ⟨w, hw⟩, Json.exists_since_iff.mp ⟨b, hb⟩,
      Json.exists_since_iff.mp ⟨e, he⟩⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨w, hw⟩ := Json.exists_since_iff (what := "withdrawals") |>.mpr h1
    obtain ⟨b, hb⟩ := Json.exists_since_iff (what := "blobGasUsed") |>.mpr h2
    obtain ⟨e, he⟩ := Json.exists_since_iff (what := "excessBlobGas") |>.mpr h3
    simp only [Json.AnyPayload.atFork, hw, hb, he, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩

/-- A payload at a fork reads back the optional fields of the structure that it comes from. -/
theorem sinceValue_of_atFork {p : Json.AnyPayload} {q : ExecutionPayload fork}
    (h : p.atFork fork = .ok q) :
    sinceValue q.withdrawals = p.withdrawals ∧ sinceValue q.blobGasUsed = p.blobGasUsed ∧
      sinceValue q.excessBlobGas = p.excessBlobGas := by
  simp only [Json.AnyPayload.atFork, bind_ok_iff] at h
  obtain ⟨w, hw, b, hb, e, he, h⟩ := h
  cases h
  exact ⟨Json.sinceValue_of_since hw, Json.sinceValue_of_since hb, Json.sinceValue_of_since he⟩

/-- Two structures that give one payload at some fork give the same result at every fork.

The payload at a fork reads only the common fields and the optional fields, never the version. -/
theorem atFork_eq_of_atFork {p₁ p₂ : Json.AnyPayload} {f : Fork} {q : ExecutionPayload f}
    (h₁ : p₁.atFork f = .ok q) (h₂ : p₂.atFork f = .ok q) (g : Fork) :
    p₁.atFork g = p₂.atFork g := by
  obtain ⟨w₁, b₁, e₁⟩ := sinceValue_of_atFork h₁
  obtain ⟨w₂, b₂, e₂⟩ := sinceValue_of_atFork h₂
  -- The common fields are those of the payload at the fork, on both sides.
  have common : p₁.common = p₂.common := by
    obtain ⟨_, c₁, _, _, _⟩ := p₁
    obtain ⟨_, c₂, _, _, _⟩ := p₂
    simp only [Json.AnyPayload.atFork, bind_ok_iff] at h₁ h₂
    obtain ⟨_, _, _, _, _, _, r₁⟩ := h₁
    obtain ⟨_, _, _, _, _, _, r₂⟩ := h₂
    cases r₁
    simp only [pure, Except.pure, Except.ok.injEq, ExecutionPayload.mk.injEq] at r₂
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, -⟩ := r₂
    cases c₁
    cases c₂
    simp_all only
    -- The fields from later forks are absent at Paris on both sides.
    congr <;> funext h <;> exact absurd h (by decide)
  unfold Json.AnyPayload.atFork
  rw [common, ← w₁.symm.trans w₂, ← b₁.symm.trans b₂, ← e₁.symm.trans e₂]

/-- A decoded payload takes a fork exactly when its version is the version of that fork.

Version 1 takes the forks before Shapella.

Version 2 takes Shapella, and version 3 the forks from Dencun.

At Glamsterdam the payload here holds the fields of version 3 of a payload of version 4.

So version 3 also takes Glamsterdam.

The fork is not checked to be from Paris on. -/
theorem exists_atFork_iff_of_anyPayload {j : Lean.Json} {p : Json.AnyPayload}
    (h : Json.anyPayload j = .ok p) :
    (∃ q : ExecutionPayload fork, p.atFork fork = .ok q) ↔
      (p.version = 1 ∧ fork < .shapella) ∨ (p.version = 2 ∧ fork = .shapella) ∨
        (p.version = 3 ∧ .dencun ≤ fork) := by
  obtain ⟨hv, hw, hb, he⟩ := Json.shape_of_anyPayload h
  rw [exists_atFork_iff]
  -- Each version fixes which fields are present, and the order of the forks does the rest.
  rcases hv with hv | hv | hv <;> simp only [hw, hb, he, hv] <;> cases fork <;> decide

/-! ## The structure of a payload of the beacon chain -/

/-- The structure of a payload of the beacon chain has the version and fields of its fork. -/
private theorem facts_of_anyPayloadOf {p : Consensus.ExecutionPayload preset fork}
    {any : Json.AnyPayload} (h : anyPayloadOf p = some any) :
    any.version = (if .dencun ≤ fork then 3 else if .shapella ≤ fork then 2 else 1) ∧
      (any.withdrawals.isSome ↔ .shapella ≤ fork) ∧ (any.blobGasUsed.isSome ↔ .dencun ≤ fork) ∧
        (any.excessBlobGas.isSome ↔ .dencun ≤ fork) := by
  unfold anyPayloadOf at h
  split at h
  · cases h
    refine ⟨rfl, ?_, ?_, ?_⟩
    · by_cases hf : .shapella ≤ fork <;> simp [sinceValue, hf]
    · by_cases hf : .dencun ≤ fork <;> simp [sinceValue, hf]
    · by_cases hf : .dencun ≤ fork <;> simp [sinceValue, hf]
  · cases h

/-- The structure of a payload of the beacon chain has version 1, 2 or 3. -/
theorem version_of_anyPayloadOf {p : Consensus.ExecutionPayload preset fork}
    {any : Json.AnyPayload} (h : anyPayloadOf p = some any) :
    any.version = 1 ∨ any.version = 2 ∨ any.version = 3 := by
  rw [(facts_of_anyPayloadOf h).1]
  split <;> try split
  all_goals simp

/-- The structure of a payload of the beacon chain holds withdrawals exactly from version 2. -/
theorem withdrawals_isSome_iff_of_anyPayloadOf {p : Consensus.ExecutionPayload preset fork}
    {any : Json.AnyPayload} (h : anyPayloadOf p = some any) :
    any.withdrawals.isSome ↔ 2 ≤ any.version := by
  obtain ⟨hv, hw, -⟩ := facts_of_anyPayloadOf h
  rw [hw, hv]
  cases fork <;> decide

/-- The structure of a payload of the beacon chain holds the blob gas used exactly in version 3. -/
theorem blobGasUsed_isSome_iff_of_anyPayloadOf {p : Consensus.ExecutionPayload preset fork}
    {any : Json.AnyPayload} (h : anyPayloadOf p = some any) :
    any.blobGasUsed.isSome ↔ 3 ≤ any.version := by
  obtain ⟨hv, -, hb, -⟩ := facts_of_anyPayloadOf h
  rw [hb, hv]
  cases fork <;> decide

/-- The structure of a payload of the beacon chain has the excess blob gas exactly in version 3. -/
theorem excessBlobGas_isSome_iff_of_anyPayloadOf {p : Consensus.ExecutionPayload preset fork}
    {any : Json.AnyPayload} (h : anyPayloadOf p = some any) :
    any.excessBlobGas.isSome ↔ 3 ≤ any.version := by
  obtain ⟨hv, -, -, he⟩ := facts_of_anyPayloadOf h
  rw [he, hv]
  cases fork <;> decide

/-- The structure of a payload of the beacon chain has the shape of a decoded payload.

Its version is 1, 2 or 3, and its optional fields match that version. -/
theorem shape_of_anyPayloadOf {p : Consensus.ExecutionPayload preset fork}
    {any : Json.AnyPayload} (h : anyPayloadOf p = some any) :
    (any.version = 1 ∨ any.version = 2 ∨ any.version = 3) ∧
      (any.withdrawals.isSome ↔ 2 ≤ any.version) ∧ (any.blobGasUsed.isSome ↔ 3 ≤ any.version) ∧
        (any.excessBlobGas.isSome ↔ 3 ≤ any.version) :=
  ⟨version_of_anyPayloadOf h, withdrawals_isSome_iff_of_anyPayloadOf h,
    blobGasUsed_isSome_iff_of_anyPayloadOf h, excessBlobGas_isSome_iff_of_anyPayloadOf h⟩

/-- The structure of a payload of the beacon chain takes the fork of that payload. -/
theorem exists_atFork_of_anyPayloadOf {p : Consensus.ExecutionPayload preset fork}
    {any : Json.AnyPayload} (h : anyPayloadOf p = some any) :
    ∃ q : ExecutionPayload fork, any.atFork fork = .ok q := by
  obtain ⟨-, hw, hb, he⟩ := facts_of_anyPayloadOf h
  exact exists_atFork_iff.mpr ⟨hw, hb, he⟩

/-- From Gloas, the block hash that gossip computes for an envelope is the hash of its block header.

The block is the one that the execution layer builds from the payload, before its hash check. -/
theorem envelopeBlockHash_eq_of_toBlockUnchecked
    {envelope : Consensus.ExecutionPayloadEnvelope preset fork} {any : Json.AnyPayload}
    {payload : ExecutionPayload fork} {requests : List ByteArray} {block : Block fork Transaction}
    (gloas : .glamsterdam ≤ fork) (converted : anyPayloadOf envelope.payload = some any)
    (shaped : any.atFork fork = .ok payload)
    (listed : Consensus.getExecutionRequestsList envelope.executionRequests = .ok requests)
    (built : payload.toBlockUnchecked (fun _ => envelope.parentBeaconBlockRoot) (fun _ => requests)
      (fun _ => ⟨(envelope.payload.blockAccessList gloas).data⟩)
      (fun _ => envelope.payload.slotNumber gloas) = .ok block) :
    envelopeBlockHash envelope = block.header.hash.toOption := by
  simp only [ExecutionPayload.toBlockUnchecked, bind_ok_iff] at built
  obtain ⟨_, _, root, rooted, hashes, hashed, header, headed, result⟩ := built
  cases result
  simp only [Since.sequence, gloas, ↓reduceDIte] at hashed
  unfold ExecutionPayload.blockAccessListHashOf at hashed
  split at hashed <;>
    simp only [Functor.map, Except.map, reduceCtorEq] at hashed
  cases hashed
  have hr : Execution.Blocks.indexedRoot payload.transactions = .ok root := by
    revert rooted
    cases Execution.Blocks.indexedRoot payload.transactions <;> simp [Except.mapError]
  unfold envelopeBlockHash
  simp only [converted, shaped, listed, hr, sinceValue, gloas, ↓reduceDIte, Except.toOption,
    bind, Option.bind, headed]

/-- From Gloas, a payload that passes the block hash check of the execution layer passes gossip's.

The block hash that gossip computes for its envelope is then the block hash of the payload. -/
theorem envelopeBlockHash_eq_of_toBlock
    {envelope : Consensus.ExecutionPayloadEnvelope preset fork} {any : Json.AnyPayload}
    {payload : ExecutionPayload fork} {requests : List ByteArray} {block : Block fork Transaction}
    (gloas : .glamsterdam ≤ fork) (converted : anyPayloadOf envelope.payload = some any)
    (shaped : any.atFork fork = .ok payload)
    (listed : Consensus.getExecutionRequestsList envelope.executionRequests = .ok requests)
    (built : payload.toBlock (fun _ => envelope.parentBeaconBlockRoot) (fun _ => requests)
      (fun _ => ⟨(envelope.payload.blockAccessList gloas).data⟩)
      (fun _ => envelope.payload.slotNumber gloas) = .ok block) :
    envelopeBlockHash envelope = some envelope.payload.blockHash := by
  simp only [ExecutionPayload.toBlock, bind_ok_iff] at built
  obtain ⟨unchecked, unbuilt, _, checked, -⟩ := built
  rw [envelopeBlockHash_eq_of_toBlockUnchecked gloas converted shaped listed unbuilt]
  -- The structure of the payload, and the payload at the fork, keep the block hash.
  have same : payload.blockHash = envelope.payload.blockHash := by
    unfold anyPayloadOf at converted
    split at converted
    · cases converted
      simp only [Json.AnyPayload.atFork, bind_ok_iff] at shaped
      obtain ⟨_, _, _, _, _, _, result⟩ := shaped
      cases result
      rfl
    · cases converted
  -- The block hash check makes the hash of the header the block hash of the payload.
  simp only [ExecutionPayload.checkBlockHash, bind_ok_iff] at checked
  obtain ⟨computed, hashed, equal⟩ := checked
  split at equal
  · rename_i h
    revert hashed
    cases unchecked.header.hash <;> simp_all [Except.mapError, Except.toOption]
  · cases equal

end EthLib.Engine
