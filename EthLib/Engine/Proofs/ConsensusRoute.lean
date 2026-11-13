module

public import EthLib.Engine.Proofs.ExecutionEngine
public import EthLib.Engine.Proofs.NewPayload
import EthLib.Consensus.Proofs.Containers.Requests
import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the JSON of a payload request gets the answer of the execution layer of the beacon chain

The beacon chain reads a payload request directly, through its model of the execution layer.

Between two nodes, the request travels instead as the JSON parameters of the method.

From Bellatrix to Gloas, the method on a chain answers valid exactly when the model accepts.

The last block of the chain must pass the terminal block check, which only the method makes.

A chain without the parent of the payload gives no valid answer on either route.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (BlockChain RecentBlock)

variable {preset : Consensus.Preset} {fork : Fork}

/-! ## The request lists -/

/-- The request lists that the beacon chain makes pass the check of the method. -/
theorem validRequests_of_getExecutionRequestsList
    {requests : Consensus.ExecutionRequests preset fork} {out : List ByteArray}
    (made : Consensus.getExecutionRequestsList requests = .ok out) : validRequests out = true := by
  have size := Consensus.getExecutionRequestsList_size_gt_one made
  refine validRequests_iff.mpr ⟨size, ?_⟩
  have increasing := Consensus.getExecutionRequestsList_increasing made
  rw [List.pairwise_map] at increasing ⊢
  -- Each entry has a first byte, its type, so the types compare as bytes.
  refine increasing.imp_of_mem fun {r s} hr hs hlt => ?_
  have r0 : r.data[0]? = some r[0]! := by
    have pos : 0 < r.data.size := by
      have := size r hr
      simp only [ByteArray.size] at this
      omega
    rw [getElem!_def, getElem?_pos r 0 pos, Array.getElem?_eq_getElem pos]
    rfl
  have s0 : s.data[0]? = some s[0]! := by
    have pos : 0 < s.data.size := by
      have := size s hs
      simp only [ByteArray.size] at this
      omega
    rw [getElem!_def, getElem?_pos s 0 pos, Array.getElem?_eq_getElem pos]
    rfl
  rw [r0, s0] at hlt
  exact Option.some_lt_some.mp hlt

/-! ## The version and the structure at a fork of the beacon chain -/

/-- From Bellatrix to Gloas, the version of the method fits the structure that the request writes.

The version is one of 1 to 5.

Below version 5 it takes the structure version of the fork of the written payload.

From version 5 that fork is Dencun.

Version 5 comes from Gloas, version 4 from Electra, and version 3 from Deneb. -/
private theorem version_facts (hFork : .bellatrix ≤ fork ∧ fork < .hegota) :
    (1 ≤ newPayloadVersion fork ∧ newPayloadVersion fork ≤ 5) ∧
    (newPayloadVersion fork < 5 → acceptsStructure (newPayloadVersion fork)
      (if Fork.dencun ≤ (if Fork.dencun ≤ fork then Fork.dencun
          else if Fork.shapella ≤ fork then Fork.shapella else Fork.paris) then 3
        else if Fork.shapella ≤ (if Fork.dencun ≤ fork then Fork.dencun
          else if Fork.shapella ≤ fork then Fork.shapella else Fork.paris) then 2 else 1) =
        true) ∧
    (5 ≤ newPayloadVersion fork → Fork.dencun ≤ (if Fork.dencun ≤ fork then Fork.dencun
      else if Fork.shapella ≤ fork then Fork.shapella else Fork.paris)) ∧
    (5 ≤ newPayloadVersion fork ↔ .glamsterdam ≤ fork) ∧
    (4 ≤ newPayloadVersion fork ↔ .pectra ≤ fork) ∧
    (3 ≤ newPayloadVersion fork ↔ .dencun ≤ fork) := by
  obtain ⟨low, high⟩ := hFork
  cases fork <;> revert low high <;> decide

/-- From Bellatrix to Gloas, the fork that the request writes its payload at has the same fields.

That fork is Paris, Shapella, or Dencun from Deneb on.

It is from Shapella exactly when the fork is, and from Dencun exactly when the fork is. -/
private theorem shape_facts (hFork : .bellatrix ≤ fork ∧ fork < .hegota) :
    (Fork.shapella ≤ fork ↔ Fork.shapella ≤ (if Fork.dencun ≤ fork then Fork.dencun
      else if Fork.shapella ≤ fork then Fork.shapella else Fork.paris)) ∧
    (Fork.dencun ≤ fork ↔ Fork.dencun ≤ (if Fork.dencun ≤ fork then Fork.dencun
      else if Fork.shapella ≤ fork then Fork.shapella else Fork.paris)) := by
  obtain ⟨low, high⟩ := hFork
  cases fork <;> revert low high <;> decide

/-! ## The block of a payload of the beacon chain -/

/-- A payload at a fork keeps the number, the timestamp and the extra data of its structure. -/
private theorem atFork_common {any : Json.AnyPayload} {f : Fork} {q : ExecutionPayload f}
    (h : any.atFork f = .ok q) :
    q.blockNumber = any.common.blockNumber ∧ q.timestamp = any.common.timestamp ∧
      q.extraData = any.common.extraData := by
  simp only [Json.AnyPayload.atFork, bind_ok_iff] at h
  obtain ⟨_, _, _, _, _, _, result⟩ := h
  cases result
  exact ⟨rfl, rfl, rfl⟩

/-- The structure of a payload of the beacon chain has its number, timestamp and extra data. -/
private theorem common_of_anyPayloadOf {p : Consensus.ExecutionPayload preset fork}
    {any : Json.AnyPayload} (h : anyPayloadOf p = some any) :
    any.common.blockNumber = p.blockNumber ∧ any.common.timestamp = p.timestamp ∧
      any.common.extraData = ⟨p.extraData.data⟩ := by
  unfold anyPayloadOf at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- The block of a payload has the extra data of the payload. -/
private theorem toBlock_extraData {f : Fork} {p : ExecutionPayload f}
    {beacon : Since .dencun f Hash32} {lists : Since .pectra f (List ByteArray)}
    {accessList : Since .glamsterdam f ByteArray} {slot : Since .glamsterdam f UInt64}
    {b : Execution.Blocks.Block f Execution.Transactions.Transaction}
    (h : p.toBlock beacon lists accessList slot = .ok b) : b.header.extraData = p.extraData := by
  simp only [ExecutionPayload.toBlock, ExecutionPayload.toBlockUnchecked,
    ExecutionPayload.toHeader, bind_ok_iff] at h
  obtain ⟨_, ⟨_, -, _, -, _, -, _, ⟨_, -, built⟩, result⟩, _, -, final⟩ := h
  cases final
  cases result
  cases built
  rfl

/-- A payload of the beacon chain has a block exactly when each of its steps succeeds.

The structure of the payload gives a payload at the active fork, which the version must take.

The root, the requests, the access list and the slot decode at that fork.

The block of that payload, with them, must then decode. -/
private theorem payloadBlock_eq_some_iff {config : ChainConfig}
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

/-! ## The checks of the method on decoded parameters -/

/-- A payload that passes the checks has its block at the active fork of its decoded structure.

The block comes from the payload at that fork, with the decoded root, requests, list and slot.

Its blob transactions carry the decoded versioned hashes, when they are given. -/
private theorem of_checkNewPayload_ok {config : ChainConfig} {version : Nat}
    {params : Lean.Json} {any : Json.AnyPayload} {amsterdam : Option (ByteArray × UInt64)}
    {hashes : Option (List Hash32)} {beaconRoot : Option Hash32}
    {requests : Option (List ByteArray)}
    (hDecode : newPayloadParams version params =
      .ok (any, amsterdam, hashes, beaconRoot, requests))
    {checked : CheckedBlock version}
    (h : checkNewPayload config version params = .ok (.ok checked)) :
    config.activeFork any.common.blockNumber.toNat any.common.timestamp.toNat =
        some checked.fork ∧
      ∃ (payload : ExecutionPayload checked.fork) (beacon : Since .dencun checked.fork Hash32)
        (lists : Since .pectra checked.fork (List ByteArray))
        (accessList : Since .glamsterdam checked.fork ByteArray)
        (slot : Since .glamsterdam checked.fork UInt64),
        any.atFork checked.fork = .ok payload ∧
        Json.since "parentBeaconBlockRoot" beaconRoot = .ok beacon ∧
        Json.since "executionRequests" requests = .ok lists ∧
        Json.since "blockAccessList" (amsterdam.map (·.1)) = .ok accessList ∧
        Json.since "slotNumber" (amsterdam.map (·.2)) = .ok slot ∧
        payload.toBlock beacon lists accessList slot = .ok checked.block ∧
        ∀ hs, hashes = some hs →
          ExecutionPayload.blobVersionedHashes checked.block.transactions = hs := by
  unfold checkNewPayload at h
  rw [hDecode] at h
  dsimp only at h
  -- Walk every step: a failing step contradicts the result, and each value read is kept.
  repeat' (first
    | (cases h; done)
    | (have step := bind_ok_iff.mp h
       clear h
       obtain ⟨_, step, h⟩ := step
       try cases step)
    | split at h)
  -- Each success gives the block of the payload, with every value read on the way.
  all_goals
    cases h
    refine ⟨by assumption, _, _, _, _, _, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, fun hs e => ?_⟩
    -- The hashes, when given, passed their check.
    subst e
    simp_all

/-- Decoded parameters whose payload has a block at the active fork pass the checks.

The request lists must pass their check, and the version must take the fork.

The block comes from the payload at that fork, with the decoded root, requests, list and slot.

Its blob transactions must carry the decoded versioned hashes, when they are given. -/
private theorem checkNewPayload_eq_ok {config : ChainConfig} {version : Nat}
    {params : Lean.Json} {any : Json.AnyPayload} {amsterdam : Option (ByteArray × UInt64)}
    {hashes : Option (List Hash32)} {beaconRoot : Option Hash32}
    {requests : Option (List ByteArray)}
    (hDecode : newPayloadParams version params =
      .ok (any, amsterdam, hashes, beaconRoot, requests))
    (hValid : ∀ rs, requests = some rs → validRequests rs = true) {f : Fork}
    (hActive : config.activeFork any.common.blockNumber.toNat any.common.timestamp.toNat = some f)
    (hAccepted : acceptsFork version f = true) {payload : ExecutionPayload f}
    {beacon : Since .dencun f Hash32} {lists : Since .pectra f (List ByteArray)}
    {accessList : Since .glamsterdam f ByteArray} {slot : Since .glamsterdam f UInt64}
    (hPayload : any.atFork f = .ok payload)
    (hBeacon : Json.since "parentBeaconBlockRoot" beaconRoot = .ok beacon)
    (hLists : Json.since "executionRequests" requests = .ok lists)
    (hAccess : Json.since "blockAccessList" (amsterdam.map (·.1)) = .ok accessList)
    (hSlot : Json.since "slotNumber" (amsterdam.map (·.2)) = .ok slot)
    {b : Execution.Blocks.Block f Execution.Transactions.Transaction}
    (hBlock : payload.toBlock beacon lists accessList slot = .ok b)
    (hHashes : ∀ hs, hashes = some hs →
      ExecutionPayload.blobVersionedHashes b.transactions = hs) :
    checkNewPayload config version params = .ok (.ok ⟨f, hAccepted, b⟩) := by
  unfold checkNewPayload
  rw [hDecode]
  dsimp only
  cases requests <;> cases hashes <;>
    simp [hValid, hActive, hAccepted, hPayload, hBeacon, hLists, hAccess, hSlot, hBlock,
      hHashes, bind, Except.bind, pure, Except.pure]

/-- From Bellatrix to Gloas, the written JSON of a request is valid exactly when the model accepts.

The last block of the chain must pass the terminal block check. -/
private theorem valid_iff_accepts_of_json {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {r : Consensus.NewPayloadRequest preset fork}
    {params : Lean.Json} (hFork : .bellatrix ≤ fork ∧ fork < .hegota)
    (hJson : newPayloadRequestJson r = some params)
    (hTerminal : ∀ parent, chain.recent.getLast? = some parent →
      passesTerminalCheck transition totalDifficulty parent = true) :
    (∃ answer, newPayloadOnChain transition totalDifficulty chain (newPayloadVersion fork) params =
        .ok answer ∧ answer.1.status = .valid) ↔
      (executionEngine chain).verifyAndNotifyNewPayload r = .ok true := by
  obtain ⟨hv, layout, dencunShape, five, four, three⟩ := version_facts hFork
  unfold newPayloadRequestJson at hJson
  have hne : newPayloadVersion fork ≠ 0 := by omega
  simp only [hne, ne_eq, not_false_eq_true, guard, ite_true, pure_bind] at hJson
  cases hAny : anyPayloadOf r.executionPayload with
  | none => simp [hAny] at hJson
  | some any =>
  simp only [hAny, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at hJson
  obtain ⟨payload, hPay, requests, hReq, hParams⟩ := hJson
  replace hPay := toOption_eq_some hPay
  replace hReq := toOption_eq_some hReq
  simp only [pure, Option.some.injEq] at hParams
  subst hParams
  generalize hAm : ((sinceValue r.executionPayload.blockAccessList).bind fun accessList =>
    (sinceValue r.executionPayload.slotNumber).bind fun slot =>
      pure (({ data := accessList.data } : ByteArray), slot)) = amsterdam
  -- The access list and the slot are written exactly from Gloas, and read back as the payload's.
  have fiveA : amsterdam.isSome ↔ 5 ≤ newPayloadVersion fork := by
    rw [← hAm, five]
    by_cases gloas : Fork.glamsterdam ≤ fork <;> simp [sinceValue, gloas]
  have dencunA : amsterdam.isSome → Fork.dencun ≤ if Fork.dencun ≤ fork then Fork.dencun
      else if Fork.shapella ≤ fork then Fork.shapella else Fork.paris :=
    fun h => dencunShape (fiveA.mp h)
  have hA1 : amsterdam.map (·.1) =
      (sinceValue r.executionPayload.blockAccessList).map fun list => ⟨list.data⟩ := by
    rw [← hAm]
    by_cases gloas : Fork.glamsterdam ≤ fork <;> simp [sinceValue, gloas]
  have hA2 : amsterdam.map (·.2) = sinceValue r.executionPayload.slotNumber := by
    rw [← hAm]
    by_cases gloas : Fork.glamsterdam ≤ fork <;> simp [sinceValue, gloas]
  -- The root and the request lists are written exactly from their forks.
  have hRoot : (if 3 ≤ newPayloadVersion fork
      then some ((sinceValue r.parentBeaconBlockRoot).getD 0) else none) =
      sinceValue r.parentBeaconBlockRoot := by
    by_cases deneb : Fork.dencun ≤ fork <;> simp [sinceValue, deneb, three]
  have hRequests : (if 4 ≤ newPayloadVersion fork
      then some ((sinceValue requests).getD []) else none) = sinceValue requests := by
    by_cases electra : Fork.pectra ≤ fork <;> simp [sinceValue, electra, four]
  -- The hashes are written from Deneb, as those of the request.
  have hHashes : ∀ hs, (if 3 ≤ newPayloadVersion fork then
      some (((sinceValue r.versionedHashes).map (·.data.toList)).getD []) else none) = some hs →
      ∀ deneb : Fork.dencun ≤ fork, hs = (r.versionedHashes deneb).data.toList := by
    intro hs e deneb
    simp [sinceValue, deneb, three] at e
    exact e.symm
  have hCommon := common_of_anyPayloadOf hAny
  have hPayCommon := atFork_common hPay
  -- With extra data of at most 32 bytes, the parameters read back as the structure written.
  have decode : payload.extraData.size ≤ Execution.Blocks.MAX_EXTRA_DATA_BYTES →
      ∃ any', newPayloadParams (newPayloadVersion fork) (newPayloadParamsJson
          (newPayloadVersion fork) payload amsterdam
          (((sinceValue r.versionedHashes).map (·.data.toList)).getD [])
          ((sinceValue r.parentBeaconBlockRoot).getD 0) ((sinceValue requests).getD [])) =
        .ok (any', amsterdam,
          if 3 ≤ newPayloadVersion fork then
            some (((sinceValue r.versionedHashes).map (·.data.toList)).getD []) else none,
          if 3 ≤ newPayloadVersion fork then
            some ((sinceValue r.parentBeaconBlockRoot).getD 0) else none,
          if 4 ≤ newPayloadVersion fork then some ((sinceValue requests).getD []) else none) ∧
        (∀ g, any'.atFork g = any.atFork g) ∧
        any'.common.blockNumber = r.executionPayload.blockNumber ∧
        any'.common.timestamp = r.executionPayload.timestamp := by
    intro extra
    obtain ⟨any', hDec, hat⟩ := newPayloadParams_json_of_structure payload amsterdam _ _ _ hv
      layout dencunShape extra fiveA
    have hatCommon := atFork_common hat
    exact ⟨any', hDec, atFork_eq_of_atFork hat hPay,
      hatCommon.1.symm.trans (hPayCommon.1.trans hCommon.1),
      hatCommon.2.1.symm.trans (hPayCommon.2.1.trans hCommon.2.1)⟩
  constructor
  · -- A valid answer comes from a block that passed the checks and the state transition.
    rintro ⟨⟨status, reason, next⟩, hRun, hValid⟩
    obtain ⟨block, post, rfl⟩ := (valid_iff_of_newPayloadOnChain hRun).mp hValid
    obtain ⟨-, checked, hC, hST, -⟩ := of_newPayloadOnChain_some hRun
    have hC' := hC
    unfold checkNewPayload at hC'
    obtain ⟨x, hx, -⟩ := bind_ok_iff.mp hC'
    obtain ⟨any', hDec, hAt, hNum, hTime⟩ :=
      decode (extraData_le_of_newPayloadParams_json fiveA dencunA hx)
    obtain ⟨hActive, pl, beacon, lists, acc, slot, hPl, hB, hL, hA, hS, hBlock, hH⟩ :=
      of_checkNewPayload_ok hDec hC
    rw [hNum, hTime] at hActive
    rw [executionEngine_accepts_iff]
    refine ⟨requests, hReq, checked.fork, checked.block, payloadBlock_eq_some_iff.mpr
      ⟨any, hAny, hActive, checked.accepted, pl, beacon, lists, acc, slot,
        (hAt _).symm.trans hPl, by rw [← hRoot]; exact hB, by rw [← hRequests]; exact hL,
        by rw [← hA1]; exact hA, by rw [← hA2]; exact hS, hBlock⟩, fun deneb => ?_, post, hST⟩
    have e : (if 3 ≤ newPayloadVersion fork then
        some (((sinceValue r.versionedHashes).map (·.data.toList)).getD []) else none) =
        some (((sinceValue r.versionedHashes).map (·.data.toList)).getD []) := by
      simp [three.mpr deneb]
    rw [hH _ e]
    exact hHashes _ e deneb
  · -- An accepted request has a block that passes the transition on its parent.
    intro hAccept
    obtain ⟨requests', hReq', f, b, hPB, hBlobs, post, hST⟩ :=
      executionEngine_accepts_iff.mp hAccept
    have same : requests' = requests := Except.ok.inj (hReq'.symm.trans hReq)
    subst requests'

    obtain ⟨any₀, hAny₀, hActive, hAccepted, pl, beacon, lists, acc, slot, hPl, hB, hL, hA, hS,
      hBlock⟩ := payloadBlock_eq_some_iff.mp hPB
    obtain rfl : any₀ = any := Option.some.inj (hAny₀.symm.trans hAny)
    -- The transition checks the extra data and the parent of the block.
    obtain ⟨-, -, hCheck, -⟩ := Execution.Blocks.stateTransition_eq_ok hST
    obtain ⟨parent, hLast, -, hHash⟩ := Execution.Blocks.checkBlock_link hCheck
    obtain ⟨_, -, _, hHeader⟩ := Execution.Blocks.checkBlock_checkHeader hCheck
    have extraB := (Execution.Blocks.checkHeader_eq_ok_iff.mp hHeader).2.2.2.2.2.2.2.2.1
    have extra : payload.extraData.size ≤ Execution.Blocks.MAX_EXTRA_DATA_BYTES := by
      rw [hPayCommon.2.2, ← (atFork_common hPl).2.2, ← toBlock_extraData hBlock]
      exact extraB
    obtain ⟨any', hDec, hAt, hNum, hTime⟩ := decode extra
    have hValidRequests : ∀ rs, (if 4 ≤ newPayloadVersion fork then
        some ((sinceValue requests).getD []) else none) = some rs → validRequests rs = true := by
      intro rs e
      rw [hRequests] at e
      by_cases electra : Fork.pectra ≤ fork
      · simp only [sinceValue, electra, ↓reduceDIte, Option.some.injEq] at e
        subst e
        exact validRequests_of_getExecutionRequestsList
          ((Consensus.NewPayloadRequest.requestsList_eq_ok_iff.mp hReq) electra)
      · simp [sinceValue, electra] at e
    have hHashesB : ∀ hs, (if 3 ≤ newPayloadVersion fork then
        some (((sinceValue r.versionedHashes).map (·.data.toList)).getD []) else none) =
        some hs → ExecutionPayload.blobVersionedHashes b.transactions = hs := by
      intro hs e
      have deneb : Fork.dencun ≤ fork := three.mp (by
        by_contra low
        simp [low] at e)
      rw [hHashes hs e deneb]
      exact hBlobs deneb
    have hC := checkNewPayload_eq_ok hDec hValidRequests (by rw [hNum, hTime]; exact hActive)
      hAccepted ((hAt f).trans hPl) (by rw [hRoot]; exact hB) (by rw [hRequests]; exact hL)
      (by rw [hA1]; exact hA) (by rw [hA2]; exact hS) hBlock hHashesB
    exact ⟨_, newPayloadOnChain_of_stateTransition_ok hC hLast hHash (hTerminal _ hLast) hST,
      rfl⟩

/-- From Bellatrix to Gloas, the JSON of a request is valid exactly when the beacon chain accepts.

The JSON must exist and get a valid answer from the method on a chain.

Acceptance is that of the execution layer model of the beacon chain.

The version of the method is the one that the beacon chain calls at its fork.

The last block of the chain must pass the terminal block check, which the beacon chain skips.

Without the parent of the payload as that last block, both routes refuse the request.

The method then answers syncing or refuses at its checks, and the state transition fails. -/
theorem newPayloadOnChain_valid_iff_accepts {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {r : Consensus.NewPayloadRequest preset fork}
    (hFork : .bellatrix ≤ fork ∧ fork < .hegota)
    (hTerminal : ∀ parent, chain.recent.getLast? = some parent →
      passesTerminalCheck transition totalDifficulty parent = true) :
    (∃ params answer, newPayloadRequestJson r = some params ∧
        newPayloadOnChain transition totalDifficulty chain (newPayloadVersion fork) params =
          .ok answer ∧ answer.1.status = .valid) ↔
      (executionEngine chain).verifyAndNotifyNewPayload r = .ok true := by
  constructor
  · rintro ⟨params, answer, hJson, hRun, hValid⟩
    exact (valid_iff_accepts_of_json hFork hJson hTerminal).mp ⟨answer, hRun, hValid⟩
  · intro hAccept
    -- An accepted request has request lists and a structure, which the JSON writes.
    obtain ⟨requests, hReq, f, b, hPB, -⟩ := executionEngine_accepts_iff.mp hAccept
    obtain ⟨any, hAny, -⟩ := payloadBlock_eq_some_iff.mp hPB
    obtain ⟨hv, -⟩ := version_facts hFork
    have hne : newPayloadVersion fork ≠ 0 := by omega
    -- The structure takes the fork of the request, so it also takes the fork that it is written at.
    obtain ⟨q, hq⟩ := exists_atFork_of_anyPayloadOf hAny
    obtain ⟨hw, hb, he⟩ := exists_atFork_iff.mp ⟨q, hq⟩
    obtain ⟨shapella, dencun⟩ := shape_facts hFork
    obtain ⟨payload, hPay⟩ := exists_atFork_iff.mpr
      ⟨hw.trans shapella, hb.trans dencun, he.trans dencun⟩
    have hJson : newPayloadRequestJson r = some (newPayloadParamsJson (newPayloadVersion fork)
        payload ((sinceValue r.executionPayload.blockAccessList).bind fun accessList =>
          (sinceValue r.executionPayload.slotNumber).bind fun slot =>
            pure (({ data := accessList.data } : ByteArray), slot))
        (((sinceValue r.versionedHashes).map (·.data.toList)).getD [])
        ((sinceValue r.parentBeaconBlockRoot).getD 0) ((sinceValue requests).getD [])) := by
      unfold newPayloadRequestJson
      simp only [hne, ne_eq, not_false_eq_true, guard, ite_true, pure_bind, hAny, hPay, hReq,
        Except.toOption, Option.bind_eq_bind, Option.bind_some]
      rfl
    obtain ⟨answer, hRun, hValid⟩ :=
      (valid_iff_accepts_of_json hFork hJson hTerminal).mpr hAccept
    exact ⟨_, answer, hJson, hRun, hValid⟩

end EthLib.Engine
