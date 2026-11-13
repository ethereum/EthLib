module

public import EthLib.Engine.ForkchoiceUpdated
public import EthLib.Execution.Rpc.View
public import EthLib.Engine.Proofs.ForkchoiceUpdated

/-!
# Proofs: the tags of the JSON-RPC API agree with the last forkchoice update

A forkchoice update that sets a new head has its nonzero safe and finalized blocks on its chain.

Take a chain view whose canonical blocks are exactly that chain, with the hashes of the update.

Then the safe and the finalized tags resolve to the blocks that the update named.

The head of the view is the head of the update.

The safe and the finalized results need a nonzero hash.

The Engine API allows a zero hash until the transition block is finalized.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Rpc (ChainView)

variable {tree : PayloadTree} {finalized : Option Hash32} {state : ForkchoiceState}
  {status : PayloadStatus} {v : ChainView}

/-- A nonzero hash on the chain of the head names a canonical block of a view of that chain. -/
private theorem exists_canonical {hash : Hash32}
    (hcanon : (v.canonical.map (·.hash)).reverse = chainOf tree state.headBlockHash)
    (h : onChain tree state.headBlockHash hash = true) (nonzero : hash ≠ ZERO_HASH) :
    ∃ r, v.canonicalByHash hash = some r := by
  have hc := mem_chainOf_of_onChain h nonzero
  rw [← hcanon] at hc
  obtain ⟨r, hr, hrh⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
  cases hf : v.canonicalByHash hash with
  | some r' => exact ⟨r', rfl⟩
  | none =>
    have := List.find?_eq_none.mp hf r hr
    simp [hrh] at this

/-- After an update that sets a new head, the head of a view of its chain is that head. -/
theorem head_hash_of_forkchoiceUpdated
    (fcu : forkchoiceUpdated tree finalized state = .ok (status, some state.headBlockHash))
    (hcanon : (v.canonical.map (·.hash)).reverse = chainOf tree state.headBlockHash) :
    v.head.hash = state.headBlockHash := by
  obtain ⟨p, hp⟩ := exists_lookup_of_forkchoiceUpdated fcu
  have h1 := congrArg List.head? hcanon
  rw [List.head?_reverse, chainOf_head hp, List.getLast?_map] at h1
  have : v.canonical.getLast? = some v.head := by
    simp [ChainView.head, List.getLast?_eq_some_getLast v.nonempty]
  rw [this] at h1
  simpa using h1

/-- After an update that sets a new head, the safe tag names its safe block.

The view holds the chain of the head and the update's safe hash, which must not be zero. -/
theorem resolve_safe_of_forkchoiceUpdated
    (fcu : forkchoiceUpdated tree finalized state = .ok (status, some state.headBlockHash))
    (hcanon : (v.canonical.map (·.hash)).reverse = chainOf tree state.headBlockHash)
    (hsafe : v.safe = some state.safeBlockHash) (nonzero : state.safeBlockHash ≠ ZERO_HASH) :
    ∃ r, v.resolve (.tag .safe) = .ok (some r) ∧ r.hash = state.safeBlockHash := by
  obtain ⟨-, hs, -⟩ := onChain_of_forkchoiceUpdated fcu
  obtain ⟨r, hr⟩ := exists_canonical hcanon hs nonzero
  refine ⟨r, ?_, ?_⟩
  · simp [ChainView.resolve, ChainView.byTag, hsafe, hr]
  · simpa using (List.find?_some hr)

/-- After an update that sets a new head, the finalized tag names its finalized block.

The view holds the chain of the head and the update's finalized hash, which must not be zero. -/
theorem resolve_finalized_of_forkchoiceUpdated
    (fcu : forkchoiceUpdated tree finalized state = .ok (status, some state.headBlockHash))
    (hcanon : (v.canonical.map (·.hash)).reverse = chainOf tree state.headBlockHash)
    (hfinalized : v.finalized = some state.finalizedBlockHash)
    (nonzero : state.finalizedBlockHash ≠ ZERO_HASH) :
    ∃ r, v.resolve (.tag .finalized) = .ok (some r) ∧ r.hash = state.finalizedBlockHash := by
  obtain ⟨-, -, hf⟩ := onChain_of_forkchoiceUpdated fcu
  obtain ⟨r, hr⟩ := exists_canonical hcanon hf nonzero
  refine ⟨r, ?_, ?_⟩
  · simp [ChainView.resolve, ChainView.byTag, hfinalized, hr]
  · simpa using (List.find?_some hr)

end EthLib.Engine
