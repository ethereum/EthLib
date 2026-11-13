module

public import EthLib.Execution.Rpc.View
public import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the chain view

A number or a hash resolves only to a block of that number or that hash.

A query by hash that requires a canonical block resolves only to a canonical block.

The latest tag resolves to the head.

In a valid view, the canonical blocks have consecutive numbers, and each links to its parent.

So every number from the lowest block to the head resolves to a block.

The state of each canonical block has the state root of its header.
-/

public section

namespace EthLib.Execution.Rpc.ChainView

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.State (stateRoot)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- A canonical block that a lookup by hash finds is canonical and has that hash. -/
private theorem canonicalByHash_some {v : ChainView} {hash : Hash32} {r : BlockRecord}
    (h : v.canonicalByHash hash = some r) : r ∈ v.canonical ∧ r.hash = hash :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A number resolves only to a canonical block of that number. -/
theorem resolve_number {v : ChainView} {n : Nat} {r : BlockRecord}
    (h : v.resolve (.number n) = .ok (some r)) :
    r ∈ v.canonical ∧ r.block.header.number = n := by
  have hf : v.byNumber n = some r := by simpa [ChainView.resolve] using h
  have hp := List.find?_some hf
  exact ⟨List.mem_of_find?_eq_some hf, by simpa using hp⟩

/-- A hash resolves only to a block of that hash that the node holds. -/
theorem resolve_hash {v : ChainView} {hash : Hash32} {c : Bool} {r : BlockRecord}
    (h : v.resolve (.hash hash c) = .ok (some r)) :
    r ∈ v.canonical ++ v.side ∧ r.hash = hash := by
  unfold ChainView.resolve at h
  cases hb : v.byHash hash with
  | none => simp [hb] at h
  | some r' =>
    simp only [hb] at h
    split at h <;> simp at h
    subst h
    exact ⟨List.mem_of_find?_eq_some hb, by simpa using List.find?_some hb⟩

/-- The latest tag resolves to the head. -/
@[simp] theorem resolve_latest (v : ChainView) : v.resolve (.tag .latest) = .ok (some v.head) :=
  rfl

/-- A hash that must name a canonical block resolves only to a canonical block of that hash. -/
theorem resolve_hash_canonical {v : ChainView} {hash : Hash32} {r : BlockRecord}
    (h : v.resolve (.hash hash true) = .ok (some r)) :
    r ∈ v.canonical ∧ r.hash = hash := by
  unfold ChainView.resolve at h
  cases hb : v.byHash hash with
  | none => simp [hb] at h
  | some r' =>
    simp only [hb] at h
    split at h
    · simp at h
    · rename_i hc
      obtain ⟨r'', hr''⟩ := Option.ne_none_iff_exists'.mp (by simpa using hc)
      have hb' : v.byHash hash = some r'' := by
        unfold ChainView.byHash
        unfold ChainView.canonicalByHash at hr''
        rw [List.find?_append, hr'']
        rfl
      rw [hb] at hb'
      cases hb'
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact canonicalByHash_some hr''

/-- A hash that names no held block resolves to no block, with or without the flag.

So a block that is not found resolves to no block before the canonical check. -/
theorem resolve_hash_none {v : ChainView} {hash : Hash32} {c : Bool}
    (h : v.byHash hash = none) : v.resolve (.hash hash c) = .ok none := by
  simp [ChainView.resolve, h]

/-- A hash that must name a canonical block, and names a held block off that chain, fails.

The error is the invalid input of EIP-1898. -/
theorem resolve_hash_notCanonical {v : ChainView} {hash : Hash32} {r : BlockRecord}
    (h : v.byHash hash = some r) (hc : v.canonicalByHash hash = none) :
    v.resolve (.hash hash true) = .error ChainView.notCanonical := by
  simp [ChainView.resolve, h, hc]

/-- The safe tag resolves only to the canonical block of the safe hash. -/
theorem resolve_safe {v : ChainView} {r : BlockRecord}
    (h : v.resolve (.tag .safe) = .ok (some r)) :
    r ∈ v.canonical ∧ v.safe = some r.hash := by
  have hf : v.safe.bind v.canonicalByHash = some r := by
    simpa [ChainView.resolve, ChainView.byTag] using h
  obtain ⟨x, hx, hc⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨hm, hh⟩ := canonicalByHash_some hc
  exact ⟨hm, by rw [hx, hh]⟩

/-- The finalized tag resolves only to the canonical block of the finalized hash. -/
theorem resolve_finalized {v : ChainView} {r : BlockRecord}
    (h : v.resolve (.tag .finalized) = .ok (some r)) :
    r ∈ v.canonical ∧ v.finalized = some r.hash := by
  have hf : v.finalized.bind v.canonicalByHash = some r := by
    simpa [ChainView.resolve, ChainView.byTag] using h
  obtain ⟨x, hx, hc⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨hm, hh⟩ := canonicalByHash_some hc
  exact ⟨hm, by rw [hx, hh]⟩

/-- A block parameter resolves only to a block that the node holds, or to its pending block. -/
theorem resolve_mem {v : ChainView} {p : BlockParam} {r : BlockRecord}
    (h : v.resolve p = .ok (some r)) : r ∈ v.canonical ++ v.side ∨ v.pending = some r := by
  match p, h with
  | .number _, h => exact .inl (List.mem_append_left _ (resolve_number h).1)
  | .hash _ _, h => exact .inl (resolve_hash h).1
  | .tag .safe, h => exact .inl (List.mem_append_left _ (resolve_safe h).1)
  | .tag .finalized, h => exact .inl (List.mem_append_left _ (resolve_finalized h).1)
  | .tag .pending, h => exact .inr (by simpa [ChainView.resolve, ChainView.byTag] using h)
  | .tag .latest, h =>
    obtain rfl : v.head = r := by simpa [ChainView.resolve, ChainView.byTag] using h
    exact .inl (List.mem_append_left _ (List.getLast_mem _))
  | .tag .earliest, h =>
    obtain rfl : v.lowest = r := by simpa [ChainView.resolve, ChainView.byTag] using h
    exact .inl (List.mem_append_left _ (List.head_mem _))

/-- The last recent block of the chain after the canonical block at index `i` is that block. -/
private theorem chainAt_getLast {v : ChainView} (i : Nat) (hi : i < v.canonical.length) :
    (v.chainAt i hi).recent.getLast? = some v.canonical[i].recent := by
  unfold ChainView.chainAt
  rw [List.take_add_one, List.map_append, ← List.append_assoc]
  simp [List.getElem?_eq_getElem hi]

/-- In a valid view, a canonical block is numbered one above the block before it.

The header of the block before it hashes to its parent hash. -/
private theorem Valid.link {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal) (i : Nat)
    (hi : i + 1 < v.canonical.length) :
    v.canonical[i + 1].block.header.number = v.canonical[i].block.header.number + 1 ∧
      v.canonical[i].block.header.hash = .ok v.canonical[i + 1].block.header.parentHash := by
  obtain ⟨hst, -⟩ := hv.follows i hi
  obtain ⟨parent, hlast, hn, hh⟩ := checkBlock_link (stateTransition_eq_ok hst).2.2.1
  rw [chainAt_getLast] at hlast
  cases hlast
  exact ⟨hn, hh⟩

/-- The lowest block is the canonical block at index zero. -/
private theorem lowest_eq (v : ChainView) (h : 0 < v.canonical.length) :
    v.lowest = v.canonical[0] :=
  List.head_eq_getElem _

/-- In a valid view, the canonical block at index `i` is numbered `i` above the lowest block. -/
theorem Valid.number {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal) (i : Nat)
    (hi : i < v.canonical.length) :
    v.canonical[i].block.header.number = v.lowest.block.header.number + i := by
  induction i with
  | zero => rw [lowest_eq v hi]; rfl
  | succ i ih =>
    rw [(hv.link i hi).1, ih (by omega)]
    omega

/-- In a valid view, each canonical block above the lowest has the block before it as parent. -/
theorem Valid.parentHash {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal) (i : Nat)
    (hi : i + 1 < v.canonical.length) :
    v.canonical[i + 1].block.header.parentHash = v.canonical[i].hash := by
  have h1 := (hv.link i hi).2
  have h2 := hv.hash v.canonical[i] (List.mem_append_left _ (List.getElem_mem _))
  rw [h1] at h2
  exact (Except.ok.inj h2)

/-- In a valid view, every number from the lowest block to the head resolves to a block. -/
theorem Valid.resolve_number {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {n : Nat} (hlow : v.lowest.block.header.number ≤ n) (hhigh : n ≤ v.head.block.header.number) :
    ∃ r, v.resolve (.number n) = .ok (some r) := by
  have hlen := v.nonempty
  have hpos : 0 < v.canonical.length := List.length_pos_iff.mpr hlen
  have hhead : v.head = v.canonical[v.canonical.length - 1] := by
    simp [ChainView.head, List.getLast_eq_getElem]
  have hlast := hv.number (v.canonical.length - 1) (by omega)
  rw [hhead, hlast] at hhigh
  have hi : n - v.lowest.block.header.number < v.canonical.length := by omega
  have hnum := hv.number _ hi
  have hn : v.canonical[n - v.lowest.block.header.number].block.header.number = n := by
    rw [hnum]; omega
  cases hf : v.byNumber n with
  | some r => exact ⟨r, by simp [ChainView.resolve, hf]⟩
  | none =>
    have := List.find?_eq_none.mp hf _ (List.getElem_mem hi)
    simp [hn] at this

/-- In a valid view, the state of each canonical block has the state root of its header. -/
theorem Valid.stateRoot_eq {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {r : BlockRecord} (hr : r ∈ v.canonical) :
    stateRoot keccak256 r.state = .ok r.block.header.stateRoot := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  cases i with
  | zero =>
    have := hv.lowest
    rwa [lowest_eq v hi] at this
  | succ i =>
    obtain ⟨hst, -⟩ := hv.follows i hi
    exact (of_stateTransition hst).2

end EthLib.Execution.Rpc.ChainView
