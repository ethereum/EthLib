module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.Ommers

/-!
# Proofs: the ommers of a block

A block whose ommers pass the check commits to them by its ommers hash.

It holds at most two ommers, none twice.

Each ommer is one to six blocks older than the block, and is not a sibling of the block.

The Python suite shows that valid ommers pass.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- A bound computation that succeeds has a first step that succeeds. -/
private theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-- A check passes exactly when its condition holds. -/
theorem ensure_eq_ok {condition : Bool} {error : OmmerError} :
    ensure condition error = .ok () ↔ condition = true := by
  unfold ensure
  cases condition <;> simp

/-- A check over a list passes exactly when it passes for each element. -/
theorem forM_eq_ok {α : Type} (f : α → Except OmmerError Unit) :
    ∀ l : List α, l.forM f = .ok () ↔ ∀ x ∈ l, f x = .ok () := by
  intro l
  induction l with
  | nil => simp [List.forM, pure, Except.pure]
  | cons x rest ih =>
    simp only [List.forM, List.mem_cons, forall_eq_or_imp]
    cases hx : f x with
    | error e => exact ⟨(fun h => nomatch h), fun ⟨h, _⟩ => nomatch h⟩
    | ok u => exact ⟨fun h => ⟨rfl, ih.mp h⟩, fun ⟨_, h⟩ => ih.mpr h⟩

/-- A map in `Except` that succeeds keeps the length of the list. -/
private theorem length_of_mapM_eq_ok {ε α β : Type} (f : α → Except ε β) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro r h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
    rfl
  | cons x rest ih =>
    intro r h
    rw [List.mapM_cons] at h
    obtain ⟨b, -, h⟩ := bind_eq_ok h
    obtain ⟨bs, hbs, h⟩ := bind_eq_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
    simp [ih bs hbs]

/-- The facts that valid ommers give about a block. -/
theorem validateOmmers_spec {fork : Fork} {checkSeal : Bool} {recent : List RecentBlock}
    {header : Header fork} {ommers : List (Header fork)}
    (h : validateOmmers checkSeal recent header ommers = .ok ()) :
    (∃ encoded, encode (Codec.toItem ommers) = .ok encoded ∧
      keccak256 encoded = header.ommersHash) ∧
    ommers.length ≤ MAX_OMMERS ∧
    (∃ hashes, ommers.mapM headerHash = .ok hashes ∧ hashes.Nodup) ∧
    ∀ ommer ∈ ommers, 1 ≤ ommer.number ∧ ommer.number < header.number ∧
      1 ≤ header.number - ommer.number ∧ header.number - ommer.number ≤ MAX_OMMER_DEPTH ∧
      ommer.parentHash ≠ header.parentHash := by
  unfold validateOmmers at h
  obtain ⟨encoded, henc, h⟩ := bind_eq_ok h
  obtain ⟨_, hhash, h⟩ := bind_eq_ok h
  obtain ⟨_, hfirst, h⟩ := bind_eq_ok h
  obtain ⟨_, hcount, h⟩ := bind_eq_ok h
  obtain ⟨ommerHashes, hhashes, h⟩ := bind_eq_ok h
  obtain ⟨_, hnodup, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  have hhash := ensure_eq_ok.mp hhash
  have hcount := ensure_eq_ok.mp hcount
  have hfirst := (forM_eq_ok _ ommers).mp hfirst
  have hlast := (forM_eq_ok _ (ommers.zip ommerHashes)).mp h
  -- One hash per ommer, so each ommer meets its hash in the pairs.
  have hlen : ommerHashes.length = ommers.length := length_of_mapM_eq_ok _ _ _ hhashes
  refine ⟨⟨encoded, mapError_ok_iff.mp henc, eq_of_beq hhash⟩, by simpa using hcount,
    ⟨ommerHashes, hhashes, by simpa using ensure_eq_ok.mp hnodup⟩, fun ommer hm => ?_⟩
  obtain ⟨_, hrange, -⟩ := bind_eq_ok (hfirst ommer hm)
  have hrange := ensure_eq_ok.mp hrange
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrange
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  have hpair : (ommers[i], ommerHashes[i]'(hlen ▸ hi)) ∈ ommers.zip ommerHashes := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hlen, hi], by simp⟩
  have hp := hlast _ hpair
  obtain ⟨_, -, hp⟩ := bind_eq_ok hp
  obtain ⟨_, -, hp⟩ := bind_eq_ok hp
  obtain ⟨_, hage, hp⟩ := bind_eq_ok hp
  obtain ⟨_, -, hp⟩ := bind_eq_ok hp
  have hage := ensure_eq_ok.mp hage
  have hsib := ensure_eq_ok.mp hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hage
  simp only [bne_iff_ne, ne_eq] at hsib
  exact ⟨hrange.1, hrange.2, hage.1, hage.2, hsib⟩

/-- Two errors with one code come from one constructor. -/
theorem OmmerError.code_injective (e₁ e₂ : OmmerError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [OmmerError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Blocks
