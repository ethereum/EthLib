module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.Ommers

/-!
# Proofs: the ommers of a block

A block whose ommers pass the check commits to them by its ommers hash.

It holds at most two ommers, none twice.

Each ommer is one to six blocks older than the block, and is not a sibling of the block.

In the first ten blocks of the DAO Fork, each ommer carries the extra data of that fork.

The ommers pass the check exactly when they meet these rules and the rest of the check.

The Python suite shows that valid ommers pass.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The facts that valid ommers give about a block. -/
theorem validateOmmers_spec {fork : Fork} {config : ChainConfig} {checkSeal : Bool}
    {recent : List RecentBlock} {header : Header fork} {ommers : List ((f : Fork) × Header f)}
    (h : validateOmmers config checkSeal recent header ommers = .ok ()) :
    (∃ encoded, encode (ommersItem ommers) = .ok encoded ∧
      keccak256 encoded = header.ommersHash) ∧
    ommers.length ≤ MAX_OMMERS ∧
    (∃ hashes, ommers.mapM (headerHash ·.2) = .ok hashes ∧ hashes.Nodup) ∧
    ∀ ommer ∈ ommers, 1 ≤ ommer.2.number ∧ ommer.2.number < header.number ∧
      1 ≤ header.number - ommer.2.number ∧ header.number - ommer.2.number ≤ MAX_OMMER_DEPTH ∧
      ommer.2.parentHash ≠ header.parentHash := by
  unfold validateOmmers at h
  obtain ⟨encoded, henc, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hhash, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hfirst, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hcount, h⟩ := bind_ok_iff.mp h
  obtain ⟨ommerHashes, hhashes, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hnodup, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  have hhash := ensure_ok_iff.mp hhash
  have hcount := ensure_ok_iff.mp hcount
  have hfirst := forM_ok_iff.mp hfirst
  have hlast := forM_ok_iff.mp h
  -- One hash per ommer, so each ommer meets its hash in the pairs.
  have hlen : ommerHashes.length = ommers.length := mapM_ok_length hhashes
  refine ⟨⟨encoded, mapError_ok_iff.mp henc, eq_of_beq hhash⟩, by simpa using hcount,
    ⟨ommerHashes, hhashes, by simpa using ensure_ok_iff.mp hnodup⟩, fun ommer hm => ?_⟩
  obtain ⟨_, hrange, -⟩ := bind_ok_iff.mp (hfirst ommer hm)
  have hrange := ensure_ok_iff.mp hrange
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrange
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  have hpair : (ommers[i], ommerHashes[i]'(hlen ▸ hi)) ∈ ommers.zip ommerHashes := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hlen, hi], by simp⟩
  have hp := hlast _ hpair
  obtain ⟨_, -, hp⟩ := bind_ok_iff.mp hp
  obtain ⟨_, -, hp⟩ := bind_ok_iff.mp hp
  obtain ⟨_, hage, hp⟩ := bind_ok_iff.mp hp
  obtain ⟨_, -, hp⟩ := bind_ok_iff.mp hp
  have hage := ensure_ok_iff.mp hage
  have hsib := ensure_ok_iff.mp hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hage
  simp only [bne_iff_ne, ne_eq] at hsib
  exact ⟨hrange.1, hrange.2, hage.1, hage.2, hsib⟩

/-- Valid ommers in the first ten blocks of the DAO Fork carry the extra data of that fork. -/
theorem validateOmmers_daoExtraData {fork : Fork} {config : ChainConfig} {checkSeal : Bool}
    {recent : List RecentBlock} {header : Header fork} {ommers : List ((f : Fork) × Header f)}
    (h : validateOmmers config checkSeal recent header ommers = .ok ()) :
    ∀ ommer ∈ ommers, daoExtraDataValid config ommer.2 = true := by
  unfold validateOmmers at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hfirst, -⟩ := bind_ok_iff.mp h
  intro ommer hm
  obtain ⟨_, -, hcheck⟩ := bind_ok_iff.mp (forM_ok_iff.mp hfirst ommer hm)
  unfold checkOmmerHeader at hcheck
  -- The extra data check is the last step of the header check of the ommer.
  cases hfind : recent.find? (·.header.number + 1 = ommer.2.number) with
  | none => simp [hfind] at hcheck
  | some parent =>
    simp only [hfind] at hcheck
    split at hcheck
    · obtain ⟨_, -, hdao⟩ := bind_ok_iff.mp hcheck
      exact ensure_ok_iff.mp hdao
    · obtain ⟨_, h, -⟩ := bind_ok_iff.mp hcheck
      exact nomatch h

/-- Two errors with one code come from one constructor. -/
theorem OmmerError.code_injective (e₁ e₂ : OmmerError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [OmmerError.code] at h; exact absurd h (by decide))

/-- A statement about the one value of `Unit` holds for some value exactly when it holds. -/
private theorem exists_unit {P : Unit → Prop} : (∃ u, P u) ↔ P () :=
  ⟨fun ⟨(), h⟩ => h, fun h => ⟨(), h⟩⟩

/-- The ommers of a block pass the check exactly when every rule of the check holds.

The block commits to them by its ommers hash, and each ommer header passes its own checks.

The number of each ommer is at least 1 and below the number of the block.

There are at most two ommers, and no two have one hash.

No ommer is the block, a block of the recent chain, or an ommer that the recent chain holds.

Each ommer is one to six blocks older than the block, and its parent is in the recent chain.

No ommer is a sibling of the block. -/
theorem validateOmmers_eq_ok_iff {fork : Fork} {config : ChainConfig} {checkSeal : Bool}
    {recent : List RecentBlock} {header : Header fork} {ommers : List ((f : Fork) × Header f)} :
    validateOmmers config checkSeal recent header ommers = .ok () ↔
      ∃ encoded, Serialization.Rlp.encode (ommersItem ommers) = .ok encoded ∧
        keccak256 encoded = header.ommersHash ∧
        (∀ ommer ∈ ommers, (1 ≤ ommer.2.number ∧ ommer.2.number < header.number) ∧
          checkOmmerHeader config checkSeal recent ommer = .ok ()) ∧
        ommers.length ≤ MAX_OMMERS ∧
        ∃ hashes, ommers.mapM (headerHash ·.2) = .ok hashes ∧ hashes.Nodup ∧
        ∃ blockHash, headerHash header = .ok blockHash ∧
        ∃ recentHashes, recent.mapM (fun b => headerHash b.header) = .ok recentHashes ∧
        ∃ recentOmmerHashes,
          (recent.flatMap fun b => b.ommers.map (headerHash ·.2)).mapM id = .ok recentOmmerHashes ∧
        ∀ p ∈ ommers.zip hashes, p.2 ≠ blockHash ∧ p.2 ∉ recentHashes ∧
          p.2 ∉ recentOmmerHashes ∧
          (1 ≤ header.number - p.1.2.number ∧ header.number - p.1.2.number ≤ MAX_OMMER_DEPTH) ∧
          p.1.2.parentHash ∈ recentHashes ∧ p.1.2.parentHash ≠ header.parentHash := by
  unfold validateOmmers
  simp only [bind_ok_iff, exists_unit, ensure_ok_iff, forM_ok_iff, mapError_ok_iff,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.eq_false_iff, List.contains_iff_mem, and_assoc]
  -- The hash check compares by `==`, which holds exactly for equal hashes.
  exact exists_congr fun _ => and_congr_right fun _ =>
    and_congr_left fun _ => ⟨eq_of_beq, fun h => h ▸ beq_self_eq_true _⟩

end EthLib.Execution.Blocks
