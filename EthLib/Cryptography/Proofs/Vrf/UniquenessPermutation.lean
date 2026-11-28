module

public import EthLib.Cryptography.Proofs.Vrf.Uniqueness
public import EthLib.Cryptography.Proofs.Hash.Keccak.OneBlock
public import EthLib.Cryptography.Proofs.Hash.Keccak.QueryBound

/-!
# Proofs: one output per index over a uniform permutation

This module bounds the chance that an adversary opens one index of a root to two outputs.

Each hash is Keccak-256 with a uniform permutation in place of Keccak-f[1600].

With Keccak-f[1600] itself, each check is the check of the specification.

A win gives two messages of one block with one digest, which the permutation makes unlikely.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants
open OracleSpec OracleComp ENNReal
open EthLib.Cryptography.LazyPermutation (PermComp permImpl forward isQueryBoundP_forward
  simulateQ_permImpl_forward oneCallHash collisionAdvantage)
open EthLib.Cryptography.Hash.Keccak (State RATE_256 blockCount ShortMessage keccakF keccak256With
  keccak256With_eq_squeeze256 keccak256With_keccakF simulateQ_keccak256With_of_pure
  isQueryBoundP_keccak256With oneBlockState oneCallHash_eq keccak256_collisionAdvantage_le)
open EthLib.Cryptography.Hash.Keccak.Internal (squeeze256)

/-! ## The hash over the permutation -/

/-- Keccak-256 with forward calls to the permutation in place of Keccak-f[1600], as a digest. -/
def permHash (x : ByteArray) : PermComp State Digest :=
  keccak256With forward x

/-- The hash of fewer than 136 bytes makes at most one call to the permutation. -/
theorem isQueryBoundP_permHash {x : ByteArray} (hx : x.size < RATE_256) :
    IsQueryBoundP (permHash x) (·.isRight = true) 1 :=
  -- Keccak-256 calls the permutation once per block, and such an input is one block.
  (isQueryBoundP_keccak256With isQueryBoundP_forward x).mono
    (by simp [blockCount, Nat.div_eq_of_lt hx])

/-- Run with the permutation `π`, the hash is Keccak-256 with `π` in place of Keccak-f[1600]. -/
theorem simulateQ_permHash (π : Equiv.Perm State) (x : ByteArray) :
    simulateQ (permImpl π) (permHash x) = pure (Id.run (keccak256With (fun S => pure (π S)) x)) :=
  simulateQ_keccak256With_of_pure _ _ _ (simulateQ_permImpl_forward π) x

/-! ## The reduction to a collision -/

/-- A found pair as two messages of one block, when both inputs fit in one.

Otherwise, and when no pair is found, it is the empty message twice, which is no collision. -/
def shortPair : Option (ByteArray × ByteArray) → ShortMessage × ShortMessage
  | some p =>
    if h : p.1.size < RATE_256 ∧ p.2.size < RATE_256 then (⟨p.1, h.1⟩, ⟨p.2, h.2⟩)
    else (⟨.empty, by simp [RATE_256]⟩, ⟨.empty, by simp [RATE_256]⟩)
  | none => (⟨.empty, by simp [RATE_256]⟩, ⟨.empty, by simp [RATE_256]⟩)

/-- A pair that the search with `H` finds stays a collision of `H` as two messages of one block.

Its inputs are two node inputs or the two leaf inputs, of 75 or 43 bytes. -/
theorem shortPair_collision {H : ByteArray → Digest} {i : UInt32} {o o' : Opening}
    {p : ByteArray × ByteArray} (hp : findHashCollisionWith H i o o' = some p) :
    IsHashCollisionWith H ((shortPair (some p)).1.1, (shortPair (some p)).2.1) := by
  have hsize : p.1.size < RATE_256 ∧ p.2.size < RATE_256 := by
    rw [findHashCollisionWith_eq] at hp
    split at hp
    · cases hp
      simp [RATE_256]
    · split at hp
      · cases hp
        simp [RATE_256]
      · cases hp
  simp only [shortPair, dite_eq_left hsize]
  exact findHashCollisionWith_valid hp

/-- Run with answers that give each hash the value `G`, the search is the one over `G`. -/
theorem simulateQ_searchHashCollisionWith_of_pure {ι : Type} {spec : OracleSpec ι}
    {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl spec r)
    {H : ByteArray → OracleComp spec Digest} {G : ByteArray → Digest}
    (hH : ∀ x, simulateQ impl (H x) = pure (G x)) (i : UInt32) (o o' : Opening) :
    simulateQ impl (searchHashCollisionWith H i o o') = pure (findHashCollisionWith G i o o') := by
  simp only [searchHashCollisionWith, simulateQ_bind, simulateQ_pure, hH, pure_bind,
    Merkle.simulateQ_findCollision_of_pure impl (nodeWith H)
      (fun _ left right => G (nodeInput left right)) (fun _ _ _ => hH _)]
  rfl

/-- An event on the output is at most as likely as a one-block collision that the search finds.

It holds when the search returns a collision of Keccak-256 after each output with the event. -/
theorem prEvent_le_collisionAdvantage {α : Type} (adversary : PermComp State α)
    (search : α → PermComp State (ShortMessage × ShortMessage))
    (event : Equiv.Perm State → α → Prop)
    (hsearch : ∀ π a, event π a → ∀ r ∈ support (simulateQ (permImpl π) (search a)),
      IsHashCollisionWith (fun x => Id.run (keccak256With (fun S => pure (π S)) x))
        (r.1.1, r.2.1)) :
    Pr{let π ← $ᵗ (Equiv.Perm State); let a ← simulateQ (permImpl π) adversary}[event π a] ≤
      collisionAdvantage (fun m : ShortMessage => oneBlockState m.1) squeeze256
        (adversary >>= search) := by
  unfold collisionAdvantage
  refine prEvent_bind_mono_of_support _ _ _ fun π _ => ?_
  rw [simulateQ_bind]
  -- On every run, an output with the event makes the search return a collision.
  refine prEvent_le_prEvent_bind_of_support _ _ _ _ fun a _ ha =>
    prEvent_eq_one_of_forall_mem_support _ _ fun r hr => ?_
  obtain ⟨hne, heq⟩ := hsearch π a ha r hr
  -- The game's hash of a message of one block is Keccak-256 over the permutation.
  have hgame : ∀ m : ShortMessage, oneCallHash (fun m : ShortMessage => oneBlockState m.1)
      squeeze256 π m = Id.run (keccak256With (fun S => pure (π S)) m.1) := fun m => by
    rw [oneCallHash_eq, keccak256With_eq_squeeze256, Id.run_map]
  exact ⟨fun h => hne (congrArg Subtype.val h), (hgame r.1).trans (heq.trans (hgame r.2).symm)⟩

/-- The collision search of two openings, with each hash Keccak-256 over the permutation.

It returns the pair that the search finds as two messages of one block.

When the search finds none, it returns the empty message twice. -/
def collisionSearch (claim : OpeningsClaim) : PermComp State (ShortMessage × ShortMessage) :=
  shortPair <$> searchHashCollisionWith permHash claim.index claim.first claim.second

/-- The search makes at most `2 (h + 1)` calls to the permutation, for a tree of height `h`.

It hashes the two leaves, then at most two nodes per level. -/
theorem isQueryBoundP_collisionSearch (claim : OpeningsClaim) :
    IsQueryBoundP (collisionSearch claim) (·.isRight = true) (2 * (VRF_TREE_HEIGHT + 1)) := by
  -- Each input of the tree is one block, so each hash calls the permutation at most once.
  have hsearch := Merkle.isQueryBoundP_findCollision (hash := nodeWith permHash)
    (fun _ _ _ => isQueryBoundP_permHash (by simp [RATE_256])) claim.first.path.toList
    claim.second.path.toList ⟨0, claim.index.toNat⟩
  unfold collisionSearch searchHashCollisionWith
  refine (isQueryBoundP_map_iff _ _ _).2 <|
    (isQueryBoundP_bind (isQueryBoundP_permHash (by simp [RATE_256])) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_permHash (by simp [RATE_256])) fun _ _ =>
        isQueryBoundP_bind (hsearch _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
  -- Each path has one sibling per level of the tree.
  simp only [Vector.length_toList, min_self]
  omega

/-- A win with `H` as the hash makes every run of the search return a collision of `H`.

It holds when each hash, run with the permutation, returns its value under `H`. -/
theorem collisionSearch_collision_of_outputsWin {π : Equiv.Perm State} {H : ByteArray → Digest}
    (hH : ∀ x, simulateQ (permImpl π) (permHash x) = pure (H x))
    {claim : OpeningsClaim}
    (hwin : OutputsWin (extractOutputs (m := Id) (fun x => pure (H x)) claim).run)
    {r : ShortMessage × ShortMessage}
    (hr : r ∈ support (simulateQ (permImpl π) (collisionSearch claim))) :
    IsHashCollisionWith H (r.1.1, r.2.1) := by
  obtain ⟨pair, hpair, -⟩ := findHashCollisionWith_of_outputsWin hwin
  rw [collisionSearch, simulateQ_map, simulateQ_searchHashCollisionWith_of_pure _ hH, hpair,
    map_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  -- The search returns the pair that the win exposes.
  exact shortPair_collision hpair

/-! ## The bound -/

/-- **Two outputs at one index over a uniform permutation.**

The adversary makes at most `q` classical queries to the permutation and its inverse.

For the tree height `h`, `Q = q + 2 (h + 2)` adds the calls of the search and of the collision game.

A win has chance at most `(Q (Q - 1) / 2 * 2^1344 + Q * 2^1088) / (2^1600 - Q)`. -/
theorem prEvent_outputsWin_keccak256With_le (adversary : PermComp State OpeningsClaim) {q : ℕ}
    (hq : IsQueryBoundP adversary (·.isRight = true) q) :
    Pr{let π ← $ᵗ (Equiv.Perm State); let claim ← simulateQ (permImpl π) adversary}[
      OutputsWin (extractOutputs (m := Id) (keccak256With fun S => pure (π S)) claim).run] ≤
      (((q + 2 * (VRF_TREE_HEIGHT + 2)).choose 2 * 2 ^ 1344 +
        (q + 2 * (VRF_TREE_HEIGHT + 2)) * 2 ^ 1088 : ℕ) : ℝ≥0∞) /
        ((2 ^ 1600 - (q + 2 * (VRF_TREE_HEIGHT + 2)) : ℕ) : ℝ≥0∞) := by
  -- The reduction runs the adversary, then the search, and the game hashes its two messages.
  have hbound := keccak256_collisionAdvantage_le (adversary >>= collisionSearch)
    (isQueryBoundP_bind hq fun claim _ => isQueryBoundP_collisionSearch claim)
  rw [show q + 2 * (VRF_TREE_HEIGHT + 1) + 2 = q + 2 * (VRF_TREE_HEIGHT + 2) by omega] at hbound
  refine le_trans ?_ hbound
  -- On every run, a win of the adversary makes the search return a collision.
  exact prEvent_le_collisionAdvantage adversary collisionSearch _ fun π _ hwin _ hr =>
    collisionSearch_collision_of_outputsWin (simulateQ_permHash π) hwin hr

/-! ## Over Keccak-f[1600] -/

/-- Over Keccak-f[1600] itself, a win is two openings that verify with two different outputs.

Both openings verify at the claimed index under the claimed root. -/
theorem outputsWin_keccak256With_keccakF_iff {claim : OpeningsClaim} :
    OutputsWin (extractOutputs (m := Id) (keccak256With fun S => pure (keccakF S)) claim).run ↔
      ∃ y y', verify claim.root claim.index claim.first = some y ∧
        verify claim.root claim.index claim.second = some y' ∧ y ≠ y' := by
  -- Over Keccak-f[1600], the sponge is Keccak-256, the hash of the specification.
  have hhash : (keccak256With (m := Id) fun S => pure (keccakF S)) =
      fun x => (pure (hash x) : Id Digest) :=
    funext keccak256With_keccakF
  rw [hhash]
  exact outputsWin_keccak256_iff

end EthLib.Cryptography.Vrf
