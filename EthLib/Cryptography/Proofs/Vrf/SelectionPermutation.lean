module

public import EthLib.Cryptography.Proofs.Vrf.SelectionRandomOracle
public import EthLib.Cryptography.Proofs.Vrf.UniquenessPermutation

/-!
# Proofs: the collision search of a selection over a uniform permutation

This module bounds the chance that a selection's search finds a pair, in an experiment of its own.

Each hash is Keccak-256 with a uniform permutation in place of Keccak-f[1600].

With Keccak-f[1600] itself, the extraction is the search of the selection bound.

A found pair is two messages of one block with one digest, which the permutation makes unlikely.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants
open OracleSpec OracleComp ENNReal
open EthLib.Cryptography.LazyPermutation (PermComp permImpl)
open EthLib.Cryptography.Hash.Keccak (State RATE_256 ShortMessage keccakF keccak256With
  keccak256With_keccakF keccak256_collisionAdvantage_le)

/-! ## The reduction to a collision -/

/-- A pair found with `H` as the hash makes every run of the reduction return a collision of `H`.

It holds when each hash, run with the permutation, returns its value under `H`. -/
theorem shortPair_collision_of_extractCollision {π : Equiv.Perm State} {H : ByteArray → Digest}
    (hH : ∀ x, simulateQ (permImpl π) (permHash x) = pure (H x)) {claim : SelectionClaim}
    (hfound : (extractCollision (m := Id) (fun x => pure (H x)) claim).run.isSome)
    {r : ShortMessage × ShortMessage}
    (hr : r ∈ support (simulateQ (permImpl π) (shortPair <$> extractCollision permHash claim))) :
    IsHashCollisionWith H (r.1.1, r.2.1) := by
  rw [simulateQ_map, simulateQ_extractCollision_of_pure _ hH, map_pure, support_pure,
    Set.mem_singleton_iff] at hr
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hfound
  rw [hp] at hr
  subst hr
  rw [extractCollision_pure] at hp
  exact shortPair_collision hp

/-! ## The bound -/

/-- **The collision search of a selection over a uniform permutation.**

The adversary makes at most `q` classical queries to the permutation and its inverse.

For tree height `h`, `Q = q + 2^(h + 1) + 2 h + 2` adds the calls of the extraction and the game.

A pair is found with chance at most `(Q (Q - 1) / 2 * 2^1344 + Q * 2^1088) / (2^1600 - Q)`. -/
theorem prEvent_extractCollision_isSome_keccak256With_le
    (adversary : PermComp State SelectionClaim) {q : ℕ}
    (hq : IsQueryBoundP adversary (·.isRight = true) q) :
    Pr{let π ← $ᵗ (Equiv.Perm State); let claim ← simulateQ (permImpl π) adversary}[
      (extractCollision (m := Id) (keccak256With fun S => pure (π S)) claim).run.isSome] ≤
      (((q + 2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT + 2).choose 2 * 2 ^ 1344 +
        (q + 2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT + 2) * 2 ^ 1088 : ℕ) : ℝ≥0∞) /
        ((2 ^ 1600 - (q + 2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT + 2) : ℕ) : ℝ≥0∞) := by
  -- Each input of the tree is one block, so each hash calls the permutation at most once.
  have hcalls := isQueryBoundP_extractCollision (H := permHash)
    (fun _ => isQueryBoundP_permHash (by simp [RATE_256]))
    (fun _ _ => isQueryBoundP_permHash (by simp [RATE_256]))
  -- The reduction runs the adversary, then the extraction, and the game hashes its two messages.
  have hbound := keccak256_collisionAdvantage_le
    (adversary >>= fun claim => shortPair <$> extractCollision permHash claim)
    (isQueryBoundP_bind hq fun claim _ => (isQueryBoundP_map_iff _ _ _).2 (hcalls claim))
  rw [show q + (2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT) + 2 =
    q + 2 ^ (VRF_TREE_HEIGHT + 1) + 2 * VRF_TREE_HEIGHT + 2 by omega] at hbound
  refine le_trans ?_ hbound
  -- On every run, a pair found by the extraction makes the reduction return a collision.
  exact prEvent_le_collisionAdvantage adversary _ _ fun π _ hfound _ hr =>
    shortPair_collision_of_extractCollision (simulateQ_permHash π) hfound hr

/-! ## Over Keccak-f[1600] -/

/-- Over Keccak-f[1600] itself, the extraction is the search of the selection bound.

That search compares the opening with the honest opening of the specification, at the index. -/
theorem extractCollision_keccak256With_keccakF (claim : SelectionClaim) :
    (extractCollision (m := Id) (keccak256With fun S => pure (keccakF S)) claim).run =
      findHashCollision claim.index claim.revealed (opening claim.secrets claim.index) := by
  -- Over Keccak-f[1600], the sponge is Keccak-256, the hash of the specification.
  have hhash : (keccak256With (m := Id) fun S => pure (keccakF S)) =
      fun x => (pure (hash x) : Id Digest) :=
    funext keccak256With_keccakF
  rw [hhash]
  exact extractCollision_keccak256 claim

end EthLib.Cryptography.Vrf
