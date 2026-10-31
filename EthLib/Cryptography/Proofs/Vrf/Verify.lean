import EthLib.Cryptography.Vrf.Verify
import EthLib.Cryptography.Vrf.KeyGen
import EthLib.Cryptography.Proofs.Vrf.Hash
import EthLib.Cryptography.Proofs.Vrf.Tree

/-!
# Proofs: `Vrf.Verify`

The two properties of a VRF that hold without assumptions on the hash.

- Provability: the opening of an honest tree verifies, with the output of the secret at that index.
- Uniqueness: two openings that verify at one index under one root give one output, or Keccak-256 collides.

Uniqueness holds for every root, including one the holder built to cheat.

The third property, pseudorandomness, needs a model of the hash and is not proved here.

Source: the three properties are those of [Micali, Rabin and Vadhan, "Verifiable Random Functions", FOCS 1999](https://doi.org/10.1109/SFFCS.1999.814584).
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-- A collision of Keccak-256: two different inputs with one hash. -/
def HashCollision : Prop :=
  ∃ a b : ByteArray, a ≠ b ∧ hash a = hash b

/-! ## What verification checks -/

/-- An opening verifies exactly when its path leads from its leaf to the root, and the output is the secret's. -/
theorem verify_eq_some_iff {root : Digest} {i : UInt32} {o : Opening} {y : Digest} :
    verify root i o = some y ↔
      Tree.climb nodeHash i.toNat (leafHash o.secret) o.path.toList = root ∧ y = outputHash o.secret := by
  unfold verify
  by_cases hp : Tree.climb nodeHash i.toNat (leafHash o.secret) o.path.toList = root <;>
    simp [hp, eq_comm]

/-- The output of a valid opening is the hash of its secret. -/
theorem verify_output {root : Digest} {i : UInt32} {o : Opening} {y : Digest}
    (h : verify root i o = some y) : y = outputHash o.secret :=
  (verify_eq_some_iff.mp h).2

/-! ## Provability -/

/-- The opening of an honest tree at index `i` verifies, with the output of secret `i`. -/
theorem verify_opening (secrets : UInt32 → Digest) (i : UInt32) :
    verify (root secrets) i (opening secrets i) = some (outputHash (secrets i)) := by
  refine verify_eq_some_iff.mpr ⟨?_, rfl⟩
  -- Leaf `i` of the tree commits to secret `i`.
  have hleaf : leaves secrets i.toNat = leafHash (secrets i) := by simp [leaves]
  show Tree.climb nodeHash i.toNat (leafHash (secrets i))
    (Tree.path nodeHash VRF_TREE_HEIGHT (leaves secrets) i.toNat).toList = _
  rw [← hleaf]
  exact Tree.climb_path nodeHash VRF_TREE_HEIGHT (leaves secrets) i.toNat_lt

/-! ## Uniqueness -/

/-- A collision of the node hash is a collision of Keccak-256. -/
theorem hashCollision_of_nodeCollision : Tree.Collision nodeHash → HashCollision := by
  rintro ⟨x, y, hne, heq⟩
  refine ⟨nodeInput x.1 x.2, nodeInput y.1 y.2, fun h => hne ?_, heq⟩
  -- A node input determines its two children.
  obtain ⟨h1, h2⟩ := nodeInput_inj.mp h
  exact Prod.ext h1 h2

/-- Two secrets with one leaf are equal, or Keccak-256 collides. -/
theorem leafHash_binding {s s' : Digest} (h : leafHash s = leafHash s') :
    s = s' ∨ HashCollision := by
  by_cases hs : s = s'
  · exact .inl hs
  · -- A leaf input determines its secret, so the two inputs differ.
    exact .inr ⟨leafInput s, leafInput s', fun he => hs (leafInput_inj.mp he), h⟩

/-- Two openings that verify at one index under one root reveal one secret, or Keccak-256 collides. -/
theorem verify_secret_unique {root : Digest} {i : UInt32} {o o' : Opening} {y y' : Digest}
    (h : verify root i o = some y) (h' : verify root i o' = some y') :
    o.secret = o'.secret ∨ HashCollision := by
  -- Both paths lead to the same root from the same index.
  have hroot := (verify_eq_some_iff.mp h).1.trans (verify_eq_some_iff.mp h').1.symm
  rcases Tree.climb_binding nodeHash (by simp) hroot with ⟨hleaf, -⟩ | hcol
  · -- Equal leaves come from equal secrets, unless the leaf hash collides.
    exact leafHash_binding hleaf
  · exact .inr (hashCollision_of_nodeCollision hcol)

/-- Uniqueness: two openings that verify at one index under one root give one output, or Keccak-256 collides. -/
theorem verify_unique {root : Digest} {i : UInt32} {o o' : Opening} {y y' : Digest}
    (h : verify root i o = some y) (h' : verify root i o' = some y') :
    y = y' ∨ HashCollision := by
  rcases verify_secret_unique h h' with hs | hcol
  · -- One secret has one output.
    rw [verify_output h, verify_output h', hs]
    exact .inl rfl
  · exact .inr hcol

/-- Against an honest tree, every valid opening at index `i` gives the output of secret `i`, or Keccak-256 collides. -/
theorem verify_root_unique {secrets : UInt32 → Digest} {i : UInt32} {o : Opening} {y : Digest}
    (h : verify (root secrets) i o = some y) : y = outputHash (secrets i) ∨ HashCollision :=
  verify_unique h (verify_opening secrets i)

end EthLib.Cryptography.Vrf
