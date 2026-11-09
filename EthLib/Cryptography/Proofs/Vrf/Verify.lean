module

public import EthLib.Cryptography.Vrf.Verify
public import EthLib.Cryptography.Vrf.KeyGen
public import EthLib.Cryptography.Proofs.Vrf.Hash
public import EthLib.Cryptography.Proofs.Merkle.Binding

/-!
# Proofs: VRF verification

The two properties of a VRF that hold without assumptions on the hash.

- Provability: an opening of an honest tree verifies, with the output of the secret there.
- Uniqueness: two openings that verify at one index under one root give one output.
  Otherwise the collision search returns a collision of Keccak-256.

Uniqueness holds for every root, including one the holder built to cheat.

The third property, pseudorandomness, needs a model of the hash and is not proved here.

It could hold only for an honest tree: a holder that chooses its secrets can bias every output.

Source: the three properties are those of [Micali, Rabin and Vadhan][mrv99].

Their paper is "Verifiable Random Functions", FOCS 1999.

[mrv99]: https://doi.org/10.1109/SFFCS.1999.814584
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## What verification checks -/

/--
An opening verifies exactly when its path leads from its leaf to the root.

The output is then the secret's.
-/
theorem verify_eq_some_iff {root : Digest} {i : UInt32} {o : Opening} {y : Digest} :
    verify root i o = some y ↔
      (Merkle.climb treeHash 0 i.toNat (leafHash o.secret) o.path.toList).run = root ∧
        y = outputHash i o.secret := by
  unfold verify
  by_cases hp : (Merkle.climb treeHash 0 i.toNat (leafHash o.secret) o.path.toList).run = root <;>
    simp [hp, eq_comm]

/-- The output of a valid opening is the hash of its secret. -/
theorem verify_output {root : Digest} {i : UInt32} {o : Opening} {y : Digest}
    (h : verify root i o = some y) : y = outputHash i o.secret :=
  (verify_eq_some_iff.mp h).2

/-! ## Provability -/

/-- The opening of an honest tree at index `i` verifies, with the output of secret `i`. -/
theorem verify_opening (secrets : UInt32 → Digest) (i : UInt32) :
    verify (root secrets) i (opening secrets i) = some (outputHash i (secrets i)) := by
  refine verify_eq_some_iff.mpr ⟨?_, rfl⟩
  -- Leaf `i` of the tree commits to secret `i`.
  have hleaf : leaves secrets i.toNat = leafHash (secrets i) := by simp [leaves]
  show (Merkle.climb treeHash 0 i.toNat (leafHash (secrets i))
    (Merkle.path treeHash (m := Id) (leaves secrets) VRF_TREE_HEIGHT i.toNat).run.toList).run = _
  rw [← hleaf]
  exact Merkle.climb_path_root treeHash (leaves secrets) i.toNat_lt

/-! ## Uniqueness -/

/-- Two different inputs with one Keccak-256 hash. -/
def IsHashCollision (p : ByteArray × ByteArray) : Prop :=
  p.1 ≠ p.2 ∧ hash p.1 = hash p.2

/-- The Keccak-256 collision two openings at index `i` run into, if any.

It is the two node inputs of the Merkle collision search, at the lowest level where one exists.

With none, it is the two leaf inputs, if the secrets differ but their leaves are equal. -/
def findHashCollision (i : UInt32) (o o' : Opening) : Option (ByteArray × ByteArray) :=
  match Merkle.findCollision treeHash 0 i.toNat (leafHash o.secret) (leafHash o'.secret)
      o.path.toList o'.path.toList with
  | some c => some (nodeInput c.x.1 c.x.2, nodeInput c.y.1 c.y.2)
  | none =>
    if o.secret ≠ o'.secret ∧ leafHash o.secret = leafHash o'.secret then
      some (leafInput o.secret, leafInput o'.secret)
    else none

/-- A collision of the node hash is a collision of Keccak-256. -/
theorem isHashCollision_of_collision {c : Merkle.Collision Digest} (h : c.Valid treeHash) :
    IsHashCollision (nodeInput c.x.1 c.x.2, nodeInput c.y.1 c.y.2) := by
  obtain ⟨hne, heq⟩ := h
  refine ⟨fun he => hne ?_, heq⟩
  -- A node input determines its two children.
  obtain ⟨h1, h2⟩ := nodeInput_inj.mp he
  exact Prod.ext h1 h2

/-- Every pair that the search returns is a collision of Keccak-256. -/
theorem findHashCollision_valid {i : UInt32} {o o' : Opening} {p : ByteArray × ByteArray}
    (h : findHashCollision i o o' = some p) : IsHashCollision p := by
  unfold findHashCollision at h
  split at h
  · -- A node collision, which `findCollision_valid` proves valid.
    next c hc =>
    cases h
    exact isHashCollision_of_collision (Merkle.findCollision_valid treeHash _ _ _ _ _ _ c hc).1
  · -- A leaf collision: a leaf input determines its secret, so the two inputs differ.
    split at h
    · next hleaf =>
      cases h
      exact ⟨fun he => hleaf.1 (leafInput_inj.mp he), hleaf.2⟩
    · cases h

/-! ## The output binds its index -/

/-- Two outputs are equal only for one index and one secret.

Otherwise their two output inputs, which differ, are a Keccak-256 collision. -/
theorem outputHash_binding {i j : UInt32} {s s' : Digest} (h : outputHash i s = outputHash j s') :
    (i = j ∧ s = s') ∨ IsHashCollision (outputInput i s, outputInput j s') := by
  by_cases he : outputInput i s = outputInput j s'
  · exact .inl (outputInput_inj.mp he)
  · exact .inr ⟨he, h⟩

/-- One secret at two different indices gives two different outputs.

Otherwise its two output inputs are a Keccak-256 collision. -/
theorem outputHash_index_binding {i j : UInt32} (hij : i ≠ j) (s : Digest)
    (h : outputHash i s = outputHash j s) : IsHashCollision (outputInput i s, outputInput j s) :=
  (outputHash_binding h).resolve_left fun he => hij he.1

/-- Two openings that verify at two different indices give two different outputs.

The roots may differ, and the two secrets may be equal.

Otherwise the two output inputs of the openings are a Keccak-256 collision. -/
theorem verify_index_binding {root root' : Digest} {i j : UInt32} (hij : i ≠ j) {o o' : Opening}
    {y : Digest} (h : verify root i o = some y) (h' : verify root' j o' = some y) :
    IsHashCollision (outputInput i o.secret, outputInput j o'.secret) :=
  ((outputHash_binding ((verify_output h).symm.trans (verify_output h'))).resolve_left
    fun he => hij he.1)

/-- One opening compared with itself exposes no collision. -/
theorem findHashCollision_self (i : UInt32) (o : Opening) : findHashCollision i o o = none := by
  simp only [findHashCollision, Merkle.findCollision_self, ne_eq, not_true_eq_false, false_and,
    ↓reduceIte]

/--
Two openings that verify at one index under one root reveal one secret.

Otherwise the collision search returns a collision of Keccak-256.
-/
theorem verify_secret_unique {root : Digest} {i : UInt32} {o o' : Opening} {y y' : Digest}
    (h : verify root i o = some y) (h' : verify root i o' = some y') :
    o.secret = o'.secret ∨ ∃ p, findHashCollision i o o' = some p ∧ IsHashCollision p := by
  -- Both paths lead to the same root from the same index.
  have hroot := (verify_eq_some_iff.mp h).1.trans (verify_eq_some_iff.mp h').1.symm
  have binding := Merkle.climb_binding treeHash _ _ 0 i.toNat _ _ (by simp) hroot
  -- The search succeeds unless the secrets are equal.
  have found : o.secret = o'.secret ∨ (findHashCollision i o o').isSome := by
    unfold findHashCollision
    rcases binding with ⟨hleaf, -⟩ | hfound
    · -- Equal leaves come from equal secrets, or the leaf hash collides.
      by_cases hs : o.secret = o'.secret
      · exact .inl hs
      · right
        split
        · rfl
        · simp only [ne_eq, hs, not_false_eq_true, hleaf, and_self, ↓reduceIte,
            Option.isSome_some]
    · -- Otherwise the search finds a collision of the node hash.
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hfound
      rw [hc]
      exact .inr rfl
  -- What the search returns is a collision of Keccak-256.
  refine found.imp id fun hsome => ?_
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨p, hp, findHashCollision_valid hp⟩

/--
Uniqueness: two openings that verify at one index under one root give one output.

Otherwise the collision search returns a collision of Keccak-256.

For a Merkle tree, the same property is usually called position binding.

One index under one root opens to one leaf, as the theorem above states.
-/
theorem verify_unique {root : Digest} {i : UInt32} {o o' : Opening} {y y' : Digest}
    (h : verify root i o = some y) (h' : verify root i o' = some y') :
    y = y' ∨ ∃ p, findHashCollision i o o' = some p ∧ IsHashCollision p := by
  rcases verify_secret_unique h h' with hs | hcol
  · -- One secret has one output.
    rw [verify_output h, verify_output h', hs]
    exact .inl rfl
  · exact .inr hcol

/-- Against an honest tree, every valid opening at index `i` gives the output of secret `i`.

Otherwise the collision search returns a Keccak-256 collision with the honest opening. -/
theorem verify_root_unique {secrets : UInt32 → Digest} {i : UInt32} {o : Opening} {y : Digest}
    (h : verify (root secrets) i o = some y) :
    y = outputHash i (secrets i) ∨
      ∃ p, findHashCollision i o (opening secrets i) = some p ∧ IsHashCollision p :=
  verify_unique h (verify_opening secrets i)

end EthLib.Cryptography.Vrf
