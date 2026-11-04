module

public import EthLib.Execution.Proofs.Trie.Proof

/-!
# Proofs: the root binds the value of every key

Every 32-byte hash of byte strings has collisions.

So "two tries with one root agree, or the hash collides" would say nothing.

Instead, each theorem names a search that returns the collision.

The search reads the proofs of one key in the two tries, node by node from the root.

It returns the first two nodes at one place that differ but have one hash.

Two proofs that verify against one root follow one path while their nodes agree.

So when the search finds nothing, both proofs give the key one value.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## The search -/

/-- Two different node encodings with one hash. -/
def IsCollision (hash : ByteArray → Hash32) (pair : ByteArray × ByteArray) : Prop :=
  pair.1 ≠ pair.2 ∧ hash pair.1 = hash pair.2

/-- The first place where two proofs hold different nodes with one hash. -/
def findProofCollision (hash : ByteArray → Hash32) :
    List ByteArray → List ByteArray → Option (ByteArray × ByteArray)
  | a :: p, b :: q => if a ≠ b ∧ hash a = hash b then some (a, b) else findProofCollision hash p q
  | _, _ => none

/-- Every pair that the search returns is a collision. -/
theorem findProofCollision_valid (hash : ByteArray → Hash32) :
    (p q : List ByteArray) → {pair : ByteArray × ByteArray} →
      findProofCollision hash p q = some pair → IsCollision hash pair
  | a :: p, b :: q, pair, h => by
    simp only [findProofCollision] at h
    split at h
    · rename_i hfound
      cases h
      exact hfound
    · exact findProofCollision_valid hash p q h

/-- A proof compared with itself has no collision. -/
theorem findProofCollision_self (hash : ByteArray → Hash32) :
    (p : List ByteArray) → findProofCollision hash p p = none
  | [] => rfl
  | a :: p => by simp [findProofCollision, findProofCollision_self hash p]

/-! ## Two proofs of one key -/

/-- Two proofs with no collision follow one reference to one item.

The proofs left after it have no collision either. -/
theorem resolve_binding (hash : ByteArray → Hash32) {reference : Item} {p q p' q' : List ByteArray}
    {item item' : Item} (hp : resolve hash reference p = .ok (item, p'))
    (hq : resolve hash reference q = .ok (item', q'))
    (hcollision : findProofCollision hash p q = none) :
    item = item' ∧ findProofCollision hash p' q' = none := by
  unfold resolve at hp hq
  split at hp
  · -- A node held inside its parent takes no proof node.
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp hq
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨rfl, rfl⟩ := hq
    exact ⟨rfl, hcollision⟩
  · rename_i digest
    split at hp
    · -- The empty reference points to no node, and takes no proof node.
      rename_i hsize
      simp only [hsize, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hp hq
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl⟩ := hq
      exact ⟨rfl, hcollision⟩
    · rename_i hsize
      split at hp
      · -- A node held by hash is the next node of each proof, and both have the hash.
        rename_i hsize32
        simp only [hsize32, ↓reduceIte] at hq
        match p, q, hp, hq with
        | [], _, hp, _ => cases hp
        | _ :: _, [], _, hq => simp at hq
        | a :: p, b :: q, hp, hq =>
          simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte] at hp hq
          by_cases ha : (hash a).toList = digest.data.toList
          · by_cases hb : (hash b).toList = digest.data.toList
            · -- The two nodes have one hash, so without a collision they are one node.
              have hhash : hash a = hash b := Vector.toList_inj.mp (ha.trans hb.symm)
              simp only [findProofCollision, hhash, and_true, ite_not] at hcollision
              split at hcollision
              · rename_i hab
                subst hab
                simp only [ha, ↓reduceIte] at hp hq
                cases hdecode : decode a with
                | error => simp [hdecode, Except.mapError, Bind.bind, Except.bind] at hp
                | ok decoded =>
                  simp only [hdecode, Except.mapError, Bind.bind, Except.bind, pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at hp hq
                  obtain ⟨rfl, rfl⟩ := hp
                  obtain ⟨rfl, rfl⟩ := hq
                  exact ⟨rfl, hcollision⟩
              · cases hcollision
            · simp [hb] at hq
          · simp [ha] at hp
      · cases hp

/-- Two proofs with no collision that the walk accepts on one path from one item give one value. -/
theorem walk_binding (hash : ByteArray → Hash32) :
    (fuel : Nat) → (node : Item) → (path : List Nibble) → {p q p' q' : List ByteArray} →
      {v w : Option ByteArray} → walk hash fuel node path p = .ok (v, p') →
      walk hash fuel node path q = .ok (w, q') →
      findProofCollision hash p q = none → v = w
  | 0, _, _, _, _, _, _, _, _, hp, _, _ => by cases hp
  | fuel + 1, .bytes data, path, p, q, p', q', v, w, hp, hq, _ => by
    -- The empty byte string is no node, so neither proof sets the key.
    simp only [walk] at hp hq
    split at hp
    · rename_i hsize
      simp only [hsize, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hp hq
      rw [← hp.1, ← hq.1]
    · cases hp
  | fuel + 1, .list items, path, p, q, p', q', v, w, hp, hq, hcollision => by
    cases hdecode : decodeNode (.list items) with
    | error => simp [walk, hdecode, Bind.bind, Except.bind] at hp
    | ok decoded =>
      -- Both proofs follow one child to one item, and walk on from it.
      have hfollow : ∀ (reference : Item) (rest : List Nibble) {p q p' q' : List ByteArray}
          {v w : Option ByteArray}, follow hash fuel reference rest p = .ok (v, p') →
          follow hash fuel reference rest q = .ok (w, q') →
          findProofCollision hash p q = none → v = w := by
        intro reference rest p q p' q' v w hp hq hcollision
        simp only [follow] at hp hq
        cases hp' : resolve hash reference p with
        | error => simp [hp', Except.bind] at hp
        | ok next =>
          cases hq' : resolve hash reference q with
          | error => simp [hq', Except.bind] at hq
          | ok next' =>
            simp only [hp', hq', Except.bind] at hp hq
            obtain ⟨hitem, hnext⟩ := resolve_binding hash hp' hq' hcollision
            rw [hitem] at hp
            exact walk_binding hash fuel _ rest hp hq hnext
      cases decoded with
      | leaf restOfKey value =>
        simp only [walk_decoded hash fuel hdecode] at hp hq
        simp only [Except.ok.injEq, Prod.mk.injEq] at hp hq
        rw [← hp.1, ← hq.1]
      | extension keySegment subnode =>
        simp only [walk_decoded hash fuel hdecode] at hp hq
        split at hp
        · rename_i hsegment
          rw [ite_eq_left hsegment] at hq
          exact hfollow _ _ hp hq hcollision
        · rename_i hsegment
          rw [ite_eq_right hsegment] at hq
          simp only [Except.ok.injEq, Prod.mk.injEq] at hp hq
          rw [← hp.1, ← hq.1]
      | branch subnodes value =>
        simp only [walk_decoded hash fuel hdecode] at hp hq
        cases path with
        | nil =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hp hq
          rw [← hp.1, ← hq.1]
        | cons nibble rest => exact hfollow _ _ hp hq hcollision

/-- Binding of a proof: two proofs that verify one key against one root give one value.

Otherwise the search finds a collision in the two proofs. -/
theorem verifyProof_binding (hash : ByteArray → Hash32) {root : Hash32} {secured : Bool}
    {key : ByteArray} {p q : List ByteArray} {v w : Option ByteArray}
    (hp : verifyProof hash root secured key p = .ok v)
    (hq : verifyProof hash root secured key q = .ok w) :
    v = w ∨ ∃ pair, findProofCollision hash p q = some pair ∧ IsCollision hash pair := by
  cases hcollision : findProofCollision hash p q with
  | some pair => exact .inr ⟨pair, rfl, findProofCollision_valid hash p q hcollision⟩
  | none =>
    refine .inl ?_
    simp only [verifyProof, Bind.bind, Except.bind] at hp hq
    -- Both proofs resolve the root to one item, then walk the key's path from it.
    cases hp' : resolve hash (.bytes ⟨root.toArray⟩) p with
    | error => simp [hp'] at hp
    | ok next =>
      cases hq' : resolve hash (.bytes ⟨root.toArray⟩) q with
      | error => simp [hq'] at hq
      | ok next' =>
        obtain ⟨item, rest⟩ := next
        obtain ⟨item', rest'⟩ := next'
        obtain ⟨rfl, hrest⟩ := resolve_binding hash hp' hq' hcollision
        simp only [hp', hq'] at hp hq
        generalize keyPath hash secured key = path at hp hq
        cases hp'' : walk hash (path.length + 1) item path rest with
        | error => simp [hp''] at hp
        | ok outcome =>
          cases hq'' : walk hash (path.length + 1) item path rest' with
          | error => simp [hq''] at hq
          | ok outcome' =>
            obtain ⟨value, unused⟩ := outcome
            obtain ⟨value', unused'⟩ := outcome'
            have hvalue := walk_binding hash _ _ _ hp'' hq'' hrest
            simp only [hp'', hq''] at hp hq
            split at hp
            · split at hq
              · simp only [pure, Except.pure, Except.ok.injEq] at hp hq
                rw [← hp, ← hq, hvalue]
              · cases hq
            · cases hp

/-! ## Two tries with one root -/

/-- The first collision in the proofs of one key in two tries, if any. -/
def findCollision (hash : ByteArray → Hash32) (trie₁ trie₂ : Trie) (key : ByteArray) :
    Option (ByteArray × ByteArray) :=
  match getProof hash trie₁ key, getProof hash trie₂ key with
  | .ok p, .ok q => findProofCollision hash p q
  | _, _ => none

/-- Every pair that the search returns is a collision. -/
theorem findCollision_valid (hash : ByteArray → Hash32) {trie₁ trie₂ : Trie} {key : ByteArray}
    {pair : ByteArray × ByteArray} (h : findCollision hash trie₁ trie₂ key = some pair) :
    IsCollision hash pair := by
  unfold findCollision at h
  split at h
  · exact findProofCollision_valid hash _ _ h
  · cases h

/-- A trie compared with itself has no collision. -/
theorem findCollision_self (hash : ByteArray → Hash32) (trie : Trie) (key : ByteArray) :
    findCollision hash trie trie key = none := by
  unfold findCollision
  split
  · rename_i p q hp hq
    rw [hp] at hq
    cases hq
    exact findProofCollision_self hash p
  · rfl

/-- Binding of the root: two tries with one root give every key one value.

Otherwise the search finds a collision in the proofs of that key.

The two tries must hash their keys alike, and the keys of each must have distinct paths. -/
theorem root_binding (hash : ByteArray → Hash32) {trie₁ trie₂ : Trie} {root' : Hash32}
    (hsecured : trie₁.secured = trie₂.secured)
    (hroot₁ : root hash trie₁ = .ok root') (hroot₂ : root hash trie₂ = .ok root')
    (hpaths₁ : (trie₁.data.map fun entry => keyPath hash trie₁.secured entry.1).Nodup)
    (hpaths₂ : (trie₂.data.map fun entry => keyPath hash trie₂.secured entry.1).Nodup)
    (key : ByteArray) :
    valueAt hash trie₁ key = valueAt hash trie₂ key ∨
      ∃ pair, findCollision hash trie₁ trie₂ key = some pair ∧ IsCollision hash pair := by
  -- Each trie's proof of the key verifies against the one root, with the trie's value of the key.
  obtain ⟨p, hp⟩ := getProof_ok hash hroot₁ key
  obtain ⟨q, hq⟩ := getProof_ok hash hroot₂ key
  have hverify₁ := verifyProof_getProof hash hroot₁ hp hpaths₁
  have hverify₂ := verifyProof_getProof hash hroot₂ hq hpaths₂
  rw [hsecured] at hverify₁
  rcases verifyProof_binding hash hverify₁ hverify₂ with hvalue | ⟨pair, hfind, hvalid⟩
  · exact .inl hvalue
  · exact .inr ⟨pair, by simp [findCollision, hp, hq, hfind], hvalid⟩

end EthLib.Execution.Trie
