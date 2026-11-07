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

So when the search finds nothing, the two proofs are one proof, and give the key one value.

Soundness follows: a proof that verifies against a trie's root is the trie's own proof.

Otherwise the search finds a collision between the two.

A secured trie gives one root for any order of its entries.

Otherwise a search over its keys returns two keys with one hash.

The same search covers two keys that share a path in soundness and in binding.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## The search -/

/-- Two different byte strings with one hash, such as two node encodings or two keys. -/
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

/-- A common prefix of two proofs holds no collision. -/
theorem findProofCollision_append (hash : ByteArray → Hash32) (p q : List ByteArray) :
    (used : List ByteArray) →
      findProofCollision hash (used ++ p) (used ++ q) = findProofCollision hash p q
  | [] => rfl
  | a :: used => by simp [findProofCollision, findProofCollision_append hash p q used]

/-! ## Two proofs of one key -/

/-- Two proofs with no collision follow one reference to one item.

They use the same proof nodes to reach it. -/
theorem resolve_binding (hash : ByteArray → Hash32) {reference : Item} {p q p' q' : List ByteArray}
    {item item' : Item} (hp : resolve hash reference p = .ok (item, p'))
    (hq : resolve hash reference q = .ok (item', q'))
    (hcollision : findProofCollision hash p q = none) :
    item = item' ∧ ∃ used, p = used ++ p' ∧ q = used ++ q' := by
  unfold resolve at hp hq
  split at hp
  · -- A node held inside its parent takes no proof node.
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp hq
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨rfl, rfl⟩ := hq
    exact ⟨rfl, [], rfl, rfl⟩
  · rename_i digest
    split at hp
    · -- The empty reference points to no node, and takes no proof node.
      rename_i hsize
      simp only [hsize, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hp hq
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl⟩ := hq
      exact ⟨rfl, [], rfl, rfl⟩
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
                  exact ⟨rfl, [a], rfl, rfl⟩
              · cases hcollision
            · simp [hb] at hq
          · simp [ha] at hp
      · cases hp

/-- Two proofs with no collision that the walk accepts on one path from one item give one value.

They use the same proof nodes to reach it. -/
theorem walk_binding (hash : ByteArray → Hash32) :
    (fuel : Nat) → (node : Item) → (path : List Nibble) → {p q p' q' : List ByteArray} →
      {v w : Option ByteArray} → walk hash fuel node path p = .ok (v, p') →
      walk hash fuel node path q = .ok (w, q') →
      findProofCollision hash p q = none → v = w ∧ ∃ used, p = used ++ p' ∧ q = used ++ q'
  | 0, _, _, _, _, _, _, _, _, hp, _, _ => by cases hp
  | fuel + 1, .bytes data, path, p, q, p', q', v, w, hp, hq, _ => by
    -- The empty byte string is no node, so neither proof sets the key or uses a node.
    simp only [walk] at hp hq
    split at hp
    · rename_i hsize
      simp only [hsize, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hp hq
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl⟩ := hq
      exact ⟨rfl, [], rfl, rfl⟩
    · cases hp
  | fuel + 1, .list items, path, p, q, p', q', v, w, hp, hq, hcollision => by
    cases hdecode : decodeNode (.list items) with
    | error => simp [walk, hdecode, Bind.bind, Except.bind] at hp
    | ok decoded =>
      -- Both proofs follow one child to one item, and walk on from it.
      have hfollow : ∀ (reference : Item) (rest : List Nibble) {p q p' q' : List ByteArray}
          {v w : Option ByteArray}, follow hash fuel reference rest p = .ok (v, p') →
          follow hash fuel reference rest q = .ok (w, q') →
          findProofCollision hash p q = none → v = w ∧ ∃ used, p = used ++ p' ∧ q = used ++ q' := by
        intro reference rest p q p' q' v w hp hq hcollision
        simp only [follow] at hp hq
        cases hp' : resolve hash reference p with
        | error => simp [hp', Except.bind] at hp
        | ok next =>
          cases hq' : resolve hash reference q with
          | error => simp [hq', Except.bind] at hq
          | ok next' =>
            obtain ⟨item, after⟩ := next
            obtain ⟨item', after'⟩ := next'
            simp only [hp', hq', Except.bind] at hp hq
            obtain ⟨rfl, used, rfl, rfl⟩ := resolve_binding hash hp' hq' hcollision
            rw [findProofCollision_append] at hcollision
            obtain ⟨hvalue, used', rfl, rfl⟩ := walk_binding hash fuel _ rest hp hq hcollision
            exact ⟨hvalue, used ++ used', by simp, by simp⟩
      cases decoded with
      | leaf restOfKey value =>
        simp only [walk_decoded hash fuel hdecode] at hp hq
        simp only [Except.ok.injEq, Prod.mk.injEq] at hp hq
        obtain ⟨rfl, rfl⟩ := hp
        obtain ⟨rfl, rfl⟩ := hq
        exact ⟨rfl, [], rfl, rfl⟩
      | extension keySegment subnode =>
        simp only [walk_decoded hash fuel hdecode] at hp hq
        split at hp
        · rename_i hsegment
          rw [ite_eq_left hsegment] at hq
          exact hfollow _ _ hp hq hcollision
        · rename_i hsegment
          rw [ite_eq_right hsegment] at hq
          simp only [Except.ok.injEq, Prod.mk.injEq] at hp hq
          obtain ⟨rfl, rfl⟩ := hp
          obtain ⟨rfl, rfl⟩ := hq
          exact ⟨rfl, [], rfl, rfl⟩
      | branch subnodes value =>
        simp only [walk_decoded hash fuel hdecode] at hp hq
        cases path with
        | nil =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hp hq
          obtain ⟨rfl, rfl⟩ := hp
          obtain ⟨rfl, rfl⟩ := hq
          exact ⟨rfl, [], rfl, rfl⟩
        | cons nibble rest => exact hfollow _ _ hp hq hcollision

/-- Binding of a proof: two proofs that verify one key against one root are one proof.

So they give one value.

Otherwise the search finds a collision in the two proofs. -/
theorem verifyProof_binding (hash : ByteArray → Hash32) {root : Hash32} {secured : Bool}
    {key : ByteArray} {p q : List ByteArray} {v w : Option ByteArray}
    (hp : verifyProof hash root secured key p = .ok v)
    (hq : verifyProof hash root secured key q = .ok w) :
    (p = q ∧ v = w) ∨ ∃ pair, findProofCollision hash p q = some pair ∧ IsCollision hash pair := by
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
        obtain ⟨rfl, used, rfl, rfl⟩ := resolve_binding hash hp' hq' hcollision
        rw [findProofCollision_append] at hcollision
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
            obtain ⟨hvalue, used', rfl, rfl⟩ := walk_binding hash _ _ _ hp'' hq'' hcollision
            simp only [hp'', hq''] at hp hq
            -- Each proof is the nodes that the walk used, with no node left.
            split at hp
            · split at hq
              · rename_i hunused hunused'
                simp only [pure, Except.pure, Except.ok.injEq] at hp hq
                simp [List.isEmpty_iff.mp hunused, List.isEmpty_iff.mp hunused', ← hp, ← hq, hvalue]
              · cases hq
            · cases hp

/-! ## Keys with one hash -/

/-- The first two different keys of the list with one hash, if any. -/
def findKeyCollision (hash : ByteArray → Hash32) : List ByteArray → Option (ByteArray × ByteArray)
  | [] => none
  | key :: rest =>
    match rest.find? fun other => other ≠ key ∧ hash other = hash key with
    | some other => some (key, other)
    | none => findKeyCollision hash rest

/-- Every pair that the search returns is a collision. -/
theorem findKeyCollision_valid (hash : ByteArray → Hash32) :
    (keys : List ByteArray) → {pair : ByteArray × ByteArray} →
      findKeyCollision hash keys = some pair → IsCollision hash pair
  | [], _, h => by cases h
  | key :: rest, pair, h => by
    unfold findKeyCollision at h
    split at h
    · rename_i other hfind
      cases h
      have hother := List.find?_some hfind
      simp only [ne_eq, decide_eq_true_eq] at hother
      exact ⟨fun heq => hother.1 heq.symm, hother.2.symm⟩
    · exact findKeyCollision_valid hash rest h

/-- Keys with distinct hashes have no collision, so the search can return none. -/
theorem findKeyCollision_of_nodup (hash : ByteArray → Hash32) :
    (keys : List ByteArray) → (keys.map hash).Nodup → findKeyCollision hash keys = none
  | [], _ => rfl
  | key :: rest, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    unfold findKeyCollision
    rw [List.find?_eq_none.mpr fun other hmem hother => h.1 other hmem (by simp_all)]
    exact findKeyCollision_of_nodup hash rest h.2

/-- Distinct keys in which the search finds no collision have distinct hashes. -/
theorem nodup_map_of_findKeyCollision (hash : ByteArray → Hash32) :
    (keys : List ByteArray) → keys.Nodup → findKeyCollision hash keys = none →
      (keys.map hash).Nodup
  | [], _, _ => List.nodup_nil
  | key :: rest, hkeys, h => by
    rw [List.nodup_cons] at hkeys
    unfold findKeyCollision at h
    split at h
    · cases h
    · rename_i hfind
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      refine ⟨fun other hmem heq => ?_, nodup_map_of_findKeyCollision hash rest hkeys.2 h⟩
      have hother := List.find?_eq_none.mp hfind other hmem
      simp only [ne_eq, decide_eq_true_eq, not_and] at hother
      -- A key with the hash of the first key is the first key, which the rest does not hold.
      exact hkeys.1 (Decidable.byContradiction (fun hne => hother hne heq) ▸ hmem)

/-- Two different keys of a trie with one path.

Only a secured trie can have them, as two keys with one hash. -/
def findPathCollision (hash : ByteArray → Hash32) (trie : Trie) : Option (ByteArray × ByteArray) :=
  if trie.secured then findKeyCollision hash (trie.data.map Prod.fst) else none

/-- Every pair that the search returns is a collision. -/
theorem findPathCollision_valid (hash : ByteArray → Hash32) {trie : Trie}
    {pair : ByteArray × ByteArray} (h : findPathCollision hash trie = some pair) :
    IsCollision hash pair := by
  unfold findPathCollision at h
  split at h
  · exact findKeyCollision_valid hash _ h
  · cases h

/-- Distinct keys have distinct paths, unless the search finds two keys with one hash. -/
theorem keyPath_nodup (hash : ByteArray → Hash32) {trie : Trie}
    (hkeys : (trie.data.map Prod.fst).Nodup) (hsearch : findPathCollision hash trie = none) :
    (trie.data.map fun entry => keyPath hash trie.secured entry.1).Nodup := by
  obtain ⟨secured, data⟩ := trie
  unfold findPathCollision at hsearch
  cases secured with
  | false =>
    -- A plain trie: distinct keys have distinct nibbles.
    simpa [keyPath, List.map_map, Function.comp_def] using
      nodup_map_of_injective (fun _ _ h => bytesToNibbleList_injective h) hkeys
  | true =>
    -- A secured trie: distinct hashes have distinct bytes, and distinct bytes distinct nibbles.
    simp only [↓reduceIte] at hsearch
    have hhashes := nodup_map_of_findKeyCollision hash _ hkeys hsearch
    have hbytes := nodup_map_of_injective hashBytes_injective hhashes
    simpa [keyPath, List.map_map, Function.comp_def] using
      nodup_map_of_injective (fun _ _ h => bytesToNibbleList_injective h) hbytes

/-- Soundness: a proof that verifies against the trie's root is the proof that the trie builds.

So it gives the trie's value of the key.

Otherwise the search finds a collision between the proof and the honest proof.

Or a secured trie has two keys with one hash, which the key search finds.

The keys of the trie must be distinct. -/
theorem verifyProof_sound (hash : ByteArray → Hash32) {trie : Trie} {key : ByteArray}
    {root' : Hash32}
    {honestProof proof : List ByteArray} {result : Option ByteArray}
    (hroot : root hash trie = .ok root') (hhonest : getProof hash trie key = .ok honestProof)
    (hkeys : (trie.data.map Prod.fst).Nodup)
    (hverify : verifyProof hash root' trie.secured key proof = .ok result) :
    (proof = honestProof ∧ result = valueAt hash trie key) ∨
      (∃ pair, findProofCollision hash proof honestProof = some pair ∧ IsCollision hash pair) ∨
      ∃ pair, findPathCollision hash trie = some pair ∧ IsCollision hash pair := by
  cases hsearch : findPathCollision hash trie with
  | some pair => exact .inr (.inr ⟨pair, rfl, findPathCollision_valid hash hsearch⟩)
  | none =>
    have hpaths := keyPath_nodup hash hkeys hsearch
    rcases verifyProof_binding hash hverify (verifyProof_getProof hash hroot hhonest hpaths)
      with hhonest | hfound
    · exact .inl hhonest
    · exact .inr (.inl hfound)

/-- Soundness for the map built by setting pairs in order, as in the trie root export.

Later entries replace earlier values, and an empty value removes its key.

Verification hashes the key exactly when the empty trie does.

The construction gives distinct keys, which the trie of Yellow Paper Appendix D assumes. -/
theorem verifyProof_sound_foldl_trieSet (hash : ByteArray → Hash32) (secured : Bool)
    (pairs : List (ByteArray × ByteArray)) :
    let trie := pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured, []⟩
    ∀ {key : ByteArray} {root' : Hash32} {honestProof proof : List ByteArray}
      {result : Option ByteArray},
      root hash trie = .ok root' → getProof hash trie key = .ok honestProof →
      verifyProof hash root' secured key proof = .ok result →
      (proof = honestProof ∧ result = valueAt hash trie key) ∨
        (∃ pair, findProofCollision hash proof honestProof = some pair ∧ IsCollision hash pair) ∨
        ∃ pair, findPathCollision hash trie = some pair ∧ IsCollision hash pair := by
  intro trie key root' honestProof proof result hroot hhonest hverify
  -- Setting pairs keeps the flag of the empty trie.
  have hsecured : trie.secured = secured := secured_foldl_trieSet pairs _
  exact verifyProof_sound hash hroot hhonest
    (nodup_keys_foldl_trieSet secured pairs) (hsecured ▸ hverify)

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

Or one of two secured tries has two keys with one hash, which the key search finds.

The two tries must hash their keys alike, and the keys of each must be distinct. -/
theorem root_binding (hash : ByteArray → Hash32) {trie₁ trie₂ : Trie} {root' : Hash32}
    (hsecured : trie₁.secured = trie₂.secured)
    (hroot₁ : root hash trie₁ = .ok root') (hroot₂ : root hash trie₂ = .ok root')
    (hkeys₁ : (trie₁.data.map Prod.fst).Nodup) (hkeys₂ : (trie₂.data.map Prod.fst).Nodup)
    (key : ByteArray) :
    valueAt hash trie₁ key = valueAt hash trie₂ key ∨
      (∃ pair, findCollision hash trie₁ trie₂ key = some pair ∧ IsCollision hash pair) ∨
      (∃ pair, findPathCollision hash trie₁ = some pair ∧ IsCollision hash pair) ∨
      ∃ pair, findPathCollision hash trie₂ = some pair ∧ IsCollision hash pair := by
  -- A secured trie with two keys of one hash gives the collision outright.
  cases hsearch₁ : findPathCollision hash trie₁ with
  | some pair => exact .inr (.inr (.inl ⟨pair, rfl, findPathCollision_valid hash hsearch₁⟩))
  | none =>
  cases hsearch₂ : findPathCollision hash trie₂ with
  | some pair => exact .inr (.inr (.inr ⟨pair, rfl, findPathCollision_valid hash hsearch₂⟩))
  | none =>
  have hpaths₁ := keyPath_nodup hash hkeys₁ hsearch₁
  have hpaths₂ := keyPath_nodup hash hkeys₂ hsearch₂
  -- Each trie's proof of the key verifies against the one root, with the trie's value of the key.
  obtain ⟨p, hp⟩ := getProof_ok hash hroot₁ key
  obtain ⟨q, hq⟩ := getProof_ok hash hroot₂ key
  have hverify₁ := verifyProof_getProof hash hroot₁ hp hpaths₁
  have hverify₂ := verifyProof_getProof hash hroot₂ hq hpaths₂
  rw [hsecured] at hverify₁
  rcases verifyProof_binding hash hverify₁ hverify₂ with ⟨-, hvalue⟩ | ⟨pair, hfind, hvalid⟩
  · exact .inl hvalue
  · exact .inr (.inl ⟨pair, by simp [findCollision, hp, hq, hfind], hvalid⟩)

/-- Binding for maps built by setting pairs in order, as in the trie root export.

The lists may repeat keys or remove them with empty values.

Each construction gives distinct keys, which the trie of Yellow Paper Appendix D assumes. -/
theorem root_binding_foldl_trieSet (hash : ByteArray → Hash32) (secured : Bool)
    (pairs₁ pairs₂ : List (ByteArray × ByteArray)) :
    let trie₁ := pairs₁.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured, []⟩
    let trie₂ := pairs₂.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured, []⟩
    ∀ {root' : Hash32}, root hash trie₁ = .ok root' → root hash trie₂ = .ok root' →
      ∀ key : ByteArray, valueAt hash trie₁ key = valueAt hash trie₂ key ∨
        (∃ pair, findCollision hash trie₁ trie₂ key = some pair ∧ IsCollision hash pair) ∨
        (∃ pair, findPathCollision hash trie₁ = some pair ∧ IsCollision hash pair) ∨
        ∃ pair, findPathCollision hash trie₂ = some pair ∧ IsCollision hash pair := by
  intro trie₁ trie₂ root' hroot₁ hroot₂ key
  -- Both maps retain the same choice of plain or hashed paths through every update.
  have hsecured : trie₁.secured = trie₂.secured := by
    dsimp [trie₁, trie₂]
    rw [secured_foldl_trieSet, secured_foldl_trieSet]
  exact root_binding hash hsecured hroot₁ hroot₂
    (nodup_keys_foldl_trieSet secured pairs₁) (nodup_keys_foldl_trieSet secured pairs₂) key

/-- Order of a secured trie: any order of its entries gives one root.

Otherwise the search over its keys returns two keys with one hash.

The keys must be distinct. -/
theorem root_secured_perm (hash : ByteArray → Hash32) {data data' : List (ByteArray × ByteArray)}
    (hperm : data.Perm data') (hkeys : (data.map Prod.fst).Nodup) :
    root hash ⟨true, data⟩ = root hash ⟨true, data'⟩ ∨
      ∃ pair, findKeyCollision hash (data.map Prod.fst) = some pair ∧ IsCollision hash pair := by
  cases hfind : findKeyCollision hash (data.map Prod.fst) with
  | some pair => exact .inr ⟨pair, rfl, findKeyCollision_valid hash _ hfind⟩
  | none =>
    refine .inl (root_perm hash hperm ?_)
    -- Distinct hashes have distinct bytes, and distinct bytes have distinct nibbles.
    have hhashes := nodup_map_of_findKeyCollision hash _ hkeys hfind
    have hbytes := nodup_map_of_injective hashBytes_injective hhashes
    simpa [keyPath, List.map_map, Function.comp_def] using
      nodup_map_of_injective (fun _ _ h => bytesToNibbleList_injective h) hbytes

end EthLib.Execution.Trie
