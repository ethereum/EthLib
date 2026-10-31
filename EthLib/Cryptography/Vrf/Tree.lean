import EthLib.Cryptography.Vrf.Types

/-!
# `Vrf.Tree`

A binary Merkle tree of height `h`, generic in its nodes and its node hash.

For `1 <= lambda <= h`:

```text
    X_{0,j} = leaves(j)
    X_{lambda,j} = hash(X_{lambda-1,2j}, X_{lambda-1,2j+1})
```

The root is `X_{h,0}`.

The path of leaf `i` holds the sibling of `i`'s ancestor on each level, from the leaf up.

Climbing a leaf with its path recomputes the root.

Nothing here is specific to the VRF, which uses this tree with its own leaves and node hash.
-/

namespace EthLib.Cryptography.Vrf.Tree

variable {α : Type} (hash : α → α → α)

/-- `X_{level,j}`: node `j` on `level`.

Computing it evaluates the `2^level` leaves below it. -/
def node (leaves : Nat → α) : (level j : Nat) → α
  | 0, j => leaves j
  -- The children of node `j` on level `l + 1` are `2j` and `2j + 1` on level `l`.
  | l + 1, j => hash (node leaves l (2 * j)) (node leaves l (2 * j + 1))

/-- The root of the tree of height `h`: its one node on level `h`. -/
def root (h : Nat) (leaves : Nat → α) : α :=
  node hash leaves h 0

/-- The siblings of leaf `i`'s ancestors on `n` consecutive levels, from level `k` up.

The sibling on level `k` is that ancestor with its low bit flipped. -/
def siblings (leaves : Nat → α) (i : Nat) : (k n : Nat) → List α
  | _, 0 => []
  | k, n + 1 => node hash leaves k ((i >>> k) ^^^ 1) :: siblings leaves i (k + 1) n

/-- There is one sibling per level. -/
theorem length_siblings (leaves : Nat → α) (i : Nat) :
    ∀ k n, (siblings hash leaves i k n).length = n
  | _, 0 => rfl
  | k, n + 1 => by simp [siblings, length_siblings leaves i (k + 1) n]

/-- The path of leaf `i` in a tree of height `h`, from the leaf up.

```text
    pi_lambda = X_{lambda, floor(i / 2^lambda) xor 1}
```
-/
def path (h : Nat) (leaves : Nat → α) (i : Nat) : Vector α h :=
  ⟨⟨siblings hash leaves i 0 h⟩, by simp [length_siblings]⟩

/-- The node reached by climbing from a node, hashing in one sibling per level.

The low bit of `i` says which child the held node is, and the climb goes on with `i / 2`. -/
def climb : (i : Nat) → α → List α → α
  | _, current, [] => current
  | i, current, sibling :: rest =>
    -- Bit zero: the held node is the left child.
    -- Bit one: it is the right child.
    climb (i / 2) (if i % 2 = 0 then hash current sibling else hash sibling current) rest

end EthLib.Cryptography.Vrf.Tree
