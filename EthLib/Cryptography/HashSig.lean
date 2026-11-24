module

public import EthLib.Base.Bytes

/-!
# The common frame of the hash-based signatures

leanXMSS and leanSPHINCS share three tools, and neither scheme owns them.

- A hash function as a computation in the identity monad.
- A read of a fixed-size object out of a buffer, which fails on a short buffer.
- A vector computed entry by entry, index 0 first.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open EthLib.Base (readBytes)

/-! ## The hash as a computation

Every definition of the two schemes that hashes takes the hash `H` as an argument, in a monad.

EthLib passes the concrete hash in the identity monad, and a random-oracle proof passes a query.
-/

/-- A hash function, as a computation in the identity monad.

The input and output types are parameters: leanSPHINCS hashes bytes, leanXMSS lanes. -/
def pureHash {α β : Type} (f : α → β) (input : α) : Id β :=
  pure (f input)

/-! ## Reading fixed-size objects -/

/-- Read a fixed-size object out of a buffer at an offset.

Returns nothing when the buffer has no room for the object.
-/
def unpackBytes? (n : Nat) (b : ByteArray) (offset : Nat := 0) :
    Option (Vector UInt8 n) :=
  -- Take `b = ByteArray.mk #[10, 20, 30, 40]` as an example.
  --
  -- Then 4 bytes at offset 0 read as `some #v[10, 20, 30, 40]`.
  --
  -- 2 bytes at offset 1 read as `some #v[20, 30]`.
  --
  -- 2 bytes at offset 3 read as `none`.
  --
  -- The read never pads and never truncates.
  --
  -- The guard is the whole validation: a buffer without room is rejected.
  if h : offset + n ≤ b.size then some (readBytes b offset n h) else none

/-! ## Computing a vector in order -/

/-- Run one computation per index, index 0 first, and collect the results.

The order matters when each computation calls the hash.

It fixes the sequence of hash calls, which a proof in the random oracle model counts. -/
def ofFnInOrder {m : Type → Type} [Monad m] {α : Type} (n : Nat) (f : Fin n → m α) :
    m (Vector α n) :=
  -- Core's monadic vector builder recurses on a well-founded measure.
  --
  -- The kernel does not reduce that recursion.
  --
  -- So this one recurses structurally on the number of entries left.
  go n (Array.emptyWithCapacity n) (by simp)
where
  /-- The results of the last `k` indices, after the results of the others in `acc`.

  Structural recursion, so the kernel can evaluate it.

  Each result is pushed at the end, so `n` results take linear time. -/
  go : (k : Nat) → (acc : Array α) → acc.size + k = n → m (Vector α n)
    | 0, acc, h => pure ⟨acc, by omega⟩
    | k + 1, acc, h => do
      -- The next index is the number of results so far.
      let x ← f ⟨acc.size, by omega⟩
      go k (acc.push x) (by simp only [Array.size_push]; omega)

end EthLib.Cryptography.HashSig
