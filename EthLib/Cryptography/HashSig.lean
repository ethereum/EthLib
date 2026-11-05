module

public import EthLib.Base.Bytes

/-!
# The common frame of the hash-based signatures

leanXMSS and leanSPHINCS share three tools, and neither scheme owns them.

- A hash function as a computation in the identity monad.
- A read of a fixed-size object out of a buffer, which fails on a short buffer.
- A vector computed entry by entry, index 0 first.

Every definition of the two schemes that hashes takes the hash `H` as an argument, in a monad.

EthLib passes the concrete hash in the identity monad.

A proof in the random oracle model passes a query to the oracle.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open EthLib.Base (readBytes)

/-! ## The hash as a computation -/

/-- A hash function, as a computation in the identity monad. -/
def pureHash (f : ByteArray → Vector UInt8 32) (input : ByteArray) : Id (Vector UInt8 32) :=
  pure (f input)

/-! ## Reading fixed-size objects -/

/-- Read a fixed-size object out of a buffer at an offset.

Returns nothing when the buffer has no room for the object.

Never pads and never truncates.

Examples, with `b = ByteArray.mk #[10, 20, 30, 40]`:
* `unpackBytes? 4 b = some #v[10, 20, 30, 40]`
* `unpackBytes? 2 b 1 = some #v[20, 30]`
* `unpackBytes? 2 b 3 = none`
-/
def unpackBytes? (n : Nat) (b : ByteArray) (offset : Nat := 0) :
    Option (Vector UInt8 n) :=
  -- The guard is the whole validation: a buffer without room is rejected.
  if h : offset + n ≤ b.size then some (readBytes b offset n h) else none

/-! ## Computing a vector in order -/

/-- Run one computation per index, index 0 first, and collect the results.

The order matters when each computation calls the hash.

It fixes the sequence of hash calls, which a proof in the random oracle model counts. -/
def ofFnInOrder {m : Type → Type} [Monad m] {α : Type} :
    (n : Nat) → (Fin n → m α) → m (Vector α n)
  | 0, _ => pure #v[]
  -- Structural recursion, so the kernel can evaluate it.
  | n + 1, f => do
    let head ← f 0
    let tail ← ofFnInOrder n fun i => f i.succ
    return (#v[head] ++ tail).cast (Nat.add_comm 1 n)

end EthLib.Cryptography.HashSig
