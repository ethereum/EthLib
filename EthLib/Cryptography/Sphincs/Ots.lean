import EthLib.Cryptography.Sphincs.Encoding

/-!
# `Sphincs.Ots`

The WOTS+C one-time signature: 64 hash chains of 4 positions.

Revealing a chain at position `k` lets anyone reach the positions above `k`.

It reveals nothing about the positions below.

The chains of key `K` (a layer, a tree and a leaf), for `i < 64` and `mu < 3`:

```text
    C_{i,0}    = H_{i mod 2}(P | A_prf(K, floor(i / 2)) | S)
    C_{i,mu+1} = Th(P, A_chain(K, i, mu), C_{i,mu})
    leaf       = Th(P, A_leaf(K), C_{0,3} | ... | C_{63,3})
```

The key signs a message `M` with the least counter `c` that makes this a codeword:

```text
    D = Th(P, A_enc(K), M | LE_32(c))
```

Source: [ePrint 2022/778](https://eprint.iacr.org/2022/778) for WOTS+C.

The algorithms follow `otsSecrets`, `chainWalk`, `encode`, `otsSign` and `otsLeaf` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Chains -/

/-- The 32 hashes of the seed that start the 64 chains of one key.

Chains `2j` and `2j + 1` start at the two halves of hash `j`. -/
def chainStarts (pp : PublicParam) (seed : Seed) (key : OtsKey) : Vector Digest V :=
  -- One hash per pair of chains, so 32 hashes for 64 chains.
  let pairs : Vector HashOutput (V / 2) :=
    Vector.ofFn fun j => thFull pp (addrPrf key j) (packBytes seed)
  -- Chain `i` takes half `i mod 2` of hash `floor(i / 2)`.
  Vector.ofFn fun i =>
    halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
      (pairs[i.val / 2]'(by have := i.isLt; simp only [V] at *; omega))

/-- One step of chain `i`, from position `mu` to the next.

The chain index is in the address, so the payload is the value alone. -/
def chainStep (pp : PublicParam) (key : OtsKey) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1))
    (value : Digest) : Digest :=
  th pp (addrChain key i mu) (packBytes value)

/-- Walk chain `i` for `steps` steps, starting at position `start`.

The walk ends at position `start + steps`, which the bound keeps on the chain. -/
def chain (pp : PublicParam) (key : OtsKey) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) : Digest :=
  match steps, h with
  | 0, _ => value
  -- The last step leaves position `start + s`, having walked `s` before it.
  | s + 1, h => chainStep pp key i ⟨start + s, by simp only [CHAIN_LENGTH] at *; omega⟩
      (chain pp key i start s (by omega) value)

/-! ## The one-time key's leaf -/

/-- The Merkle leaf of a one-time key, from the ends of its 64 chains. -/
def otsLeafHash (pp : PublicParam) (key : OtsKey) (ends : Vector Digest V) : Digest :=
  th pp (addrLeaf key) (packDigests ends)

/-- The leaf of a key, computed from the seed. -/
def otsPublicLeaf (pp : PublicParam) (seed : Seed) (key : OtsKey) : Digest :=
  let starts := chainStarts pp seed key
  -- Every chain walked from position 0 to position 3.
  otsLeafHash pp key
    (Vector.ofFn fun i => chain pp key i 0 (CHAIN_LENGTH - 1) (by decide) starts[i])

/-! ## The encoding -/

/-- `Enc(P, K, M, c)`: the codeword a counter gives a message, if any.

The counter comes last, so all counter trials share every block before the last one. -/
def encode (pp : PublicParam) (key : OtsKey) (msg : ByteArray) (counter : UInt32) :
    Option Codeword :=
  codeword? (th pp (addrEncoding key) (msg ++ packBytes (littleEndian COUNTER_LEN counter.toNat)))

namespace Internal

/-- Try the counters from `c` onward, at most `fuel` of them.

Returns the first counter whose encoding is a codeword, with the codeword. -/
def findCounter (pp : PublicParam) (key : OtsKey) (msg : ByteArray) (c fuel : Nat) :
    Option (UInt32 × Codeword) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    -- The least admissible counter wins, and a failed one moves on to the next counter.
    (encode pp key msg (UInt32.ofNat c)).elim (findCounter pp key msg (c + 1) fuel)
      fun x => some (UInt32.ofNat c, x)

end Internal

/-! ## Signing and recovering the leaf -/

/-- `Ots.sign(K, M)`: the counter and the 64 chain values that sign `M`.

Takes the least counter `c < 2^32` whose encoding is a codeword `x`.

Reveals chain `i` at position `x_i`.

Returns nothing when no counter gives a codeword.

Deterministic, so signing one message again gives the same signature. -/
def otsSign (pp : PublicParam) (seed : Seed) (key : OtsKey) (msg : ByteArray) :
    Option (UInt32 × Vector Digest V) := do
  -- Step 1: search the counter until the encoding is a codeword.
  let (counter, x) ← Internal.findCounter pp key msg 0 MAX_COUNTER_TRIALS
  -- Step 2: reveal each chain at the position its digit names.
  let starts := chainStarts pp seed key
  return (counter, Vector.ofFn fun i => chain pp key i 0 x[i] (by simp) starts[i])

/-- `Ots.leaf(K, M, c, y)`: the leaf a claimed one-time signature leads to.

Returns nothing when the counter does not encode the message as a codeword. -/
def otsLeaf (pp : PublicParam) (key : OtsKey) (msg : ByteArray) (counter : UInt32)
    (y : Vector Digest V) : Option Digest := do
  -- Step 1: recompute the codeword.
  let x ← encode pp key msg counter
  -- Step 2: walk chain `i` from position `x_i` to position 3.
  let ends := Vector.ofFn fun i =>
    chain pp key i x[i] (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega) y[i]
  -- Step 3: hash the ends into the leaf.
  return otsLeafHash pp key ends

end EthLib.Cryptography.Sphincs
