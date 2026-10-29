import EthLib.Cryptography.Xmss.Encoding

/-!
# `Xmss.Ots`

The WOTS+C one-time signature: 58 hash chains of 4 positions.

Revealing a chain at position `k` lets anyone reach the positions above `k`.

It reveals nothing about the positions below.

The chains of key `e` on layer `l`, for `i < 58` and `mu < 3`:

```text
    C_{i,0}      = H_{i mod 2}(P | A_prf(l, e, floor(i / 2)) | S)
    C_{i,mu+1}   = Th(P, A_chain(l, e, mu), C_{i,mu} | LE_128(i))
    leaf X_{0,e} = Th(P, A_leaf(l, e), C_{0,3} | ... | C_{57,3})
```

Every definition takes the hash `H` and makes its calls in a fixed order.

Chains go by index, and each chain is walked step by step from its start.

Source: the leanXMSS specification draft, section "WOTS+C".
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-! ## Chains -/

/-- The 29 hashes of the seed that start the 58 chains of one key.

Chains `2j` and `2j + 1` start at the two halves of hash `j`. -/
def chainStarts (pp : PublicParam) (seed : Seed) (layer : Layer) (e : UInt32) :
    m (Vector Digest V) := do
  -- One hash per pair of chains, so 29 hashes for 58 chains.
  let pairs ← ofFnInOrder (V / 2) fun j => H (thInput pp (addrPrf layer e j) (packBytes seed))
  -- Chain `i` takes half `i mod 2` of hash `floor(i / 2)`.
  return Vector.ofFn fun i =>
    halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
      (pairs[i.val / 2]'(by have := i.isLt; simp only [V] at *; omega))

/-- One step of chain `i`, from position `mu` to the next.

The chain index follows the value, so every chain of a key shares the step's address. -/
def chainStep (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) : m Digest :=
  th H pp (addrChain layer e mu) (packBytes value ++ packBytes (littleEndian 16 i.val))

/-- Walk chain `i` for `steps` steps, starting at position `start`.

The walk ends at position `start + steps`, which the bound keeps on the chain. -/
def chain (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) : m Digest :=
  match steps, h with
  | 0, _ => pure value
  -- The last step leaves position `start + s`, having walked `s` before it.
  | s + 1, h => do
    let previous ← chain pp layer e i start s (by omega) value
    chainStep H pp layer e i ⟨start + s, by simp only [CHAIN_LENGTH] at *; omega⟩ previous

/-! ## The one-time key's leaf -/

/-- The Merkle leaf of a one-time key, from the ends of its 58 chains. -/
def otsLeafHash (pp : PublicParam) (layer : Layer) (e : UInt32) (ends : Vector Digest V) :
    m Digest :=
  th H pp (addrLeaf layer e) (packDigests ends)

/-- `X_{0,e}`: the leaf of key `e`, computed from the seed. -/
def otsPublicLeaf (pp : PublicParam) (seed : Seed) (layer : Layer) (e : UInt32) : m Digest := do
  let starts ← chainStarts H pp seed layer e
  -- Every chain walked from position 0 to position 3, chain 0 first.
  let ends ← ofFnInOrder V fun i => chain H pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i]
  otsLeafHash H pp layer e ends

/-! ## The digest a key signs -/

/-- `D = Th(P, A_msg(l, e), M | rho)`: the digest key `e` signs under one randomizer.

`M` is the 32-byte message on the bottom layer, and a 16-byte root on the top. -/
def messageDigest (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (rho : Randomizer) : m Digest :=
  th H pp (addrMsg layer e) (msg ++ packBytes rho)

/-- `R_0 = Th(P, A_rnd(l, e), S | M)`: the base every randomizer trial adds to.

The seed is in the input, so the randomizers stay secret until signed. -/
def randomizerBase (pp : PublicParam) (seed : Seed) (layer : Layer) (e : UInt32)
    (msg : ByteArray) : m Randomizer :=
  th H pp (addrRnd layer e) (packBytes seed ++ msg)

/-- `rho_c = LE_128(LE^-1(R_0) + c mod 2^128)`: the randomizer of trial `c`.

A sum, not a hash, so each trial costs the one hash of its digest. -/
def trialRandomizer (base : Randomizer) (c : Nat) : Randomizer :=
  littleEndian RANDOMIZER_LEN ((fromLittleEndian base + c) % 2 ^ 128)

namespace Internal

/-- Try the trials from `c` onward, at most `fuel` of them.

Returns the first trial's randomizer whose digest is a codeword, with the codeword. -/
def findCodeword (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) :
    m (Option (Randomizer × Vector (Fin CHAIN_LENGTH) V)) :=
  match fuel with
  | 0 => pure none
  | fuel + 1 => do
    let rho := trialRandomizer base c
    match codeword? (← messageDigest H pp layer e msg rho) with
    -- The least admissible trial wins.
    | some x => pure (some (rho, x))
    -- Otherwise move on to the next trial.
    | none => findCodeword pp layer e msg base (c + 1) fuel

end Internal

/-! ## Signing and recovering the leaf -/

/-- `Ots.sign(l, e, M)`: the randomizer and the 58 chain values that sign `M`.

Takes the least trial `c < 2^32` whose digest is a codeword `x`.

Reveals chain `i` at position `x_i`.

Returns nothing when no trial gives a codeword.

Deterministic, so signing one message again gives the same signature. -/
def otsSign (pp : PublicParam) (seed : Seed) (layer : Layer) (e : UInt32)
    (msg : ByteArray) : m (Option (Randomizer × Vector Digest V)) := do
  -- Step 1: grind the randomizer until the digest is a codeword.
  let base ← randomizerBase H pp seed layer e msg
  let some (rho, x) ← Internal.findCodeword H pp layer e msg base 0 MAX_RANDOMIZER_TRIALS
    | return none
  -- Step 2: reveal each chain at the position its digit names, chain 0 first.
  let starts ← chainStarts H pp seed layer e
  let y ← ofFnInOrder V fun i => chain H pp layer e i 0 x[i] (by simp) starts[i]
  return some (rho, y)

/-- `Ots.leaf(l, e, M, rho, y)`: the leaf a claimed one-time signature leads to.

Returns nothing when the digest is not a codeword. -/
def otsLeaf (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (rho : Randomizer) (y : Vector Digest V) : m (Option Digest) := do
  -- Step 1: recompute the codeword.
  let some x := codeword? (← messageDigest H pp layer e msg rho) | return none
  -- Step 2: walk chain `i` from position `x_i` to position 3, chain 0 first.
  let ends ← ofFnInOrder V fun i =>
    chain H pp layer e i x[i] (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega) y[i]
  -- Step 3: hash the ends into the leaf.
  return some (← otsLeafHash H pp layer e ends)

end EthLib.Cryptography.Xmss
