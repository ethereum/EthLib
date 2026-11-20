module

public import EthLib.Cryptography.Wots
public import EthLib.Cryptography.Xmss.Encoding

/-!
# WOTS+C one-time signatures

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

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-! ## Chains -/

/-- The 29 derivations from the seed that start the 58 chains of one key.

Chains `2j` and `2j + 1` start at the two halves of derivation `j`, whose suffix is empty. -/
def chainStarts (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32) :
    m (Vector Digest V) := do
  -- One derivation per pair of chains, so 29 derivations for 58 chains.
  let pairs ← ofFnInOrder (V / 2) fun j => prf pp (addrPrf layer e j) .empty
  -- Chain `i` takes half `i mod 2` of derivation `floor(i / 2)`.
  return Vector.ofFn fun i =>
    halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
      (pairs[i.val / 2]'(by have := i.isLt; simp only [V] at *; omega))

/-- One step of chain `i`, from position `mu` to the next.

The chain index follows the value, so every chain of a key shares the step's address. -/
def chainStep (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) : m Digest :=
  th H pp (addrChain layer e mu) (packBytes value ++ packBytes (uintToBytes 16 i.val))

/-- Walk chain `i` for `steps` steps, starting at position `start`.

The walk ends at position `start + steps`, which the bound keeps on the chain. -/
def chain (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) : m Digest :=
  Wots.chain (chainStep H pp layer e i) start steps (Nat.le_sub_one_of_lt h) value

/-! ## The one-time key's leaf -/

/-- The Merkle leaf of a one-time key, from the ends of its 58 chains. -/
def otsLeafHash (pp : PublicParam) (layer : Layer) (e : UInt32) (ends : Vector Digest V) :
    m Digest :=
  th H pp (addrLeaf layer e) (packDigests ends)

/-- `X_{0,e}`: the leaf of key `e`, computed from the derivations of the seed. -/
def otsPublicLeaf (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32) :
    m Digest := do
  let starts ← chainStarts pp prf layer e
  -- Every chain walked from position 0 to position 3, chain 0 first.
  let ends ← ofFnInOrder V fun i => chain H pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i]
  otsLeafHash H pp layer e ends

/-! ## The digest a key signs -/

/-- `D = Th(P, A_msg(l, e), M | rho)`: the digest key `e` signs under one randomizer.

`M` is the 32-byte message on the bottom layer, and a 16-byte root on the top. -/
def messageDigest (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (rho : Randomizer) : m Digest :=
  th H pp (addrMsg layer e) (msg ++ packBytes rho)

/-- `R_0`: the base every randomizer trial adds to, derived at `A_rnd(l, e)` with suffix `M`.

With the derivations from the scheme seed `S`, it is `Th(P, A_rnd(l, e), S | M)`.

Since `S` is in the input, the randomizers stay secret until signed. -/
def randomizerBase (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32)
    (msg : ByteArray) : m Randomizer := do
  return halfOf 0 (← prf pp (addrRnd layer e) msg)

/-! ## Randomizers as words

A randomizer search keeps its randomizers, and the digests of its trials, as two 64-bit words. -/

/-- A 16-byte string as two 64-bit words: its little-endian integer, split at bit 64. -/
structure WordPair where
  /-- Bytes 0 to 7, byte 0 least significant. -/
  lo : UInt64
  /-- Bytes 8 to 15, byte 8 least significant. -/
  hi : UInt64

namespace WordPair

/-- The integer below `2^128` that the two words make: `lo + 2^64 * hi`. -/
def toNat (w : WordPair) : Nat :=
  w.lo.toNat + 2 ^ 64 * w.hi.toNat

/-- The 16 bytes of the two words, least significant first.

Byte `j` is bits `8j` to `8j + 7` of the low word, or of the high word from byte 8 on. -/
def bytes (w : WordPair) : Vector UInt8 16 :=
  #v[w.lo.toUInt8, (w.lo >>> 8).toUInt8, (w.lo >>> 16).toUInt8, (w.lo >>> 24).toUInt8,
    (w.lo >>> 32).toUInt8, (w.lo >>> 40).toUInt8, (w.lo >>> 48).toUInt8, (w.lo >>> 56).toUInt8,
    w.hi.toUInt8, (w.hi >>> 8).toUInt8, (w.hi >>> 16).toUInt8, (w.hi >>> 24).toUInt8,
    (w.hi >>> 32).toUInt8, (w.hi >>> 40).toUInt8, (w.hi >>> 48).toUInt8, (w.hi >>> 56).toUInt8]

/-- The two words of 16 bytes: bytes 0 to 7 and bytes 8 to 15, each read as a Keccak lane. -/
def ofBytes (v : Vector UInt8 16) : WordPair :=
  ⟨Hash.Keccak.Internal.laneAt (packBytes v) 0, Hash.Keccak.Internal.laneAt (packBytes v) 8⟩

end WordPair

/-- The randomizer of trial `c` as words: `R_0 + c mod 2^128`, with `R_0` as words.

The low words add modulo `2^64`, and the low word wraps exactly when it ends below `R_0`'s.

That wrap carries 1 into the high word, which adds the rest of `c` and drops its own carry. -/
def trialWords (base : WordPair) (c : Nat) : WordPair :=
  let lo := base.lo + UInt64.ofNat c
  let carry : UInt64 := if lo < base.lo then 1 else 0
  ⟨lo, base.hi + UInt64.ofNat (c >>> 64) + carry⟩

/-- `rho_c = LE_128(LE^-1(R_0) + c mod 2^128)`: the randomizer of trial `c`.

A sum, not a hash, so each trial costs the one hash of its digest.

The sum runs on the two 64-bit words of the little-endian integer. -/
def trialRandomizer (base : Randomizer) (c : Nat) : Randomizer :=
  (trialWords (WordPair.ofBytes base) c).bytes

/-! ## Randomizer trials -/

/-- The trials of one search: whether the digest of a randomizer is a codeword, and which.

Every trial hashes the same bytes `P | A_msg(l, e) | M`, followed by its own randomizer.

It is a structure, not a function, so a source does its per-search work once.

The compiler merges a function that returns a function into one function of all the arguments.

That merged function would redo, on every trial, the work meant for once per search. -/
structure Trials (m : Type → Type) where
  /-- The codeword the digest of a randomizer is, if any. -/
  codeword : Randomizer → m (Option (Vector (Fin CHAIN_LENGTH) V))

/-- The trials of every search, from the fixed bytes that start each trial's input.

A search builds its trials once, so the work that only the fixed bytes need is done once.

A source is the scheme's only when its trials give the codewords that `H` gives.

Nothing checks it: the theorems are about the default source, which hashes each trial with `H`. -/
abbrev TrialSource (m : Type → Type) :=
  ByteArray → Trials m

/-- The trials as `H` computes them: a trial hashes the fixed bytes followed by the randomizer. -/
def hashTrials : TrialSource m :=
  fun before => ⟨fun rho => codeword? <$> (do return halfOf 0 (← H (before ++ packBytes rho)))⟩

/-- The trials as Keccak-256 computes them, with one permutation each.

The randomizer is the last 16 bytes of the input.

When they fill two whole lanes of the last block, only those two lanes change between trials.

The state before the last permutation is then built once, with the randomizer bytes set to zero.

A trial XORs its randomizer into the two lanes, permutes, and reads the digest from lanes 0 and 1.

Otherwise each trial hashes its whole input.

These are the trials of Keccak-256, by a theorem. -/
def keccakTrials : TrialSource Id := fun before =>
  -- The randomizer starts on a lane, and the padding of the last block comes after it.
  if before.size % 8 = 0 ∧ before.size % Hash.Keccak.RATE_256 + 16 < Hash.Keccak.RATE_256 then
    let zeros := ByteArray.mk (Array.replicate 16 0)
    let S := Hash.Keccak.stateBeforeLastPermutation Hash.Keccak.keccakF Hash.Keccak.RATE_256
      (before ++ zeros)
    -- The randomizer fills lanes k and k + 1 of the last block.
    let k := before.size % Hash.Keccak.RATE_256 / 8
    ⟨fun rho =>
      let w := WordPair.ofBytes rho
      let T := Hash.Keccak.keccakF ((S.xorLane (k + 1) w.hi).xorLane k w.lo)
      -- The digest is the first 16 bytes of the output: lanes 0 and 1.
      pure (codeword? (WordPair.bytes ⟨T.a0, T.a1⟩))⟩
  else hashTrials hashId before

namespace Internal

/-- Try the trials from `c` onward, at most `fuel` of them.

Returns the first trial's randomizer whose digest is a codeword, with the codeword.

With the default source, each trial hashes `P | A_msg(l, e) | M | rho_c` to get its digest.

Only `rho_c` changes between trials, so the trials are built once from the bytes before it.

The base is read as words once, and each trial's randomizer is the sum of trial `c`. -/
def findCodeword (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) (trials : TrialSource m := hashTrials H) :
    m (Option (Randomizer × Vector (Fin CHAIN_LENGTH) V)) :=
  -- The input of every trial starts with `P | A_msg(l, e) | M`.
  let t := trials (thInput pp (addrMsg layer e) msg)
  -- The base as words, read once, so that each trial's randomizer is a sum of words.
  let b := WordPair.ofBytes base
  Wots.findFirst (fun c => (trialWords b c).bytes) t.codeword c fuel

end Internal

/-! ## Signing and recovering the leaf -/

namespace Internal

/-- `Ots.sign(l, e, M)`, with the trials of its search taken from a source. -/
def otsSignTrials (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (trials : TrialSource m) : m (Option (Randomizer × Vector Digest V)) := do
  -- Step 1: grind the randomizer until the digest is a codeword.
  let base ← randomizerBase pp prf layer e msg
  let some (rho, x) ← findCodeword H pp layer e msg base 0 MAX_RANDOMIZER_TRIALS trials
    | return none
  -- Step 2: reveal each chain at the position its digit names, chain 0 first.
  let starts ← chainStarts pp prf layer e
  let y ← ofFnInOrder V fun i => chain H pp layer e i 0 x[i] (by simp) starts[i]
  return some (rho, y)

end Internal

/-- `Ots.sign(l, e, M)`: the randomizer and the 58 chain values that sign `M`.

Takes the least trial `c < 2^32` whose digest is a codeword `x`.

Reveals chain `i` at position `x_i`.

Returns nothing when no trial gives a codeword.

Deterministic, so signing one message again gives the same signature.

Each trial of the search hashes its input with `H`. -/
def otsSign (pp : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32)
    (msg : ByteArray) : m (Option (Randomizer × Vector Digest V)) :=
  Internal.otsSignTrials H pp prf layer e msg (hashTrials H)

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
