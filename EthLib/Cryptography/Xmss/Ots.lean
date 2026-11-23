module

public import EthLib.Cryptography.Wots
public import EthLib.Cryptography.Xmss.Encoding

/-!
# WOTS+C one-time signatures

The WOTS+C one-time signature: 58 hash chains of 4 positions.

Source: the leanXMSS specification draft, section "WOTS+C".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

-- Every definition takes the hash `H` and makes its calls in a fixed order.
-- Chains go by index, and each chain is walked step by step from its start.
variable {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)

/-! ## Chains -/

/-- The 29 derivations from the seed that start the 58 chains of one key.

Key `e` on layer `l` has the chains `C_{i,mu}`, for `i < 58` and positions `mu <= 3`.

Chains `2j` and `2j + 1` start at the two halves of derivation `j`, whose suffix is empty. -/
def chainStarts (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32) :
    m (Vector Digest V) := do
  -- One derivation per pair of chains, so 29 derivations for 58 chains.
  let pairs ← ofFnInOrder (V / 2) fun j => prf publicParam (addrPrf layer e j) #[]
  -- `C_{i,0} = H_{i mod 2}(P | A_prf(l, e, floor(i / 2)) | S)`.
  --
  -- Chains `2j` and `2j + 1` start at the halves `H_0` and `H_1` of derivation `j`.
  return (pairs.flatMap fun p => #v[halfOf 0 p, halfOf 1 p]).cast (by decide)

/-- One step of chain `i`, from position `mu` to the next.

A step of the hash chains of Construction 2 of [ePrint 2025/055][hbms], §4.2.

- `publicParam`: the 16-byte public parameter `P`.
- `layer` and `e`: the layer, bottom or top, and the index of the one-time key on it.
- `i`: the chain, from 0 to 57.
- `mu`: the current position, from 0 to 2, so the step reaches position `mu + 1`.
- `value`: the 16-byte chain value `C_{i,mu}`.

[hbms]: https://eprint.iacr.org/2025/055
-/
def chainStep (publicParam : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) : m Digest :=
  -- `C_{i,mu+1} = Th(P, A_chain(l, e, mu), C_{i,mu} | LE_128(i))`.
  --
  -- `Th(P, A, M)` is the first 16 bytes of `H(P | A | M)`, with `H` Keccak-256.
  th H publicParam
    -- `A_chain(l, e, mu)` names the key and the step, so the 58 chains share it.
    (addrChain layer e mu)
    -- `M`: the two lanes of `C_{i,mu}`, then the two lanes of `LE_128(i)`.
    #[value.lo, value.hi,
      -- `LE_128(i)`: `i` in the first lane, zero in the second.
      -- The index keeps the 58 chains apart, where Construction 2 uses the tweak.
      i.val.toUInt64, 0]

/-- Walk chain `i` for `steps` steps, starting at position `start`.

The walk ends at position `start + steps`, which the bound keeps on the chain.

Revealing a chain at position `k` lets anyone reach the positions above `k`.

It reveals nothing about the positions below. -/
def chain (publicParam : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) : m Digest :=
  -- The generic walk of a hash chain, with the step of chain `i`.
  Wots.chain (chainStep H publicParam layer e i) start steps (Nat.le_sub_one_of_lt h) value

/-! ## The one-time key's leaf -/

/-- The Merkle leaf of a one-time key, from the ends of its 58 chains. -/
def otsLeafHash (publicParam : PublicParam) (layer : Layer) (e : UInt32) (ends : Vector Digest V) :
    m Digest :=
  -- `X_{0,e} = Th(P, A_leaf(l, e), C_{0,3} | ... | C_{57,3})`.
  th H publicParam (addrLeaf layer e) (digestLanes ends)

/-- `X_{0,e}`: the leaf of key `e`, computed from the derivations of the seed. -/
def otsPublicLeaf (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32) :
    m Digest := do
  -- The 58 chain starts, from 29 derivations of the seed.
  let starts ← chainStarts publicParam prf layer e
  -- Every chain walked from position 0 to position 3, chain 0 first.
  let ends ← ofFnInOrder V fun i => chain H publicParam layer e i 0 (CHAIN_LENGTH - 1)
    (by decide) starts[i]
  otsLeafHash H publicParam layer e ends

/-! ## The digest a key signs -/

/-- `D = Th(P, A_msg(l, e), M | rho)`: the digest key `e` signs under one randomizer.

`M` is the 32-byte message on the bottom layer, and a 16-byte root on the top. -/
def messageDigest (publicParam : PublicParam) (layer : Layer) (e : UInt32) (msg : Array UInt64)
    (rho : Randomizer) : m Digest :=
  -- `D_c = Th(P, A_msg(l, e), M | rho_c)`.
  th H publicParam (addrMsg layer e) (msg ++ rho.toArray)

/-- `R_0`: the base every randomizer trial adds to, derived at `A_rnd(l, e)` with suffix `M`.

With the derivations from the scheme seed `S`, it is `Th(P, A_rnd(l, e), S | M)`.

Since `S` is in the input, the randomizers stay secret until signed. -/
def randomizerBase (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32)
    (msg : Array UInt64) : m Randomizer := do
  -- `R_0 = Th(P, A_rnd(l, e), S | M)`.
  return halfOf 0 (← prf publicParam (addrRnd layer e) msg)

/-! ## Randomizers as words

A randomizer is two lanes, so a randomizer search adds to it on two 64-bit words. -/

/-- `rho_c = LE_128(LE^-1(R_0) + c mod 2^128)`: the randomizer of trial `c`.

A sum, not a hash, so each trial costs the one hash of its digest.

The low lanes add modulo `2^64`, and the low lane wraps exactly when it ends below `R_0`'s.

That wrap carries 1 into the high lane, which adds the rest of `c` and drops its own carry. -/
def trialRandomizer (base : Randomizer) (c : Nat) : Randomizer :=
  -- The low lane adds the low 64 bits of `c`, modulo `2^64`.
  let lo := base.lo + UInt64.ofNat c
  -- It wrapped exactly when it ends below the low lane of `R_0`.
  let carry : UInt64 := if lo < base.lo then 1 else 0
  -- The high lane adds the rest of `c` and the carry, modulo `2^64`.
  ⟨lo, base.hi + UInt64.ofNat (c >>> 64) + carry⟩

/-! ## Randomizer trials -/

/-- The trials of one search: whether the digest of a randomizer is a codeword, and which.

Every trial hashes the same lanes `P | A_msg(l, e) | M`, followed by its own randomizer.

It is a structure, not a function, so a source does its per-search work once.

The compiler merges a function that returns a function into one function of all the arguments.

That merged function would redo, on every trial, the work meant for once per search. -/
structure Trials (m : Type → Type) where
  /-- The codeword the digest of a randomizer is, if any. -/
  codeword : Randomizer → m (Option (Vector (Fin CHAIN_LENGTH) V))

/-- The trials of every search, from the fixed lanes that start each trial's input.

A search builds its trials once, so the work that only the fixed lanes need is done once.

A source is the scheme's only when its trials give the codewords that `H` gives.

Nothing checks it: the theorems are about the default source, which hashes each trial with `H`. -/
abbrev TrialSource (m : Type → Type) :=
  Array UInt64 → Trials m

/-- The trials as `H` computes them: a trial hashes the fixed lanes followed by the randomizer. -/
def hashTrials : TrialSource m :=
  fun before => ⟨fun rho => codeword? <$> (do return halfOf 0 (← H (before ++ rho.toArray)))⟩

/-- The trials of a randomizer search, with one Keccak-256 permutation each.

They give the codewords of hashing each trial's whole input, by a theorem. -/
def keccakTrials : TrialSource Id := fun before =>
  -- The fast path needs the randomizer's 16 bytes to end before the padding of the last block.
  -- The leanXMSS inputs are 80 bytes at the bottom and 64 at the top, below the 136-byte rate.
  if (8 * before.size) % Hash.Keccak.RATE_256 + 16 < Hash.Keccak.RATE_256 then
    -- Only the randomizer changes between trials.
    -- So the state before the last permutation is built once, with the randomizer lanes at zero.
    let S := Hash.Keccak.Internal.stateBeforeLastPermutation Hash.Keccak.keccakF
      Hash.Keccak.RATE_256 (8 * (before.size + 2)) (Hash.Keccak.Internal.laneOfArray before)
    -- The randomizer fills lanes `k` and `k + 1` of the last block.
    let k := (8 * before.size) % Hash.Keccak.RATE_256 / 8
    ⟨fun rho =>
      -- One trial: XOR the randomizer into its two lanes, then one permutation.
      let T := Hash.Keccak.keccakF ((S.xorLane (k + 1) rho.hi).xorLane k rho.lo)
      -- The digest is the first 16 bytes of the output: lanes 0 and 1.
      pure (codeword? ⟨T.a0, T.a1⟩)⟩
  -- Otherwise each trial hashes its whole input, which leanXMSS inputs never need.
  else hashTrials hashId before

namespace Internal

/-- Try the trials from `c` onward, at most `fuel` of them.

Returns the first trial's randomizer whose digest is a codeword, with the codeword.

With the default source, each trial hashes `P | A_msg(l, e) | M | rho_c` to get its digest.

Only `rho_c` changes between trials, so the trials are built once from the lanes before it.

The randomizer of trial `c` is the sum `rho_c` above. -/
def findCodeword (publicParam : PublicParam) (layer : Layer) (e : UInt32) (msg : Array UInt64)
    (base : Randomizer) (c fuel : Nat) (trials : TrialSource m := hashTrials H) :
    m (Option (Randomizer × Vector (Fin CHAIN_LENGTH) V)) :=
  -- The input of every trial starts with `P | A_msg(l, e) | M`.
  let t := trials (thInput publicParam (addrMsg layer e) msg)
  Wots.findFirst (trialRandomizer base) t.codeword c fuel

end Internal

/-! ## Signing and recovering the leaf -/

namespace Internal

/-- `Ots.sign(l, e, M)`, with the trials of its search taken from a source. -/
def otsSignTrials (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32)
    (msg : Array UInt64) (trials : TrialSource m) :
    m (Option (Randomizer × Vector Digest V)) := do
  -- Step 1: grind the randomizer until the digest is a codeword.
  let base ← randomizerBase publicParam prf layer e msg
  let some (rho, x) ← findCodeword H publicParam layer e msg base 0 MAX_RANDOMIZER_TRIALS trials
    | return none
  -- Step 2: reveal each chain at the position its digit names, chain 0 first.
  let starts ← chainStarts publicParam prf layer e
  let y ← ofFnInOrder V fun i => chain H publicParam layer e i 0 x[i] (by simp) starts[i]
  return some (rho, y)

end Internal

/-- `Ots.sign(l, e, M)`: the randomizer and the 58 chain values that sign `M`.

Takes the least trial `c < 2^32` whose digest is a codeword `x`.

Reveals chain `i` at position `x_i`.

Returns nothing when no trial gives a codeword.

Deterministic, so signing one message again gives the same signature.

Each trial of the search hashes its input with `H`. -/
def otsSign (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : UInt32)
    (msg : Array UInt64) : m (Option (Randomizer × Vector Digest V)) :=
  Internal.otsSignTrials H publicParam prf layer e msg (hashTrials H)

/-- `Ots.leaf(l, e, M, rho, y)`: the leaf a claimed one-time signature leads to.

Returns nothing when the digest is not a codeword. -/
def otsLeaf (publicParam : PublicParam) (layer : Layer) (e : UInt32) (msg : Array UInt64)
    (rho : Randomizer) (y : Vector Digest V) : m (Option Digest) := do
  -- Step 1: recompute the codeword.
  let some x := codeword? (← messageDigest H publicParam layer e msg rho) | return none
  -- Step 2: walk chain `i` from position `x_i` to position 3, chain 0 first.
  let ends ← ofFnInOrder V fun i =>
    chain H publicParam layer e i x[i] (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega) y[i]
  -- Step 3: hash the ends into the leaf.
  return some (← otsLeafHash H publicParam layer e ends)

end EthLib.Cryptography.Xmss
