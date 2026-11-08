module

public import EthLib.Cryptography.Sphincs.Encoding
public import EthLib.Cryptography.Wots

/-!
# WOTS+C one-time signatures

The WOTS+C one-time signature: 64 hash chains of 4 positions, hashed as FIPS 205's WOTS+.

Revealing a chain at position `k` lets anyone reach the positions above `k`.

It reveals nothing about the positions below.

The chains of key `K = (l, tau, e)`, for `i < 64` and `mu < 3`:

```text
    C_{i,0}    = PRF(PK.seed, SK.seed, ADRS_prf(K, i))
    C_{i,mu+1} = F(PK.seed, ADRS_chain(K, i, mu), C_{i,mu})
    leaf       = T_v(PK.seed, ADRS_pk(K), C_{0,3} | ... | C_{63,3})
```

The key signs a 16-byte message `M` with the least counter `c` that makes this a codeword:

```text
    D = Th(PK.seed, ADRS_enc(K), M | BE_32(c))
```

Source: WOTS+C of [leanSPHINCS.tex][note] §1, and WOTS+ of [FIPS 205][fips205] §5.

WOTS+C is [ePrint 2022/778][wotsc].

Every definition takes the hash `H` and makes its calls in a fixed order.

Chains go by index, and each chain is walked step by step from its start.

[note]: https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex
[fips205]: https://doi.org/10.6028/NIST.FIPS.205
[wotsc]: https://eprint.iacr.org/2022/778
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-! ## Chains -/

/-- The starts of the 64 chains of one key, one `PRF` each, chain 0 first.

Chain `i` starts at `PRF(PK.seed, SK.seed, ADRS_prf(K, i))`, as in FIPS 205's `wots_pkGen`. -/
def chainStarts (prf : Prf m) (key : OtsKey) : m (Vector Digest V) :=
  ofFnInOrder V fun i => prf (adrsPrf key i)

/-- One step of chain `i`, from position `mu` to the next: `F` under `ADRS_chain(K, i, mu)`.

The chain index and the position are in the address, so the payload is the value alone. -/
def chainStep (pkSeed : PkSeed) (key : OtsKey) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1))
    (value : Digest) : m Digest :=
  th H pkSeed (adrsChain key i mu) (packBytes value)

/-- Walk chain `i` for `steps` steps, starting at position `start`: FIPS 205's `chain`.

The walk ends at position `start + steps`, which the bound keeps on the chain. -/
def chain (pkSeed : PkSeed) (key : OtsKey) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) : m Digest :=
  Wots.chain (chainStep H pkSeed key i) start steps (Nat.le_sub_one_of_lt h) value

/-! ## The one-time key's leaf -/

/-- `T_v` over the ends of the 64 chains: the Merkle leaf of a one-time key. -/
def otsLeafHash (pkSeed : PkSeed) (key : OtsKey) (ends : Vector Digest V) : m Digest :=
  th H pkSeed (adrsPk key) (packDigests ends)

/-- The leaf of a key, computed from its secrets: FIPS 205's `wots_pkGen`. -/
def otsPublicLeaf (pkSeed : PkSeed) (prf : Prf m) (key : OtsKey) : m Digest := do
  let starts ← chainStarts prf key
  -- Every chain walked from position 0 to position 3, chain 0 first.
  let ends ← ofFnInOrder V fun i => chain H pkSeed key i 0 (CHAIN_LENGTH - 1) (by decide) starts[i]
  otsLeafHash H pkSeed key ends

/-! ## The encoding -/

/-- `Enc(K, M, c)`: the codeword a counter gives a message, if any.

It hashes `M | BE_32(c)` under `ADRS_enc(K)`, 68 bytes in all.

The counter comes last, so all counter trials share every block before the last one. -/
def encode (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (counter : UInt32) :
    m (Option Codeword) :=
  codeword? <$>
    th H pkSeed (adrsEnc key) (packBytes msg ++ packBytes (toByte COUNTER_LEN counter.toNat))

namespace Internal

/-- Try the counters from `c` onward, at most `fuel` of them.

Returns the first counter whose encoding is a codeword, with the codeword. -/
def findCounter (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (c fuel : Nat) :
    m (Option (UInt32 × Codeword)) :=
  Wots.findFirst UInt32.ofNat (encode H pkSeed key msg) c fuel

end Internal

/-! ## Signing and recovering the leaf -/

/-- `Wots.sign(K, M)`: the counter and the 64 chain values that sign `M`.

Takes the least counter `c < 2^32` whose encoding is a codeword `x`.

Reveals chain `i` at position `x_i`.

Returns nothing when no counter gives a codeword.

Deterministic, so signing one message again gives the same signature.

Two signatures of one message under one key reveal the same positions. -/
def otsSign (pkSeed : PkSeed) (prf : Prf m) (key : OtsKey) (msg : Digest) :
    m (Option (UInt32 × Vector Digest V)) := do
  -- Step 1: search the counter until the encoding is a codeword.
  let some (counter, x) ← Internal.findCounter H pkSeed key msg 0 MAX_COUNTER_TRIALS
    | return none
  -- Step 2: reveal each chain at the position its digit names, chain 0 first.
  let starts ← chainStarts prf key
  let y ← ofFnInOrder V fun i => chain H pkSeed key i 0 x[i] (by simp) starts[i]
  return some (counter, y)

/-- `Wots.leaf(K, M, c, y)`: the leaf a claimed one-time signature leads to.

It is FIPS 205's `wots_pkFromSig`, with the codeword in place of the message and checksum.

Returns nothing when the counter does not encode the message as a codeword. -/
def otsLeaf (pkSeed : PkSeed) (key : OtsKey) (msg : Digest) (counter : UInt32)
    (y : Vector Digest V) : m (Option Digest) := do
  -- Step 1: recompute the codeword.
  let some x ← encode H pkSeed key msg counter | return none
  -- Step 2: walk chain `i` from position `x_i` to position 3, chain 0 first.
  let ends ← ofFnInOrder V fun i =>
    chain H pkSeed key i x[i] (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega) y[i]
  -- Step 3: hash the ends into the leaf.
  return some (← otsLeafHash H pkSeed key ends)

end EthLib.Cryptography.Sphincs
