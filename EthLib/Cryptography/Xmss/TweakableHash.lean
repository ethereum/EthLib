module

public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.HashSig
public import EthLib.Cryptography.Xmss.Address

/-!
# The leanXMSS tweakable hash

The hash every other definition is built from: `Th(P, A, M)` is the first half of `H(P | A | M)`.

Every definition that hashes takes `H` as an argument, in a monad:

- EthLib computes Keccak-256, in the identity monad;
- a proof in the random oracle model passes a query to the oracle;
- so the definitions that run are the ones the security proof is about.

Source: the leanXMSS specification draft, sections "Hashing and parameters" and "Security".

It is a tweakable hash of [ePrint 2025/055][hbms], §3.1, with the address `A` as the tweak.

The derivations follow its section "WOTS+C".

[hbms]: https://eprint.iacr.org/2025/055
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- Keccak-256 of a string of lanes, the scheme's hash: 32 bytes, as four lanes. -/
def hash (input : Array UInt64) : Lanes4 :=
  -- FIPS 202's 256-bit hash with Keccak's original padding, as Ethereum uses it.
  -- Every input part is 16 or 32 bytes, or the 8-byte name before a seed: whole lanes of 8 bytes.
  -- Keccak absorbs and squeezes these lanes, so no byte is moved on the way.
  Hash.Keccak.keccak256Lanes input

export EthLib.Cryptography.HashSig (pureHash)

/-- `H` as EthLib computes it: Keccak-256, in the identity monad.

An abbreviation, so a theorem about `pureHash f` applies to it with `f = hash`. -/
abbrev hashId : Array UInt64 → Id Lanes4 :=
  pureHash hash

/-- `H_0` or `H_1`: the first or the last 16 bytes of a 32-byte hash value. -/
@[inline] def halfOf (half : Fin 2) (full : Lanes4) : Digest :=
  -- The first two lanes, or the last two.
  if half.val = 0 then ⟨full.w0, full.w1⟩ else ⟨full.w2, full.w3⟩

/-- The lanes one tweakable hash call hashes: `P | A | M`, with `A` the encoding of the address. -/
@[inline] def thInput (publicParam : PublicParam) (address : Address) (payload : Array UInt64) :
    Array UInt64 :=
  -- `A = enc(tau, mu, hi, lo)`.
  let address := address.encode
  -- `P` and `A` are 16 bytes each, so the payload `M` always starts at byte 32.
  -- Fixed-length prefixes, so the input splits back into its three parts one way.
  #[publicParam.lo, publicParam.hi, address.lo, address.hi] ++ payload

/-- `Th(P, A, M)`: hash a payload at one address, encoded as `A`, with one call of `H`. -/
@[inline] def th {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)
    (publicParam : PublicParam) (address : Address) (payload : Array UInt64) : m Digest := do
  -- `Th(P, A, M) = H_0(P | A | M)`.
  return halfOf 0 (← H (thInput publicParam address payload))

/-! ## Derivations from the seed -/

/-- A source of derived values: the derivation at a parameter, an address and a suffix.

The signer derives the public parameter and every secret through one source.

- So a proof can replace the derivations as a whole.
- It takes the parameter, because the public parameter is itself a derivation.
- It returns 32 bytes, because two chains start at the two halves of one derivation. -/
abbrev SeedPrf (m : Type → Type) := PublicParam → Address → Array UInt64 → m Lanes4

/-- `H(P | A | S | suffix)`: the derivations from the scheme seed `S`. -/
def seedPrf {m : Type → Type} (H : Array UInt64 → m Lanes4) (s : Seed) : SeedPrf m :=
  -- The seed right after the address, then the suffix.
  -- The chain starts, `R_0` and `P` are halves of the result.
  fun publicParam address suffix => H (thInput publicParam address (s.toArray ++ suffix))

end EthLib.Cryptography.Xmss
