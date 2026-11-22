module

public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.HashSig
public import EthLib.Cryptography.Xmss.Address

/-!
# The leanXMSS tweakable hash

The hash every other definition is built from: `Th(P, A, M)` is the first half of `H(P | A | M)`.

- `H` is Keccak-256, Ethereum's hash: FIPS 202's 256-bit hash with Keccak's original padding.
- `H_0` and `H_1` are the first and last 16 bytes of its output.
- `P` and `A` are 16 bytes each, so the payload `M` always starts at byte 32.

Every part of every input is 16 or 32 bytes, except the 8-byte name hashed before a seed.

So `H` takes its input as Keccak lanes, and returns its output as lanes.

These are the lanes Keccak-256 absorbs and squeezes, so no byte is moved on the way.

Every definition that hashes takes the hash `H` as an argument, in a monad `m`.

- The hash that EthLib computes is Keccak-256, in the identity monad.
- A proof in the random oracle model passes a query to the oracle instead.

So the definitions that run are the definitions that the security proof is about.

A derivation from the scheme seed `S` is a hash of `P | A | S | suffix`.

Definitions that derive a value from the seed take the derivations as one function argument.

Source: the leanXMSS specification draft, sections "Hashing and parameters" and "Security".

It is a tweakable hash of [ePrint 2025/055][hbms], §3.1, with the address `A` as the tweak.

The derivations follow its section "WOTS+C".

[hbms]: https://eprint.iacr.org/2025/055
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- Keccak-256 of a string of lanes, the scheme's hash: 32 bytes, as four lanes.

The input has 8 bytes per lane. -/
def hash (input : Array UInt64) : Lanes4 :=
  Hash.Keccak.keccak256Lanes input

export EthLib.Cryptography.HashSig (pureHash)

/-- `H` as EthLib computes it: Keccak-256, in the identity monad.

An abbreviation, so a theorem about `pureHash f` applies to it with `f = hash`. -/
abbrev hashId : Array UInt64 → Id Lanes4 :=
  pureHash hash

/-- `H_0` or `H_1`: the first or the last 16 bytes of a 32-byte hash value.

They are its first two lanes or its last two lanes. -/
@[inline] def halfOf (half : Fin 2) (full : Lanes4) : Digest :=
  if half.val = 0 then ⟨full.w0, full.w1⟩ else ⟨full.w2, full.w3⟩

/-- The lanes one tweakable hash call hashes: `P | A | M`. -/
def thInput (pp : PublicParam) (address : Address) (payload : Array UInt64) : Array UInt64 :=
  -- Fixed-length prefixes, so the input splits back into its three parts one way.
  #[pp.lo, pp.hi, address.lo, address.hi] ++ payload

/-- `Th(P, A, M)`: hash a payload under one address of one key, with one call of `H`. -/
def th {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4) (pp : PublicParam)
    (address : Address) (payload : Array UInt64) : m Digest := do
  -- `Th(P, A, M) = H_0(P | A | M)`.
  return halfOf 0 (← H (thInput pp address payload))

/-! ## Derivations from the seed -/

/-- A source of derived values: the derivation at a parameter, an address and a suffix.

The signer derives the public parameter and every secret through one such source.

So a proof can replace the derivations as a whole.

It takes the parameter because the public parameter is itself a derivation.

It returns all 32 bytes because a pair of chains starts at the two halves of one derivation. -/
abbrev SeedPrf (m : Type → Type) := PublicParam → Address → Array UInt64 → m Lanes4

/-- `H(P | A | S | suffix)`: the derivations from the scheme seed `S`.

The seed comes right after the address, and the suffix comes last. -/
def seedPrf {m : Type → Type} (H : Array UInt64 → m Lanes4) (s : Seed) : SeedPrf m :=
  -- `H(P | A | S | suffix)`: the chain starts, `R_0` and `P` are halves of it.
  fun pp address suffix => H (thInput pp address (s.toArray ++ suffix))

end EthLib.Cryptography.Xmss
