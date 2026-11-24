module

public import EthLib.Cryptography.Proofs.Hash.Keccak.OneBlock
public import EthLib.Cryptography.Proofs.Indifferentiability

/-!
# Proofs: Keccak-256 as a random oracle, under a hypothesis

Many security bounds of EthLib model Keccak-256 as a random oracle on byte strings.

This file states the hypothesis that carries such a bound to the sponge over a random permutation.

The bound is the one of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge], §4.3.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

open OracleComp OracleSpec ENNReal EthLib.Cryptography.LazyPermutation
  EthLib.Cryptography.Indifferentiability

/-- Keccak-256 with the permutation `f` in place of Keccak-f[1600]. -/
def keccak256With (f : State → State) (msg : ByteArray) : Vector UInt8 DIGEST_LEN_256 :=
  Internal.squeeze256 (Internal.spongeAbsorb f RATE_256 msg.size (Internal.laneAt msg))

/-- With Keccak-f[1600], it is Keccak-256. -/
theorem keccak256With_keccakF : keccak256With keccakF = keccak256 := rfl

/-- The cost of a Keccak-256 call: one permutation call for each block of the padded message. -/
def keccak256Cost (msg : ByteArray) : ℕ :=
  -- A hash call on `len` bytes costs `len / 136 + 1` permutation calls.
  --
  -- These are the blocks of its padded input.
  --
  -- That is the cost of §3.5 of Bertoni et al. for an output of 256 bits, which fits in one block.
  --
  -- The messages here are byte strings, so the cost above is also the one of pad10*1.
  blockCount RATE_256 msg.size

/-- Every Keccak-256 call costs at least one permutation call. -/
theorem one_le_keccak256Cost (msg : ByteArray) : 1 ≤ keccak256Cost msg :=
  Nat.le_add_left 1 _

/-- **The hypothesis that Keccak-256 behaves as a random oracle.**

The padded sponge over a uniform permutation is indifferentiable from a random oracle.

Its bound is the closed form of Bertoni et al., equation (6), with `r = 1088` and `c = 512`.

For a cost `N`, that closed form is `((1 - 2^-r) N^2 + (1 + 2^-r) N) / 2^(c + 1)`.

The proof of Bertoni et al. is written for the padding of their §3.3.

Keccak pads with pad10*1 instead.

Their §3.3 asks only for an injective padding whose last block is not zero, which pad10*1 meets.

Their distinguisher may ask for outputs of any length, and the one here only for 256 bits.

EthLib does not prove it.

Theorems that use it take it as an argument. -/
def Keccak256Indifferentiable : Prop :=
  Indifferentiable keccak256With keccak256Cost (spongeBound 1088 512)

/-- **The hypothesis from the exact term of Bertoni et al.**

It needs indifferentiability with the exact term of their Lemma 5, for `r = 1088` and `c = 512`.

Their Theorem 2 allows every bound above that term, for a cost below `2^c`.

The closed form bounds the exact term, so the hypothesis follows. -/
theorem keccak256Indifferentiable_of_spongeExact
    (h : Indifferentiable keccak256With keccak256Cost (spongeExact 1088 512)) :
    Keccak256Indifferentiable :=
  indifferentiable_spongeBound h

/-- **A random-oracle bound on Keccak-256, carried to the sponge.**

Assume the hypothesis above, and take a game that costs at most `N`.

Let `δ` bound its image in the random-oracle model, for every simulator that asks once per call.

The simulator of §4.3, Algorithm 3, of Bertoni et al. asks its oracle at most once per call.

Then over a uniform permutation, the game wins with chance at most `δ` plus the bound below.

The bound is `((1 - 2^-1088) N^2 + (1 + 2^-1088) N) / 2^513`. -/
theorem keccak256_realProb_le (h : Keccak256Indifferentiable)
    {game : OracleComp (GameSpec State ByteArray (Vector UInt8 DIGEST_LEN_256)) Bool} {N : ℕ}
    (hN : WithinCost keccak256Cost game N) {δ : ℝ≥0∞}
    (hδ : ∀ (σ : Type) (s₀ : σ) (S : QueryImpl (PermSpec State)
      (StateT σ (OracleComp (RomSpec ByteArray (Vector UInt8 DIGEST_LEN_256))))),
      AsksOnce S → romProb (romGame S s₀ game) ≤ δ) :
    realProb keccak256With game ≤ δ + spongeBound 1088 512 N :=
  -- The image then asks the random oracle at most `N` times, by the theorem on its calls.
  realProb_le_of_romProb_le h hN hδ

end EthLib.Cryptography.Hash.Keccak
