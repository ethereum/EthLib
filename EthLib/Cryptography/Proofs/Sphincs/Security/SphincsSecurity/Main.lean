module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Lifetimes

/-!
# leanSPHINCS: the security theorem

This module states the main theorem of the security proof.

It states the theorem from the definitions of the game alone, so a reader can check it.

The game is the SUF-CMA game, and the hash is a random oracle with 32-byte answers.

The game samples a uniform 32-byte seed `S0`.

Key generation hashes it into the scheme seed `S = H(leanSPHINCS || S0)`.

The adversary gets the public key, the random oracle and a signing oracle.

It outputs a message and a signature.

It wins if they verify and the signing oracle did not return that signature for that message.

It also needs at most `N = 1,182,000,000` signing requests to win.

Every hash call of a run counts, repeated calls included.

The calls of key generation, signing and verification count too.

Let `q ≥ 1`.

If every run makes at most `q` hash calls, the adversary wins with probability at most `q / 2^127`.

The key has 26 levels, in three layers of heights 10, 8 and 8 from the top.

FORS has 24 trees of height 10.
-/

@[expose] public section

namespace SphincsSecurity

open Security ENNReal

/-- The claim for the parameters `P`: 127 bits of classical security.

Let `q ≥ 1`.

An adversary whose runs make at most `q` hash calls wins with probability at most `q / 2^127`. -/
def Secure127 (P : Params) : Prop :=
  letI := P
  ∀ q : ℕ, 1 ≤ q → ∀ adversary : Adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ 127 : ℕ) : ℝ≥0∞)

/-- leanSPHINCS with a layered key of height 26 has 127 bits of classical security.

The layers have heights 10, 8 and 8, FORS has 24 trees of height 10, and `N = 1,182,000,000`. -/
theorem h26_layered : Secure127 (.layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10)
    (N := 1_182_000_000)) :=
  Lifetimes.h26_layered_bits

/-- The claim is the security target of the statement at 127 bits, written out. -/
theorem secure127_iff (P : Params) : Secure127 P ↔ SecurityBits P 127 := Iff.rfl

end SphincsSecurity
