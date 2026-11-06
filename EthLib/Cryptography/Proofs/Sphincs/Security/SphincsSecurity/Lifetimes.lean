module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Certificates.H26

/-!
# The proof of the security theorem

The proof applies the closing theorem of both routes to the numeric certificates.

Small budgets use the linear potential, the one-coin cover potential and the contact bound.

Large budgets use the covers at the survival-weighted baseline.

The entry point of the proof states the theorem again and uses this proof.
-/

@[expose] public section

namespace SphincsSecurity.Lifetimes

open Security ForsPotential

/-- The layered key of height 26 (10 + 8 + 8) has 127 bits of classical security.

Its signature limit is 1,182,000,000. -/
theorem h26_layered_bits : SecurityBits (.layered 26 3 8 24 10 1182000000) 127 :=
  @det_bitsFH (.layered 26 3 8 24 10 1182000000) (by decide) 26 26 24 10 231424 1182000000
    (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) 512487451133699472151040029945233408
    H0.rho_h26_b26 H0.tab_h26_b26 H0.small_h26_b26 H0.near_h26_b26 H0.tab_h26_b26_ok
        H0.rate_h26_b26_ok H0.small_h26_b26_ok
    H0.near_h26_b26_ok H0.check_h26_b26_ok [H0.cover_h26_b26_0] [] H0.covers_h26_L_ok

end SphincsSecurity.Lifetimes
