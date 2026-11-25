module

public import EthLib.Cryptography.Vrf.Types
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Proofs: the VRF hash as a random oracle

The oracle that answers each byte string with a 32-byte value, and how many such values exist.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants
open OracleSpec OracleComp

/-- The hash as an oracle from byte strings to 32-byte values. -/
abbrev HashSpec := ByteArray →ₒ Digest

/-- One call to the hash oracle. -/
def oracleHash (x : ByteArray) : OracleComp HashSpec Digest :=
  liftM (HashSpec.query x)

/-- There are `2^256` values of 32 bytes. -/
theorem natCard_digest : Nat.card Digest = 2 ^ 256 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun,
    Fintype.card_fin, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, VRF_HASH_SIZE]
  norm_num

end EthLib.Cryptography.Vrf
