module

public import EthLib.Cryptography.Vrf.Types
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: the VRF hash as a random oracle

The oracle that answers each byte string with a 32-byte value, and how many such values exist.

One call to it makes at most one query.

Calls on a list of inputs cost at most the sum of their costs.
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

/-- One call to the hash oracle makes at most one query. -/
theorem oracleHash_queryBound (x : ByteArray) :
    IsQueryBoundP (oracleHash x) (fun _ => True) 1 := by
  simp [oracleHash]

/-- Calls of the hash oracle on a list of inputs cost at most the sum of their costs. -/
theorem isQueryBound_mapM_oracleHash {α : Type} (hashCost : ByteArray → ℕ) (l : List α)
    (input : α → ByteArray) :
    IsQueryBound (l.mapM fun a => oracleHash (input a)) (l.map fun a => hashCost (input a)).sum
      (fun x n => hashCost x ≤ n) fun x n => n - hashCost x := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.mapM_cons, List.map_cons, List.sum_cons, oracleHash, bind_pure_comp,
      isQueryBound_query_bind_iff, isQueryBound_map_iff, Nat.add_sub_cancel_left]
    exact ⟨Nat.le_add_right _ _, fun _ => ih⟩

/-- There are `2^256` values of 32 bytes. -/
theorem natCard_digest : Nat.card Digest = 2 ^ 256 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun,
    Fintype.card_fin, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, VRF_HASH_SIZE]
  norm_num

end EthLib.Cryptography.Vrf
