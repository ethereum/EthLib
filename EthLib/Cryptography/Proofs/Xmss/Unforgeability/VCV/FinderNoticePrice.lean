module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeGame
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistry
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchBookingPrice

/-!
# First-search allowance for the physical forgery experiment

The lower and upper finders use the snapshot taken before their first private randomizer lookup.

The returned allowance counts fresh unregistered physical trials on the same capped execution.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open Constants HashSig OracleSpec OracleComp CachedCodeword EarlierDigest EarlierDigest.Ledger
open TrialGraphWatch
open scoped ENNReal Classical

/-- The ledger can include every signing key in both layers. -/
noncomputable def allKeys : Finset Key :=
  ({Layer.bottom, Layer.top} : Finset Layer) ×ˢ (Finset.univ : Finset UInt32)

@[simp] theorem mem_allKeys (k : Key) : k ∈ allKeys := by
  cases k with
  | mk l e => cases l <;> simp [allKeys]

/-- Keep both the actual registry and every saved first-attempt snapshot. -/
@[expose] noncomputable def booked (pp : PublicParam) (A : Adversary) (left : Nat)
    (r : ResidualCache pp) :=
  let initial : Observed Registry × History :=
    ((((((∅, ∅), []), fun _ => none), 0), 0, 0), ((∅, ∅), fun _ => none))
  (simulateQ (watched pp cut register (fun s b => (target pp s b).isSome) left)
    (WeightedCap.capCompOpt fee left ((game pp A).run r))).run initial

/-- First-attempt snapshots and fresh valid replies share one physical query allowance. -/
theorem first_price (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    (small : left ≤ 2 ^ 127) :
    let run := booked pp A left r
    (∑' z, Pr{let u ← run}[u = z] *
      (total allKeys (searchMass pp 0 MAX_RANDOMIZER_TRIALS) z.2.2 + z.2.1.2.2)) ≤
      (2 * (CODE_SIZE / 2 ^ 128 : ℝ≥0∞)) * ∑' z, Pr{let u ← run}[u = z] * (z.2.1.2.1 : ℝ≥0∞) :=
  booking_price pp allKeys cut register _ (tracks pp) _ (by simp)
    0 MAX_RANDOMIZER_TRIALS (by rfl) left small ((game pp A).run r) left le_rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
