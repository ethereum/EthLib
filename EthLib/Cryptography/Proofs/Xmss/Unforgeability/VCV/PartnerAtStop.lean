module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CollisionTiming
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderIntervals

/-!
# The partner in the stopped finder's own table

Only the selected signing key matters to the two partner lookups.

Later tree work or an upper finder at a different key leaves those two earlier words intact.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig Constants OracleComp OracleSpec EarlierDigest EarlierDigest.Ledger
open CachedCodeword PostSigning

/-- Equality on one signing key suffices to move a two-word partner witness. -/
theorem partner_of_key_rows {pp : PublicParam} {c t : HashSpec.QueryCache}
    (k : Layer × UInt32) (a : HashInput) (key : messageKey pp a = some k)
    (rows : ∀ b, messageKey pp b = some k → c b = t b) (old : Partner pp c a) :
    Partner pp t a := by
  obtain ⟨w,first,d,valid,b,ne,eq,u,second,same⟩ := old
  exact ⟨w,(rows a key).symm.trans first,d,valid,b,ne,eq,u,
    (rows b (eq.trans key)).symm.trans second,same⟩

/-- A later cold call hits the target or the partner was present when the finder stopped. -/
theorem FirstPair.partner_at_stop {pp s l e m n a b y}
    (pair : FirstPair pp s l e m n a b y) (order : Ordered s.2 (live s.1) (targets s.1))
    (seen : SeenPost pp s) (prior : JointState)
    (note : Arrival.note (selectedNotice pp l e n b.randomizer y) prior ∈ s.2)
    (consistent : Agrees s.2 l e (selectedDigest y)) (stop : HashSpec.QueryCache)
    (rows : ∀ z, messageKey pp z = some (l,e) → live prior z = stop z) :
    s.1.2 = true ∨ Partner pp stop (trialInput pp l e n b.randomizer) := by
  apply (pair.partner_at_notice order seen prior note consistent).imp_right
  apply partner_of_key_rows (l,e) _ _ rows
  exact messageKey_trial ..

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
