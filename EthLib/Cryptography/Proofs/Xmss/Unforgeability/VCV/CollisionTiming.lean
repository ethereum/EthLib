module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CollisionArrivals
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NoticeOrder

/-!
# A collision already present at registration or observed afterwards

The two distinct physical inputs have the same valid low digest at the same signing key.

A matching first read after a coherent registration sets the hit flag.

Otherwise both complete words were in the live cache at every such registration.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleComp OracleSpec EarlierDigest CachedCodeword PostSigning TrialGraphWatch

/-- At each registration of this input, the partner exists or the hit flag fires. -/
theorem FirstPair.partner_at_notice {pp s l e m n a b y}
    (pair : FirstPair pp s l e m n a b y) (order : Ordered s.2 (live s.1) (targets s.1))
    (seen : SeenPost pp s) (prior : JointState)
    (note : Arrival.note (selectedNotice pp l e n b.randomizer y) prior ∈ s.2)
    (consistent : Agrees s.2 l e (selectedDigest y)) :
    s.1.2 = true ∨ Partner pp (live prior) (trialInput pp l e n b.randomizer) := by
  obtain ⟨ne,w,u,first,issued,found,sign,was,signed,valid,lowA,lowB,_⟩ := pair
  by_cases flag : s.1.2 = true
  · exact Or.inl flag
  · right
    have keep (msg : ByteArray) (rho : Randomizer) (v : HashOutput) (cut : JointState)
        (logged : Arrival.word (trialInput pp l e msg rho) v cut ∈ s.2)
        (cold : TrialGraphWatch.cold pp (trialInput pp l e msg rho) cut.1.1.1.1.1 = true)
        (low : halfOf 0 (ofOutput v) = selectedDigest y) :
        live prior (trialInput pp l e msg rho) = some v := by
      obtain saved | registered := order.before_or_registered note logged consistent
      · exact saved
      · apply False.elim (flag _)
        apply seen _ _ cut logged cold
        rw [target, messageKey_trial]
        exact registered.trans (congrArg some low.symm)
    have decode {v : HashOutput} (low : halfOf 0 (ofOutput v) = selectedDigest y) :
        validDigest v = some (selectedDigest y) := by
      simp [validDigest, digits, low, valid]
    exact ⟨u,keep n _ u issued sign signed lowB,_,decode lowB,_,ne,
      by rw [messageKey_trial, messageKey_trial], w,keep m _ w first found was lowA,decode lowA⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
