module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderReceiptCollision
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ColdMarks
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishCharge
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PartnerAtStop

/-!
# The first marked finder at a registered signing key

A later registration of this key names the same physical input as the signed collision.

The two input rows at that registration agree with those at the end of the selected finder.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig Constants OracleSpec OracleComp CachedCodeword PostSigning EarlierDigest

/--
The earlier partner already existed at the end of this first search, unless the post-hit flag fired.
-/
theorem hit_of_registered_stop {pp s l e m n a b y prior}
    (reg : RegisteredPair pp s l e m n a b y prior)
    (order : Ordered s.2 (live s.1) (targets s.1)) (seen : SeenPost pp s)
    {x : Finish pp} (key : (x.call.layer,x.call.epoch) = (l,e))
    (first : bookings x.before (l, e) = none)
    (cold : x.call.privateIn.2 (privateLow pp x.call.layer x.call.epoch x.call.msg) = none)
    {rho digits st} (found : x.result.1 = some (rho,digits))
    (note : Arrival.note (selectedNotice pp x.call.layer x.call.epoch x.call.msg rho digits) st
      ∈ s.2)
    (frame : ∀ z, messageKey pp z = some (x.call.layer,x.call.epoch) →
      live x.after_.1 z = live st z) :
    s.1.2 = true ∨ FirstHit x := by
  obtain ⟨layer,epoch⟩ := Prod.mk.inj key
  subst l e
  let addr := trialInput pp x.call.layer x.call.epoch x.call.msg rho
  have registered : Arrival.note (.register x.call.layer x.call.epoch addr
      (selectedDigest digits)) st ∈ s.2 := note
  have same := reg.sameInput addr (selectedDigest digits) st registered
  rcases reg.at_registration order seen registered with post | partner
  · exact Or.inl post
  · right
    refine ⟨first,cold,rho,digits,found,?_⟩
    rw [← same] at partner
    exact partner_of_key_rows (x.call.layer,x.call.epoch) addr (messageKey_trial ..)
      (fun z k => (frame z k).symm) partner

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
