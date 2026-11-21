module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistrationProjection
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.BookingFrame
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PrivateKeyFrame

/-!
# No private finder base before its first booking

Only an actual finder of the same key can warm the low private row.

It always books the key before the randomizer and retains that booking afterwards.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig Constants OracleComp OracleSpec EarlierDigest EarlierDigest.Ledger TrialGraphWatch

/-- Every key still unbooked has a cold randomizer low row for each possible message. -/
@[expose] def CoveredPrivate {pp : PublicParam} (r : ResidualCache pp)
    (s : ChronicleState) : Prop :=
  ∀ l e, bookings s (l,e) = none → ∀ m, r.2 (privateLow pp l e m) = none

theorem covered_initial (w : HashOutput) :
    CoveredPrivate (SecretEncoding.Residual.localState _ _
      (toKeyedState (parameterOfWord w) (afterWord w))) initial :=
  fun l e _ m => prefix_private_cold w l e m

private theorem finder_frame {pp q} (l layer : Layer) (e epoch : UInt32)
    (msg m : ByteArray) (other : (layer,epoch) ≠ (l,e)) {r s a out t}
    (actual : Ran q (find pp l e msg) r s a out t) :
    out.2 (privateLow pp layer epoch m) = r.2 (privateLow pp layer epoch m) := by
  have seen := actual.project
  rw [forget_find] at seen
  obtain ⟨bytes,g,seed,_⟩ := find_cut pp _ l e msg seen
  exact randomizer_frame layer l epoch e m msg other r
    (mem_support_of_mem_support_simulateQ_run _ _ _ seed)

private theorem other_of_unbooked {pp q} (l : Layer) (e : UInt32) (msg : ByteArray)
    {r s a out t} (ran : ((a,out),t) ∈ support
      ((simulateQ (chronicle pp q) ((find pp l e msg).run r)).run s))
    {k : Key} (empty : bookings t k = none) : k ≠ (l,e) := by
  rintro rfl
  have h := find_booked l e msg ran
  rw [empty] at h
  contradiction

/-- The next observed finder preserves coverage of all remaining unbooked keys. -/
theorem find_covered {pp q} (l : Layer) (e : UInt32) (msg : ByteArray) {r s a out t}
    (before : CoveredPrivate r s) (ran : ((a,out),t) ∈ support
      ((simulateQ (chronicle pp q) ((find pp l e msg).run r)).run s)) :
    CoveredPrivate out t := by
  intro layer epoch missing m
  have other := other_of_unbooked l e msg ran missing
  have unseen : bookings s (layer,epoch) = none := by
    cases old : bookings s (layer,epoch) with
    | none => rfl
    | some entry =>
      have booked := booked_persists ran (layer,epoch) (by rw [old]; rfl)
      rw [missing] at booked
      contradiction
  exact (finder_frame l layer e epoch msg m other ran).trans
    (before layer epoch unseen m)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
