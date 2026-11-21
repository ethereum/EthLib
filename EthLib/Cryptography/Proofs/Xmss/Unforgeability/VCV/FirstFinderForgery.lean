module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RegisteredFinderStop
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedRequest
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FirstBookings
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.BookedNotices
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderReceiptAgreement
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealClient

/-!
# A forgery meets the first finder or a later registered target

A unique lower leaf identifies its signing request in the valid raw log.

At a shared upper key all requests search over the same bottom root.

An earlier exhausted search would replay to exhaustion at the same private row.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp TwoLayerGraph Honest
open CachedCodeword PostSigning EarlierDigest VerifierProbe TrialGraphWatch
open ChainGraph (digestEquiv)

private theorem pick {pp l e m n a b y prior} {s : State pp}
    (reg : RegisteredPair pp s.1 l e m n a b y prior)
    (order : Ordered s.1.2 (live s.1.1) (targets s.1.1)) (seen : SeenPost pp s.1)
    (occupied : ∀ n p, Arrival.note n p ∈ s.1.2 → (bookings s.1 n.key).isSome)
    (firsts : FirstBookings s) (cold : ColdMarks s.2)
    (registered : ∀ x ∈ s.2, (x.call.layer,x.call.epoch) = (l,e) → RegisteredStop x s.1.2) :
    s.1.1.2 = true ∨ Hit s.2 := by
  obtain ⟨x,mem,key,first⟩ := firsts (l,e) (occupied _ _ reg.notice)
  obtain ⟨rho,d,st,found,note,rows⟩ := registered x mem key
  have before : bookings x.before (x.call.layer,x.call.epoch) = none := key.symm ▸ first
  exact (hit_of_registered_stop reg order seen key first (cold x mem before) found note
    (fun b atKey => (rows b atKey).symm)).imp_right fun h => ⟨x,mem,h⟩

attribute [local irreducible] mixedGame graph guardedGraph simulateQ game chronicleGame

/-- Both layers of a winning path use only its first finder and post-hit flag. -/
theorem post_or_first_of_marks (pp : PublicParam) (A : Adversary) (left : Nat)
    (r : ResidualCache pp)
    {obs : Outcome} {out : ResidualCache pp} {s : State pp} {last : SharedState}
    (actual : (some (obs,out),s.1) ∈ support (chronicleGame pp A left r))
    (fill : last ∈ support (RelabelState.endFill (FinderNotices.physical s.1.1)))
    (win : wins obs = true) (clean : ¬ (graph pp).Conflict last)
    (safe : ¬ (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project last))
    (firsts : FirstBookings s) (cold : ColdMarks s.2)
    (issued : ∀ x ∈ s.2, ∃ req ans, (req,ans) ∈ obs.log ∧
      IssuedAt x req.leafIndex req.message ans last s.1.2)
    (searches : ∀ x ∈ s.2, SearchFact pp x.call.layer x.call.epoch x.call.msg x.result.1 out last) :
    s.1.1.2 = true ∨ Hit s.2 := by
  have raw : (some (obs,out),FinderNotices.physical s.1.1) ∈ support
    ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run ((∅,∅),[])) := by
    rw [← project_graph pp A left r,support_map]
    exact ⟨_,actual,rfl⟩
  have later := RelabelState.le_of_mem_support_endFill fill
  have facts := signed_history pp A left r _ obs out _ raw last later
  have valid : (Valid (eraseLog obs.log) ∧ ¬Contains (eraseLog obs.log) obs.candidate) ∧
    obs.verified = true := by
    simpa only [wins, Bool.and_eq_true, decide_eq_true_eq] using win
  let body := WeightedCap.capCompOpt fee left ((game pp A).run r)
  have run := actual
  unfold chronicleGame at run
  have occupied := noted_booked (pp := pp) (q := left) (p := body) (s := initial.1)
    (z := (some (obs,out),s.1)) run
  have seen := seen_run pp left body initial.1 (z := (some (obs,out),s.1)) run
  have order := ordered_run pp left body initial.1 (z := (some (obs,out),s.1)) run
  obtain ⟨req,sig,logged,c,lower | upper⟩ := registered_collision pp A left r
    actual fill win clean safe
  · obtain ⟨_,reg⟩ := lower
    apply pick reg order seen occupied firsts cold
    intro x member key
    obtain ⟨other,ans,entry,address,auth⟩ := issued x member
    obtain ⟨layer,epoch⟩ := Prod.mk.inj key
    simp only [Addressed, layer] at address
    have same : req.leafIndex = other.leafIndex := by simpa using epoch.symm.trans address.1
    have unique : (obs.log.map fun a => a.1.leafIndex).Nodup := by
      simpa [Valid,eraseLog,List.map_map,Function.comp_def] using valid.1.1
    have eq := (Prod.mk.inj (List.inj_on_of_nodup_map unique logged entry same)).2
    cases eq
    exact auth
  · obtain ⟨_,candidate,read,stored,reg⟩ := upper
    apply pick reg order seen occupied firsts cold
    intro x member key
    obtain ⟨other,ans,entry,address,auth⟩ := issued x member
    cases ans with
    | ok sig' => exact auth
    | error why =>
      obtain ⟨layer,epoch⟩ := Prod.mk.inj key
      have failed : x.result.1 = none := auth.resolve_left (fun h => by rw [layer] at h; cases h)
      simp only [Addressed,layer] at address
      obtain ⟨atEpoch,root,bytes,row⟩ := address
      have same := nat_key (epoch.symm.trans atEpoch)
      rw [← same] at row
      have rootEq := digestEquiv.injective (Option.some.inj (row.symm.trans stored))
      obtain ⟨_,anchor,_,_,row',_,top⟩ := facts req sig logged
      have anchorEq := digestEquiv.injective (Option.some.inj (row'.symm.trans stored))
      have selected := searches x member
      rw [layer,epoch,bytes,rootEq,failed] at selected
      rw [anchorEq] at top
      cases selected.agree top.find clean

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
