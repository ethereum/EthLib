module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedCuts
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.BookingCuts
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistrations

/-!
# The first completed finder for every booked signing key

The full marked client retains finder returns for unsuccessful signing requests too.

A registration can only repeat the booking made by its preceding finder.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp EarlierDigest
    TwoLayerGraph Honest LayerGraph.Hidden

/-- Each occupied booking has its actual first completed finder in the same stream. -/
@[expose] def FirstBookings {pp : PublicParam} (s : State pp) : Prop :=
  ∀ k, (bookings s.1 k).isSome → ∃ x ∈ s.2,
    (x.call.layer,x.call.epoch) = k ∧ bookings x.before k = none

private def Keeps {pp : PublicParam} {α : Type} (p : Body pp α) : Prop :=
  ∀ q r s a out t, FirstBookings s → Done q p r s a out t → FirstBookings t

private theorem keeps_pure {pp} {α : Type} (a : α) : Keeps (pure a : Body pp α) := by
  intro q r s b out t old ran
  obtain ⟨_,_,rfl⟩ := ran.pure_result
  exact old

private theorem keeps_bind {pp} {α β : Type} {p : Body pp α} {f : α → Body pp β}
    (first : Keeps p) (rest : ∀ a, Keeps (f a)) : Keeps (p >>= f) := by
  intro q r s a out t old ran
  obtain ⟨b,mid,g,h,k⟩ := ran.bind
  exact rest b q mid g a out t (first q r s b mid g old h) k

private theorem keeps_map {pp} {α β : Type} {p : Body pp α} (f : α → β) (h : Keeps p) :
    Keeps (f <$> p) := by
  rw [map_eq_pure_bind]
  exact keeps_bind h fun _ => keeps_pure _

private theorem keeps_carry {pp} {α : Type} (p : MixedLocal pp α) : Keeps (physical (carry p)) := by
  intro q r s a out t old ran k used
  obtain ⟨real, marks⟩ := ran.physical
  rw [carry_bookings real] at used
  rw [marks]
  exact old k used

private theorem carried {pp q} {α : Type} {p : MixedLocal pp α} {r s a out t}
    (ran : Done q (physical (carry p)) r s a out t) (old : FirstBookings s) : FirstBookings t :=
  keeps_carry p q r s a out t old ran

private theorem keeps_search {pp q l e m r s a out t}
    (ran : Done q (search pp l e m) r s a out t) (old : FirstBookings s) : FirstBookings t := by
  obtain ⟨real, marks⟩ := ran.search
  intro k occupied
  rw [marks]
  cases was : bookings s.1 k with
  | some h =>
    obtain ⟨x,member,key,first⟩ := old k (by rw [was]; rfl)
    exact ⟨x,List.mem_cons_of_mem _ member,key,first⟩
  | none =>
    have key : k = (l,e) := by
      by_contra other
      rw [find_other_booking l e m real k other,was] at occupied
      contradiction
    exact ⟨_,List.mem_cons_self, key.symm,was⟩

private theorem registered_old {pp q i m n rho tau x y r s a out t}
    (ran : Ran q (afterUpper pp i m n rho tau x y) r s a out t)
    (k : EarlierDigest.Key) (lower : k ≠ (.bottom,UInt32.ofNat i.toNat))
    (upper : k ≠ (.top,UInt32.ofNat (bottomTree i))) : bookings t k = bookings s k := by
  unfold afterUpper at ran
  obtain ⟨_,_,_,stage1,tail⟩ := ran.bind
  obtain ⟨_,_,_,stage2,tail⟩ := tail.bind
  obtain ⟨_,_,_,stage3,tail⟩ := tail.bind
  obtain ⟨_,_,_,stage4,tail⟩ := tail.bind
  obtain ⟨_,_,_,bottom,tail⟩ := tail.bind
  obtain ⟨_,_,_,top,ret⟩ := tail.bind
  obtain ⟨_,_,rfl⟩ := ret.pure_result
  rw [notice_other_booking _ top k upper,notice_other_booking _ bottom k lower,
    carry_bookings stage4,carry_bookings stage3,carry_bookings stage2,carry_bookings stage1]

attribute [local irreducible] emitStructure beforeValues revealValues pathSchedule
    search afterUpper find

private theorem keeps_signing (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    Keeps (signing pp idx msg) := by
  intro q r s ans out t old ran
  unfold signing at ran
  obtain ⟨a,_,_,lower,tail⟩ := ran.bind
  have h₁ := keeps_search lower old
  rcases a with _ | ⟨rho,x⟩
  · obtain ⟨_,_,rfl⟩ := tail.pure_result
    exact h₁
  · obtain ⟨_,_,_,chain,tail⟩ := tail.bind
    obtain ⟨root,_,_,tree,tail⟩ := tail.bind
    obtain ⟨b,_,stop,top,ret⟩ := tail.bind
    have h₂ := carried chain h₁
    have h₃ := carried tree h₂
    have h₄ := keeps_search top h₃
    rcases b with _ | ⟨tau,y⟩
    · obtain ⟨_,_,rfl⟩ := ret.pure_result
      exact h₄
    · obtain ⟨real,marks⟩ := ret.physical
      intro k used
      rw [marks]
      apply h₄ k
      by_cases lo : k = (.bottom,UInt32.ofNat idx.toNat)
      · subst k
        have saved := find_booked _ _ _ lower.search.1
        exact booked_persists top.search.1 _
          (by rw [carry_bookings tree.physical.1,carry_bookings chain.physical.1]; exact saved)
      by_cases hi : k = (.top,UInt32.ofNat (bottomTree idx))
      · subst k
        exact find_booked _ _ _ top.search.1
      rw [registered_old real k lo hi] at used
      exact used

private theorem keeps_request (pp : PublicParam) (t : (World + SigningSpec).Domain) :
    Keeps ((clientOracle pp t).run) := by
  rcases t with u | req
  · change Keeps ((fun x => (x,([] : RawLog))) <$> physical (carry (mixedWorldPass pp u)))
    exact keeps_map _ (keeps_carry _)
  · change Keeps (_ >>= _)
    apply keeps_bind (keeps_carry _)
    intro _
    apply keeps_bind (keeps_carry _)
    intro _
    exact keeps_bind (keeps_signing pp req.leafIndex req.message) fun _ => keeps_pure _

private theorem keeps_client {α : Type} (pp : PublicParam)
    (p : OracleComp (World + SigningSpec) α) :
    Keeps ((simulateQ (clientOracle pp) p).run) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure,WriterT.run_pure]; apply keeps_pure
  | query_bind t f ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,WriterT.run_bind']
    exact keeps_bind (keeps_request pp t) fun z => keeps_map _ (ih z.1)

private theorem keeps_caller (pp : PublicParam) (A : Adversary) : Keeps (caller pp A) := by
  unfold caller
  apply keeps_bind (keeps_carry _)
  intro _
  apply keeps_bind (keeps_client pp _)
  rintro ⟨_,_⟩
  exact keeps_bind (keeps_carry _) fun _ => keeps_pure _

attribute [local irreducible] caller complete chronicle signing graphPrf

/-- Every booking on a completed real marked caller came from a genuine first finder. -/
theorem first_bookings {pp} (A : Adversary) (left : Nat) (r : ResidualCache pp)
    {obs : Outcome} {out : ResidualCache pp} {rem : Nat} {s : State pp}
    (ran : ((some (obs,out),rem),s) ∈ support (observedGame pp A left r)) : FirstBookings s := by
  have actual : Done left (caller pp A) r (initial,[]) obs out s :=
    complete_of_guard left ((caller pp A).run r) left (initial,[]) ran
  have empty : FirstBookings (pp := pp) (initial,[]) := by
    intro k h
    change false = true at h
    contradiction
  exact keeps_caller pp A _ _ _ _ _ _ empty actual

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
