module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderCallerInvariant
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PrivateBookings

/-!
# Private randomizer state at every completed marked finder

Before the first booking for a key its low private word is cold.

The complete physical caller keeps this invariant through public words and local randomness.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest

/-- Every completed search whose signing key was unbooked sampled a new low private word. -/
@[expose] def ColdMarks {pp : PublicParam} (xs : List (Finish pp)) : Prop :=
  ∀ (x : Finish pp), x ∈ xs → bookings x.before (x.call.layer,x.call.epoch) = none →
    x.call.privateIn.2 (privateLow pp x.call.layer x.call.epoch x.call.msg) = none

private def Holds {pp : PublicParam} (r : ResidualCache pp) (s : State pp) : Prop :=
  CoveredPrivate r s.1 ∧ ColdMarks s.2

private abbrev Preserves {pp : PublicParam} {α : Type} (p : Body pp α) := Maintains Holds p

private theorem regular_search (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray) :
    Preserves (search pp l e m) := by
  intro q r s a out t prior ran
  obtain ⟨actual, marks⟩ := ran.search
  refine ⟨find_covered l e m prior.1 actual,?_⟩
  rw [marks]
  intro x member old
  rcases List.mem_cons.mp member with eq | earlier
  · subst x
    exact prior.1 l e old m
  · exact prior.2 x earlier old

private theorem regular_physical {pp} {α : Type} {p : Program pp α}
    (same : ∀ r z, z ∈ support (p.run r) → ∀ l e m,
      z.2.2 (privateLow pp l e m) = r.2 (privateLow pp l e m)) :
    Preserves (physical p) := by
  intro q r s a out t prior ran
  obtain ⟨actual,marks⟩ := ran.physical
  refine ⟨?_,marks ▸ prior.2⟩
  intro l e unused m
  have old : bookings s.1 (l,e) = none := by
    cases initial : bookings s.1 (l,e) with
    | none => rfl
    | some h =>
      have occupied := booked_persists actual (l,e) (by simp [initial])
      simp [unused] at occupied
  rw [same r (a,out) (mem_support_of_mem_support_simulateQ_run _ _ _ actual) l e m]
  exact prior.1 l e old m

private theorem regular_carry {pp} {α : Type} {p : MixedLocal pp α}
    (same : ∀ r z, z ∈ support (p.run r) → ∀ l e m,
      z.2.2 (privateLow pp l e m) = r.2 (privateLow pp l e m)) :
    Preserves (physical (carry p)) := by
  apply regular_physical
  intro r z ran
  exact same r z (support_simulateQ_subset raw _ ran)

private theorem regular_tick (pp : PublicParam) : Preserves (physical (carry (mixedTick pp))) := by
  apply regular_carry
  intro r z actual l e m
  rw [mixedTick_private pp r actual]

private theorem regular_parameter (pp : PublicParam) : Preserves
    (physical (carry (mixedParameter pp))) := by
  apply regular_carry
  intro r z actual l e m
  rw [mixedParameter,StateT.run_map,support_map] at actual
  obtain ⟨y,h,rfl⟩ := actual
  exact parameter_frame l e m r h

private theorem regular_caller (pp : PublicParam) (A : Adversary) : Preserves (caller pp A) :=
  (show Steps pp Holds from ⟨regular_search pp,fun p same => regular_physical fun r z h _ _ _ =>
    by rw [same r z h],regular_tick pp,regular_parameter pp⟩).caller A

attribute [local irreducible] caller complete chronicle signing find graphPrf

/-- This caller preserves the cold low row at every first booking. -/
theorem cold_marks_of_run (pp : PublicParam) (r : ResidualCache pp) (A : Adversary) (left : Nat)
    (obs : Outcome) (out : ResidualCache pp) (rem : Nat) (s : State pp)
    (cold : CoveredPrivate r initial)
    (ran : ((some (obs,out),rem),s) ∈ support (observedGame pp A left r)) : ColdMarks s.2 := by
  have actual : Done left (caller pp A) r (initial,[]) obs out s :=
    complete_of_guard left ((caller pp A).run r) left (initial,[]) ran
  have initialFacts : Holds r (initial,[]) := ⟨cold,fun _ membership =>
    (List.not_mem_nil membership).elim⟩
  exact (regular_caller pp A left r _ obs out s initialFacts actual).2

/-- Every first finder mark in the original initialized game has a cold private low row. -/
theorem first_private_cold (w : HashOutput) (A : Adversary) (left : Nat) :
    let pp := parameterOfWord w
    let r : ResidualCache pp := SecretEncoding.Residual.localState _ _
      (toKeyedState pp (afterWord w))
    ∀ (obs : Outcome) (out : ResidualCache pp) (rem : Nat) (s : State pp),
      ((some (obs,out),rem),s) ∈ support (observedGame pp A left r) → ColdMarks s.2 := by
  intro pp r obs out rem s
  exact cold_marks_of_run pp r A left obs out rem s (covered_initial w)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
