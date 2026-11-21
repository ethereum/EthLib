module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchLedger
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchCounts

/-!
# The first-search counts on the physically capped watched graph

The active keys exclude every already registered signing key.

The ordinary trial watch counts each live miss and its validity bit.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger

open HashSig OracleComp OracleSpec PostSigning CachedCodeword
open RealClient.GraphPrefix RealClient.GraphPrefix.TrialGraphWatch
open scoped Classical

noncomputable def watched {Note R : Type} (pp : PublicParam) (cut : Note → Option Key)
    (notice : Note → R → R) (registered : R → HashInput → Bool) (q : Nat) :=
  (observe pp notice registered q fun w => (digits w).isSome).extendState
    fun t _ w _ h => update pp cut t w h

def Compatible {R : Type} (pp : PublicParam) (registered : R → HashInput → Bool)
    (r : R) (saved : Snapshots) : Prop :=
  ∀ b k, messageKey pp b = some k → registered r b → (saved k).isSome

/-- Whenever a notice newly marks a physical key, the same notice identifies that key for booking.
-/
def TracksRegistration {Note R : Type} (pp : PublicParam) (cut : Note → Option Key)
    (notice : Note → R → R) (registered : R → HashInput → Bool) : Prop :=
  ∀ n r b k, messageKey pp b = some k → registered (notice n r) b →
    registered r b ∨ cut n = some k

private theorem still_saved (saved : Snapshots) (i k : Key) (s : Entry)
    (old : (saved k).isSome) : ((begin saved i s) k).isSome := by
  by_cases eq : k = i
  · subst k
    simp [begin]
  · simpa [begin, Function.update_of_ne eq] using old

private theorem notice_compatible {Note R : Type} {pp : PublicParam} {cut : Note → Option Key}
    {notice : Note → R → R} {registered : R → HashInput →
      Bool} (tracks : TracksRegistration pp cut notice registered)
    (n : Note) (r : R) (h : History) (earlier : Compatible pp registered r h.2) :
    Compatible pp registered (notice n r) (update pp cut (.inr n) () h).2 := by
  intro b k key active
  rcases tracks n r b k key active with old | first
  · have saved := earlier b k key old
    cases opened : cut n with
    | none => simpa only [update, opened] using saved
    | some i => simpa only [update, opened] using still_saved h.2 i k h.1 saved
  · simp [update, first, begin]

/-- Compare the live and booked counts with the actual pre-registration trial counters. -/
structure Counted {R : Type} (pp : PublicParam) (keys : Finset Key)
    (registered : R → HashInput → Bool)
    (s : Observed R × History) : Prop where
  sound : Sound pp (s.1.1.1.1, s.2)
  compatible : Compatible pp registered s.1.1.1.2 s.2.2
  inputs : initialCount keys (inputCount pp) s.2.2 s.2.1 ≤ s.1.2.1
  valid : initialCount keys (validCount pp) s.2.2 s.2.1 ≤ s.1.2.2

private def regAfter {Note R : Type} (notice : Note → R → R) (t : (Spec Note).Domain) (r : R) : R :=
  match t with | .inr n => notice n r | _ => r

private theorem pair_request {Note R : Type} (pp : PublicParam) (notice : Note → R → R)
    (t : (Spec Note).Domain) (st : D) (r : R) (x : (Spec Note).Range t) (st' : D) (r' : R)
    (ran : (x, st', r') ∈ support (((base pp notice) t).run (st, r))) :
    (x, st') ∈ support (((backend pp) t).run st) ∧
      r' = regAfter notice t r := by
  cases t with
  | inl raw =>
    simp only [base, StateT.run_mk, support_map] at ran
    obtain ⟨z, run, eq⟩ := ran
    cases eq
    exact ⟨run, rfl⟩
  | inr n =>
    simp only [base, StateT.run_mk, mem_support_pure_iff] at ran
    cases ran
    exact ⟨by simp [backend], rfl⟩

private theorem counts_at_notice {Note : Type} (pp : PublicParam) (cut : Note → Option Key)
    (n : Note) (h : History) (keys : Finset Key) (f : Key → Entry → Nat) :
    let next := update pp cut (.inr n) () h
    initialCount keys f next.2 next.1 = initialCount keys f h.2 h.1 := by
  cases opened : cut n <;> simp only [update, opened, initialCount_begin]

private theorem add_when_le {n m : Nat} (le : n ≤ m) (a b : Prop) [Decidable a] [Decidable b]
    (included : a → b) : n + (if a then 1 else 0) ≤ m + (if b then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all
  omega

/-- Compare one real graph query or notice while enough room remains for its physical fee. -/
theorem counted_step {Note R : Type} (pp : PublicParam) (keys : Finset Key) (cut : Note →
    Option Key)
    (notice : Note → R → R) (registered : R → HashInput → Bool)
    (tracks : TracksRegistration pp cut notice registered)
    (q : Nat) (t : (Spec Note).Domain) (s : Observed R × History)
      (before : Counted pp keys registered s)
    (room : s.1.2.1 + fee t ≤ q) {z} (hz : z
      ∈ support (((watched pp cut notice registered q) t).run s)) :
    Counted pp keys registered z.2 ∧ z.2.1.2.1 ≤ s.1.2.1 + fee t := by
  rcases s with ⟨⟨⟨⟨st, r⟩, post⟩, n, v⟩, hist⟩
  rcases z with ⟨x, ⟨⟨⟨st', r'⟩, post'⟩, n', v'⟩, hist'⟩
  obtain ⟨hobs, hhist⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp hz
  obtain ⟨hpost, hcount⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp hobs
  obtain ⟨hbase, hpostUpdate⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp hpost
  obtain ⟨hrun, hreg⟩ := pair_request pp notice t st r x st' r' hbase
  change hist' = update pp cut t x hist at hhist
  change (n', v') = BernoulliMoment.update q (pre pp registered)
    (TrialGraphWatch.valid (Note := Note) fun w => (digits w).isSome) t ((st, r), post) x
    ((st', r'), post') (n, v) at hcount
  change n + fee t ≤ q at room
  have hs : Sound pp (st', hist') := sound_step pp cut t (st, hist) before.sound (x, st', hist') <|
    (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mpr ⟨hrun, hhist⟩
  have hn := before.inputs
  have hv := before.valid
  have hc := before.compatible
  change initialCount keys (inputCount pp) hist.2 hist.1 ≤ n at hn
  change initialCount keys (validCount pp) hist.2 hist.1 ≤ v at hv
  change Compatible pp registered r hist.2 at hc
  clear hz hobs hpost hbase hpostUpdate hrun
  subst hist'
  rcases t with ((coin | a) | op) | note <;> simp only [regAfter] at hreg
  · simp only [pre, BernoulliMoment.update, Bool.false_and, Bool.false_eq_true, ite_false,
      Prod.mk.injEq] at hcount
    obtain ⟨rfl, rfl⟩ := hcount
    subst r'
    exact ⟨⟨hs, hc, hn, hv⟩, Nat.le_add_right _ _⟩
  · subst r'
    by_cases real : MessageAt pp a
    · obtain ⟨l, e, m, rho, encoded⟩ := real
      have present : MessageAt pp a := ⟨l, e, m, rho, encoded⟩
      have physical : trialInput pp l e m rho = a := encoded
      have key := physical ▸ messageKey_trial pp l e m rho
      obtain ⟨lo, hi⟩ := before.sound.rows a present
      cases cached : hist.1.1 a with
      | some w =>
        simp only [cached, Option.map_some] at lo hi
        have hot : cold pp a st = false := by simp [cold, lo]
        simp [pre, BernoulliMoment.update, hot] at hcount
        obtain ⟨rfl, rfl⟩ := hcount
        simp only [update, cached, reduceCtorEq, and_false, ite_false] at hs ⊢
        exact ⟨⟨hs, hc, hn, hv⟩, Nat.le_add_right _ _⟩
      | none =>
        have new : a ∉ hist.1.2 := by
          intro old
          have stored := before.sound.stored a old
          simp [cached] at stored
        simp only [cached, Option.map_none] at lo hi
        have fresh : cold pp a st = true := by simp [cold, present, lo, hi]
        have enough : n < q := by change n + 1 ≤ q at room; omega
        have delta := initialCount_probe pp keys hist.2 hist.1 a (l,e) key cached new x
        simp only [update, present, cached, and_self, ite_true] at hs ⊢
        let live := (l,e) ∈ keys ∧ hist.2 (l,e) = none
        have unpaid (active : live) : registered r a = false := by
          cases paid : registered r a with
          | false => rfl
          | true =>
            have saved := hc a (l,e) key paid
            simp [active.2] at saved
        have actual : n' = n + (if registered r a = false then 1 else 0) ∧
            v' = v + (if registered r a = false ∧ x ∈ accepted then 1 else 0) := by
          cases paid : registered r a <;> cases ok : (digits x).isSome <;>
            simpa [pre, BernoulliMoment.update, TrialGraphWatch.valid, fresh, paid, enough, ok,
              mem_accepted] using hcount
        refine ⟨⟨hs, hc, ?_, ?_⟩, ?_⟩
        · change initialCount keys (inputCount pp) hist.2 (hist.1.1.cacheQuery a x,
            insert a hist.1.2) ≤ n'
          rw [delta.1, actual.1]
          exact add_when_le hn _ _ unpaid
        · change initialCount keys (validCount pp) hist.2 (hist.1.1.cacheQuery a x,
            insert a hist.1.2) ≤ v'
          rw [delta.2, actual.2]
          exact add_when_le hv _ _ fun h => ⟨unpaid h.1, h.2⟩
        · change n' ≤ n + 1
          rw [actual.1]
          split <;> omega
    · have other : cold pp a st = false := by simp [cold, real]
      simp [pre, BernoulliMoment.update, other] at hcount
      obtain ⟨rfl, rfl⟩ := hcount
      simp only [update, real, false_and, ite_false] at hs ⊢
      exact ⟨⟨hs, hc, hn, hv⟩, Nat.le_add_right _ _⟩
  · simp [pre, BernoulliMoment.update] at hcount
    obtain ⟨rfl, rfl⟩ := hcount
    subst r'
    exact ⟨⟨hs, hc, hn, hv⟩, Nat.le_add_right _ _⟩
  · simp [pre, BernoulliMoment.update] at hcount
    obtain ⟨rfl, rfl⟩ := hcount
    subst r'
    cases x
    exact ⟨⟨hs, notice_compatible tracks note r hist hc,
      (counts_at_notice pp cut note hist keys _).trans_le hn,
      (counts_at_notice pp cut note hist keys _).trans_le hv⟩, Nat.le_add_right _ _⟩

/-- The same observed outcome bounds both first-attempt counts, including at a refused call. -/
theorem counted_cap {Note R α : Type} (pp : PublicParam) (keys : Finset Key) (cut : Note →
    Option Key)
    (notice : Note → R → R) (registered : R → HashInput → Bool)
    (tracks : TracksRegistration pp cut notice registered)
    (q : Nat) (p : OracleComp (Spec Note) α) (left : Nat) (s : Observed R × History)
    (sound : Counted pp keys registered s) (within : s.1.2.1 + left ≤ q) {z}
    (run : z ∈ support ((simulateQ (watched pp cut notice registered q)
      (WeightedCap.capCompOpt fee left p)).run s)) : Counted pp keys registered z.2 := by
  induction p using OracleComp.inductionOn generalizing left s with
  | pure x =>
    simp only [WeightedCap.capCompOpt_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at run
    subst z
    exact sound
  | query_bind t next ih =>
    rw [WeightedCap.capCompOpt_query_bind] at run
    split_ifs at run with fits
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨y, dy, tail⟩ := run
      have ⟨updated, step⟩ := counted_step pp keys cut notice registered tracks q t s sound
        (by omega) dy
      exact ih y.1 (left - fee t) y.2 updated (by omega) tail
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      subst z
      exact sound

/-- The initial graph is cold and no successful signature has yet registered a key. -/
theorem counted_empty {R : Type} (pp : PublicParam) (keys : Finset Key)
    (registered : R → HashInput → Bool) (r : R) (empty : ∀ b, registered r b = false) :
    Counted pp keys registered ((((((∅, ∅), []), r), 0), 0, 0), ((∅, ∅), fun _ => none)) := by
  refine ⟨sound_empty pp, ?_, ?_, ?_⟩
  · intro b k _ active
    simp [empty] at active
  · simp [initialCount, entry, inputCount, inputsAtKey]
  · simp [initialCount, entry, validCount, validInputs]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger
