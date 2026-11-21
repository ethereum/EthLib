module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeOrigin

/-!
# The order of first physical reads and signing registrations

A first read after a registration sees its target unless a later registration changes that key.

A first read before registration is already present in that registration's incoming cache.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleComp OracleSpec EarlierDigest.Ledger TrialGraphWatch CachedCodeword
open scoped Classical

abbrev live (s : JointState) := s.1.2.1.1
abbrev targets (s : JointState) := s.1.1.1.1.2

/-- The exact live word table and registry after each observed arrival, newest arrival first. -/
inductive Ordered : List Arrival → HashSpec.QueryCache → Registry → Prop where
  | nil (cache : HashSpec.QueryCache) (reg : Registry) : Ordered [] cache reg
  | word {xs cache reg} (prev : Ordered xs cache reg) (b : HashInput) (w : HashOutput)
      (st : JointState) (cold : cache b = none) (incoming : targets st = reg) :
      Ordered (.word b w st :: xs) (cache.cacheQuery b w) reg
  | note {xs cache reg} (prev : Ordered xs cache reg) (n : FinderNotice)
      (st : JointState) (prior : live st = cache) :
      Ordered (.note n st :: xs) cache (register n reg)

private theorem registry_step {pp q} {t : Queries.Domain} {s z}
    (h : z ∈ support (((joint pp q) t).run s)) :
    targets z.2 = match t with
      | .inl _ => targets s
      | .inr n => register n (targets s) := by
  have watch := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp h).1
  have obs := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp watch).1
  have post := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp obs).1
  have basic := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp post).1
  rcases t with a | n
  · rw [base, StateT.run_mk, support_map] at basic
    obtain ⟨_,_,eq⟩ := basic
    exact (congrArg (fun z => z.2.2) eq).symm
  · rw [base, StateT.run_mk, mem_support_pure_iff] at basic
    exact congrArg (fun z => z.2.2) basic

/-- A real observer step is a first word, a notice, or an operation preserving both tables. -/
theorem ordered_step (pp : PublicParam) (q : Nat) :
    (chronicle pp q).PreservesInv (fun s => Ordered s.2 (live s.1) (targets s.1)) := by
  rintro t ⟨s, xs⟩ prev ⟨x, next, after⟩ actual
  obtain ⟨step, log⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp actual
  have reg := registry_step step
  obtain ⟨watch,_⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp step
  obtain ⟨_, upd⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp watch
  change next.1.2 = update pp cut t x s.1.2 at upd
  change after = remember pp t s x xs at log
  subst after
  change Ordered _ (live next) (targets next)
  have vals := congrArg (fun h : History => h.1.1) upd
  change live next = _ at vals
  change targets next = _ at reg
  rw [vals, reg]
  rcases t with ((coin | b) | op) | note
  · exact prev
  · by_cases fresh : MessageAt pp b ∧ live s b = none
    · simpa only [update, remember, ite_eq_left fresh, recordWordAt] using
        Ordered.word prev b x s fresh.2 rfl
    · simpa only [update, remember, fresh, ite_false] using prev
  · exact prev
  · simpa only [remember, update, cut] using Ordered.note prev note s rfl

/-- Every actual capped path retains the order certificate, including paths ending in refusal. -/
theorem ordered_run {α : Type} (pp : PublicParam) (q : Nat) (p : OracleComp Queries α)
    (s : JointState) {z} (ran : z ∈ support ((simulateQ (chronicle pp q) p).run (s,[]))) :
    Ordered z.2.2 (live z.2.1) (targets z.2.1) :=
  by
    apply simulateQ_run_preservesInv _ _ (ordered_step pp q) _ _ _ _ ran
    exact Ordered.nil _ _

/-- Only the first read of each byte string is entered, and its full word is retained. -/
theorem Ordered.saved {xs cache reg} (h : Ordered xs cache reg) {b w st}
    (old : Arrival.word b w st ∈ xs) : cache b = some w := by
  induction h with
  | nil => cases old
  | word prev a u _ cold _ ih =>
    rcases List.mem_cons.mp old with eq | earlier
    · cases eq
      exact QueryCache.cacheQuery_self ..
    · have original := ih earlier
      have different : b ≠ a := fun eq => by subst a; rw [cold] at original; cases original
      simpa [QueryCache.cacheQuery_of_ne, different] using original
  | note _ _ _ _ ih => exact ih ((List.mem_cons.mp old).resolve_left (by simp))

/-- Every registration at this key in the complete transcript installed the specified target. -/
@[expose] def Agrees (xs : List Arrival) (l : Layer) (e : UInt32) (d : Digest) : Prop :=
  ∀ input other st, Arrival.note (.register l e input other) st ∈ xs → other = d

private theorem Agrees.tail {a xs l e d} (h : Agrees (a :: xs) l e d) : Agrees xs l e d :=
  fun _ _ _ old => h _ _ _ (List.mem_cons_of_mem _ old)

private theorem Ordered.registered {xs cache reg} (h : Ordered xs cache reg)
    {l e input d prior} (seen : Arrival.note (.register l e input d) prior ∈ xs)
    (consistent : Agrees xs l e d) : reg (l,e) = some d := by
  induction h with
  | nil => cases seen
  | word _ _ _ _ _ _ ih =>
    exact ih ((List.mem_cons.mp seen).resolve_left (by simp)) consistent.tail
  | note prev n state _ ih =>
    rcases List.mem_cons.mp seen with eq | old
    · cases eq
      simp [register]
    · have anchor := ih old consistent.tail
      cases n with
      | attempt => exact anchor
      | register l' e' b v =>
        by_cases same : (l,e) = (l',e')
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
          have dEq := consistent b v state List.mem_cons_self
          simp [register,dEq]
        · simpa [register, Function.update_of_ne same] using anchor

/-- Compare the actual cold first response with the incoming tables at any matching registration. -/
theorem Ordered.before_or_registered {xs cache reg} (h : Ordered xs cache reg)
    {l e input d prior b w first} (note : Arrival.note (.register l e input d) prior ∈ xs)
    (word : Arrival.word b w first ∈ xs) (consistent : Agrees xs l e d) :
    live prior b = some w ∨ targets first (l,e) = some d := by
  induction h with
  | nil => cases note
  | word prev a u st _ atStart ih =>
    have oldNote := (List.mem_cons.mp note).resolve_left (by simp)
    rcases List.mem_cons.mp word with now | old
    · cases now
      exact Or.inr (atStart ▸ prev.registered oldNote consistent.tail)
    · exact ih oldNote old consistent.tail
  | note prev n st atStart ih =>
    have oldWord := (List.mem_cons.mp word).resolve_left (by simp)
    rcases List.mem_cons.mp note with now | old
    · cases now
      exact Or.inl (atStart ▸ prev.saved oldWord)
    · exact ih old oldWord consistent.tail

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
