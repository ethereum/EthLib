module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderReceiptLog

/-!
# Both directions of correspondence between signing replies and registrations

A successful raw reply supplies its two actual recorded notices.

Every successful registration in a completed initially empty run belongs to a successful raw reply.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig

private theorem Records.includes {pp q idx msg ans pre post}
    (h : Records pp q idx msg ans pre post) : pre ⊆ post := by
  cases ans with
  | error _ => rw [show post = pre from h]
  | ok sig =>
    obtain ⟨c,eq⟩ := h
    rw [eq]
    exact fun n hn => List.mem_append_right _ hn

theorem ReceiptLog.includes {pp q log pre post}
    (h : ReceiptLog pp q log pre post) : pre ⊆ post := by
  induction h with
  | nil => exact fun _ h => h
  | cons one _ ih => exact fun _ h => ih (one.includes h)

/-- Both registrations of this successful raw reply occur in the final history. -/
theorem ReceiptLog.of_success {pp q log pre post} (h : ReceiptLog pp q log pre post) {req sig}
    (member : (req, Except.ok sig) ∈ log) :
    ∃ c : Receipt pp q req.leafIndex req.message sig, c.notes ⊆ post := by
  induction h with
  | nil => cases member
  | cons one rest ih =>
    rcases List.mem_cons.mp member with eq | later
    · cases eq
      obtain ⟨c,eq⟩ := one
      refine ⟨c, fun n hn => rest.includes ?_⟩
      rw [eq]
      exact List.mem_append_left _ hn
    · exact ih later

/-- The stream contains no registration from any response absent from the original raw log. -/
theorem ReceiptLog.of_register {pp q log pre post} (h : ReceiptLog pp q log pre post) {n}
    (member : n ∈ post) :
    n ∈ pre ∨ ∃ req sig, (req, Except.ok sig) ∈ log ∧
      ∃ c : Receipt pp q req.leafIndex req.message sig, n ∈ c.notes ∧ c.notes ⊆ post := by
  induction h with
  | nil => exact Or.inl member
  | @cons req ans rest before mid after one tail ih =>
    rcases ih member with earlier | ⟨req',sig,logged,c,mem,all⟩
    · cases ans with
      | error _ =>
        rw [show mid = before from one] at earlier
        exact Or.inl earlier
      | ok sig =>
        obtain ⟨c,eq⟩ := one
        rw [eq] at earlier
        rcases List.mem_append.mp earlier with here | old
        · refine Or.inr ⟨req,sig,List.mem_cons_self,c,here,?_⟩
          intro v mv
          apply tail.includes
          rw [eq]
          exact List.mem_append_left _ mv
        · exact Or.inl old
    · exact Or.inr ⟨req',sig,List.mem_cons_of_mem _ logged,c,mem,all⟩

/-- Filtering the chronological stream preserves the exact incoming state of each registration. -/
theorem member_register {l e b d s} (xs : List Arrival) :
    (FinderNotice.register l e b d, s) ∈ registrations xs ↔
      Arrival.note (.register l e b d) s ∈ xs := by
  rw [registrations, List.mem_filterMap]
  constructor
  · rintro ⟨a,observed,eq⟩
    cases a with
    | word => cases eq
    | note note prior =>
      cases note with
      | attempt => cases eq
      | register role epoch bytes digest =>
        have equal : (FinderNotice.register role epoch bytes digest,prior) =
          (.register l e b d,s) :=
          Option.some.inj eq
        cases equal
        exact observed
  · intro observed
    exact ⟨.note (.register l e b d) s, observed, rfl⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
