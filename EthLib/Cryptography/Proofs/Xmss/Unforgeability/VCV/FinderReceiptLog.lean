module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderSigningReceipt

/-!
# Successful signing receipts on the original adaptive raw log

Every error retains the old registration list.

Every success adds exactly its returned bottom and top notices in execution order.

The verifier issues physical hash calls and contributes no registrations.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleComp OracleSpec TrialGraphWatch

/-- One exact registration transition for each original raw reply, in the client's request order. -/
inductive ReceiptLog (pp : PublicParam) (q : Nat) : RawLog → List Registered →
    List Registered → Prop
  | nil (before) : ReceiptLog pp q [] before before
  | cons {req : SignRequest} {ans rest before mid after}
      (one : Records pp q req.leafIndex req.message ans before mid)
      (remaining : ReceiptLog pp q rest mid after) :
      ReceiptLog pp q ((req, ans) :: rest) before after

theorem ReceiptLog.append {pp q l r first mid last}
    (head : ReceiptLog pp q l first mid) (tail : ReceiptLog pp q r mid last) :
      ReceiptLog pp q (l ++ r) first last := by
  induction head with
  | nil => exact tail
  | cons one _ ih => exact .cons one (ih tail)

private theorem Ran.mapped {pp q} {α β : Type} {p : Program pp α} {f : α → β} {r s b out t}
    (ran : Ran q (f <$> p) r s b out t) : ∃ a, Ran q p r s a out t ∧ f a = b := by
  rw [← bind_pure_comp] at ran
  obtain ⟨a,_,_,head,tail⟩ := ran.bind
  obtain ⟨same,rfl,rfl⟩ := tail.pure_result
  exact ⟨a,head,same.symm⟩

attribute [local irreducible] simulateQ TwoLayerGraph.graph Xmss.Internal.findCodeword mixedFind
  TwoLayerGraph.Honest.selection Xmss.verifyWith

private theorem receipts_query {pp q} (t : (World + SigningSpec).Domain) {r s a out last}
    (ran : Ran q (oracle pp t).run r s a out last) :
    ReceiptLog pp q a.2 (registrations s.2) (registrations last.2) := by
  cases t with
  | inl u =>
    change Ran q ((fun v => (v, ([] : RawLog))) <$> carry (mixedWorldPass pp u)) _ _ _ _ _ at ran
    obtain ⟨_, raw, rfl⟩ := ran.mapped
    rw [raw.carry_registers]
    exact .nil _
  | inr req =>
    change Ran q (request pp req) _ _ _ _ _ at ran
    unfold request at ran
    obtain ⟨_,_,_,tick,rest⟩ := ran.bind
    obtain ⟨_,_,_,parameter,rest⟩ := rest.bind
    obtain ⟨ans,_,_,sign,done⟩ := rest.bind
    obtain ⟨rfl,_,rfl⟩ := done.pure_result
    have receipt := signing_receipt sign
    rw [parameter.carry_registers, tick.carry_registers] at receipt
    exact .cons receipt (.nil _)

/-- The adaptive caller receives each optional reply and logs every attempted signing request. -/
theorem receipts_client {pp q} {α : Type} (p : OracleComp (World + SigningSpec) α) {r s z out t}
    (ran : Ran q (simulateQ (oracle pp) p).run r s z out t) :
    ReceiptLog pp q z.2 (registrations s.2) (registrations t.2) := by
  induction p using OracleComp.inductionOn generalizing r s t out z with
  | pure a =>
    simp only [simulateQ_pure, WriterT.run_pure] at ran
    obtain ⟨rfl, _, rfl⟩ := ran.pure_result
    exact .nil _
  | query_bind query k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind'] at ran
    obtain ⟨⟨answer, pre⟩,_,_,step,tail⟩ := ran.bind
    obtain ⟨⟨_, post⟩,rest,rfl⟩ := tail.mapped
    exact (receipts_query query step).append (ih answer rest)

private theorem uncapped {pp : PublicParam} {α : Type} (q : Nat) (p : Program pp α)
    (r : ResidualCache pp) (s : ChronicleState) {a out t}
    (actual : (some (a,out),t) ∈ support ((simulateQ (chronicle pp q)
      (WeightedCap.capCompOpt fee q (p.run r))).run s)) : Ran q p r s a out t :=
  WeightedCap.mem_support_of_capCompOpt_some (chronicle pp q) fee (p.run r) q s (a,out) t actual

/-- The completed capped transcript records exactly the successful signing registrations. -/
theorem completed_receipts (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    {obs : Outcome} {out : ResidualCache pp} {t : ChronicleState}
    (actual : (some (obs,out),t) ∈ support (chronicleGame pp A left r)) :
    ReceiptLog pp left obs.log [] (registrations t.2) := by
  unfold chronicleGame at actual
  have ran := uncapped left (game pp A) r initial actual
  unfold game at ran
  obtain ⟨root,_,_,key,rest⟩ := ran.bind
  obtain ⟨⟨candidate, entries⟩,_,_,client,rest⟩ := rest.bind
  obtain ⟨_,_,_,verify,done⟩ := rest.bind
  obtain ⟨rfl,_,rfl⟩ := done.pure_result
  rw [verify.carry_registers]
  have log := receipts_client _ client
  rw [key.carry_registers] at log
  exact log

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
