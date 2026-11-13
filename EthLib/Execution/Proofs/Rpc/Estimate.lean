module

public import EthLib.Execution.Rpc.Estimate
import EthLib.Execution.Proofs.Rpc.Call

/-!
# Proofs: `eth_estimateGas` and `eth_createAccessList`

The estimate is a gas limit with which the call completes.

The method fails exactly when `eth_call` fails, with the same error.

It is the least positive such limit when the limits that complete form an interval.

The result of `eth_createAccessList` lists what the call read or wrote.

Its gas used and its error are those of the call with that list.
-/

public section

namespace EthLib.Execution.Rpc

namespace ChainView

variable {v : ChainView} {tx : GenericTransaction} {p : BlockParam} {c : CallChoices}

/-- The search answers at most its upper bound. -/
theorem searchGas_le (lo hi : Nat) : v.searchGas tx p c lo hi ≤ hi := by
  induction lo, hi using searchGas.induct v tx p c with
  | case1 lo hi h mid hmid ih =>
    dsimp only [mid] at hmid ih
    rw [searchGas]
    simp only [h, hmid, ↓reduceIte]
    omega
  | case2 lo hi h mid hmid ih =>
    dsimp only [mid] at hmid ih
    rw [searchGas]
    simp only [h, hmid, ↓reduceIte]
    exact ih
  | case3 lo hi h =>
    rw [searchGas]
    simp only [h, ↓reduceIte, Nat.le_refl]

/-- The search answers a limit with which the call completes, when it completes at the bound. -/
theorem searchGas_completes {lo hi : Nat} (h : v.Completes tx p c hi) :
    v.Completes tx p c (v.searchGas tx p c lo hi) := by
  induction lo, hi using searchGas.induct v tx p c with
  | case1 lo hi hlt mid hmid ih =>
    dsimp only [mid] at hmid ih
    rw [searchGas]
    simp only [hlt, hmid, ↓reduceIte]
    exact ih hmid
  | case2 lo hi hlt mid hmid ih =>
    dsimp only [mid] at hmid ih
    rw [searchGas]
    simp only [hlt, hmid, ↓reduceIte]
    exact ih h
  | case3 lo hi hlt =>
    rw [searchGas]
    simp only [hlt, ↓reduceIte]
    exact h

/-- The search answers at most each limit above `lo` with which the call completes.

It needs the call to complete at `hi`, and the limits that complete to form an interval. -/
theorem searchGas_least
    (hconv : ∀ a b d, a ≤ b → b ≤ d → v.Completes tx p c a → v.Completes tx p c d →
      v.Completes tx p c b)
    {lo hi g : Nat} (hhi : v.Completes tx p c hi) (hg : lo < g) (hc : v.Completes tx p c g) :
    v.searchGas tx p c lo hi ≤ g := by
  induction lo, hi using searchGas.induct v tx p c with
  | case1 lo hi hlt mid hmid ih =>
    dsimp only [mid] at hmid ih
    rw [searchGas]
    simp only [hlt, hmid, ↓reduceIte]
    exact ih hmid hg
  | case2 lo hi hlt mid hmid ih =>
    dsimp only [mid] at hmid ih
    rw [searchGas]
    simp only [hlt, hmid, ↓reduceIte]
    refine ih hhi (Nat.lt_of_not_le fun hle => hmid (hconv g _ hi hle ?_ hc hhi))
    omega
  | case3 lo hi hlt =>
    rw [searchGas]
    simp only [hlt, ↓reduceIte]
    omega

/-- A call completes with gas limit `g` exactly when `eth_call` answers data at that limit. -/
theorem completes_iff {g : Nat} :
    v.Completes tx p c g ↔ ∃ out, v.ethCall { tx with gas := some g } p c = .ok out := by
  simp only [Completes, ethCall_eq_ok_iff, runCall_eq_ok]
  constructor
  · rintro ⟨s, o, ⟨hs, hr⟩, he⟩
    exact ⟨o.output, s, o, hs, hr, he, rfl⟩
  · rintro ⟨_, s, o, hs, hr, he, -⟩
    exact ⟨s, o, ⟨hs, hr⟩, he⟩

/-- The estimate is a gas limit with which the call completes.

It is at most the gas limit of the call that the request prepares. -/
theorem estimateGas_completes {g : Nat} (h : v.estimateGas tx p c = .ok g) :
    v.Completes tx p c g ∧ ∃ s, v.prepareCall tx p c = .ok s ∧ g ≤ s.transaction.gas.toNat := by
  unfold estimateGas at h
  rcases hs : v.prepareCall tx p c with e | s
  · simp [hs, bind, Except.bind] at h
  simp only [hs, bind, Except.bind] at h
  rcases hr : v.runCall { tx with gas := some s.transaction.gas.toNat } p c with e | ⟨s', o⟩
  · simp [hr] at h
  simp only [hr] at h
  rcases ha : callAnswer o with e | out
  · simp [ha] at h
  simp only [ha, pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hdone : o.error = none := by
    unfold callAnswer at ha
    split at ha <;> simp_all
  exact ⟨searchGas_completes ⟨s', o, hr, hdone⟩, s, rfl, searchGas_le _ _⟩

/-- The estimate is at most each positive gas limit with which the call completes.

This holds when the limits with which the call completes form an interval.

Code that reads the gas left can break that hypothesis. -/
theorem estimateGas_least
    (hconv : ∀ a b d, a ≤ b → b ≤ d → v.Completes tx p c a → v.Completes tx p c d →
      v.Completes tx p c b)
    {g g' : Nat} (h : v.estimateGas tx p c = .ok g) (hpos : 0 < g')
    (hc : v.Completes tx p c g') : g ≤ g' := by
  unfold estimateGas at h
  rcases hs : v.prepareCall tx p c with e | s
  · simp [hs, bind, Except.bind] at h
  simp only [hs, bind, Except.bind] at h
  rcases hr : v.runCall { tx with gas := some s.transaction.gas.toNat } p c with e | ⟨s', o⟩
  · simp [hr] at h
  simp only [hr] at h
  rcases ha : callAnswer o with e | out
  · simp [ha] at h
  simp only [ha, pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hdone : o.error = none := by
    unfold callAnswer at ha
    split at ha <;> simp_all
  exact searchGas_least hconv ⟨s', o, hr, hdone⟩ hpos hc

/-- `eth_estimateGas` fails exactly when `eth_call` fails, and with the same error. -/
theorem estimateGas_eq_error_iff {e : Serialization.JsonRpc.RpcError} :
    v.estimateGas tx p c = .error e ↔ v.ethCall tx p c = .error e := by
  unfold estimateGas ethCall
  rcases hs : v.prepareCall tx p c with e' | s
  · simp [hs, runCall, bind, Except.bind]
  simp only [bind, Except.bind]
  rw [runCall_gas_self hs]
  rcases v.runCall tx p c with e' | ⟨s', o⟩
  · simp
  simp only
  rcases callAnswer o with e' | out <;> simp [pure, Except.pure]

/-- With one gas less than the answer of the search, the call does not complete, or that gas is 0.

It needs `lo` below `hi`, and `lo` to be 0 or a limit with which the call does not complete. -/
theorem searchGas_pred_not_completes {lo hi : Nat} (hlt : lo < hi)
    (hlo : lo = 0 ∨ ¬ v.Completes tx p c lo) :
    v.searchGas tx p c lo hi - 1 = 0 ∨ ¬ v.Completes tx p c (v.searchGas tx p c lo hi - 1) := by
  induction lo, hi using searchGas.induct v tx p c with
  | case1 lo hi h mid hmid ih =>
    dsimp only [mid] at hmid ih
    rw [searchGas]
    simp only [h, hmid, ↓reduceIte]
    exact ih (by omega) hlo
  | case2 lo hi h mid hmid ih =>
    dsimp only [mid] at hmid ih
    rw [searchGas]
    simp only [h, hmid, ↓reduceIte]
    exact ih (by omega) (Or.inr hmid)
  | case3 lo hi h =>
    rw [searchGas]
    simp only [h, ↓reduceIte]
    have : hi - 1 = lo := by omega
    rw [this]
    exact hlo

/-- The call does not complete with one gas less than the estimate.

That holds unless the estimate is at most 1. -/
theorem estimateGas_pred_not_completes {g : Nat} (h : v.estimateGas tx p c = .ok g) :
    g ≤ 1 ∨ ¬ v.Completes tx p c (g - 1) := by
  unfold estimateGas at h
  rcases hs : v.prepareCall tx p c with e | s
  · simp [hs, bind, Except.bind] at h
  simp only [hs, bind, Except.bind] at h
  rcases hr : v.runCall { tx with gas := some s.transaction.gas.toNat } p c with e | ⟨s', o⟩
  · simp [hr] at h
  simp only [hr] at h
  rcases ha : callAnswer o with e | out
  · simp [ha] at h
  simp only [ha, pure, Except.pure, Except.ok.injEq] at h
  subst h
  rcases Nat.eq_zero_or_pos s.transaction.gas.toNat with h0 | hpos
  · left
    rw [h0, searchGas]
    simp
  · rcases searchGas_pred_not_completes (v := v) (tx := tx) (p := p) (c := c) hpos (Or.inl rfl)
      with h1 | h1
    · left
      omega
    · exact Or.inr h1

/-- The result of `eth_createAccessList` reports the call with its own access list.

From Berlin, that list is what the call of the request read or wrote.

The gas used and the error message are then those of the call with that list.

Before Berlin, the list is empty, and they are those of the call of the request. -/
theorem createAccessList_eq_ok {r : AccessListResult} (h : v.createAccessList tx p c = .ok r) :
    ∃ s₁ o₁, v.runCall tx p c = .ok (s₁, o₁) ∧
      if s₁.fork < .berlin then
        r = { accessList := [], gasUsed := callGasUsed s₁ o₁, error := callErrorMessage o₁ }
      else
        r.accessList = accessedList s₁ o₁ ∧ ∃ s o,
          v.runCall { tx with accessList := some r.accessList
                              type := if tx.kind = 0 then some 1 else tx.type } p c = .ok (s, o) ∧
          r.gasUsed = callGasUsed s o ∧ r.error = callErrorMessage o := by
  unfold createAccessList at h
  rcases h1 : v.runCall tx p c with e | ⟨s₁, o₁⟩
  · simp [h1, bind, Except.bind] at h
  simp only [h1, bind, Except.bind] at h
  refine ⟨s₁, o₁, rfl, ?_⟩
  by_cases hf : s₁.fork < .berlin
  · simp only [hf, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h ⊢
    exact h.symm
  simp only [hf, ↓reduceIte] at h ⊢
  rcases h2 : v.runCall { tx with accessList := some (accessedList s₁ o₁)
                                  type := if tx.kind = 0 then some 1 else tx.type } p c
    with e | ⟨s, o⟩
  · simp [h2] at h
  simp only [h2, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, s, o, h2, rfl, rfl⟩

end ChainView

/-- The error message of a call is absent exactly when its message ends without an error. -/
theorem callErrorMessage_eq_none {o : Transactions.CallOutput} :
    callErrorMessage o = none ↔ o.error = none := by
  unfold callErrorMessage callAnswer
  rcases o.error with _ | (_ | _) <;> simp

end EthLib.Execution.Rpc
