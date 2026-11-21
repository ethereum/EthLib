module

public import EthLib.Cryptography.Proofs.EvalDistEq
public import EthLib.Cryptography.Proofs.HashSig.ProgrammedTable
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Seeded.StoppedRun
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.ConsistentQueryBound

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

/-- Run a preparation first, then the computation from the cache that the preparation leaves.

This does not change the output distribution of the computation. -/
theorem evalDist_presample_computation {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    ((simulateQ romImpl computation).run' cache) =ᵈ ((simulateQ romImpl preparation).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2) :=
  EthLib.Cryptography.HashSig.evalDist_presample_computation computation preparation cache

theorem hashQueryBound_after_preparation {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound computation cache q) (prepared : β × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ romImpl preparation).run cache)) :
    HashQueryBound computation prepared.2 q := by
  intro result hresult
  apply hbound result
  rw [OracleComp.support_eq_of_evalDistEq
    (evalDist_presample_computation (countHashQueries computation) preparation cache),
    mem_support_bind_iff]
  exact ⟨prepared, hprepared, hresult⟩

end XmssSecurity.Seeded
