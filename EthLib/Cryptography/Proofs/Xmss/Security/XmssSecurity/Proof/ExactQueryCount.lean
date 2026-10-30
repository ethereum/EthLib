import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.IdealStatement

open OracleComp OracleSpec
open scoped BigOperators

namespace XmssSecurity

inductive ExactQueryCount {index : Type} {spec : OracleSpec index} :
    OracleComp spec α → Nat → Prop where
  | pure (value : α) : ExactQueryCount (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat) (hnext : ∀ output, ExactQueryCount (next output) count) :
      ExactQueryCount (liftM (spec.query input) >>= next) (count + 1)

inductive ExactPredicateQueryCount {index : Type} {spec : OracleSpec index}
    (predicate : spec.Domain → Prop) [DecidablePred predicate] :
    OracleComp spec α → Nat → Prop where
  | pure (value : α) : ExactPredicateQueryCount predicate (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat)
      (hnext : ∀ output, ExactPredicateQueryCount predicate (next output) count) :
      ExactPredicateQueryCount predicate
        (liftM (spec.query input) >>= next)
        (count + if predicate input then 1 else 0)

namespace ExactQueryCount

theorem bind {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count)
    (next : α → OracleComp spec β) (nextCount : Nat)
    (hnext : ∀ value, ExactQueryCount (next value) nextCount) :
    ExactQueryCount (computation >>= next) (count + nextCount) := by
  induction hcomputation with
  | pure value => simpa using hnext value
  | query input rest restCount hrest ih =>
      rw [bind_assoc]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ExactQueryCount.query input (fun output => rest output >>= next)
          (restCount + nextCount) ih

theorem map {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count) (f : α → β) :
    ExactQueryCount (f <$> computation) count := by
  convert hcomputation.bind
    (fun value => (Pure.pure (f value) : OracleComp spec β)) 0
    (fun value => ExactQueryCount.pure (f value)) using 1
  simp [map_eq_bind_pure_comp]

theorem withQueryLog {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count) :
    ExactQueryCount computation.withQueryLog count := by
  induction hcomputation with
  | pure value => simpa using ExactQueryCount.pure (value, [])
  | query input next count hnext ih =>
      rw [OracleComp.withQueryLog_bind, OracleComp.withQueryLog_query, bind_assoc]
      exact .query input (fun output =>
        Prod.map id ([⟨input, output⟩] ++ ·) <$> (next output).withQueryLog)
        count (fun output => by
          exact (ih output).map (Prod.map id ([⟨input, output⟩] ++ ·)))

namespace ExactPredicateQueryCount

variable {index : Type} {spec : OracleSpec index}
variable {predicate : spec.Domain → Prop} [DecidablePred predicate]

theorem bind {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactPredicateQueryCount predicate computation count)
    (next : α → OracleComp spec β) (nextCount : Nat)
    (hnext : ∀ value, ExactPredicateQueryCount predicate (next value) nextCount) :
    ExactPredicateQueryCount predicate (computation >>= next) (count + nextCount) := by
  induction hcomputation with
  | pure value => simpa using hnext value
  | query input rest restCount hrest ih =>
      rw [bind_assoc]
      convert ExactPredicateQueryCount.query input
        (fun output => rest output >>= next) (restCount + nextCount) ih using 1
      by_cases hinput : predicate input
      · simp [hinput]
        omega
      · simp [hinput]

theorem bind_right_of_mem_support
    {computation : OracleComp spec α} {next : α → OracleComp spec β}
    {count bound : Nat}
    (hexact : ExactPredicateQueryCount predicate computation count)
    (hbound : (computation >>= next).IsQueryBoundP predicate bound)
    (result : α) (hresult : result ∈ support computation) :
    count ≤ bound ∧
      (next result).IsQueryBoundP predicate (bound - count) := by
  induction hexact generalizing bound result with
  | pure value =>
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simpa only [pure_bind, Nat.sub_zero] using And.intro (Nat.zero_le bound) hbound
  | query input rest restCount hrest ih =>
      rw [bind_assoc, OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [mem_support_bind_iff] at hresult
      obtain ⟨output, _hquery, hresult⟩ := hresult
      by_cases hinput : predicate input
      · have hpositive : 0 < bound := hbound.1.resolve_left (not_not.mpr hinput)
        have hrec := ih output (by simpa [hinput] using hbound.2 output) result hresult
        constructor
        · simpa [hinput] using show restCount + 1 ≤ bound by omega
        · simpa [hinput, Nat.sub_sub, Nat.add_comm] using hrec.2
      · have hrec := ih output (by simpa [hinput] using hbound.2 output) result hresult
        constructor
        · simpa [hinput] using hrec.1
        · simpa [hinput] using hrec.2

end ExactPredicateQueryCount

theorem oracleHash (input : HashInput) :
    ExactQueryCount (Concrete.oracleHash input : OracleComp HashSpec HashOutput) 1 := by
  exact .query input (fun output => (Pure.pure output : OracleComp HashSpec HashOutput)) 0
    (fun output => ExactQueryCount.pure output)

theorem tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    ExactQueryCount
      (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) 1 := by
  unfold Concrete.tweakableHash
  exact (oracleHash _).map truncateHash

theorem chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest)
    (hposition : position + steps ≤ chainLength - 1) :
    ExactQueryCount
      (Concrete.chainWalk (m := OracleComp HashSpec) parameter leafIndex chain
        position steps value) steps := by
  induction steps generalizing value with
  | zero => exact .pure value
  | succ steps ih =>
      rw [Concrete.chainWalk]
      have hstep : position + steps < chainLength - 1 := by omega
      simp only [hstep, ↓reduceDIte]
      exact (ih value (by omega)).bind
        (fun previous => Concrete.chainHash parameter leafIndex chain
          ⟨position + steps, hstep⟩ previous) 1
        (fun previous => tweakableHash parameter (.chain leafIndex chain
          ⟨position + steps, hstep⟩) (Concrete.digestBytes previous))

theorem sequenceFin {n : Nat} (computation : Fin n → OracleComp spec α)
    (count : Fin n → Nat)
    (hcomputation : ∀ index, ExactQueryCount (computation index) (count index)) :
    ExactQueryCount (Concrete.sequenceFin computation)
      (∑ index, count index) := by
  induction n with
  | zero => exact .pure Fin.elim0
  | succ n ih =>
      rw [Concrete.sequenceFin, Fin.sum_univ_succ]
      exact (hcomputation 0).bind
        (fun head => do
          let tail ← Concrete.sequenceFin fun index : Fin n => computation index.succ
          Pure.pure (show Fin (n + 1) → α from Fin.cases head tail))
        (∑ index : Fin n, count index.succ)
        (fun head => (ih (fun index => computation index.succ)
          (fun index => count index.succ) (fun index => hcomputation index.succ)).bind
            (fun tail => Pure.pure
              (show Fin (n + 1) → α from Fin.cases head tail)) 0
            (fun tail => ExactQueryCount.pure
              (show Fin (n + 1) → α from Fin.cases head tail)))

end ExactQueryCount
end XmssSecurity
