module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.Cost
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Seed.Guess

/-!
# Stopped runs with a lazy outside oracle

This module runs the hidden-row model with a lazy random oracle for every other input.

The outside oracle samples each answer on first use and caches it.

So the raw inputs may form an infinite type, such as all byte lists.

No distribution on infinite answer functions is needed.
-/

@[expose] public section

section

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Security.HiddenReveal

variable [Params]
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable
variable {ι : Type} [Fintype ι]

/-- The run stopped, or it finished with a bad result. -/
def StopOr {α : Type} (bad : α → Prop) : Option α → Prop
  | none => True
  | some value => bad value

end SphincsSecurity.Security.HiddenReveal

end

section

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Security.HiddenOutside

variable [Params]
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

abbrev Cache (D R : Type) := QueryCache (D →ₒ R)

section Compiler
variable {D R A ι : Type} [Fintype ι] [SampleableType R]
noncomputable local instance : DecidableEq ι := Classical.decEq _

noncomputable def outsideRead (input : D) (cache : Cache D R) : ProbComp (R × Cache D R) :=
  (randomOracle (spec := D →ₒ R) input).run cache

noncomputable def stoppedStep {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (input : (HiddenRows.SourceSpec D R ι).Domain)
    (next : (HiddenRows.SourceSpec D R ι).Range input → HiddenReveal.Knowledge ι →
      Cache D R → ProbComp (Option (α × Cache D R)))
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) : ProbComp (Option (α × Cache D R)) :=
  match input with
  | .inl draw => do
      let value ← liftM (unifSpec.query draw)
      next value known cache
  | .inr (.inr coordinate) =>
      next (table coordinate) (known.cacheQuery coordinate (table coordinate)) cache
  | .inr (.inl bytes) =>
      let ordinary := do
        let result ← outsideRead bytes cache
        next result.1 known result.2
      match model.parse bytes with
      | none => ordinary
      | some query =>
          if known (model.incoming query.1) = none ∧
              query.2 = table (model.incoming query.1) then pure none
          else if query.2 = table (model.incoming query.1) then
            next (model.combine query.1 (table (model.outgoing query.1)))
              (known.cacheQuery (model.outgoing query.1) (table (model.outgoing query.1))) cache
          else ordinary

/-- The stopped run with the lazy outside oracle.

A canonical row whose value matches the table answers with its exposed successor.

Every other input reads the lazy outside oracle.

The run stops before a canonical row whose value matches a coordinate that is still hidden. -/
noncomputable def stopped {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) :
    HiddenReveal.Knowledge ι → Cache D R → ProbComp (Option (α × Cache D R)) :=
  OracleComp.construct (fun value _ cache => pure (some (value, cache)))
    (fun input _ next => stoppedStep model table input next) computation

noncomputable def stoppedExperiment {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) : ProbComp (Option (α × Cache D R)) :=
  HiddenReveal.completion known >>= fun table => stopped model table computation known cache

end Compiler
end SphincsSecurity.Security.HiddenOutside

end
