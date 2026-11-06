module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.Rows

/-!
# The cost of a run with hidden rows

A source computation can also tick a cost, which stands for honest work done off the oracle.

A raw hash query costs one, a tick of `n` costs `n`, and private draws and reveals are free.

The trace of a run records each raw query and each tick, so its cost is the cost of the run.
-/

@[expose] public section

open OracleComp OracleSpec
namespace SphincsSecurity.Security.HiddenCost

variable [Params]
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

abbrev SourceCostSpec (D R ι : Type) := HiddenRows.SourceSpec D R ι + (Nat →ₒ Unit)
abbrev Entry (D : Type) := D ⊕ Nat

def sourceCost {D R ι : Type} : (SourceCostSpec D R ι).Domain → Nat
  | .inl (.inr (.inl _)) => 1
  | .inr amount => amount
  | _ => 0

def recorded {D R ι : Type} : (SourceCostSpec D R ι).Domain → List (Entry D)
  | .inl (.inr (.inl input)) => [.inl input]
  | .inr amount => [.inr amount]
  | _ => []

def entryCost {D : Type} : Entry D → Nat
  | .inl _ => 1
  | .inr amount => amount

def traceCost {D : Type} (entries : List (Entry D)) : Nat := (entries.map entryCost).sum

omit [Params] in
theorem traceCost_append {D : Type} (left right : List (Entry D)) :
    traceCost (left ++ right) = traceCost left + traceCost right := by simp [traceCost]

omit [Params] in
theorem recorded_cost {D R ι : Type} (input : (SourceCostSpec D R ι).Domain) :
    traceCost (recorded input) = sourceCost input := by
  cases input with
  | inl input => cases input with
    | inl draw => rfl
    | inr input => cases input <;> rfl
  | inr amount => simp [traceCost, recorded, entryCost, sourceCost]

def tick {D R ι : Type} (amount : Nat) : OracleComp (SourceCostSpec D R ι) Unit :=
  liftM ((SourceCostSpec D R ι).query (.inr amount))

def reveal {D R ι : Type} (coordinate : ι) : OracleComp (SourceCostSpec D R ι) Digest :=
  liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inr coordinate))))

def eraseQuery {D R ι : Type} :
    QueryImpl (SourceCostSpec D R ι) (OracleComp (HiddenRows.SourceSpec D R ι))
  | .inl input => liftM ((HiddenRows.SourceSpec D R ι).query input)
  | .inr _ => pure ()

def erase {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    OracleComp (HiddenRows.SourceSpec D R ι) α := simulateQ eraseQuery computation

def trace {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    OracleComp (SourceCostSpec D R ι) (α × List (Entry D)) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => do
      let value ← liftM ((SourceCostSpec D R ι).query input)
      let result ← next value
      return (result.1, recorded input ++ result.2)) computation

omit [Params] in
theorem trace_pure {D R ι α : Type} (value : α) :
    trace (pure value : OracleComp (SourceCostSpec D R ι) α) = pure (value, []) := rfl

omit [Params] in
theorem trace_query_bind {D R ι α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α) :
    trace (liftM ((SourceCostSpec D R ι).query input) >>= next) =
      (liftM ((SourceCostSpec D R ι).query input) >>= fun value =>
        (fun result => (result.1, recorded input ++ result.2)) <$> trace (next value)) := by
  change (liftM ((SourceCostSpec D R ι).query input) >>= fun value =>
      trace (next value) >>= fun result => pure (result.1, recorded input ++ result.2)) = _
  simp only [bind_pure_comp]

/-- The run under a budget: it stops before an operation that costs more than the budget left. -/
def cap {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    Nat → OracleComp (SourceCostSpec D R ι) (Option α) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun input _ next budget =>
      if sourceCost input ≤ budget then do
        let value ← liftM ((SourceCostSpec D R ι).query input)
        next value (budget - sourceCost input)
      else pure none) computation

end SphincsSecurity.Security.HiddenCost
