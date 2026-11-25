module

public import EthLib.Execution.Exports.Rpc
import all EthLib.Execution.Exports.Rpc
import EthLib.Execution.Proofs.Blocks.History

/-!
# Proofs: the chain view of the RPC export

A run of each block on all the records before it gives the records of the view.

From Paris the view passes only the last 255 recent blocks, which gives the same records.
-/

@[expose] public section

namespace EthLib.Execution.Rpc.Exports

open EthLib.Base (ChainConfig)
open EthLib.Exports (Result UnreadArgument toResult)
open EthLib.Execution.Blocks (BlockChain RecentBlock stateTransition)
open EthLib.Execution.Blocks.Exports (blockOf)

/-- The last 255 entries of an array, as a list, drop the others from its list. -/
private theorem toList_extract_recent (recent : Array RecentBlock) :
    (recent.extract (recent.size - 255) recent.size).toList =
      recent.toList.drop (recent.toList.length - 255) := by
  rw [Array.toList_extract, List.extract_eq_take_drop, Array.length_toList]
  exact List.take_of_length_le (by simp)

/-- The next record, on recent blocks kept in an array, is the one on all the records before. -/
private theorem nextRecord_eq (config : ChainConfig) (checkSeal : Bool) (lowest : BlockRecord)
    (recent : Array RecentBlock) (records : List BlockRecord)
    (hrecent : recent.toList = records.map BlockRecord.recent) (block : String × ByteArray) :
    nextRecord config checkSeal recent (records.getLast?.getD lowest) block = (do
      let prev := records.getLast?.getD lowest
      let ⟨_, block⟩ ← blockOf config block.1 block.2
      let chain : BlockChain := ⟨config, prev.state, records.map BlockRecord.recent⟩
      let state ← toResult s!"block {block.header.number}" (stateTransition chain block checkSeal)
      let hash ← toResult none
        (block.header.hash.mapError fun e => UnreadArgument.mk s!"block hash: {reprStr e}")
      toResult s!"block {block.header.number}" (BlockRecord.ofRun chain block hash state)) := by
  unfold nextRecord
  refine bind_congr fun ⟨fork, block⟩ => ?_
  dsimp only
  by_cases h : .paris ≤ fork
  · -- From Paris, the chain keeps the last 255 recent blocks, and the run reads only those.
    simp only [h, ite_true, toList_extract_recent, hrecent]
    let chain : BlockChain :=
      ⟨config, (records.getLast?.getD lowest).state, records.map BlockRecord.recent⟩
    have hst := Blocks.stateTransition_drop_recent chain block checkSeal h
    have hrun := fun o p => Blocks.runBody_drop_recent chain block o p
    dsimp only [chain] at hst hrun
    simp only [hst, BlockRecord.ofRun, hrun]
  · -- Before Paris, the chain keeps every recent block.
    simp only [h, ite_false, hrecent]

/-- A run over records and their recent blocks in arrays is a run over the list of records. -/
private theorem foldlM_records (config : ChainConfig) (checkSeal : Bool) (lowest : BlockRecord)
    (step : List BlockRecord → String × ByteArray → Result (List BlockRecord))
    (hstep : ∀ records block, step records block = (do
      let record ← nextRecord config checkSeal (records.map BlockRecord.recent).toArray
        (records.getLast?.getD lowest) block
      return records ++ [record]))
    (rest : List (String × ByteArray)) (records : Array BlockRecord) (recent : Array RecentBlock)
    (hrecent : recent.toList = records.toList.map BlockRecord.recent) :
    (do
      let (records, _) ← rest.foldlM (init := (records, recent))
        fun (records, recent) block => do
          let record ← nextRecord config checkSeal recent (records.back?.getD lowest) block
          return (records.push record, recent.push record.recent)
      return records.toList) = rest.foldlM step records.toList := by
  induction rest generalizing records recent with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.foldlM_cons, hstep, bind_assoc, pure_bind] at ih ⊢
    -- The array of recent blocks and the last record are those of the list of records.
    rw [← hrecent, Array.toArray_toList, Array.getLast?_toList]
    refine bind_congr fun record => ?_
    -- Both runs push the new record, and the arrays stay in step.
    have := ih (records.push record) (recent.push record.recent) (by simp [hrecent])
    rwa [Array.toList_push] at this

/-- The records of a view are those of a run over the list of all the records before each block.
-/
theorem recordsOf_eq (config : ChainConfig) (checkSeal : Bool) (lowest : BlockRecord)
    (rest : List (String × ByteArray)) :
    recordsOf config checkSeal lowest rest =
      rest.foldlM (init := [lowest]) fun records block => do
        let prev := records.getLast?.getD lowest
        let ⟨_, block⟩ ← blockOf config block.1 block.2
        let chain : BlockChain := ⟨config, prev.state, records.map BlockRecord.recent⟩
        let state ← toResult s!"block {block.header.number}" (stateTransition chain block checkSeal)
        let hash ← toResult none
          (block.header.hash.mapError fun e => UnreadArgument.mk s!"block hash: {reprStr e}")
        let record ← toResult s!"block {block.header.number}"
          (BlockRecord.ofRun chain block hash state)
        return records ++ [record] := by
  unfold recordsOf
  -- The run starts from the lowest record and its recent block.
  refine foldlM_records config checkSeal lowest _ ?_ rest #[lowest] #[lowest.recent] rfl
  intro records block
  -- Each step is the next record on all the records before it.
  rw [nextRecord_eq config checkSeal lowest _ records rfl]
  simp only [bind_assoc]

end EthLib.Execution.Rpc.Exports
