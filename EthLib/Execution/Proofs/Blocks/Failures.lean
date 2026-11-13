module

public import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the errors with which a block fails

A result meets a property on its errors when each error that it fails with has the property.

A sequence, a map and a change of error keep that, so a proof follows the steps of a definition.

The checks of a block before its body fail with no abort and no error of the state.

Nor do they fail for a system call or for a transaction kept out of the block.

Nor do the recent hashes, the roots and the checks of its output.

So the transition of a block fails only with errors of a property when its body does.

The property must also hold for the other errors of the block, and for the abort from Hegotá on.

A failed system call can be left out of the property as well, since the checks never give one.

So can a transaction kept out of the block, for the same reason.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork}

/-! ## Results whose errors meet a property -/

/-- Whether every failure of a result meets a property. -/
def ErrorsMeet {α : Type} (P : BlockError → Prop) (r : Except BlockError α) : Prop :=
  ∀ e, r = .error e → P e

/-- A success has no failure. -/
theorem ErrorsMeet.ok {α : Type} {P : BlockError → Prop} (a : α) :
    ErrorsMeet P (.ok a : Except BlockError α) :=
  fun _ h => by cases h

/-- A pure result has no failure. -/
theorem ErrorsMeet.pure {α : Type} {P : BlockError → Prop} (a : α) :
    ErrorsMeet P (Pure.pure a : Except BlockError α) :=
  fun _ h => by cases h

/-- A failure with an error that meets the property meets it. -/
theorem ErrorsMeet.error {α : Type} {P : BlockError → Prop} {e : BlockError} (h : P e) :
    ErrorsMeet P (.error e : Except BlockError α) :=
  fun _ he => by cases he; exact h

/-- A throw of an error that meets the property meets it. -/
theorem ErrorsMeet.throw {α : Type} {P : BlockError → Prop} {e : BlockError} (h : P e) :
    ErrorsMeet P (MonadExcept.throw e : Except BlockError α) :=
  fun _ he => by cases he; exact h

/-- A sequence meets the property when its first part does, and its rest after it. -/
theorem ErrorsMeet.bind {α β : Type} {P : BlockError → Prop} {x : Except BlockError α}
    {f : α → Except BlockError β} (hx : ErrorsMeet P x)
    (hf : ∀ a, x = .ok a → ErrorsMeet P (f a)) : ErrorsMeet P (x >>= f) := by
  intro e h
  rcases Base.bind_eq_error h with h | ⟨a, ha, h⟩
  · exact hx e h
  · exact hf a ha e h

/-- A map of a result that meets the property meets it. -/
theorem ErrorsMeet.map {α β : Type} {P : BlockError → Prop} {x : Except BlockError α}
    (f : α → β) (hx : ErrorsMeet P x) : ErrorsMeet P (f <$> x) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx e hx'
  | ok a => rw [hx'] at h; cases h

/-- A change of error meets the property when each changed failure does. -/
theorem ErrorsMeet.mapError {ε α : Type} {P : BlockError → Prop} {x : Except ε α}
    {f : ε → BlockError} (hf : ∀ e, x = .error e → P (f e)) : ErrorsMeet P (x.mapError f) := by
  intro e h
  cases hx : x with
  | error e' => rw [hx] at h; cases h; exact hf e' hx
  | ok a => rw [hx] at h; cases h

/-- An abort meets the property when each of its errors does, as an abort. -/
theorem ErrorsMeet.aborted {α : Type} {P : BlockError → Prop} {x : Except EvmError α}
    (h : ∀ e, x = .error e → P (.aborted e)) : ErrorsMeet P (x.mapError .aborted) :=
  ErrorsMeet.mapError h

/-- A step on a block state meets the property when each of its errors does, as a state error. -/
theorem ErrorsMeet.onBlock {P : BlockError → Prop} {block : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (h : ∀ e, step (.ofBlock block) = .error e → P (.state e)) :
    ErrorsMeet P (onBlock block step) :=
  ErrorsMeet.bind (ErrorsMeet.mapError h) fun _ _ => ErrorsMeet.pure _

/-- The first failure of a list of checks is one of their errors. -/
theorem errorsMeet_firstFailure {P : BlockError → Prop} :
    ∀ (l : List (Bool × BlockError)), (∀ x ∈ l, P x.2) → ErrorsMeet P (firstFailure l)
  | [], _ => ErrorsMeet.ok _
  | (b, e) :: rest, h => by
    unfold firstFailure
    split
    · exact errorsMeet_firstFailure rest fun x hx => h x (List.mem_cons_of_mem _ hx)
    · exact ErrorsMeet.error (h (b, e) List.mem_cons_self)

/-! ## The checks of a block -/

/-- Whether an error of a block is no abort, no state error and no failed system call.

Nor is it a transaction kept out of the block. -/
private def Plain (e : BlockError) : Prop :=
  (∀ error, e ≠ .aborted error) ∧ (∀ error, e ≠ .state error) ∧
    (∀ address error, e ≠ .systemCallFailed address error) ∧
    ∀ index error, e ≠ .invalidTransaction index error

/-- The checks of a header against its parent fail with no abort, state error or failed call.

Nor do they keep a transaction out. -/
private theorem plain_headerChecks {parentFork : Fork} (hFork : parentFork ≤ fork)
    (parent : Header parentFork) (header : Header fork)
    (schedule : Since .dencun fork BlobSchedule) :
    ∀ x ∈ headerChecks hFork parent header schedule, Plain x.2 := by
  unfold headerChecks
  dsimp only
  simp only [List.forall_mem_append, List.forall_mem_cons]
  and_intros
  all_goals repeat' split
  all_goals simp [Plain]

/-- A check of a header against its parent fails with no abort, state error or failed call.

Nor does it keep a transaction out. -/
private theorem plain_validateHeader {parentFork : Fork} (hFork : parentFork ≤ fork)
    (parent : Header parentFork) (header : Header fork)
    (schedule : Since .dencun fork BlobSchedule) :
    ErrorsMeet Plain (validateHeader hFork parent header schedule) := by
  unfold validateHeader
  refine ErrorsMeet.bind
    (errorsMeet_firstFailure _ (plain_headerChecks hFork parent header schedule)) fun _ _ => ?_
  split
  · exact ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩
  · exact ErrorsMeet.pure _

/-- The checks of a block before its body fail with no abort, state error or failed call.

Nor do they keep a transaction out. -/
private theorem plain_checkBlock {config : ChainConfig} {checkSeal : Bool}
    {recent : List RecentBlock} {block : Block fork Transaction} :
    ErrorsMeet Plain (checkBlock config checkSeal recent block) := by
  unfold checkBlock
  refine ErrorsMeet.bind ?_ fun items _ => ?_
  · unfold bodyItems
    exact ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩)
      fun _ _ => ErrorsMeet.pure _
  refine ErrorsMeet.bind ?_ fun _ _ => ?_
  · unfold validateBlockSize
    split
    · refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩)
        fun _ _ => errorsMeet_firstFailure _ ?_
      simp [Plain]
    · exact ErrorsMeet.ok _
  have ommers : ErrorsMeet Plain (if fork < .paris then
      (validateOmmers config checkSeal recent block.header block.ommers).mapError .ommers
    else if block.ommers.isEmpty = true then pure () else throw .ommersAfterParis) := by
    split
    · exact ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩
    · split
      · exact ErrorsMeet.pure _
      · exact ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩
  split
  · dsimp only
    split
    · split
      · refine ErrorsMeet.bind (plain_validateHeader _ _ _ _) fun _ _ => ?_
        split
        · exact ommers
        · exact ErrorsMeet.bind (ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩)
            fun _ _ => ommers
      · refine ErrorsMeet.bind (errorsMeet_firstFailure _ (plain_headerChecks _ _ _ _))
          fun _ _ => ?_
        split
        · exact ommers
        · exact ErrorsMeet.bind (ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩)
            fun _ _ => ommers
    · refine ErrorsMeet.bind (ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩) fun _ _ => ?_
      split
      · exact ommers
      · exact ErrorsMeet.bind (ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩)
          fun _ _ => ommers
  · exact ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩

/-- The checks of a block before its body never fail with an abort or an error of the state. -/
theorem checkBlock_eq_error {config : ChainConfig} {checkSeal : Bool} {recent : List RecentBlock}
    {block : Block fork Transaction} {e : BlockError}
    (h : checkBlock config checkSeal recent block = .error e) :
    (∀ error, e ≠ .aborted error) ∧ ∀ error, e ≠ .state error :=
  ⟨(plain_checkBlock e h).1, (plain_checkBlock e h).2.1⟩

/-! ## The transition -/

/-- The transition of a block fails only with errors of a property when its body does.

The property must hold for every error that is no abort, no state error and no failed system call.

It need not hold for a failed system call or a transaction kept out of the block.

The checks never give one, so only the body must meet it there.

It must hold for the abort from Hegotá on, for a fork whose rules are not yet specified. -/
theorem errorsMeet_stateTransition_of_plain {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {P : BlockError → Prop}
    (plain : ∀ e, (∀ x, e ≠ .aborted x) → (∀ x, e ≠ .state x) →
      (∀ a x, e ≠ .systemCallFailed a x) → (∀ i x, e ≠ .invalidTransaction i x) → P e)
    (hegota : .hegota ≤ fork → P (.aborted (.forkNotYetSpecified fork)))
    (body : ∀ env, ErrorsMeet P (applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩)) :
    ErrorsMeet P (stateTransition chain block checkSeal) := by
  have other : ∀ {β : Type} {x : Except BlockError β}, ErrorsMeet Plain x → ErrorsMeet P x :=
    fun hx e h => plain e (hx e h).1 (hx e h).2.1 (hx e h).2.2.1 (hx e h).2.2.2
  have trie : ∀ {β : Type} (x : Except Trie.TrieError β), ErrorsMeet P (x.mapError .trie) :=
    fun _ => other (ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩)
  have rest : ErrorsMeet P (do
      checkBlock chain.config checkSeal chain.recent block
      let result ← runBody chain block
      firstFailure (outputChecks block.header result.output result.roots)
      pure result.post : Except BlockError State) := by
    refine ErrorsMeet.bind (other plain_checkBlock) fun _ _ => ?_
    refine ErrorsMeet.bind ?_ fun result _ => ?_
    · unfold runBody
      refine ErrorsMeet.bind ?_ fun hashes _ => ?_
      · unfold recentHashes
        dsimp only
        split
        · exact ErrorsMeet.pure _
        · exact ErrorsMeet.bind
            (other (ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩))
            fun _ _ => ErrorsMeet.pure _
      refine ErrorsMeet.bind (body _) fun output _ => ?_
      refine ErrorsMeet.bind ?_ fun _ _ => ErrorsMeet.pure _
      unfold outputRoots
      refine ErrorsMeet.bind (trie _) fun _ _ => ?_
      refine ErrorsMeet.bind (trie _) fun _ _ => ?_
      refine ErrorsMeet.bind (trie _) fun _ _ => ?_
      refine ErrorsMeet.bind ?_ fun _ _ => ErrorsMeet.pure _
      unfold withdrawalsRootOf
      split
      · exact ErrorsMeet.map _ (trie _)
      · exact ErrorsMeet.ok _
    refine ErrorsMeet.bind (other (errorsMeet_firstFailure _ ?_)) fun _ _ => ErrorsMeet.pure _
    unfold outputChecks
    dsimp only
    simp only [List.forall_mem_append, List.forall_mem_cons]
    and_intros
    all_goals repeat' split
    all_goals simp [Plain]
  unfold stateTransition
  dsimp only
  split
  · rename_i hle
    refine ErrorsMeet.bind (ErrorsMeet.throw (hegota hle)) fun _ _ => ?_
    split
    · exact rest
    · exact ErrorsMeet.bind (ErrorsMeet.throw (plain _ nofun nofun nofun nofun))
        fun _ _ => rest
  · split
    · exact rest
    · exact ErrorsMeet.bind (ErrorsMeet.throw (plain _ nofun nofun nofun nofun))
        fun _ _ => rest

/-- The transition of a block fails only with errors of a property when its body does.

The property must hold for every error that is neither an abort nor an error of the state.

It must hold for the abort from Hegotá on, for a fork whose rules are not yet specified. -/
theorem errorsMeet_stateTransition {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {P : BlockError → Prop}
    (plain : ∀ e, (∀ x, e ≠ .aborted x) → (∀ x, e ≠ .state x) → P e)
    (hegota : .hegota ≤ fork → P (.aborted (.forkNotYetSpecified fork)))
    (body : ∀ env, ErrorsMeet P (applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩)) :
    ErrorsMeet P (stateTransition chain block checkSeal) :=
  errorsMeet_stateTransition_of_plain (fun e ha hs _ _ => plain e ha hs) hegota body

end EthLib.Execution.Blocks
