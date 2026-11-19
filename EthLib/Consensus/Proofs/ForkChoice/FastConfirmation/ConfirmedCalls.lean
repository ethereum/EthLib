module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ReceiverExits
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.RootViability
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.TargetCount
public import EthLib.Consensus.Proofs.ForkChoice.JustifiedVotes
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Committees
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedWalk
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalCoverage
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalTransport
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HonestHeads
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDrift
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.ForkChoice.RealizedJustification
import EthLib.Consensus.Proofs.HonestAggregation

/-!
# The confirmed roots of the calls of one validator

After consecutive calls of the rule by one honest validator, its last confirmed root covers heads.

It is on every up-to-date honest head from the slot after the last call to a horizon.

Otherwise two honest stores collide, or accountable-safety evidence holds.

`CallAt` names one call in a run of calls by one validator.

Each call keeps a private call invariant, given the invariant at every earlier call.

It assumes the inputs `CallObligations` of the call.

`Execution.confirmedRoot_covers` reads that step at every call of a run.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models Serialization.Ssz SszType

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-! ## The walks of the calls and the current slot -/

section Walks

open EthLib.Consensus.Store Models.ForkChoice

variable {store : Store preset fork}

/-- A node that descends from a known block descends from the parent of that block.

The store must hold the parent, at an earlier slot than the block.

Both nodes are pending, so this holds at every fork. -/
private theorem Store.isAncestor_parentRoot_of_isAncestor {node root : Root}
    {block parent : BeaconBlock preset fork}
    (descends : store.isAncestor ⟨node, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) :
    store.isAncestor ⟨node, .pending⟩ ⟨block.parentRoot, .pending⟩ = .ok true := by
  have known : store.block root = .ok block := block_ok_iff.mpr found
  simp only [isAncestor, known, bind, Except.bind] at descends
  cases walk : store.getAncestor ⟨node, .pending⟩ block.slot with
  | error e => simp [walk] at descends
  | ok reached =>
    rw [walk] at descends
    -- The walk to the block's slot reaches the block, with some payload status.
    have sameRoot : reached.root = root := by
      by_cases gloas : .glamsterdam ≤ fork <;> simp_all [pure, Except.pure]
    have reachedFound : store.blocks[reached.root]? = some block := sameRoot ▸ found
    -- Going on to the parent's slot steps from the block to its parent.
    have onward : store.getAncestor ⟨node, .pending⟩ parent.slot =
        .ok ⟨block.parentRoot, parentPayloadStatus block parent⟩ := by
      rw [getAncestor_trans (UInt64.le_of_lt lower) walk]
      exact getAncestor_parent_of_slot_lt reachedFound parentFound lower
    by_cases gloas : .glamsterdam ≤ fork
    · simp [isAncestor_pending gloas, block_ok_iff.mpr parentFound, onward, bind, Except.bind,
        pure, Except.pure]
    · have pending := parentPayloadStatus_of_lt (block := block) (parent := parent)
        (Nat.lt_of_not_le gloas)
      simp [isAncestor, block_ok_iff.mpr parentFound, onward, pending, gloas, bind, Except.bind,
        pure, Except.pure]

/-- The walk from a root, as it goes on: each listed root has the root before it as parent.

The first new root has the terminal block as parent, and the head descends from every root.

The roots `acc` that the walk already holds must hang off `root` in the same way. -/
private theorem Store.parentRoot_of_getAncestorRoots_aux {head root terminal : Root}
    {acc roots : List Root}
    (walked : store.getAncestorRoots root terminal acc = .ok roots)
    (accParents : ∀ (older newer : List Root) (member : Root) (block : BeaconBlock preset fork),
      acc = older ++ member :: newer → store.block member = .ok block →
      block.parentRoot = older.getLast?.getD root)
    (accBelow : ∀ m ∈ acc, store.isAncestor ⟨head, .pending⟩ ⟨m, .pending⟩ = .ok true)
    (rootBelow : ∀ block : BeaconBlock preset fork, store.blocks[root]? = some block →
      store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true) :
    (∀ (older newer : List Root) (member : Root) (block : BeaconBlock preset fork),
      roots = older ++ member :: newer → store.block member = .ok block →
      block.parentRoot = older.getLast?.getD terminal) ∧
    ∀ m ∈ roots, store.isAncestor ⟨head, .pending⟩ ⟨m, .pending⟩ = .ok true := by
  fun_induction getAncestorRoots store root terminal acc generalizing roots with
  | case1 => cases walked
  | case2 root acc block found ih =>
    -- Putting the root in front of `acc` keeps the parents, with the root's parent as base.
    have consParents : ∀ (older newer : List Root) (member : Root)
        (memberBlock : BeaconBlock preset fork), root :: acc = older ++ member :: newer →
        store.block member = .ok memberBlock →
        memberBlock.parentRoot = older.getLast?.getD block.parentRoot := by
      intro older newer member memberBlock split memberOk
      cases older with
      | nil =>
        obtain ⟨rfl, -⟩ := List.cons.inj split
        obtain rfl : block = memberBlock :=
          Except.ok.inj ((block_ok_iff.mpr found).symm.trans memberOk)
        rfl
      | cons first older =>
        obtain ⟨rfl, rest⟩ := List.cons.inj split
        rw [accParents older newer member memberBlock rest memberOk]
        rw [List.getLast?_cons, Option.getD_some]
    have consBelow : ∀ m ∈ root :: acc,
        store.isAncestor ⟨head, .pending⟩ ⟨m, .pending⟩ = .ok true := by
      intro m mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact rootBelow block found
      · exact accBelow m mem
    rw [bind_ok_iff] at walked
    obtain ⟨terminalBlock, -, walked⟩ := walked
    split at walked
    · -- The walk is empty.
      cases Except.ok.inj walked
      simp
    · dsimp only at walked
      split at walked
      · -- The parent is the terminal block, so the walk ends with this root.
        rename_i atTerminal
        cases Except.ok.inj walked
        exact ⟨atTerminal ▸ consParents, consBelow⟩
      · split at walked
        · cases walked
        · rename_i parent parentFound
          split at walked
          · rename_i lower
            exact ih parent parentFound lower walked consParents consBelow fun _ _ =>
              isAncestor_parentRoot_of_isAncestor (rootBelow block found) found parentFound
                lower
          · cases walked

/-- The walk from a root, as it goes on: each listed root descends from the terminal block.

The roots `acc` that the walk already holds must descend from `root`. -/
private theorem Store.isAncestor_terminal_of_getAncestorRoots_aux {root terminal : Root}
    {acc roots : List Root}
    (walked : store.getAncestorRoots root terminal acc = .ok roots)
    (accAbove : ∀ m ∈ acc, store.isAncestor ⟨m, .pending⟩ ⟨root, .pending⟩ = .ok true) :
    ∀ m ∈ roots, store.isAncestor ⟨m, .pending⟩ ⟨terminal, .pending⟩ = .ok true := by
  fun_induction getAncestorRoots store root terminal acc generalizing roots with
  | case1 => cases walked
  | case2 root acc block found ih =>
    rw [bind_ok_iff] at walked
    obtain ⟨terminalBlock, terminalOk, walked⟩ := walked
    split at walked
    · -- The walk is empty.
      cases Except.ok.inj walked
      simp
    · rename_i higher
      -- Each root held so far, and the root itself, descends from the root's known parent.
      have consAbove : ∀ (parent : BeaconBlock preset fork),
          store.blocks[block.parentRoot]? = some parent → parent.slot < block.slot →
          ∀ m ∈ root :: acc,
            store.isAncestor ⟨m, .pending⟩ ⟨block.parentRoot, .pending⟩ = .ok true := by
        intro parent parentFound lower m mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact isAncestor_pending_parent_of_slot_lt (node := ⟨m, .pending⟩) found parentFound
            lower
        · exact isAncestor_parentRoot_of_isAncestor (accAbove m mem) found parentFound lower
      dsimp only at walked
      split at walked
      · -- The parent is the terminal block, which sits below the root.
        rename_i atTerminal
        cases Except.ok.inj walked
        have terminalFound := block_ok_iff.mp terminalOk
        rw [← atTerminal] at terminalFound ⊢
        exact consAbove terminalBlock terminalFound (UInt64.not_le.mp higher)
      · split at walked
        · cases walked
        · rename_i parent parentFound
          split at walked
          · rename_i lower
            exact ih parent parentFound lower walked (consAbove parent parentFound lower)
          · cases walked

/-- Each root of a successful walk descends from the terminal block. -/
private theorem Store.isAncestor_terminal_of_getAncestorRoots {head terminal member : Root}
    {roots : List Root} (walked : store.getAncestorRoots head terminal = .ok roots)
    (mem : member ∈ roots) :
    store.isAncestor ⟨member, .pending⟩ ⟨terminal, .pending⟩ = .ok true :=
  isAncestor_terminal_of_getAncestorRoots_aux walked (by simp) member mem

/-- Each root of a successful walk has the root before it as parent, or the terminal block.

The walk lists the roots oldest first, so the root before a member is the last of `older`.

The head of the walk descends from each of its roots.

Each root descends from the terminal block. -/
private theorem Store.parentRoot_of_getAncestorRoots {head terminal member : Root}
    {older newer : List Root} {block : BeaconBlock preset fork}
    (walked : store.getAncestorRoots head terminal = .ok (older ++ member :: newer))
    (found : store.block member = .ok block) :
    block.parentRoot = older.getLast?.getD terminal ∧
      store.isAncestor ⟨head, .pending⟩ ⟨member, .pending⟩ = .ok true ∧
      store.isAncestor ⟨member, .pending⟩ ⟨terminal, .pending⟩ = .ok true := by
  obtain ⟨parents, below⟩ := parentRoot_of_getAncestorRoots_aux (head := head) walked
    (by simp) (by simp) fun _ headFound => isAncestor_self headFound
  exact ⟨parents older newer member block rfl found, below member (by simp),
    isAncestor_terminal_of_getAncestorRoots walked (by simp)⟩

/-- In a forward store, no counted vote supports a held block at the current slot.

Each counted vote is a latest vote, whose attestation is for a block at its slot or before.

That slot is before the current slot.

A vote counts only through a descendant of the block, which is at the block's slot or later. -/
private theorem Store.voteCountsFor_eq_false_of_slot_eq_current
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    {current : Slot} {root : Root} {block : BeaconBlock preset fork}
    (slotOk : store.getCurrentSlot config = .ok current)
    (found : store.blocks[root]? = some block) (atCurrent : block.slot = current)
    (index : ValidatorIndex) :
    store.voteCountsFor ⟨root, .pending⟩ index = false := by
  cases counts : store.voteCountsFor ⟨root, .pending⟩ index with
  | false => rfl
  | true =>
    obtain ⟨message, supported, latest, -, supportedOk, descends⟩ :=
      store.exists_of_voteCountsFor counts
    obtain ⟨attestation, rfl, origin⟩ := forward.votesHaveOrigins latest
    -- The vote's block is a descendant of the block, so at the current slot or later.
    obtain ⟨supportedBlock, supportedFound, above⟩ := slot_le_of_isAncestor found descends
    rw [getSupportedNode_root supportedOk] at supportedFound
    -- The vote's block is at the vote's slot or before, which is before the current slot.
    obtain ⟨votedBlock, votedFound, votedLe⟩ := origin.voted
    obtain ⟨current', currentOk, past⟩ := origin.past
    rw [slotOk, Except.ok.injEq] at currentOk
    subst current'
    have same : supportedBlock = votedBlock :=
      Option.some.inj (supportedFound.symm.trans votedFound)
    subst same
    exact absurd (UInt64.lt_of_le_of_lt above (UInt64.lt_of_le_of_lt votedLe past))
      (atCurrent ▸ UInt64.lt_irrefl _)

/-- In a forward store, a held block at the current slot is not one-confirmed.

This holds under the tally of any balance source. -/
private theorem Store.not_isOneConfirmed_of_slot_eq_current
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    {current : Slot} {root head : Root} {block : BeaconBlock preset fork}
    {source : BeaconState preset fork}
    (slotOk : store.getCurrentSlot config = .ok current)
    (found : store.blocks[root]? = some block) (atCurrent : block.slot = current) :
    store.isOneConfirmed config head source (store.tallyVotes source) root ≠ .ok true := by
  intro confirmed
  obtain ⟨support, threshold, supportOk, thresholdOk, -⟩ :=
    isOneConfirmed_eq_ok_true_iff.mp confirmed
  have above := threshold_lt_of_isOneConfirmed supportOk thresholdOk confirmed
  -- The support is the sum of the balances whose vote counts, and none counts.
  have zero : support.toNat = 0 := by
    rw [store.getAttestationScore_toNat_eq_sum supportOk]
    simp [voteCountsFor_eq_false_of_slot_eq_current forward slotOk found atCurrent]
  omega

/-- The unrealized justification read of a block is its stored entry. -/
private theorem Store.unrealizedJustification_found {root : Root}
    {checkpoint : Checkpoint} (read : store.unrealizedJustification root = .ok checkpoint) :
    store.unrealizedJustifications[root]? = some checkpoint := by
  unfold Store.unrealizedJustification at read
  split at read
  · rename_i stored found
    simp only [pure, Except.pure, Except.ok.injEq] at read
    rw [found, read]
  · simp [throw, throwThe, MonadExceptOf.throw] at read

end Walks

/-! ## The finalized order of honest stores -/

/-- The anchor state does not hash to the zero root, as no honest store holds a zero state root. -/
private theorem anchorState_hash_nonzero {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {last : ℕ}
    (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    {u : ValidatorIndex} (honest : u ∈ J) {n : ℕ} (inTime : (e.world n).time ≤ last) :
    hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0) := by
  intro zero
  have reached := e.reachable (fun x hx => (start x hx).symm ▸ Store.Reachable.anchor anchored)
    n u honest
  rw [reached.anchorState_root, Except.ok.injEq] at zero
  exact e.anchor_stateRoot_nonzero anchored start nonzero honest inTime zero

/-- A block of an honest store reaches each up-to-date honest receiver a delay later.

The sender's read at the block must give the finalized checkpoint of the receiver.

The receiver then holds the block with the sender's state for it.

Honest stores must agree on their blocks, and hold no state of a block with a zero state root. -/
private theorem carrier_delivered {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ last)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor) (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {m k : ℕ}
    (mBound : (e.world m).time ≤ last) (late : (e.world m).time + Δ ≤ (e.world k).time)
    (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (known : ((e.world m).state u).blocks[root]? = some block)
    (stored : ((e.world m).state u).blockStates[root]? = some state)
    (final : ((e.world m).state u).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root) :
    ((e.world k).state w).blocks[root]? = some block ∧
      ((e.world k).state w).blockStates[root]? = some state := by
  have reachedW := e.reachable (fun x hx => (start x hx).symm ▸ Store.Reachable.anchor anchored)
    k w receiver
  -- The receiver holds its finalized block, as the anchor state's root is not zero.
  have finalizedKnown := reachedW.finalized_known sound (UInt64.le_of_eq anchorSlot) positive
    window (e.anchor_stateRoot_nonzero anchored start nonzero receiver bounded)
  rcases e.blocks_of_partiallySynchronous sync preGloas admitted anchored start sender receiver
      (by simpa using late) bounded upToDate finalizedKnown known final with
    ⟨held, -⟩ | ⟨a, ha, b, hb, i, j, hi, hj, _, ⟨r, left, right⟩, found⟩
  · -- The receiver's state for the block is the sender's.
    obtain ⟨post, postFound, -, -⟩ := reachedW.blockStatesFromParents held
    have same := e.blockStates_eq anchored sender receiver (start u sender) (start w receiver)
      (agree u sender w receiver m k mBound bounded) stored postFound
    subst post
    exact ⟨held, postFound⟩
  · obtain ⟨leftFound, rightFound, different⟩ := Store.findBlockCollision_held found
    exact absurd (agree a ha b hb i j hi hj r left right leftFound rightFound) different

/-- A delay after an event of an honest store, each up-to-date honest store has justified its epoch.

That epoch is the one of the finalized checkpoint of the sender at the event.

The finalized checkpoint of each receiver must be read at the justified root of each sender.

The sender's justified checkpoint comes from the anchor, from a held state, or from its pull-up.

The block of that state reaches the receiver, whose justified epoch is then at least as late. -/
private theorem finalizedOrder {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ last)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor) (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (crossFinal : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (late : (e.world n).time + Δ ≤ (e.world k).time) (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) :
    ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachable (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored)
      i v honest
  have reachedU := (forward u sender n).reachable
  have reachedW := (forward w receiver k).reachable
  have nBound : (e.world n).time ≤ last := by omega
  have aligned : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq anchorSlot
  -- The receiver may have finalized the epoch already.
  by_cases covered : ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).finalizedCheckpoint.epoch
  · exact UInt64.le_trans covered (reachedW.finalized_le_justified sound)
  have below := UInt64.not_le.mp covered
  have finalLe := reachedU.finalized_le_justified sound
  have later : getCurrentEpoch anchorState < ((e.world n).state u).justifiedCheckpoint.epoch :=
    UInt64.lt_of_le_of_lt reachedW.anchor_le_finalized (UInt64.lt_of_lt_of_le below finalLe)
  have notZero := anchorState_hash_nonzero anchored start nonzero sender nBound
  -- The sender reads the receiver's finalized checkpoint at its justified root.
  have crossRead := crossFinal w receiver u sender k n bounded nBound
    (UInt64.le_of_lt (UInt64.lt_of_lt_of_le below finalLe))
  -- A held block that reads the sender's justified checkpoint reaches the receiver.
  have carry {root : Root} {state : BeaconState preset fork} {block : BeaconBlock preset fork}
      (known : ((e.world n).state u).blocks[root]? = some block)
      (stored : ((e.world n).state u).blockStates[root]? = some state)
      (read : ((e.world n).state u).getCheckpointBlock root
        ((e.world n).state u).justifiedCheckpoint.epoch =
          .ok ((e.world n).state u).justifiedCheckpoint.root) :
      ((e.world k).state w).blocks[root]? = some block ∧
        ((e.world k).state w).blockStates[root]? = some state := by
    refine carrier_delivered sync positive window preGloas admitted anchored sound anchorSlot start
      nonzero agree sender receiver nBound late bounded upToDate known stored ?_
    rw [Store.getCheckpointBlock_trans preGloas read
      (UInt64.le_of_lt (UInt64.lt_of_lt_of_le below finalLe))]
    exact crossRead
  obtain ⟨currentU, currentUOk⟩ := (forward u sender n).exists_getCurrentSlot slots
  rcases (forward u sender n).justified_origins_epoch positive slots currentUOk with
    ⟨root, _, same⟩ | ⟨root, state, stored, same⟩ |
      ⟨root, block, state, pulled, known, stored, run, same, earlier⟩
  · rw [same] at later
    exact (UInt64.lt_irrefl _ later).elim
  · obtain ⟨block, known⟩ := reachedU.known_of_blockState stored
    have read := (reachedU.getCheckpointBlock_of_blockState sound aligned positive window stored
      (.inl (by simp [same])) later).resolve_right notZero
    obtain ⟨_, held⟩ := carry known stored read.1
    rw [same] at finalLe
    exact UInt64.le_trans finalLe (reachedW.justified_le_of_blockState sound held)
  · have read := (reachedU.getCheckpointBlock_of_blockState sound aligned positive window stored
      (.inr ⟨pulled, run, by simp [same]⟩) later).resolve_right notZero
    obtain ⟨blockHeld, stateHeld⟩ := carry known stored read.1
    -- The receiver's clock is at or after the sender's.
    obtain ⟨currentW, currentWOk⟩ := (forward w receiver k).exists_getCurrentSlot slots
    have slotLe := e.currentSlot_le_of_time_le start sender receiver (by omega) upToDate
      currentUOk currentWOk
    have epochLe : computeEpochAtSlot preset currentU ≤ computeEpochAtSlot preset currentW :=
      UInt64.le_iff_toNat_le.mpr (epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp slotLe))
    rw [same] at finalLe
    exact UInt64.le_trans finalLe ((forward w receiver k).justified_le_of_pulledUp sound positive
      slots currentWOk blockHeld stateHeld run (UInt64.lt_of_lt_of_le earlier epochLe))

/-! ## The observed start of a call -/

/-- A delay after an earlier call, each up-to-date honest store has justified the observed epoch.

That epoch is the one of the caller's unrealized justified checkpoint at the earlier call.

A later call must hold that checkpoint as the caller's justified checkpoint.

Each receiver must be in a later epoch than the earlier call.

The finalized checkpoint of each receiver must be read at the justified root of each sender.

That read at the later call moves to the block that gives the observed checkpoint.

It then moves back to the earlier call, which holds the block, and which delivers it. -/
private theorem observedOrder {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ last)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor)
    (aboveAnchor : ∀ epoch : Epoch, getCurrentEpoch anchorState ≤ epoch →
      ∀ s, computeStartSlotAtEpoch preset epoch = .ok s → anchorBlock.slot ≤ s)
    (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (crossFinal : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {m n k : ℕ}
    (order : m ≤ n) (nBound : (e.world n).time ≤ last)
    (late : (e.world m).time + Δ ≤ (e.world k).time) (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (realized : ((e.world n).state u).justifiedCheckpoint =
      ((e.world m).state u).unrealizedJustifiedCheckpoint)
    (laterEpoch : ∀ current currentW, ((e.world m).state u).getCurrentSlot config = .ok current →
      ((e.world k).state w).getCurrentSlot config = .ok currentW →
      computeEpochAtSlot preset current < computeEpochAtSlot preset currentW) :
    ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachable (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored)
      i v honest
  have reachedM := (forward u sender m).reachable
  have reachedN := (forward u sender n).reachable
  have reachedW := (forward w receiver k).reachable
  have mBound : (e.world m).time ≤ last := by omega
  have aligned : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq anchorSlot
  -- The receiver may have finalized the epoch already.
  by_cases covered : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world k).state w).finalizedCheckpoint.epoch
  · exact UInt64.le_trans covered (reachedW.finalized_le_justified sound)
  have below := UInt64.not_le.mp covered
  have anchorLe := reachedW.anchor_le_finalized
  have later : getCurrentEpoch anchorState <
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch :=
    UInt64.lt_of_le_of_lt anchorLe below
  have notZero := anchorState_hash_nonzero anchored start nonzero sender mBound
  -- At the later call, the caller reads the receiver's finalized checkpoint at the observed root.
  have crossRead := crossFinal w receiver u sender k n bounded nBound
    (by rw [realized]; exact UInt64.le_of_lt below)
  rw [realized] at crossRead
  -- The block that gives the observed checkpoint at the earlier call reaches the receiver.
  have carry {root : Root} {state : BeaconState preset fork} {block : BeaconBlock preset fork}
      (stored : ((e.world m).state u).blockStates[root]? = some state)
      (known : ((e.world m).state u).blocks[root]? = some block)
      (member : ((e.world m).state u).unrealizedJustifiedCheckpoint ∈
          [state.currentJustifiedCheckpoint, state.previousJustifiedCheckpoint,
            state.finalizedCheckpoint] ∨
        ∃ pulled, processJustificationAndFinalization state = .ok pulled ∧
          ((e.world m).state u).unrealizedJustifiedCheckpoint ∈
            [pulled.currentJustifiedCheckpoint, pulled.previousJustifiedCheckpoint,
              pulled.finalizedCheckpoint]) :
      ((e.world k).state w).blocks[root]? = some block ∧
        ((e.world k).state w).blockStates[root]? = some state := by
    -- The later call still holds the block, with the same state.
    obtain ⟨post, storedN, -, -⟩ := reachedN.blockStatesFromParents (e.blocks_of_le order known)
    have same := e.blockStates_eq anchored sender sender (start u sender) (start u sender)
      (agree u sender u sender m n mBound nBound) stored storedN
    subst post
    have readN := (reachedN.getCheckpointBlock_of_blockState sound aligned positive window
      storedN member later).resolve_right notZero
    have finalN : ((e.world n).state u).getCheckpointBlock root
        ((e.world k).state w).finalizedCheckpoint.epoch =
          .ok ((e.world k).state w).finalizedCheckpoint.root := by
      rw [Store.getCheckpointBlock_trans preGloas readN.1 (UInt64.le_of_lt below)]
      exact crossRead
    -- The read moves back to the earlier call, which delivers the block.
    have boundaryOf := finalN
    unfold Store.getCheckpointBlock at boundaryOf
    simp only [bind_ok_iff] at boundaryOf
    obtain ⟨boundary, boundaryOk, -⟩ := boundaryOf
    have boundaryOk := mapError_ok_iff.mp boundaryOk
    exact carrier_delivered sync positive window preGloas admitted anchored sound anchorSlot start
      nonzero agree sender receiver mBound late bounded upToDate known stored
      (Store.getCheckpointBlock_of_same_blocks reachedM
        (agree u sender u sender n m nBound mBound) boundaryOk
        (aboveAnchor _ anchorLe _ boundaryOk) ⟨block, known⟩ finalN)
  rcases reachedM.justified_origins _ (.inr rfl) with
    ⟨root, _, same⟩ | ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, run, same⟩
  · rw [same] at later
    exact (UInt64.lt_irrefl _ later).elim
  · obtain ⟨block, known⟩ := reachedM.known_of_blockState stored
    obtain ⟨_, held⟩ := carry stored known (.inl (by simp [same]))
    rw [same]
    exact reachedW.justified_le_of_blockState sound held
  · obtain ⟨block, known⟩ := reachedM.known_of_blockState stored
    obtain ⟨blockHeld, stateHeld⟩ := carry stored known (.inr ⟨pulled, run, by simp [same]⟩)
    obtain ⟨currentM, currentMOk, blocksM, -⟩ := (forward u sender m).slots_le_current slots
      aligned
    obtain ⟨currentW, currentWOk⟩ := (forward w receiver k).exists_getCurrentSlot slots
    have blockLe : computeEpochAtSlot preset block.slot ≤ computeEpochAtSlot preset currentM :=
      UInt64.le_iff_toNat_le.mpr
        (epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp (blocksM root block known)))
    rw [same]
    exact (forward w receiver k).justified_le_of_pulledUp sound positive slots currentWOk
      blockHeld stateHeld run
      (UInt64.lt_of_le_of_lt blockLe (laterEpoch currentM currentW currentMOk currentWOk))

/-! ## The balance source of a walked member -/

/-- One call of the rule in a run of calls by one validator. -/
def CallAt (u : ValidatorIndex) (events : List ℕ) (first : FastConfirmationStore)
    (i n : ℕ) (fcr after : FastConfirmationStore) : Prop :=
  events[i]? = some n ∧
    ((events.take i).map fun k => (e.world k).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) first = .ok fcr ∧
    ((e.world n).state u).onFastConfirmation config fcr = .ok after

/-- A passed chain-safety test reads the observed checkpoint on the confirmed root. -/
private theorem chainSafe_read {store : Store preset fork} {fcr : FastConfirmationStore}
    {head root : Root} (safe : store.isConfirmedChainSafe config fcr head root = .ok true) :
    store.getCheckpointBlock root fcr.currentEpochObservedJustifiedCheckpoint.epoch =
      .ok fcr.currentEpochObservedJustifiedCheckpoint.root := by
  unfold Store.isConfirmedChainSafe at safe
  rw [bind_ok_iff] at safe
  obtain ⟨checkpoint, checkpointOk, rest⟩ := safe
  split at rest
  · simp [pure, Except.pure] at rest
  · rename_i same
    simp only [ne_eq, Decidable.not_not] at same
    obtain ⟨block, blockOk, rfl⟩ := Store.getCheckpointForBlock_eq_ok_iff.mp checkpointOk
    rw [same]
    exact blockOk

/-- The start test of a slot is its remainder by the epoch length. -/
private theorem isStart_eq (slot : Slot) :
    isStartSlotAtEpoch preset slot =
      .ok (decide (slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0)) := by
  have rounded := (computeStartSlotAtEpoch_ok_iff.mp
    (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot)).2
  rw [computeEpochAtSlot, UInt64.toNat_div] at rounded
  have below := Nat.div_mul_le_self slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have le : slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH ≤ slot :=
    UInt64.le_iff_toNat_le.mpr (by omega)
  have sub := UInt64.toNat_sub_of_le _ _ le
  have modNat := Nat.mod_add_div slot.toNat preset.SLOTS_PER_EPOCH.toNat
  simp only [isStartSlotAtEpoch, computeSlotsSinceEpochStart,
    computeStartSlotAtEpoch_computeEpochAtSlot, Except.mapError, bind, Except.bind, pure,
    Except.pure, Except.ok.injEq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [Nat.mul_comm] at rounded
  constructor
  · intro zero
    have := congrArg UInt64.toNat zero
    rw [sub, UInt64.toNat_zero] at this
    omega
  · intro zero
    apply UInt64.toNat_inj.mp
    rw [sub, UInt64.toNat_zero]
    omega

/-- A block epoch read names a held block. -/
private theorem found_of_blockEpoch {store : Store preset fork} {root : Root} {epoch : Epoch}
    (read : store.getBlockEpoch root = .ok epoch) :
    ∃ block : BeaconBlock preset fork, store.blocks[root]? = some block ∧
      computeEpochAtSlot preset block.slot = epoch := by
  unfold Store.getBlockEpoch at read
  obtain ⟨block, found, eq⟩ := bind_ok_iff.mp read
  simp only [pure, Except.pure, Except.ok.injEq] at eq
  exact ⟨block, Store.block_ok_iff.mp found, eq⟩

/-- A held block has an epoch. -/
private theorem blockEpoch_of_found {store : Store preset fork} {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    ∃ epoch, store.getBlockEpoch root = .ok epoch :=
  ⟨computeEpochAtSlot preset block.slot, by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr found, bind, Except.bind, pure,
      Except.pure]⟩

/-- When a root of the current epoch is one-confirmed, the current slot does not start the epoch.

At that slot the root would be a block at the current slot, which is never one-confirmed. -/
private theorem not_start_of_confirmed {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    {slot : Slot} (slotOk : store.getCurrentSlot config = .ok slot)
    {root head : Root} {source : BeaconState preset fork}
    (rootEpochOk : store.getBlockEpoch root = .ok (computeEpochAtSlot preset slot))
    (confirmed : store.isOneConfirmed config head source (store.tallyVotes source) root =
      .ok true) :
    isStartSlotAtEpoch preset slot = .ok false := by
  obtain ⟨block, held, epochEq⟩ := found_of_blockEpoch rootEpochOk
  obtain ⟨current, currentOk, blocksLe, -⟩ := forward.slots_le_current slots anchorSlot
  obtain rfl : current = slot := Except.ok.inj (currentOk.symm.trans slotOk)
  rw [isStart_eq, Except.ok.injEq, decide_eq_false_iff_not]
  intro zero
  apply Store.not_isOneConfirmed_of_slot_eq_current forward currentOk held ?_ confirmed
  apply UInt64.toNat_inj.mp
  have le := UInt64.le_iff_toNat_le.mp (blocksLe root block held)
  have epochNat := congrArg UInt64.toNat epochEq
  simp only [computeEpochAtSlot, UInt64.toNat_div] at epochNat
  have slotDiv := Nat.mod_add_div current.toNat preset.SLOTS_PER_EPOCH.toNat
  have blockDiv := Nat.mod_add_div block.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  rw [← epochNat] at slotDiv
  omega

/-- The recency facts of a root for a call of epoch `E` with observed checkpoint `c`.

They apply when the root's epoch is at least `E - 1`.

The root's epoch is then at most one past the store's unrealized justified epoch.

The checkpoint is at most two epochs before `E`, and the root reads it on its chain. -/
private def Recent (store : Store preset fork) (E : ℕ) (c : Checkpoint) (r : Root) : Prop :=
  ∀ be : Epoch, store.getBlockEpoch r = .ok be → E ≤ be.toNat + 1 →
    be.toNat ≤ store.unrealizedJustifiedCheckpoint.epoch.toNat + 1 ∧
    E ≤ c.epoch.toNat + 2 ∧ store.getCheckpointBlock r c.epoch = .ok c.root

/-- A checked walk's start is in epoch `E - 1` or later, so its recency facts apply. -/
private theorem checked_start {store : Store preset fork} {E : ℕ} {c : Checkpoint} {slot : Slot}
    (slotOk : store.getCurrentSlot config = .ok slot)
    (hE : (computeEpochAtSlot preset slot).toNat = E)
    {fcr : FastConfirmationStore} {head start root : Root}
    (startRec : Recent store E c start)
    (checked : store.FastConfirmationChecked config fcr head start root) :
    ∃ startBlock : BeaconBlock preset fork, store.blocks[start]? = some startBlock ∧
      E ≤ (computeEpochAtSlot preset startBlock.slot).toNat + 1 ∧
      E ≤ c.epoch.toNat + 2 ∧ store.getCheckpointBlock start c.epoch = .ok c.root := by
  obtain ⟨epoch, slot', rootEpoch, startEpoch, epochOk, slotOk', -, startOk, recent, -⟩ :=
    checked
  obtain rfl : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
  obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
  obtain ⟨startBlock, startFound, rfl⟩ := found_of_blockEpoch startOk
  obtain ⟨-, R, T⟩ := startRec _ startOk (by omega)
  exact ⟨startBlock, startFound, by omega, R, T⟩

/-- Each walked member's parent is the start or a root of the walk, so it is above the start. -/
private theorem parent_above {store : Store preset fork} {head start root member : Root}
    {chain later : List Root} {startBlock block : BeaconBlock preset fork}
    (startFound : store.blocks[start]? = some startBlock)
    (walked : store.getAncestorRoots head start = .ok (chain ++ root :: later))
    (mem : member ∈ chain ++ [root]) (blockOk : store.block member = .ok block) :
    store.isAncestor ⟨block.parentRoot, .pending⟩ ⟨start, .pending⟩ = .ok true := by
  have mem' : member ∈ chain ++ root :: later := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
    tauto
  obtain ⟨older, newer, split⟩ := List.append_of_mem mem'
  rw [split] at walked
  rw [(Store.parentRoot_of_getAncestorRoots walked blockOk).1]
  cases last : older.getLast? with
  | none => exact Store.isAncestor_self (node := ⟨start, .pending⟩) startFound
  | some x =>
    exact Store.isAncestor_terminal_of_getAncestorRoots walked
      (List.mem_append_left _ (List.mem_of_getLast? last))

/-- The source of a call is on the chain of each walked member's parent.

It holds at one walk, from the recency facts of the walk's start. -/
private theorem parent_source {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {E : ℕ} {c : Checkpoint} {slot : Slot} (slotOk : store.getCurrentSlot config = .ok slot)
    (hE : (computeEpochAtSlot preset slot).toNat = E) (below : c.epoch.toNat + 1 ≤ E)
    {fcr : FastConfirmationStore} {head start root : Root} {chain later : List Root}
    (startRec : Recent store E c start)
    (checked : store.FastConfirmationChecked config fcr head start root)
    (walked : store.getAncestorRoots head start = .ok (chain ++ root :: later))
    {member : Root} (mem : member ∈ chain ++ [root]) {block parent : BeaconBlock preset fork}
    (blockOk : store.block member = .ok block)
    (parentOk : store.block block.parentRoot = .ok parent) :
    SourceOnParentChain store c block.parentRoot parent := by
  obtain ⟨startBlock, startFound, recent, R, T⟩ := checked_start slotOk hE startRec checked
  have descends := parent_above startFound walked mem blockOk
  have parentFound := Store.block_ok_iff.mp parentOk
  obtain ⟨found, foundAt, le⟩ := Store.slot_le_of_isAncestor startFound descends
  obtain rfl : found = parent := Option.some.inj (foundAt.symm.trans parentFound)
  have above := epoch_le_of_slot_le (preset := preset) _ _ (UInt64.le_iff_toNat_le.mp le)
  have current := forward.block_epoch_le_current slots anchorSlot slotOk parentFound
  refine ⟨by omega, by omega, ?_⟩
  exact Store.getCheckpointBlock_of_ancestor_epoch preGloas startFound descends (by omega) T

/-- A checked walk's confirmed root keeps the recency facts of its start.

A root of the current epoch is not at the epoch's first slot, so the call kept a realized check.

That check reads the root's unrealized justification, which the store's bounds.

An older root reads a voting source two epochs back at most, which the store's also bounds. -/
private theorem root_recent {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (slots : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {E : ℕ} {c : Checkpoint} {slot : Slot} (slotOk : store.getCurrentSlot config = .ok slot)
    (hE : (computeEpochAtSlot preset slot).toNat = E) (below : c.epoch.toNat + 1 ≤ E)
    {fcr : FastConfirmationStore} {head start root : Root} {chain later : List Root}
    {source : BeaconState preset fork}
    (startRec : Recent store E c start)
    (checked : store.FastConfirmationChecked config fcr head start root)
    (walked : store.getAncestorRoots head start = .ok (chain ++ root :: later))
    (confirmed : store.isOneConfirmed config head source (store.tallyVotes source) root =
      .ok true) :
    Recent store E c root := by
  obtain ⟨startBlock, startFound, recent, R, T⟩ := checked_start slotOk hE startRec checked
  intro be beOk _
  obtain ⟨epoch, slot', rootEpoch, startEpoch, epochOk, slotOk', rootOk, -, -, branches⟩ :=
    checked
  obtain rfl : slot = slot' := Except.ok.inj (slotOk.symm.trans slotOk')
  obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
  obtain rfl : be = rootEpoch := Except.ok.inj (beOk.symm.trans rootOk)
  have descends := Store.isAncestor_terminal_of_getAncestorRoots (member := root) walked (by simp)
  refine ⟨?_, R, Store.getCheckpointBlock_of_ancestor_epoch preGloas startFound descends
    (by omega) T⟩
  by_cases same : be = computeEpochAtSlot preset slot
  · have inside := not_start_of_confirmed forward slots anchorSlot slotOk (same ▸ rootOk)
      confirmed
    rcases branches with ⟨-, different, -⟩ | ⟨nonStart, -, -⟩
    · exact absurd same different
    · obtain ⟨j, jOk, jLe⟩ := nonStart inside
      have := UInt64.le_iff_toNat_le.mp (forward.unrealizedJustification_epoch_le sound positive
        slots (Store.unrealizedJustification_found jOk))
      rw [same]
      omega
  · obtain ⟨rootBlock, rootFound, rfl⟩ := found_of_blockEpoch rootOk
    have current := forward.block_epoch_le_current slots anchorSlot slotOk rootFound
    have voting : ∃ voteSource : Checkpoint, ∃ r,
        store.getVotingSource config r = .ok voteSource ∧
        (computeEpochAtSlot preset slot).toNat ≤ voteSource.epoch.toNat + 2 := by
      rcases branches with ⟨-, -, ⟨voteSource, voteOk, voteLe, -⟩, -⟩ | ⟨-, -, older⟩
      · exact ⟨voteSource, _, voteOk, voteLe⟩
      · obtain ⟨voteSource, voteOk, voteLe⟩ := (older same).1
        exact ⟨voteSource, _, voteOk, voteLe⟩
    obtain ⟨voteSource, r, voteOk, voteLe⟩ := voting
    have := UInt64.le_iff_toNat_le.mp (forward.votingSource_epoch_le sound positive slots voteOk)
    have := UInt64.toNat_inj.not.mpr same
    omega

/-- A successful call returns a held block. -/
private theorem root_known {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (nonzero : hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0))
    {fcr after : FastConfirmationStore}
    (called : store.onFastConfirmation config fcr = .ok after) :
    ∃ epoch, store.getBlockEpoch after.confirmedRoot = .ok epoch := by
  obtain ⟨head, slot, start, -, -, selected, result⟩ := Store.onFastConfirmation_checked called
  rcases result with same | ⟨-, checked, -⟩
  · rw [same]
    obtain ⟨base, baseCase, startCase⟩ := selected
    rcases startCase with ⟨rfl, _⟩ | ⟨rfl, _, ⟨block, _, found, _⟩, _⟩
    · rcases baseCase with ⟨rfl, ⟨_, blockEpoch, _, known, _⟩, _⟩ | ⟨rfl, _⟩
      · exact ⟨blockEpoch, known⟩
      · obtain ⟨block, found⟩ := reached.finalized_known sound (UInt64.le_of_eq anchorSlot)
          positive window fun zero => nonzero (by rw [reached.anchorState_root, zero])
        exact blockEpoch_of_found found
    · exact blockEpoch_of_found (Store.block_ok_iff.mp found)
  · obtain ⟨_, _, rootEpoch, _, _, _, known, _⟩ := checked
    exact ⟨rootEpoch, known⟩

/-- A held block's epoch is the same at a later event. -/
private theorem getBlockEpoch_of_le {u : ValidatorIndex} {n k : ℕ} (later : n ≤ k)
    {root : Root} {epoch : Epoch}
    (read : ((e.world n).state u).getBlockEpoch root = .ok epoch) :
    ((e.world k).state u).getBlockEpoch root = .ok epoch := by
  unfold Store.getBlockEpoch at read ⊢
  simp only [bind_ok_iff] at read
  obtain ⟨block, found, rest⟩ := read
  rw [Store.block_ok_iff.mpr (e.blocks_of_le later (Store.block_ok_iff.mp found))]
  exact rest

/-- A call after the first one has the call before it, whose result the call reads. -/
private theorem callAt_previous {u : ValidatorIndex} {events : List ℕ}
    {first : FastConfirmationStore} {j n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events first (j + 1) n fcr after) :
    ∃ m fcr', CallAt (e := e) u events first j m fcr' fcr := by
  obtain ⟨found, run, called⟩ := calls
  have lt : j < events.length := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
    omega
  refine ⟨events[j], ?_⟩
  rw [List.take_add_one, List.getElem?_eq_getElem lt, Option.toList_some, List.map_append,
    List.foldlM_append] at run
  obtain ⟨fcr', before, step⟩ := bind_ok_iff.mp run
  simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind_ok_iff] at step
  obtain ⟨last, lastOk, eq⟩ := step
  simp only [pure, Except.pure, Except.ok.injEq] at eq
  subst eq
  exact ⟨fcr', List.getElem?_eq_getElem lt, before, lastOk⟩

/-- A successful call has a next slot. -/
private theorem next_exists {store : Store preset fork} {fcr after : FastConfirmationStore}
    (called : store.onFastConfirmation config fcr = .ok after) {slot : Slot}
    (slotOk : store.getCurrentSlot config = .ok slot) :
    ∃ next, addChecked slot 1 = .ok next := by
  unfold Store.onFastConfirmation at called
  simp only [bind_ok_iff] at called
  obtain ⟨head, -, updated, update, -⟩ := called
  unfold Store.updateFastConfirmationVariables at update
  simp only [bind_ok_iff] at update
  obtain ⟨slot', slotOk', next, nextOk, -⟩ := update
  obtain rfl : slot = slot' := Except.ok.inj (slotOk.symm.trans slotOk')
  exact ⟨next, mapError_ok_iff.mp nextOk⟩

/-- The slot after an epoch's first slot does not start an epoch. -/
private theorem next_not_start (long : 1 < preset.SLOTS_PER_EPOCH) {slot next : Slot}
    (nextOk : addChecked slot 1 = .ok next)
    (atStart : isStartSlotAtEpoch preset slot = .ok true) :
    isStartSlotAtEpoch preset next = .ok false := by
  rw [isStart_eq, Except.ok.injEq, decide_eq_true_eq] at atStart
  have value := (addChecked_ok_iff.mp nextOk).2
  have P := UInt64.lt_iff_toNat_lt.mp long
  simp only [UInt64.toNat_one] at value P
  have one : (slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 1 := by
    rw [Nat.add_mod, atStart, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt P]
  rw [isStart_eq, Except.ok.injEq, decide_eq_false_iff_not, value, one]
  omega

/-- The premises of the run of calls, bundled once. -/
private structure CallsCtx (anchor : Store preset fork) (u : ValidatorIndex) (events : List ℕ)
    (firstSlot : Slot) (limit : ℕ) : Prop where
  anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor
  sound : Invariant anchorState
  anchorSlot : anchorBlock.slot = anchorState.slot
  anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true
  start : ∀ w ∈ J, e.start w = anchor
  slots : 0 < config.SLOT_DURATION_MS
  positive : 0 < preset.SLOTS_PER_EPOCH.toNat
  long : 1 < preset.SLOTS_PER_EPOCH
  preGloas : fork < .glamsterdam
  window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  roots : HeldBlockStateRootsNonzero (e := e) limit
  absent : AnchorParentAbsent (e := e) limit
  caller : u ∈ J
  anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot
  atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
    ((e.world n).state u).getCurrentSlot config = .ok slot ∧
    slot.toNat = firstSlot.toNat + i ∧
    computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
    (e.world n).time = begin.toNat

section Calls

variable {anchor : Store preset fork} {u : ValidatorIndex} {events : List ℕ} {firstSlot : Slot}
  {limit : ℕ}

/-- The caller's stores are forward reachable. -/
private theorem CallsCtx.forward (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
    (n : ℕ) : Store.ForwardReachable config anchorState anchorBlock ((e.world n).state u) :=
  e.forwardReachable
    (fun x hx => (ctx.start x hx).symm ▸ Store.ForwardReachable.anchor ctx.anchored) n u
    ctx.caller

/-- A call's slot and time. -/
private theorem call_slot (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {i n : ℕ}
    (found : events[i]? = some n) :
    ∃ slot, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      (e.world n).time =
        genesisTimeMs.toNat + (firstSlot.toNat + i) * config.SLOT_DURATION_MS.toNat := by
  obtain ⟨slot, begin, slotOk, slotNat, beginOk, timeEq⟩ := ctx.atSlots i n found
  obtain ⟨start, startOk, value, -⟩ := exists_timeAtSlotMs_of_le (UInt64.le_refl slot) beginOk
  rw [beginOk, Except.ok.injEq] at startOk
  subst startOk
  exact ⟨slot, slotOk, slotNat, by rw [timeEq, value, slotNat]⟩

/-- Earlier calls are at earlier events and times. -/
private theorem call_order (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
    {j i m n : ℕ} (fm : events[j]? = some m) (fn : events[i]? = some n) (lt : j < i) :
    m < n ∧ (e.world m).time < (e.world n).time := by
  obtain ⟨-, -, -, tm⟩ := call_slot ctx fm
  obtain ⟨-, -, -, tn⟩ := call_slot ctx fn
  have D := UInt64.lt_iff_toNat_lt.mp ctx.slots
  simp only [UInt64.toNat_zero] at D
  have : (firstSlot.toNat + j) * config.SLOT_DURATION_MS.toNat <
      (firstSlot.toNat + i) * config.SLOT_DURATION_MS.toNat :=
    Nat.mul_lt_mul_of_pos_right (by omega) D
  have timeLt : (e.world m).time < (e.world n).time := by omega
  refine ⟨?_, timeLt⟩
  by_contra h
  have back := e.monotone_time (Nat.le_of_not_gt h)
  dsimp only at back
  omega

/-- The first call reads the anchor's fast confirmation store.

Its observed checkpoint is the anchor's finalized one. -/
private theorem call_zero (long : 1 < preset.SLOTS_PER_EPOCH) {n : ℕ}
    {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) 0 n fcr after) :
    fcr = getFastConfirmationStore anchor ∧
      after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint := by
  obtain ⟨-, run, called⟩ := calls
  simp only [List.take_zero, List.map_nil, List.foldlM_nil, pure, Except.pure,
    Except.ok.injEq] at run
  subst run
  refine ⟨rfl, ?_⟩
  obtain ⟨slot, slotOk, -, keepPrev, atStart, notStart⟩ :=
    Store.onFastConfirmation_checkpoints called
  by_cases zero : slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0
  · have st : isStartSlotAtEpoch preset slot = .ok true := by
      rw [isStart_eq]
      simp [zero]
    obtain ⟨next, nextOk⟩ := next_exists called slotOk
    rw [(atStart st).1, keepPrev next nextOk (next_not_start long nextOk st)]
    rfl
  · have st : isStartSlotAtEpoch preset slot = .ok false := by
      rw [isStart_eq]
      simp [zero]
    rw [(notStart st).1]
    rfl

/-- A later call reads the call before it.

At an epoch's first slot, its observed checkpoint is the earlier call's unrealized justified one.

At any other slot, it keeps the observed checkpoint of the earlier call. -/
private theorem call_succ (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {j n : ℕ}
    {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) (j + 1) n fcr after) :
    ∃ m fcr', CallAt (e := e) u events (getFastConfirmationStore anchor) j m fcr' fcr ∧
      m < n ∧ (e.world m).time < (e.world n).time ∧
      ∃ slot, ((e.world n).state u).getCurrentSlot config = .ok slot ∧
        slot.toNat = firstSlot.toNat + (j + 1) ∧
        ((isStartSlotAtEpoch preset slot = .ok true ∧
            after.currentEpochObservedJustifiedCheckpoint =
              ((e.world m).state u).unrealizedJustifiedCheckpoint) ∨
          (isStartSlotAtEpoch preset slot = .ok false ∧
            after.currentEpochObservedJustifiedCheckpoint =
              fcr.currentEpochObservedJustifiedCheckpoint)) := by
  obtain ⟨m, fcr', prev⟩ := callAt_previous calls
  obtain ⟨mn, tlt⟩ := call_order ctx prev.1 calls.1 (by omega)
  obtain ⟨slotN, slotNOk, slotNNat, -⟩ := call_slot ctx calls.1
  obtain ⟨slotM, slotMOk, slotMNat, -⟩ := call_slot ctx prev.1
  obtain ⟨sN, sNOk, -, keepPrev, atStart, notStart⟩ :=
    Store.onFastConfirmation_checkpoints calls.2.2
  obtain rfl : slotN = sN := Except.ok.inj (slotNOk.symm.trans sNOk)
  obtain ⟨sM, sMOk, toPrev, -, -, -⟩ := Store.onFastConfirmation_checkpoints prev.2.2
  obtain rfl : slotM = sM := Except.ok.inj (slotMOk.symm.trans sMOk)
  refine ⟨m, fcr', prev, mn, tlt, slotN, slotNOk, slotNNat, ?_⟩
  by_cases zero : slotN.toNat % preset.SLOTS_PER_EPOCH.toNat = 0
  · have st : isStartSlotAtEpoch preset slotN = .ok true := by
      rw [isStart_eq]
      simp [zero]
    obtain ⟨next, nextOk⟩ := next_exists calls.2.2 slotNOk
    have step : addChecked slotM 1 = .ok slotN := addChecked_ok_iff.mpr ⟨by
      have := slotN.toNat_lt
      simp only [UInt64.toNat_one]
      omega, by simp only [UInt64.toNat_one]; omega⟩
    refine .inl ⟨st, ?_⟩
    rw [(atStart st).1, keepPrev next nextOk (next_not_start ctx.long nextOk st),
      toPrev slotN step st]
  · have st : isStartSlotAtEpoch preset slotN = .ok false := by
      rw [isStart_eq]
      simp [zero]
    exact .inr ⟨st, (notStart st).1⟩

/-- The anchor block's epoch is the anchor state's. -/
private theorem anchor_epoch {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot) {anchorRoot : Root}
    (hashed : hashTreeRoot anchorBlock = .ok anchorRoot) {be : Epoch}
    (read : store.getBlockEpoch anchorRoot = .ok be) : be = getCurrentEpoch anchorState := by
  obtain ⟨b, bFound, rfl⟩ := found_of_blockEpoch read
  obtain ⟨key, keyHash, aFound⟩ := reached.anchor_known
  obtain rfl : key = anchorRoot := Except.ok.inj (keyHash.symm.trans hashed)
  obtain rfl : b = anchorBlock := Option.some.inj (bFound.symm.trans aFound)
  rw [anchorSlot]
  rfl

/-- The anchor root has the recency facts against the anchor's finalized checkpoint.

They hold in any caller store by the limit. -/
private theorem anchor_recent (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {n : ℕ}
    (bound : (e.world n).time ≤ limit) (E : ℕ) :
    Recent ((e.world n).state u) E anchor.finalizedCheckpoint
      anchor.finalizedCheckpoint.root := by
  obtain ⟨anchorRoot, hashed, -, -, -, finEq, ujEq, -⟩ := getForkchoiceStore_anchor ctx.anchored
  have reached := (ctx.forward n).reachable
  have mono := e.anchor_unrealized_le ctx.start ctx.caller n
  rw [ujEq] at mono
  have mono := UInt64.le_iff_toNat_le.mp mono
  dsimp only at mono
  rw [finEq]
  intro be beOk rec
  obtain rfl := anchor_epoch reached ctx.anchorSlot hashed beOk
  obtain ⟨key, keyHash, aFound⟩ := reached.anchor_known
  obtain rfl : key = anchorRoot := Except.ok.inj (keyHash.symm.trans hashed)
  dsimp only
  exact ⟨by omega, by omega, reached.getCheckpointBlock_anchor ctx.anchorSlot
    ctx.anchorBoundary (ctx.absent u ctx.caller n bound) aFound hashed⟩

/-- A reachable store past the anchor epoch reads its finalized checkpoint at some root.

The checkpoint comes from a held state or from its pull-up, whose block reads it on its chain.

The anchor state must not hash to the zero root. -/
private theorem finalized_read {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (nonzero : hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0))
    (later : getCurrentEpoch anchorState < store.finalizedCheckpoint.epoch) :
    ∃ root, store.getCheckpointBlock root store.finalizedCheckpoint.epoch =
      .ok store.finalizedCheckpoint.root := by
  have known := fun {root : Root} {state : BeaconState preset fork}
      (stored : store.blockStates[root]? = some state) member =>
    reached.getCheckpointBlock_of_blockState sound anchorSlot positive window stored
      (checkpoint := store.finalizedCheckpoint) member later
  rcases reached.finalized_origins _ (Or.inl rfl) with ⟨root, -, same⟩ |
      ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, pulledOk, same⟩
  · rw [same] at later
    exact absurd later (UInt64.lt_irrefl _)
  · rcases known stored (.inl (by simp [same])) with ⟨read, -⟩ | zero
    · exact ⟨root, read⟩
    · exact absurd zero nonzero
  · rcases known stored (.inr ⟨pulled, pulledOk, by simp [same]⟩) with ⟨read, -⟩ | zero
    · exact ⟨root, read⟩
    · exact absurd zero nonzero

/-- A finalized start within one epoch of the call is the anchor root.

That is in the run's first epoch, where the observed checkpoint is the anchor's. -/
private theorem finalized_recent (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
    {n : ℕ} (bound : (e.world n).time ≤ limit) {slot : Slot}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot) {E E0 : ℕ}
    (hE : (computeEpochAtSlot preset slot).toNat = E)
    (before : (getCurrentEpoch anchorState).toNat < E0) (first : E0 ≤ E)
    {c : Checkpoint} (cAnchor : E = E0 → c = anchor.finalizedCheckpoint) :
    Recent ((e.world n).state u) E c ((e.world n).state u).finalizedCheckpoint.root := by
  have forward := ctx.forward n
  have reached := forward.reachable
  have nonzero := anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller bound
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  obtain ⟨anchorRoot, hashed, -, -, -, finEq, -, -⟩ := getForkchoiceStore_anchor ctx.anchored
  intro be beOk rec
  by_cases lt : getCurrentEpoch anchorState <
      ((e.world n).state u).finalizedCheckpoint.epoch
  · exfalso
    obtain ⟨root, r⟩ := finalized_read reached ctx.sound (UInt64.le_of_eq ctx.anchorSlot)
      ctx.positive ctx.window nonzero lt
    obtain ⟨b, bFound, bLe, -⟩ := Store.getCheckpointBlock_self ctx.preGloas ctx.positive r
    obtain ⟨b', bFound', rfl⟩ := found_of_blockEpoch beOk
    obtain rfl : b' = b := Option.some.inj (bFound'.symm.trans bFound)
    rcases forward.finalized_add_two_le_or_anchor ctx.sound ctx.slots epochOk with lag | lag
    · omega
    · exact UInt64.not_lt.mpr lag lt
  · have le := UInt64.not_lt.mp lt
    obtain ⟨-, hash⟩ := reached.finalized_eq_anchor_of_epoch_le le
    have rootEq : ((e.world n).state u).finalizedCheckpoint.root =
        anchor.finalizedCheckpoint.root := by
      rw [finEq]
      exact Except.ok.inj (hash.symm.trans hashed)
    rw [rootEq] at beOk ⊢
    have beEq := anchor_epoch reached ctx.anchorSlot hashed (by rw [finEq] at beOk; exact beOk)
    subst beEq
    rw [cAnchor (by omega)]
    exact anchor_recent ctx bound E _ beOk rec

/-- The facts carried from call `j` at event `m` to the next call.

The observed checkpoint is before the call's epoch, and is the anchor's in the run's first epoch.

The confirmed root has the recency facts. -/
private def Facts (anchor : Store preset fork) (u : ValidatorIndex) (f j m : ℕ)
    (after : FastConfirmationStore) : Prop :=
  after.currentEpochObservedJustifiedCheckpoint.epoch.toNat + 1 ≤
      (f + j) / preset.SLOTS_PER_EPOCH.toNat ∧
    ((f + j) / preset.SLOTS_PER_EPOCH.toNat = f / preset.SLOTS_PER_EPOCH.toNat →
      after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint) ∧
    Recent ((e.world m).state u) ((f + j) / preset.SLOTS_PER_EPOCH.toNat)
      after.currentEpochObservedJustifiedCheckpoint after.confirmedRoot

/-- One call: from the facts of the call before it, the facts of the call's observed checkpoint.

Every start that the call may select, kept, finalized or observed, has the recency facts. -/
private theorem start_recent (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {i n : ℕ}
    {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (bound : (e.world n).time ≤ limit)
    (prev : ∀ j, i = j + 1 → ∀ m fcr',
      CallAt (e := e) u events (getFastConfirmationStore anchor) j m fcr' fcr →
      (e.world m).time ≤ limit → Facts (e := e) anchor u firstSlot.toNat j m fcr) :
    after.currentEpochObservedJustifiedCheckpoint.epoch.toNat + 1 ≤
        (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat ∧
      ((firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat =
          firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat →
        after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint) ∧
      ∀ (head : ForkChoiceNode) (slot : Slot) (start : Root),
        ((e.world n).state u).getHead config = .ok head →
        ((e.world n).state u).getCurrentSlot config = .ok slot →
        ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot start →
        Recent ((e.world n).state u) ((firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat)
          after.currentEpochObservedJustifiedCheckpoint start := by
  have forward := ctx.forward n
  have reached := forward.reachable
  obtain ⟨anchorRoot, hashed, -, -, -, finEq, -, -⟩ := getForkchoiceStore_anchor ctx.anchored
  have before := UInt64.lt_iff_toNat_lt.mp ctx.anchorEpochBefore
  simp only [computeEpochAtSlot, UInt64.toNat_div] at before
  obtain ⟨slotN, slotNOk, slotNNat, -⟩ := call_slot ctx calls.1
  have hE : (computeEpochAtSlot preset slotN).toNat =
      (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat := by
    simp [computeEpochAtSlot, UInt64.toNat_div, slotNNat]
  have first : firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat := Nat.div_le_div_right (by omega)
  have rel : (after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint ∧
        fcr.confirmedRoot = anchor.finalizedCheckpoint.root) ∨
      ∃ j m fcr', i = j + 1 ∧
        CallAt (e := e) u events (getFastConfirmationStore anchor) j m fcr' fcr ∧ m < n ∧
        (e.world m).time ≤ limit ∧ Facts (e := e) anchor u firstSlot.toNat j m fcr ∧
        ((isStartSlotAtEpoch preset slotN = .ok true ∧
            after.currentEpochObservedJustifiedCheckpoint =
              ((e.world m).state u).unrealizedJustifiedCheckpoint ∧
            (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat =
              (firstSlot.toNat + j) / preset.SLOTS_PER_EPOCH.toNat + 1) ∨
          (isStartSlotAtEpoch preset slotN = .ok false ∧
            after.currentEpochObservedJustifiedCheckpoint =
              fcr.currentEpochObservedJustifiedCheckpoint ∧
            (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat =
              (firstSlot.toNat + j) / preset.SLOTS_PER_EPOCH.toNat)) := by
    cases i with
    | zero =>
      obtain ⟨rfl, cEq⟩ := call_zero ctx.long calls
      exact .inl ⟨cEq, rfl⟩
    | succ j =>
      obtain ⟨m, fcr', prevCall, mn, tlt, slot', slot'Ok, -, cases'⟩ := call_succ ctx calls
      obtain rfl : slotN = slot' := Except.ok.inj (slotNOk.symm.trans slot'Ok)
      have facts := prev j rfl m fcr' prevCall (by omega)
      refine .inr ⟨j, m, fcr', rfl, prevCall, mn, by omega, facts, ?_⟩
      have succ : (firstSlot.toNat + j + 1) / preset.SLOTS_PER_EPOCH.toNat =
          (firstSlot.toNat + j) / preset.SLOTS_PER_EPOCH.toNat +
            if (firstSlot.toNat + j + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 then 1 else 0 := by
        rw [Nat.succ_div]
        simp [Nat.dvd_iff_mod_eq_zero]
      rw [← Nat.add_assoc]
      rcases cases' with ⟨st, cEq⟩ | ⟨st, cEq⟩
      · have st' := st
        rw [isStart_eq, Except.ok.injEq, decide_eq_true_eq, slotNNat, ← Nat.add_assoc] at st'
        simp only [st', ↓reduceIte] at succ
        exact .inl ⟨st, cEq, succ⟩
      · have st' := st
        rw [isStart_eq, Except.ok.injEq, decide_eq_false_iff_not, slotNNat,
          ← Nat.add_assoc] at st'
        simp only [st', ↓reduceIte, Nat.add_zero] at succ
        exact .inr ⟨st, cEq, succ⟩
  have cFacts : after.currentEpochObservedJustifiedCheckpoint.epoch.toNat + 1 ≤
        (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat ∧
      ((firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat =
          firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat →
        after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint) := by
    rcases rel with ⟨cEq, -⟩ |
        ⟨j, m, fcr', rfl, prevCall, mn, mb, ⟨cb, ca, -⟩, ⟨-, cEq, eEq⟩ | ⟨-, cEq, eEq⟩⟩
    · rw [cEq, finEq]
      exact ⟨by dsimp only; omega, fun _ => rfl⟩
    · obtain ⟨slotM, slotMOk, slotMNat, -⟩ := call_slot ctx prevCall.1
      have epochM : ((e.world m).state u).getCurrentStoreEpoch config =
          .ok (computeEpochAtSlot preset slotM) := by
        simp [Store.getCurrentStoreEpoch, slotMOk, bind, Except.bind, pure, Except.pure]
      have le := UInt64.le_iff_toNat_le.mp ((ctx.forward m).justified_epoch_le_current ctx.sound
        ctx.slots (UInt64.le_of_eq ctx.anchorSlot) epochM).2
      simp only [computeEpochAtSlot, UInt64.toNat_div, slotMNat] at le
      have firstJ : firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
          (firstSlot.toNat + j) / preset.SLOTS_PER_EPOCH.toNat := Nat.div_le_div_right (by omega)
      rw [cEq]
      exact ⟨by omega, fun h => absurd h (by omega)⟩
    · rw [cEq]
      exact ⟨by omega, fun h => ca (by omega)⟩
  refine ⟨cFacts.1, cFacts.2, ?_⟩
  intro head slot start headOk slotOk selects
  obtain rfl : slotN = slot := Except.ok.inj (slotNOk.symm.trans slotOk)
  rcases selects.eq_or with ⟨rfl, -, safe⟩ | rfl | ⟨rfl, atStart, -, ujHead⟩
  · -- The kept root: the previous call's facts, carried by the unrealized order and the blocks.
    rcases rel with ⟨cEq, rootEq⟩ | ⟨j, m, fcr', rfl, prevCall, mn, mb, ⟨-, -, recJ⟩, rest⟩
    · rw [rootEq, cEq]
      exact anchor_recent ctx bound _
    · intro be beOk rec
      have reachedM := (ctx.forward m).reachable
      obtain ⟨be', beOk'⟩ := root_known reachedM ctx.sound ctx.anchorSlot ctx.positive
        ctx.window (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller mb)
        prevCall.2.2
      obtain rfl : be = be' :=
        Except.ok.inj (beOk.symm.trans (getBlockEpoch_of_le (e := e) mn.le beOk'))
      have mono := UInt64.le_iff_toNat_le.mp (e.unrealizedJustified_epoch_le_of_le u mn.le)
      rcases rest with ⟨st, cEq, eEq⟩ | ⟨st, cEq, eEq⟩
      · obtain ⟨Q, -, -⟩ := recJ be beOk' (by omega)
        have T := chainSafe_read (safe st)
        rw [cEq] at T ⊢
        exact ⟨by omega, by omega, T⟩
      · obtain ⟨Q, R, T⟩ := recJ be beOk' (by omega)
        rw [cEq]
        exact ⟨by omega, by omega,
          Store.getCheckpointBlock_of_blocks (fun found => e.blocks_of_le mn.le found) T⟩
  · -- The finalized root.
    exact finalized_recent ctx bound slotNOk hE before first cFacts.2
  · -- The observed root: its checkpoint is the head's unrealized justification.
    rcases rel with ⟨cEq, -⟩ |
        ⟨j, m, fcr', rfl, prevCall, mn, mb, -, ⟨-, cEq, eEq⟩ | ⟨st, -, -⟩⟩
    · rw [cEq]
      exact anchor_recent ctx bound _
    · have reachedM := (ctx.forward m).reachable
      rcases reachedM.checkpoints_known ctx.sound (UInt64.le_of_eq ctx.anchorSlot) ctx.positive
          ctx.window (checkpoint := ((e.world m).state u).unrealizedJustifiedCheckpoint)
          (by simp) with ⟨epochEq, hash, -⟩ | ⟨lt, -⟩ | zero
      · have rootEq := Except.ok.inj (hash.symm.trans hashed)
        have same : after.currentEpochObservedJustifiedCheckpoint = anchor.finalizedCheckpoint :=
          calc after.currentEpochObservedJustifiedCheckpoint
              = ⟨((e.world m).state u).unrealizedJustifiedCheckpoint.epoch,
                  ((e.world m).state u).unrealizedJustifiedCheckpoint.root⟩ := by rw [cEq]
            _ = anchor.finalizedCheckpoint := by rw [epochEq, rootEq, finEq]
        rw [same]
        exact anchor_recent ctx bound _
      · rw [← cEq] at lt
        intro be beOk rec
        rcases reached.getCheckpointBlock_of_unrealizedJustification ctx.sound
            (UInt64.le_of_eq ctx.anchorSlot) ctx.positive ctx.window
            (Store.unrealizedJustification_found ujHead) lt with
          ⟨read, -⟩ | zero
        · obtain ⟨b, bFound, bLe, self⟩ :=
            Store.getCheckpointBlock_self ctx.preGloas ctx.positive read
          obtain ⟨b', bFound', rfl⟩ := found_of_blockEpoch beOk
          obtain rfl : b' = b := Option.some.inj (bFound'.symm.trans bFound)
          have := UInt64.le_iff_toNat_le.mp (forward.unrealizedJustification_epoch_le ctx.sound
            ctx.positive ctx.slots (Store.unrealizedJustification_found ujHead))
          exact ⟨by omega, by omega, self⟩
        · exact absurd zero
            (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller bound)
      · exact absurd zero
          (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller mb)
    · exact absurd (atStart.symm.trans st) (by simp)

/-- One call keeps the facts. -/
private theorem facts_step (ctx : CallsCtx (e := e) anchor u events firstSlot limit) {i n : ℕ}
    {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (bound : (e.world n).time ≤ limit)
    (prev : ∀ j, i = j + 1 → ∀ m fcr',
      CallAt (e := e) u events (getFastConfirmationStore anchor) j m fcr' fcr →
      (e.world m).time ≤ limit → Facts (e := e) anchor u firstSlot.toNat j m fcr) :
    Facts (e := e) anchor u firstSlot.toNat i n after := by
  obtain ⟨cb, ca, startRec⟩ := start_recent ctx calls bound prev
  refine ⟨cb, ca, ?_⟩
  obtain ⟨head, slot, start, headOk, slotOk, selects, result⟩ :=
    Store.onFastConfirmation_checked calls.2.2
  have startFacts := startRec head slot start headOk slotOk selects
  obtain ⟨slotN, slotNOk, slotNNat, -⟩ := call_slot ctx calls.1
  obtain rfl : slotN = slot := Except.ok.inj (slotNOk.symm.trans slotOk)
  have hE : (computeEpochAtSlot preset slotN).toNat =
      (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat := by
    simp [computeEpochAtSlot, UInt64.toNat_div, slotNNat]
  rcases result with same | ⟨-, checked, source, chain, later, -, walked, confirmed⟩
  · rw [same]
    exact startFacts
  · exact root_recent (ctx.forward n) ctx.sound ctx.positive ctx.slots
      (UInt64.le_of_eq ctx.anchorSlot) ctx.preGloas slotOk hE cb startFacts checked walked
      (confirmed _ (by simp))

/-- Every call by the limit has the facts, by induction over the calls. -/
private theorem facts (ctx : CallsCtx (e := e) anchor u events firstSlot limit) :
    ∀ i n fcr after,
      CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after →
      (e.world n).time ≤ limit → Facts (e := e) anchor u firstSlot.toNat i n after := by
  intro i
  induction i with
  | zero =>
    intro n fcr after calls bound
    exact facts_step ctx calls bound (fun j h => absurd h (by omega))
  | succ j ih =>
    intro n fcr after calls bound
    refine facts_step ctx calls bound (fun j' h m fcr' c b => ?_)
    obtain rfl : j' = j := by omega
    exact ih m fcr' fcr c b

end Calls

/-- The balance source of a call is on the chain of each walked member's parent.

The source is the call's observed checkpoint, and the walk is the accepted one.

The proof carries recency facts of the stored root from call to call. -/
private theorem sourceOnParentChain_of_walk {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (long : 1 < preset.SLOTS_PER_EPOCH) (preGloas : fork < .glamsterdam)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {limit : ℕ} (roots : HeldBlockStateRootsNonzero (e := e) limit)
    (absent : AnchorParentAbsent (e := e) limit)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    (anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot)
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot : Slot} {startRoot : Root} {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (selects : ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot
      startRoot)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root startRoot
      after.confirmedRoot)
    (walked : ((e.world n).state u).getAncestorRoots head.root startRoot =
      .ok (chain ++ after.confirmedRoot :: later)) :
    ∀ member ∈ chain ++ [after.confirmedRoot], ∀ (block parent : BeaconBlock preset fork),
      ((e.world n).state u).block member = .ok block →
      ((e.world n).state u).block block.parentRoot = .ok parent →
      SourceOnParentChain ((e.world n).state u) after.currentEpochObservedJustifiedCheckpoint
        block.parentRoot parent := by
  have ctx : CallsCtx (e := e) anchor u events firstSlot limit :=
    ⟨anchored, sound, anchorSlot, anchorBoundary, start, slots, positive, long, preGloas, window,
      roots, absent, caller, anchorEpochBefore, atSlots⟩
  obtain ⟨below, -, startRec⟩ := start_recent ctx calls nBound
    (fun j _ m fcr' c b => facts ctx j m fcr' fcr c b)
  obtain ⟨slotN, slotNOk, slotNNat, -⟩ := call_slot ctx calls.1
  obtain rfl : slotN = slot := Except.ok.inj (slotNOk.symm.trans slotOk)
  have hE : (computeEpochAtSlot preset slotN).toNat =
      (firstSlot.toNat + i) / preset.SLOTS_PER_EPOCH.toNat := by
    simp [computeEpochAtSlot, UInt64.toNat_div, slotNNat]
  intro member mem block parent blockOk parentOk
  exact parent_source (ctx.forward n) slots (UInt64.le_of_eq anchorSlot) preGloas slotNOk hE below
    (startRec head slotN startRoot headOk slotNOk selects) checked walked mem blockOk parentOk

/-! ## The call step

A call keeps the call invariant, given the invariant at every earlier call.
-/

/-- The call invariant of the root that a call of one validator stores.

The up-to-date honest heads descend from the root from the next slot to the horizon.

If the root is of the current epoch or the one before, an ancestor of it is too.

That ancestor covers the honest heads from the start of the current epoch.

A root of the current epoch passes the target checks of the call, covered to the horizon. -/
private def CallInvariant (margin limit : ℕ) (anchorRoot : Root) (u : ValidatorIndex) (n : ℕ)
    (root : Root) : Prop :=
  (∀ slot next following, ((e.world n).state u).getCurrentSlot config = .ok slot →
    addChecked slot 1 = .ok next →
    computeTimeAtSlotMs config genesisTimeMs next = .ok following →
    HonestHeadsCover (e := e) root following.toNat (limit + 1)) ∧
  (∀ epoch rootEpoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    ((e.world n).state u).getBlockEpoch root = .ok rootEpoch →
    epoch.toNat ≤ rootEpoch.toNat + 1 →
    ∃ (historical : Root) (historicalEpoch : Epoch) (epochStart : Slot) (epochStartTime : UInt64),
      ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨historical, .pending⟩ = .ok true ∧
      ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch ∧
      epoch.toNat ≤ historicalEpoch.toNat + 1 ∧
      computeStartSlotAtEpoch preset epoch = .ok epochStart ∧
      computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime ∧
      HonestHeadsCover (e := e) historical epochStartTime.toNat (limit + 1)) ∧
  (∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    ((e.world n).state u).getBlockEpoch root = .ok epoch →
    TargetChecked (e := e) margin anchorRoot u n epoch root (limit + 1))

/-- The inputs of the coverage step for one walked member of one call.

They read the member's block, its parent, the proposer score and the windows of the parent.

The member's margin then exceeds the committee weight, the boost and the adversary's weight.

The excess `shift` pays for the drift of each later window from the source's balances.

Each later window keeps a reserve at `exitReserveNear`.

The late duty majority of the parent's epoch holds from the call to the horizon.

So do the newly active voters of the parent's window.

No theorem derives the drift bound yet.

Its planned producer charges the drift from the source state, at the receivers the proof reads.

With a positive `shift`, the margin asks more than the rule's one-confirmation test.

An assumption on the run: the late duty majority and the newly active voters of the window.

The majority buys the receivers more than two epochs after the parent's epoch.

It needs one epoch's honest duties to outweigh the rest of the active stake and the boost.

The newly active voters buy the voters activated two epochs after the parent. -/
def MemberObligations [DecidablePred (· ∈ J)] (u : ValidatorIndex) (n : ℕ) (head : Root)
    (source : BeaconState preset fork) (slot : Slot) (member : Root) (limit : ℕ) : Prop :=
  ∀ (block parent : BeaconBlock preset fork) (first last beforeBlock : Slot)
    (boost maximum support discount adversary : Gwei)
    (parentParticipants : Std.TreeSet ValidatorIndex),
    ((e.world n).state u).block member = .ok block →
    ((e.world n).state u).block block.parentRoot = .ok parent →
    computeProposerScore config source = .ok boost →
    addChecked parent.slot 1 = .ok first → subChecked slot 1 = .ok last →
    subChecked block.slot 1 = .ok beforeBlock →
    ((e.world n).state u).computeCommitteeWeightBetweenSlots head source first last =
      .ok maximum →
    ((e.world n).state u).getCommitteesBetweenSlots head first beforeBlock =
      .ok parentParticipants →
    ((e.world n).state u).scoreFromTally (((e.world n).state u).tallyVotes source)
      ⟨member, .pending⟩ = .ok support →
    ((e.world n).state u).computeEmptySlotSupportDiscount config head source member =
      .ok discount →
    ((e.world n).state u).getAdversarialWeight config head source member = .ok adversary →
    ∃ shift, maximum.toNat + boost.toNat + 2 * adversary.toNat + shift <
        discount.toNat + 2 * support.toNat ∧
      WindowMarginDrift (e := e) n limit source shift ∧
      (∀ x ∈ J, ∀ m (referenceSlot finish : Slot), limit ≤ (e.world m).time →
        UpToDate config checks sources (e.world m).time ((e.world m).view x)
          ((e.world m).state x) →
        ((e.world m).state x).getCurrentSlot config = .ok referenceSlot →
        subChecked referenceSlot 1 = .ok finish →
        SourceWindowReserveWith (J := J) (config := config) ((e.world n).state u) head source
          first finish (exitReserveNear source)) ∧
      LateDutyMajority (e := e) (computeEpochAtSlot preset parent.slot) (e.world n).time limit ∧
      NewlyActiveVotersInHeadWindow (e := e) block.parentRoot (e.world n).time limit

/-- The inputs of one confirming call that the call step assumes.

They apply only when the call walks from its head to the start it selected, through the stored root.

They are the source reads of the later windows and the count.

The count bounds carry the call's pin reserve on top of the margin.

They include the realized justification guards of the accepted roots, and each member's inputs.

An assumption on the run: the count bounds and the realized guards, which the rule does not check.

They buy the call's honest target count and the realized justification of each walked root.

No theorem derives the source reads yet.

The source reads fail for a window member deposited after the source state, and on overflow.

A call that keeps its start walks no roots, so it assumes nothing. -/
def CallObligations [DecidablePred (· ∈ J)] (margin limit : ℕ) (u : ValidatorIndex) (n : ℕ)
    (fcr after : FastConfirmationStore) : Prop :=
  ∀ (head : ForkChoiceNode) (slot : Slot) (start : Root) (source : BeaconState preset fork)
    (chain later : List Root),
    ((e.world n).state u).getHead config = .ok head →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot start →
    ((e.world n).state u).checkpointState after.currentEpochObservedJustifiedCheckpoint =
      .ok source →
    ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later) →
    SourceWindowReads (e := e) n limit source ∧
    (∀ slot (pulled anc fin : BeaconState preset fork) (target : Checkpoint),
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok false →
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok pulled →
      ((e.world n).state u).getCurrentTarget config head.root = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
        ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin) →
      (anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) →
      TargetCountBounds (e := e) (margin + pinReserve config pulled anc fin) u n head.root) ∧
    AcceptedRealizedRecent ((e.world n).state u) (chain ++ [after.confirmedRoot]) ∧
    AcceptedRealizedHead ((e.world n).state u) config head.root (chain ++ [after.confirmedRoot]) ∧
    ∀ member ∈ chain ++ [after.confirmedRoot],
      MemberObligations (e := e) u n head.root source slot member limit

/-- The evidence alternatives of the call step, in its order. -/
private def Bad {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    (limit : ℕ) : Prop :=
  HonestCollision (e := e) limit ∨ HistoricalDirectSafetyEvidence (e := e) pre limit ∨
    CrossStoreDirectSafetyEvidence (e := e) pre limit ∨
    CrossStoreJustifiedEvidence (e := e) pre limit ∨ HeldStateFinalityEvidence (e := e) pre limit

/-- The facts that hold up to the horizon once the evidence alternatives are split off. -/
private structure Good (horizon : Epoch) (limit : ℕ) : Prop where
  agree : SelectedCheckpointsAgree (e := e) horizon limit
  finality : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ limit → (e.world j).time ≤ limit →
    ((e.world i).state a).finalizedCheckpoint.epoch ≤
      ((e.world j).state b).justifiedCheckpoint.epoch →
    ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
      ((e.world i).state a).finalizedCheckpoint.epoch =
        .ok ((e.world i).state a).finalizedCheckpoint.root
  blocks : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ limit → (e.world j).time ≤ limit →
    ∀ (r : Root) (left right : BeaconBlock preset fork),
    ((e.world i).state a).blocks[r]? = some left →
    ((e.world j).state b).blocks[r]? = some right → left = right
  quorum : QuorumDriftWithin (e := e) horizon limit

/-- The premises of the call step that do not depend on the call.

They extend the premises of the run of calls. -/
private structure StepCtx {g : ForkedBeaconState preset}
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (Δ : ℕ) (anchor : Store preset fork) (limit : ℕ) (horizon anchorEpoch : Epoch)
    (u : ValidatorIndex) (events : List ℕ) (firstSlot : Slot) : Prop
    extends CallsCtx (e := e) anchor u events firstSlot limit where
  bls : checks = .bls
  anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs
  sync : e.Synchronous Δ
  minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat
  exitWindow : preset.SeedLookaheadAtLeastThree
  ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat
  admitted : BlocksAdmitted e 0 Δ limit
  half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100
  maxAligned : MaxEffectiveBalancesAligned preset
  incrementPositive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  votes : ValidatedDutyVotes (e := e) limit
  fits : DelayFits fork config genesisTimeMs Δ
  prompt : Prompt e limit
  windows : AssignmentWindowAgreement (e := e) limit
  fit : config.CommitteeWindowsFit preset
  anchorEpochOk : anchor.justifiedCheckpoint.epoch = anchorEpoch
  increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0
  bounded : HonestStoreEpochsBounded (e := e) horizon limit
  unslashed : HonestCountedStatesUnslashed (e := e) limit
  ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) limit
  scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17)
  parameters : DirectSafety.Parameters preset
  genesis : Genesis config checks g
  heldEarly : HeldStatesBeforeUpgrade (e := e) limit
  enough : HeldRunStakeFloor (e := e) pre horizon limit
  terminal : HeldTerminalStakeFloor (e := e) horizon limit
  pinned : JustifiedPinned (e := e) anchorEpoch 0 0 limit
  signedAll : JustifiedHonestlySigned (e := e) anchorEpoch 0 limit
  fusaka : .fusaka ≤ fork
  band : preset.IncrementWithinUpwardBand
  withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  capEq : preset.MAX_EFFECTIVE_BALANCE = preset.MIN_ACTIVATION_BALANCE
  capOrder : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA
  forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat
  included : TargetIncluded (e := e) limit
  stale : StaleHeadVotersInWindow (e := e) limit
  reference : ∃ x ∈ J, ∃ m, ∃ referenceSlot finish : Slot, limit ≤ (e.world m).time ∧
    UpToDate config checks sources (e.world m).time ((e.world m).view x)
      ((e.world m).state x) ∧
    ((e.world m).state x).getCurrentSlot config = .ok referenceSlot ∧
    subChecked referenceSlot 1 = .ok finish
  confirmationEpoch : 2 ≤ computeEpochAtSlot preset firstSlot
  upToDate : ∀ n ∈ events, UpToDate config checks sources (e.world n).time
    ((e.world n).view u) ((e.world n).state u)
/-- The anchor block is at or before the first slot of each epoch from the anchor state's on.

The anchor block must be at its state's slot, and that slot must start an epoch. -/
private theorem anchor_le_epochStart (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true) :
    ∀ epoch : Epoch, getCurrentEpoch anchorState ≤ epoch →
      ∀ s, computeStartSlotAtEpoch preset epoch = .ok s → anchorBlock.slot ≤ s := by
  intro epoch le s sOk
  rw [isStart_eq, Except.ok.injEq, decide_eq_true_eq] at anchorBoundary
  have sNat := (computeStartSlotAtEpoch_ok_iff.mp sOk).2
  have leNat := UInt64.le_iff_toNat_le.mp le
  rw [getCurrentEpoch_toNat, ← anchorSlot] at leNat
  have modNat := Nat.mod_add_div anchorBlock.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have mul := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat leNat
  apply UInt64.le_iff_toNat_le.mpr
  rw [sNat]
  rw [Nat.mul_comm] at modNat
  omega

/-- At an epoch's first slot, a call after the first one starts from the earlier call's view.

The call replaces its base by the observed checkpoint, so its slot starts an epoch.

The observed checkpoint is the caller's unrealized justified checkpoint at the call before.

That checkpoint is of the epoch before the call's, and within the horizon.

Unless two honest stores collide or cross-store evidence holds, the call has justified it.

Each up-to-date honest store from the call to the limit has then justified its epoch. -/
private theorem observedStart {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon : Epoch} {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    {u : ValidatorIndex} {events : List ℕ} {firstSlot : Slot}
    (ctx : CallsCtx (e := e) anchor u events firstSlot limit)
    (sync : e.Synchronous Δ) (admitted : BlocksAdmitted e 0 Δ limit)
    (fits : DelayFits fork config genesisTimeMs Δ)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (agreement : SelectedCheckpointsAgree (e := e) horizon limit ∨
      CrossStoreJustifiedEvidence (e := e) pre limit)
    (finality : (∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ limit → (e.world j).time ≤ limit →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root) ∨
      CrossStoreDirectSafetyEvidence (e := e) pre limit)
    {j n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) (j + 1) n fcr after)
    (callBound : (e.world n).time ≤ limit)
    {head base : Root} {slot : Slot}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (replaces : ((e.world n).state u).ReplacesBase config after head base slot) :
    ∃ m, m ∈ events ∧ (e.world m).time + Δ < (e.world n).time ∧
      after.currentEpochObservedJustifiedCheckpoint =
        ((e.world m).state u).unrealizedJustifiedCheckpoint ∧
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch.toNat + 1 =
        (computeEpochAtSlot preset slot).toNat ∧
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤ horizon ∧
      ((((e.world n).state u).justifiedCheckpoint =
          ((e.world m).state u).unrealizedJustifiedCheckpoint ∧
        ∀ w ∈ J, ∀ k, (e.world n).time ≤ (e.world k).time → (e.world k).time ≤ limit →
          UpToDate config checks sources (e.world k).time ((e.world k).view w)
            ((e.world k).state w) →
          ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤
            ((e.world k).state w).justifiedCheckpoint.epoch) ∨
        HonestCollision (e := e) limit ∨ CrossStoreJustifiedEvidence (e := e) pre limit ∨
        CrossStoreDirectSafetyEvidence (e := e) pre limit) := by
  obtain ⟨anchored, sound, anchorSlot, anchorBoundary, start, slots, positive, long, preGloas,
    window, nonzero, -, caller, anchorBefore, atSlots⟩ := id ctx
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachable (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored)
      i v honest
  have aligned : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq anchorSlot
  obtain ⟨m, fcrM, previous, before, -, slotN', slotNOk', -, observed⟩ := call_succ ctx calls
  have order : m ≤ n := Nat.le_of_lt before
  have mMem : m ∈ events := List.mem_of_getElem? previous.1
  obtain ⟨slotM, beginM, slotMOk, indexM, beginMOk, atM⟩ := atSlots j m previous.1
  obtain ⟨slotN, beginN, slotNOk, indexN, beginNOk, atN⟩ := atSlots (j + 1) n calls.1
  have slotEq : slotN = slot := Except.ok.inj (slotNOk.symm.trans slotOk)
  subst slotEq
  have slotEq' : slotN = slotN' := Except.ok.inj (slotNOk.symm.trans slotNOk')
  subst slotEq'
  -- Consecutive calls are a delay apart.
  have sumN : slotN.toNat = slotM.toNat + 1 := by omega
  have nextOk : addChecked slotM 1 = .ok slotN := addChecked_ok_iff.mpr
    ⟨by have := slotN.toNat_lt; simpa only [UInt64.toNat_one, ← sumN] using this,
      by simpa using sumN⟩
  obtain ⟨due, dueOk⟩ := fits.1
  have fitsStep := fits.2 slotM slotN beginM due beginN nextOk beginMOk dueOk beginNOk
  have late : (e.world m).time + Δ < (e.world n).time := by omega
  have mBound : (e.world m).time ≤ limit := by omega
  -- The call's slot starts its epoch, so the previous call is in the epoch before.
  have modN : slotN.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
    have boundary := replaces.1
    rw [isStart_eq, Except.ok.injEq, decide_eq_true_eq] at boundary
    exact boundary
  have epochStep : (computeEpochAtSlot preset slotM).toNat + 1 =
      (computeEpochAtSlot preset slotN).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    rw [sumN]
    exact (Nat.succ_div_of_dvd (by rw [← sumN]; exact Nat.dvd_of_mod_eq_zero modN)).symm
  have epochMOk : ((e.world m).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slotM) := by
    simp [Store.getCurrentStoreEpoch, slotMOk, bind, Except.bind, pure, Except.pure]
  have epochNOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slotN) := by
    simp [Store.getCurrentStoreEpoch, slotNOk, bind, Except.bind, pure, Except.pure]
  -- This call observes the previous call's unrealized justified checkpoint.
  have observedEq : after.currentEpochObservedJustifiedCheckpoint =
      ((e.world m).state u).unrealizedJustifiedCheckpoint := by
    rcases observed with ⟨-, eq⟩ | ⟨notStart, -⟩
    · exact eq
    · rw [replaces.1] at notStart
      cases notStart
  have reachedM := (forward u caller m).reachable
  have reachedN := (forward u caller n).reachable
  have notZero := anchorState_hash_nonzero anchored start nonzero caller mBound
  -- The observed checkpoint is of the epoch before the call's.
  obtain ⟨observedBlock, epochN, foundN, epochNOk', ageOk⟩ := replaces.2.1
  cases Except.ok.inj (epochNOk'.symm.trans epochNOk)
  rw [observedEq] at foundN
  have age := (addChecked_ok_iff.mp ageOk).2
  simp only [UInt64.toNat_one] at age
  have observedLe : (computeEpochAtSlot preset observedBlock.slot).toNat ≤
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch.toNat := by
    rcases reachedM.checkpoints_known sound aligned positive window
        (checkpoint := ((e.world m).state u).unrealizedJustifiedCheckpoint) (by simp) with
      ⟨epochEq, hashed, -⟩ | ⟨later, -⟩ | zero
    · obtain ⟨anchorRoot, anchorHashed, held⟩ := reachedN.anchor_known
      have rootEq := Except.ok.inj (hashed.symm.trans anchorHashed)
      have blockEq : observedBlock = anchorBlock := by
        have found := Store.block_ok_iff.mp foundN
        rw [rootEq, held, Option.some.injEq] at found
        exact found.symm
      rw [blockEq, epochEq, anchorSlot]
      exact Nat.le_refl _
    · have fromRead {root : Root}
          (read : ((e.world m).state u).getCheckpointBlock root
            ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch =
              .ok ((e.world m).state u).unrealizedJustifiedCheckpoint.root) :
          (computeEpochAtSlot preset observedBlock.slot).toNat ≤
            ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch.toNat := by
        obtain ⟨block, held, le, -⟩ := Store.getCheckpointBlock_self preGloas positive read
        obtain rfl : block = observedBlock := Option.some.inj
          ((e.blocks_of_le order held).symm.trans (Store.block_ok_iff.mp foundN))
        exact le
      rcases reachedM.justified_origins _ (.inr rfl) with
        ⟨_, _, same⟩ | ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, run, same⟩
      · rw [same] at later
        exact (UInt64.lt_irrefl _ later).elim
      · exact fromRead ((reachedM.getCheckpointBlock_of_blockState sound aligned positive window
          stored (.inl (by simp [same])) later).resolve_right notZero).1
      · exact fromRead ((reachedM.getCheckpointBlock_of_blockState sound aligned positive window
          stored (.inr ⟨pulled, run, by simp [same]⟩) later).resolve_right notZero).1
    · exact (notZero zero).elim
  have upper := UInt64.le_iff_toNat_le.mp
    ((forward u caller m).justified_epoch_le_current sound slots aligned epochMOk).2
  have epochEq : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch.toNat + 1 =
      (computeEpochAtSlot preset slotN).toNat := by omega
  have uHorizon : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤ horizon :=
    UInt64.le_trans (UInt64.le_iff_toNat_le.mpr upper)
      (bounded u caller m _ mBound epochMOk)
  refine ⟨m, mMem, late, observedEq, epochEq, uHorizon, ?_⟩
  -- The caller's justified checkpoint and the receivers, unless some evidence holds.
  rcases agreement with selected | evidence
  swap
  · exact .inr (.inr (.inl evidence))
  rcases finality with crossFinal | evidence
  swap
  · exact .inr (.inr (.inr evidence))
  rcases e.blocksAgree_or_collision limit with agree | collision
  swap
  · exact .inr (.inl collision)
  left
  -- The call's justified checkpoint is of the observed epoch, so it is the observed checkpoint.
  have firstLe : (computeEpochAtSlot preset firstSlot).toNat ≤
      (computeEpochAtSlot preset slotN).toNat :=
    epoch_le_of_slot_le _ _ (by omega)
  have anchorLt := UInt64.lt_iff_toNat_lt.mp anchorBefore
  have justifiedUpper : ((e.world n).state u).justifiedCheckpoint.epoch.toNat + 1 ≤
      (computeEpochAtSlot preset slotN).toNat := by
    rcases (forward u caller n).justified_before_current sound positive slots anchorSlot
        slotNOk (by omega) with eq | lt
    · rw [eq]
      omega
    · exact UInt64.lt_iff_toNat_lt.mp lt
  have heldAtN {root : Root} {state : BeaconState preset fork}
      (stored : ((e.world m).state u).blockStates[root]? = some state) :
      ∃ block, ((e.world m).state u).blocks[root]? = some block ∧
        ((e.world n).state u).blocks[root]? = some block ∧
        ((e.world n).state u).blockStates[root]? = some state := by
    obtain ⟨block, known⟩ := reachedM.known_of_blockState stored
    have knownN := e.blocks_of_le order known
    obtain ⟨post, storedN, -, -⟩ := reachedN.blockStatesFromParents knownN
    have same := e.blockStates_eq anchored caller caller (start u caller) (start u caller)
      (agree u caller u caller m n mBound callBound) stored storedN
    subst post
    exact ⟨block, known, knownN, storedN⟩
  have justifiedLower : ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch ≤
      ((e.world n).state u).justifiedCheckpoint.epoch := by
    rcases reachedM.justified_origins _ (.inr rfl) with
      ⟨_, _, same⟩ | ⟨root, state, stored, same⟩ | ⟨root, state, pulled, stored, run, same⟩
    · rw [same]
      exact UInt64.le_trans reachedN.anchor_le_finalized (reachedN.finalized_le_justified sound)
    · obtain ⟨-, -, -, storedN⟩ := heldAtN stored
      rw [same]
      exact reachedN.justified_le_of_blockState sound storedN
    · obtain ⟨block, known, knownN, storedN⟩ := heldAtN stored
      have blockLe := (forward u caller m).block_epoch_le_current slots aligned slotMOk known
      rw [same]
      exact (forward u caller n).justified_le_of_pulledUp sound positive slots slotNOk knownN
        storedN run (UInt64.lt_iff_toNat_lt.mpr (by omega))
  have epochsEq : ((e.world n).state u).justifiedCheckpoint.epoch =
      ((e.world m).state u).unrealizedJustifiedCheckpoint.epoch := by
    apply UInt64.toNat_inj.mp
    have := UInt64.le_iff_toNat_le.mp justifiedLower
    omega
  have realized := selected u caller u caller n m callBound mBound _ _ (.inl rfl) (.inr rfl)
    epochsEq (epochsEq ▸ uHorizon)
  refine ⟨realized, ?_⟩
  -- Each receiver is in a later epoch than the previous call, so it has justified the epoch.
  intro w receiver k afterCall kBound current
  refine observedOrder sync slots positive window preGloas admitted anchored sound anchorSlot
    start (anchor_le_epochStart anchorSlot anchorBoundary) nonzero agree crossFinal caller
    receiver order callBound (by omega) kBound current realized ?_
  intro currentM currentW currentMOk currentWOk
  obtain rfl : slotM = currentM := Except.ok.inj (slotMOk.symm.trans currentMOk)
  have slotLe := e.currentSlot_le_of_time_le start caller receiver afterCall current slotNOk
    currentWOk
  have epochLe := epoch_le_of_slot_le (preset := preset) _ _ (UInt64.le_iff_toNat_le.mp slotLe)
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

/-! ## The anchor facts and the carried facts of a call -/

/-- A block with an epoch descends from itself. -/
private theorem isAncestor_self_of_blockEpoch {store : Store preset fork} {root : Root}
    {epoch : Epoch} (read : store.getBlockEpoch root = .ok epoch) :
    store.isAncestor ⟨root, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  obtain ⟨block, found, -⟩ := found_of_blockEpoch read
  exact Store.isAncestor_self (node := ⟨root, .pending⟩) found

/-- A slot that starts an epoch is the first slot of its epoch. -/
private theorem startSlot_of_isStart (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {slot : Slot} (atStart : isStartSlotAtEpoch preset slot = .ok true) :
    computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok slot := by
  have rounded := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot
  have up := le_computeStartSlotAtEpoch_of_isStartSlotAtEpoch atStart (UInt64.le_refl slot)
    rounded
  have down := (computeStartSlotAtEpoch_le_lt (UInt64.lt_iff_toNat_lt.mpr positive) rounded).1
  rw [rounded, UInt64.le_antisymm (UInt64.le_iff_toNat_le.mpr down) up]

/-- Every up-to-date honest head by the limit descends from the anchor's finalized root. -/
private theorem anchor_cover {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot) :
    HonestHeadsCover (e := e) anchor.finalizedCheckpoint.root 0 (limit + 1) := by
  intro time _ lt a ha i hd _ _ headOk
  have bound : (e.world i).time ≤ limit := by omega
  have reached := e.reachable
    (fun w hw => (ctx.start w hw).symm ▸ Store.Reachable.anchor ctx.anchored) i a ha
  have toJustified := Store.isAncestor_getHead headOk
  obtain ⟨justifiedBlock, justifiedFound⟩ := Store.held_of_isAncestor toJustified
  obtain ⟨headBlock, headFound, -⟩ := Store.slot_le_of_isAncestor justifiedFound toJustified
  have pending := Store.getHead_pending ctx.preGloas headOk
  obtain ⟨anchorRoot, hashed, -, -, -, final, -⟩ := getForkchoiceStore_anchor ctx.anchored
  have read := reached.getCheckpointBlock_anchor ctx.anchorSlot ctx.anchorBoundary
    (ctx.absent a ha i bound) headFound hashed
  obtain ⟨-, -, -, -, -, descends⟩ := Store.isAncestor_of_getCheckpointBlock ctx.preGloas read
  obtain ⟨headRoot, status⟩ := hd
  dsimp only at pending
  subst pending
  rw [final]
  exact descends

/-- The anchor's finalized root satisfies the call invariant at every call by the limit.

It also covers every up-to-date honest head from the call to the limit. -/
private theorem anchor_facts {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot) :
    ∀ n ∈ events, (e.world n).time ≤ limit →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
        anchor.finalizedCheckpoint.root ∧
      HonestHeadsCover (e := e) anchor.finalizedCheckpoint.root (e.world n).time (limit + 1) := by
  intro n member _
  have from_ (t : ℕ) : HonestHeadsCover (e := e) anchor.finalizedCheckpoint.root t (limit + 1) :=
    honestHeadsCover_mono (anchor_cover ctx) (Nat.zero_le t) le_rfl
  refine ⟨⟨fun _ _ following _ _ _ => from_ following.toNat, ?_, ?_⟩, from_ _⟩
  · intro epoch rootEpoch epochOk rootOk recent
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨slot, begin, slotOk, -, beginOk, -⟩ := ctx.atSlots index n found
    have boundary := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) slot
    have le :=
      (computeStartSlotAtEpoch_le_lt (UInt64.lt_iff_toNat_lt.mpr ctx.positive) boundary).1
    obtain ⟨time, timeOk, -⟩ :=
      exists_timeAtSlotMs_of_le (UInt64.le_iff_toNat_le.mpr le) beginOk
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
    exact ⟨_, rootEpoch, _, time, isAncestor_self_of_blockEpoch rootOk, rootOk, recent,
      boundary, timeOk, from_ _⟩
  · intro epoch _ rootOk
    exact ⟨n, le_rfl, anchor.finalizedCheckpoint.root, rootOk, rootOk,
      isAncestor_self_of_blockEpoch rootOk, Or.inl rfl, from_ _⟩

/-- The root that a call reads satisfies the call invariant at the call.

It also covers every up-to-date honest head from the call to the limit.

The first call reads the anchor's finalized root.

A later call reads the root of the call before it, whose invariant carries over. -/
private theorem carried_facts {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    (earlier : ∀ i' < i, ∀ n' fcr' after',
      CallAt (e := e) u events (getFastConfirmationStore anchor) i' n' fcr' after' →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n' after'.confirmedRoot) :
    CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n fcr.confirmedRoot ∧
      HonestHeadsCover (e := e) fcr.confirmedRoot (e.world n).time (limit + 1) := by
  cases i with
  | zero =>
    obtain ⟨rfl, -⟩ := call_zero ctx.long calls
    exact anchor_facts ctx n (List.mem_of_getElem? calls.1) nBound
  | succ j =>
    obtain ⟨m, before, previous⟩ := callAt_previous calls
    obtain ⟨slot, begin, slotOk, index, beginOk, atSlot⟩ := ctx.atSlots (j + 1) n calls.1
    obtain ⟨oldSlot, -, oldSlotOk, oldIndex, -, -⟩ := ctx.atSlots j m previous.1
    obtain ⟨eventLt, -⟩ := call_order ctx.toCallsCtx previous.1 calls.1 (Nat.lt_succ_self j)
    have nextOk : addChecked oldSlot 1 = .ok slot := addChecked_ok_iff.mpr ⟨by
      have := slot.toNat_lt
      simp only [UInt64.toNat_one]
      omega, by simp only [UInt64.toNat_one]; omega⟩
    have inv := earlier j (Nat.lt_succ_self j) m before fcr previous
    have cover : HonestHeadsCover (e := e) fcr.confirmedRoot (e.world n).time (limit + 1) := by
      rw [atSlot]
      exact inv.1 oldSlot slot begin oldSlotOk nextOk beginOk
    have mBound : (e.world m).time ≤ limit := (e.monotone_time eventLt.le).trans nBound
    obtain ⟨rootEpoch, oldRootOk⟩ := root_known (ctx.toCallsCtx.forward m).reachable ctx.sound
      ctx.anchorSlot ctx.positive ctx.window
      (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller mBound)
      previous.2.2
    have first : ∀ readSlot next following,
        ((e.world n).state u).getCurrentSlot config = .ok readSlot →
        addChecked readSlot 1 = .ok next →
        computeTimeAtSlotMs config genesisTimeMs next = .ok following →
        HonestHeadsCover (e := e) fcr.confirmedRoot following.toNat (limit + 1) := by
      intro readSlot next following readSlotOk readNextOk followingOk
      obtain rfl : readSlot = slot := Except.ok.inj (readSlotOk.symm.trans slotOk)
      obtain ⟨due, dueOk⟩ := ctx.fits.1
      have late := ctx.fits.2 readSlot next begin due following readNextOk beginOk dueOk
        followingOk
      exact honestHeadsCover_mono cover (by omega) le_rfl
    have nowRootOk := getBlockEpoch_of_le eventLt.le oldRootOk
    have readBefore {epoch : Epoch}
        (read : ((e.world n).state u).getBlockEpoch fcr.confirmedRoot = .ok epoch) :
        ((e.world m).state u).getBlockEpoch fcr.confirmedRoot = .ok epoch := by
      obtain rfl : rootEpoch = epoch := Except.ok.inj (nowRootOk.symm.trans read)
      exact oldRootOk
    refine ⟨⟨first, ?_⟩, cover⟩
    by_cases boundary : isStartSlotAtEpoch preset slot = .ok true
    · -- At an epoch start, the kept root is its own historical root, of an earlier epoch.
      have boundaryOk := startSlot_of_isStart ctx.positive boundary
      have old : rootEpoch ≠ computeEpochAtSlot preset slot := by
        intro same
        obtain ⟨block, found, blockEpoch⟩ := found_of_blockEpoch oldRootOk
        have le := (ctx.toCallsCtx.forward m).block_epoch_le_current ctx.slots
          (UInt64.le_of_eq ctx.anchorSlot) oldSlotOk found
        have zero : computeSlotsSinceEpochStart preset slot = .ok 0 := by
          unfold isStartSlotAtEpoch at boundary
          cases offset : computeSlotsSinceEpochStart preset slot with
          | error fault => simp [offset, Except.mapError, bind, Except.bind] at boundary
          | ok offset' =>
            simp [offset, Except.mapError, bind, Except.bind, pure, Except.pure] at boundary
            rw [boundary]
        have lt := UInt64.lt_iff_toNat_lt.mp
          (epoch_lt_of_offset_zero (old := oldSlot) (UInt64.lt_iff_toNat_lt.mpr (by omega)) zero)
        rw [blockEpoch, same] at le
        omega
      constructor
      · intro epoch rootEpoch' epochOk rootOk recent
        obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
        refine ⟨fcr.confirmedRoot, rootEpoch', slot, begin, isAncestor_self_of_blockEpoch rootOk,
          rootOk, recent, boundaryOk, beginOk, ?_⟩
        rw [← atSlot]
        exact cover
      · intro epoch epochOk rootOk
        obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
        exact absurd (Except.ok.inj (nowRootOk.symm.trans rootOk)) old
    · -- Inside an epoch, the previous call's historical root and target origin carry over.
      have notMod : ¬ slot % preset.SLOTS_PER_EPOCH = 0 := by
        intro modZero
        apply boundary
        rw [isStart_eq, Except.ok.injEq, decide_eq_true_eq]
        simpa [UInt64.toNat_mod] using congrArg UInt64.toNat modZero
      have sameEpoch : computeEpochAtSlot preset slot = computeEpochAtSlot preset oldSlot := by
        apply UInt64.toNat_inj.mp
        simp only [computeEpochAtSlot, UInt64.toNat_div]
        exact nextSlot_epoch_of_inside (by omega) notMod
      have epochBefore {epoch : Epoch}
          (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch) :
          ((e.world m).state u).getCurrentStoreEpoch config = .ok epoch := by
        have epochEq := Store.getCurrentStoreEpoch_eq slotOk epochOk
        simp [Store.getCurrentStoreEpoch, oldSlotOk, epochEq, sameEpoch, bind, Except.bind,
          pure, Except.pure]
      constructor
      · intro epoch rootEpoch' epochOk rootOk recent
        obtain ⟨historical, historicalEpoch, epochStart, time, below, historicalOk,
          age, startOk, timeOk, historicalCover⟩ :=
          inv.2.1 epoch rootEpoch' (epochBefore epochOk) (readBefore rootOk) recent
        exact ⟨historical, historicalEpoch, epochStart, time,
          e.isAncestor_of_le eventLt.le below, getBlockEpoch_of_le eventLt.le historicalOk,
          age, startOk, timeOk, historicalCover⟩
      · intro epoch epochOk rootOk
        obtain ⟨k, kLe, origin, -, originOk, below, checked, originCover⟩ :=
          inv.2.2 epoch (epochBefore epochOk) (readBefore rootOk)
        exact ⟨k, kLe.trans eventLt.le, origin, rootOk,
          getBlockEpoch_of_le eventLt.le originOk, e.isAncestor_of_le eventLt.le below,
          checked, originCover⟩

/-! ## The finalized reset of the confirmed root -/

/-- A caller's finalized checkpoint other than the anchor's is old.

Its root's block epoch is at most its epoch.

That epoch is at least two epochs before the current epoch. -/
private theorem finalized_old {Δ : ℕ} {anchor : Store preset fork} {limit : ℕ}
    {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {n : ℕ} (nBound : (e.world n).time ≤ limit)
    (other : ((e.world n).state u).finalizedCheckpoint ≠ anchor.finalizedCheckpoint) :
    ∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ∃ rootEpoch, ((e.world n).state u).getBlockEpoch
          ((e.world n).state u).finalizedCheckpoint.root = .ok rootEpoch ∧
        rootEpoch.toNat ≤ ((e.world n).state u).finalizedCheckpoint.epoch.toNat ∧
        ((e.world n).state u).finalizedCheckpoint.epoch.toNat + 2 ≤ epoch.toNat := by
  intro epoch epochOk
  have forward := e.forwardReachable
    (fun x hx => (ctx.start x hx).symm ▸ Store.ForwardReachable.anchor ctx.anchored) n u
    ctx.caller
  have reached := forward.reachable
  have aligned : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq ctx.anchorSlot
  obtain ⟨anchorRoot, anchorHash, -, -, -, anchorFinal, -⟩ := getForkchoiceStore_anchor ctx.anchored
  -- At or below the anchor epoch the finality is the anchor's.
  have later : getCurrentEpoch anchorState < ((e.world n).state u).finalizedCheckpoint.epoch := by
    refine UInt64.not_le.mp fun atAnchor => other ?_
    obtain ⟨epochEq, rootHash⟩ := reached.finalized_eq_anchor_of_epoch_le atAnchor
    rw [anchorHash, Except.ok.injEq] at rootHash
    rw [anchorFinal]
    cases h : ((e.world n).state u).finalizedCheckpoint
    simp_all
  have lagged := (forward.finalized_add_two_le_or_anchor ctx.sound ctx.slots epochOk).resolve_right
    (UInt64.not_le.mpr later)
  -- Past the anchor epoch the finality is read at a held block of its epoch or before.
  obtain ⟨root, read⟩ := finalized_read reached ctx.sound aligned ctx.positive ctx.window
    (anchorState_hash_nonzero ctx.anchored ctx.start ctx.roots ctx.caller nBound) later
  obtain ⟨block, found, below, -⟩ := Store.getCheckpointBlock_self ctx.preGloas ctx.positive read
  refine ⟨computeEpochAtSlot preset block.slot, ?_, below, lagged⟩
  simp [Store.getBlockEpoch, Store.block_ok_iff.mpr found, bind, Except.bind, pure, Except.pure]

/-- The caller's finalized root satisfies the call invariant.

The anchor's finalized root satisfies it by `anchorFacts`.

Any other finalized root is old, so only its coverage of the next slot remains.

A delay later, each up-to-date honest store has justified its epoch and reads it below its head. -/
private theorem finalized_invariant {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    (good : Good (e := e) horizon limit)
    (anchorFacts : ∀ n ∈ events, (e.world n).time ≤ limit →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
        anchor.finalizedCheckpoint.root ∧
      HonestHeadsCover (e := e) anchor.finalizedCheckpoint.root (e.world n).time (limit + 1))
    {n : ℕ} (member : n ∈ events) (nBound : (e.world n).time ≤ limit) :
    CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
      ((e.world n).state u).finalizedCheckpoint.root := by
  by_cases same : ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint
  · rw [same]
    exact (anchorFacts n member nBound).1
  have old := finalized_old ctx nBound same
  refine ⟨?_, ?_, ?_⟩
  · intro slot next following slotOk nextOk followingOk earlier afterNext beforeEnd a honest i
      hd timeEq upToDate headOk
    -- The call is at its slot start, a delay before the following slot.
    obtain ⟨index, indexOk⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨slot', begin, slotOk', -, beginOk, atSlot⟩ := ctx.atSlots index n indexOk
    have sameSlot : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
    subst sameSlot
    obtain ⟨due, dueOk⟩ := ctx.fits.1
    have bound := ctx.fits.2 slot' next begin due following nextOk beginOk dueOk followingOk
    have late : (e.world n).time + Δ ≤ (e.world i).time := by omega
    have iBound : (e.world i).time ≤ limit := by omega
    -- The receiver has justified the caller's finalized epoch.
    have le := finalizedOrder ctx.sync ctx.slots ctx.positive ctx.window ctx.preGloas
      ctx.admitted ctx.anchored ctx.sound ctx.anchorSlot ctx.start ctx.roots good.blocks
      good.finality ctx.caller honest late iBound upToDate
    -- The receiver reads that finality below its justified root.
    have read := good.finality u ctx.caller a honest n i nBound iBound le
    obtain ⟨-, finalBlock, -, finalFound, -, below⟩ :=
      Store.isAncestor_of_getCheckpointBlock ctx.preGloas read
    have headDescends := Store.isAncestor_getHead headOk
    obtain ⟨justifiedBlock, justifiedFound⟩ := Store.held_of_isAncestor headDescends
    exact Store.isAncestor_trans_of_lt ctx.preGloas justifiedFound finalFound headDescends below
  · intro epoch rootEpoch epochOk rootOk recent
    obtain ⟨other, otherOk, low, lagged⟩ := old epoch epochOk
    rw [rootOk, Except.ok.injEq] at otherOk
    subst otherOk
    omega
  · intro epoch epochOk rootOk
    obtain ⟨other, otherOk, low, lagged⟩ := old epoch epochOk
    rw [rootOk, Except.ok.injEq] at otherOk
    subst otherOk
    omega

/-- A checked walk from the caller's finalized root makes it the anchor's finalized checkpoint.

The walk's start is in the current epoch or the one before.

Any other finalized root is at least two epochs old. -/
private theorem finalized_start_anchor {Δ : ℕ}
    {anchor : Store preset fork} {limit : ℕ} {horizon anchorEpoch : Epoch}
    {g : ForkedBeaconState preset} {pre : Run config checks g ⟨fork, anchorState⟩}
    {u : ValidatorIndex} {events : List ℕ} {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {n : ℕ} (nBound : (e.world n).time ≤ limit)
    {fcr' : FastConfirmationStore} {head root : Root}
    (checked : ((e.world n).state u).FastConfirmationChecked config fcr' head
      ((e.world n).state u).finalizedCheckpoint.root root) :
    ((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint := by
  by_contra other
  obtain ⟨epoch, -, -, startEpoch, epochOk, -, -, startOk, recent, -⟩ := checked
  obtain ⟨blockEpoch, blockOk, low, lagged⟩ := finalized_old ctx nBound other epoch epochOk
  rw [startOk, Except.ok.injEq] at blockOk
  subst blockOk
  omega

/-- At a call that replaces its base, the observed justified checkpoint covers honest heads.

Its block is on every up-to-date honest head from the call to `limit`.

It keeps the call invariant, or one of the evidence alternatives holds.

The first call observes the anchor's finalized checkpoint, whose facts are given.

A later call observes an earlier call's unrealized justified checkpoint, of the epoch before.

A receiver's justified checkpoint of that epoch is the observed one.

A later one has an honest signer, which puts it above the observed block. -/
private theorem observed_facts [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    (good : Good (e := e) horizon limit)
    (anchorFacts : ∀ n ∈ events, (e.world n).time ≤ limit →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
          anchor.finalizedCheckpoint.root ∧
        HonestHeadsCover (e := e) anchor.finalizedCheckpoint.root (e.world n).time (limit + 1))
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head base : Root} {slot : Slot}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (replaces : ((e.world n).state u).ReplacesBase config after head base slot) :
    (CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
        after.currentEpochObservedJustifiedCheckpoint.root ∧
      HonestHeadsCover (e := e) after.currentEpochObservedJustifiedCheckpoint.root
        (e.world n).time (limit + 1)) ∨
    Bad (e := e) pre limit := by
  cases i with
  | zero =>
    -- The first call observes the anchor's finalized checkpoint.
    left
    rw [(call_zero ctx.long calls).2]
    exact anchorFacts n (List.mem_of_getElem? calls.1) nBound
  | succ j =>
    obtain ⟨m, -, mBefore, observed, epochSucc, horizonLe, rest⟩ := observedStart pre
      ctx.toCallsCtx ctx.sync ctx.admitted ctx.fits ctx.bounded (.inl good.agree)
      (.inl good.finality) calls nBound slotOk replaces
    rcases rest with ⟨-, later⟩ | collision | justified | direct
    rotate_left
    · exact .inr (.inl collision)
    · exact .inr (.inr (.inr (.inr (.inl justified))))
    · exact .inr (.inr (.inr (.inl direct)))
    by_cases collision : HonestCollision (e := e) limit
    · exact .inr (.inl collision)
    left
    rw [← observed] at epochSucc horizonLe later
    have mTime : (e.world m).time ≤ limit := by omega
    obtain ⟨slot', begin, slotOk', slotEq, beginOk, timeEq⟩ := ctx.atSlots (j + 1) n calls.1
    rw [slotOk, Except.ok.injEq] at slotOk'
    subst slot'
    have slotMod : slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have isStart := replaces.1
      rw [isStart_eq, Except.ok.injEq, decide_eq_true_eq] at isStart
      exact isStart
    obtain ⟨-, ⟨observedBlock, epoch, foundBlock, epochOk, epochAdd⟩, -, -⟩ := replaces
    have callerHeld := Store.block_ok_iff.mp foundBlock
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
    have observedNat := (addChecked_ok_iff.mp epochAdd).2
    simp only [UInt64.toNat_one] at observedNat
    have slotEpochNat : (computeEpochAtSlot preset slot).toNat =
        slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simp only [computeEpochAtSlot, UInt64.toNat_div]
    have blockEpochNat : (computeEpochAtSlot preset observedBlock.slot).toNat =
        observedBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simp only [computeEpochAtSlot, UInt64.toNat_div]
    -- The observed block is of the epoch before the call's, so before the call slot.
    have blockLe : observedBlock.slot ≤ slot := by
      apply UInt64.le_iff_toNat_le.mpr
      have lt : observedBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat <
          slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by omega
      exact Nat.le_of_lt (Nat.lt_of_div_lt_div lt)
    -- The call slot starts its epoch.
    have callSlotOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) =
        .ok slot := by
      apply computeStartSlotAtEpoch_ok_iff.mpr
      have eq : slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat =
          slot.toNat := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero slotMod)
      rw [slotEpochNat, eq]
      exact ⟨slot.toNat_lt, rfl⟩
    -- The anchor's justified epoch is before the call's.
    obtain ⟨anchorRoot, -, -, -, anchorJustified, -⟩ := getForkchoiceStore_anchor ctx.anchored
    have anchorEq : anchorEpoch = getCurrentEpoch anchorState := by
      rw [← ctx.anchorEpochOk, anchorJustified]
    have anchorNat : anchorEpoch.toNat < (computeEpochAtSlot preset slot).toNat := by
      have before := UInt64.lt_iff_toNat_lt.mp ctx.anchorEpochBefore
      rw [anchorEq]
      simp only [computeEpochAtSlot, UInt64.toNat_div] at before ⊢
      have : firstSlot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
          slot.toNat / preset.SLOTS_PER_EPOCH.toNat := Nat.div_le_div_right (by omega)
      omega
    have forward := e.forwardReachable
      (fun a ha => (ctx.start a ha) ▸ Store.ForwardReachable.anchor ctx.anchored)
    -- Coverage, by induction on the time.
    have cover : ∀ T, T ≤ limit + 1 → HonestHeadsCover (e := e)
        after.currentEpochObservedJustifiedCheckpoint.root (e.world n).time T := by
      intro T
      induction T with
      | zero => intro _ earlier _ high; omega
      | succ T ih =>
        intro bound earlier low high w receiver k hd atTime upToDate headOk
        by_cases before : earlier < T
        · exact ih (by omega) earlier low before w receiver k hd atTime upToDate headOk
        have same : earlier = T := by omega
        subst same
        have covers := ih (by omega)
        have kLow : (e.world n).time ≤ (e.world k).time := by omega
        have kHigh : (e.world k).time ≤ limit := by omega
        have headAbove := Store.isAncestor_getHead headOk
        have lower := later w receiver k kLow kHigh upToDate
        by_cases sameEpoch : after.currentEpochObservedJustifiedCheckpoint.epoch =
            ((e.world k).state w).justifiedCheckpoint.epoch
        · -- The same epoch: the justified checkpoint is the observed one.
          have eq := good.agree u ctx.caller w receiver m k mTime kHigh _ _ (.inr observed)
            (.inl rfl) sameEpoch horizonLe
          rw [eq]
          exact headAbove
        -- A later epoch: the justified block descends from the observed one, by its signer.
        have laterEpoch : (computeEpochAtSlot preset slot).toNat ≤
            ((e.world k).state w).justifiedCheckpoint.epoch.toNat := by
          have le := UInt64.le_iff_toNat_le.mp lower
          have ne : after.currentEpochObservedJustifiedCheckpoint.epoch.toNat ≠
              ((e.world k).state w).justifiedCheckpoint.epoch.toNat :=
            fun h => sameEpoch (UInt64.toNat_inj.mp h)
          omega
        have early : slot.toNat ≤
            ((e.world k).state w).justifiedCheckpoint.epoch.toNat *
              preset.SLOTS_PER_EPOCH.toNat := by
          have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat laterEpoch
          have := (computeStartSlotAtEpoch_ok_iff.mp callSlotOk).2
          omega
        obtain ⟨current, currentOk, _, _⟩ :=
          (forward k w receiver).slots_le_current ctx.slots (UInt64.le_of_eq ctx.anchorSlot)
        obtain ⟨v, honest, _, -, msg, sent, data, member, target, before⟩ := ctx.signedAll w
          receiver k current (Nat.zero_le _) kHigh upToDate currentOk
          (UInt64.lt_iff_toNat_lt.mpr (by omega))
        obtain ⟨k', -, duty⟩ := e.exists_maySign_of_signed sent member honest
        -- The signer's duty is in the justified epoch, so at or after the call's slot.
        have dutyCopy := duty
        obtain ⟨_, -, -, -, -, made, -⟩ := dutyCopy
        obtain ⟨_, _, _, _, -, -, -, -, dataOk⟩ := made
        have slotLe : slot ≤ data.slot := by
          rw [← target, target_epoch_eq_of_getAttestationData dataOk] at early
          simp only [computeEpochAtSlot, UInt64.toNat_div] at early
          have := Nat.div_mul_le_self data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
          exact UInt64.le_iff_toNat_le.mpr (by omega)
        obtain ⟨low', high'⟩ := duty_window_of_slot_le ctx.start ctx.fits beginOk receiver
          upToDate currentOk honest duty slotLe before
        obtain ⟨justifiedBlock, justifiedKnown⟩ := Store.held_of_isAncestor headAbove
        have descends := (justified_descends_of_duty ctx.anchored ctx.start ctx.anchorSlot
          ctx.anchorBoundary ctx.preGloas ctx.roots ctx.caller callerHeld nBound covers
          (by omega) receiver atTime ⟨justifiedBlock, justifiedKnown⟩
          ((UInt64.le_iff_toNat_le.mp blockLe).trans early) honest duty target (by omega)
          high').resolve_right collision
        obtain ⟨rootBlock, rootKnown⟩ := Store.held_of_isAncestor descends
        exact Store.isAncestor_trans_of_lt ctx.preGloas justifiedKnown rootKnown headAbove
          descends
    have coverAll := cover (limit + 1) le_rfl
    refine ⟨⟨?_, ?_, ?_⟩, coverAll⟩
    · -- From the next slot.
      intro slot2 next following slotOk2 nextOk followingOk
      rw [slotOk, Except.ok.injEq] at slotOk2
      subst slot2
      have nextNat := (addChecked_ok_iff.mp nextOk).2
      simp only [UInt64.toNat_one] at nextNat
      obtain ⟨start', startOk', -, startLe⟩ := exists_timeAtSlotMs_of_le
        (UInt64.le_iff_toNat_le.mpr (by omega) : slot ≤ next) followingOk
      rw [beginOk, Except.ok.injEq] at startOk'
      subst start'
      have := UInt64.le_iff_toNat_le.mp startLe
      intro earlier low high
      exact coverAll earlier (by omega) high
    · -- The observed block is its own recent historical root, covered from the epoch start.
      intro epoch rootEpoch epochOk2 rootEpochOk near
      obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk2
      refine ⟨_, rootEpoch, slot, begin,
        Store.isAncestor_self (node := ⟨after.currentEpochObservedJustifiedCheckpoint.root,
          .pending⟩) callerHeld, rootEpochOk, near, callSlotOk, beginOk, ?_⟩
      rw [← timeEq]
      exact coverAll
    · -- The observed block is not of the current epoch.
      intro epoch epochOk2 rootEpochOk
      exfalso
      obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk2
      obtain ⟨found, foundHeld, rootEq⟩ := found_of_blockEpoch rootEpochOk
      rw [callerHeld, Option.some.injEq] at foundHeld
      subst foundHeld
      have := congrArg UInt64.toNat rootEq
      omega

/-- The checkpoint inputs of a call that confirms a walked root.

The call's count bounds give its reserved count off the epoch's first slot.

The start's checked target, covered up to `limit + 1`, is covered up to the next instant.

At the epoch's first slot the root is of an earlier epoch, as none of that epoch is confirmed.

The call is at or after the first slot, so its epoch is at least two and after the anchor's. -/
private theorem walk_inputs [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot : Slot} {start : Root} {source : BeaconState preset fork}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (selects : ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot
      start)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root start
      after.confirmedRoot)
    (sourceOk : ((e.world n).state u).checkpointState
      after.currentEpochObservedJustifiedCheckpoint = .ok source)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later))
    (confirmedAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ((e.world n).state u).isOneConfirmed config head.root source
        (((e.world n).state u).tallyVotes source) member = .ok true)
    (obligations : CallObligations (e := e) 0 limit u n fcr after)
    (startInv : CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start) :
    CallCheckpointInputs (e := e) 0 anchor.finalizedCheckpoint.root u n after head start
      after.confirmedRoot := by
  obtain ⟨rootBlock, -, rootFound, -, -⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots (member := after.confirmedRoot) walked (by simp)
      (by simp)
  have headAbove := (Store.parentRoot_of_getAncestorRoots walked rootFound).2.1
  have forward := e.forwardReachable
    (fun x hx => (ctx.start x hx).symm ▸ Store.ForwardReachable.anchor ctx.anchored) n u
    ctx.caller
  refine ⟨checked, headAbove, ?_, ?_, ?_, ?_⟩
  · -- The count bounds give the honest count.
    intro slot' slotOk' inside pulled anc fin target pulledOk targetOk ancOk finOk finAnchor
    have bounds := (obligations head slot start source chain later headOk slotOk selects
      sourceOk walked).2.1 slot' pulled anc fin target slotOk' inside pulledOk targetOk ancOk
      finOk finAnchor
    have maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := by
      have := ctx.exitWindow.lookahead
      omega
    exact Execution.honestTargetVotes_of_byzantineStakeAtMost ctx.anchored ctx.start
      (UInt64.le_of_eq ctx.anchorSlot) ctx.sound ctx.maxAligned ctx.slots ctx.preGloas
      ctx.minLookahead maxLookahead (by have := ctx.ring; omega) ctx.stale ctx.increment ctx.caller
      nBound ⟨head, headOk, rfl⟩ bounds
  · -- The start's checked target is covered up to `limit + 1`, so up to the next instant.
    intro epoch currentOk startOk
    obtain ⟨k, before, origin, rootOk, originOk, below, checkedOrigin, cover⟩ :=
      startInv.2.2 epoch currentOk startOk
    exact ⟨k, before, origin, rootOk, originOk, below, checkedOrigin,
      honestHeadsCover_mono cover le_rfl (by omega)⟩
  · -- At an epoch start no walked root of the current epoch is one-confirmed.
    intro slot' epoch rootEpoch slotOk' boundary currentOk rootOk same
    have sameSlot : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
    subst slot'
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk currentOk
    subst rootEpoch
    have inside := not_start_of_confirmed forward ctx.slots
      (UInt64.le_of_eq ctx.anchorSlot) slotOk rootOk (confirmedAll _ (by simp))
    rw [boundary] at inside
    cases inside
  · -- Each call is at or after the first slot, so in epoch 2 or later and after the anchor's.
    intro epoch currentOk
    obtain ⟨slot', -, slotOk', index, -, -⟩ := ctx.atSlots i n calls.1
    have sameSlot : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
    subst slot'
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk currentOk
    have mono : (computeEpochAtSlot preset firstSlot).toNat ≤
        (computeEpochAtSlot preset slot).toNat := by
      simp only [computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right (by omega)
    have two := UInt64.le_iff_toNat_le.mp ctx.confirmationEpoch
    have before := UInt64.lt_iff_toNat_lt.mp ctx.anchorEpochBefore
    refine ⟨UInt64.lt_iff_toNat_lt.mpr ?_, UInt64.lt_iff_toNat_lt.mpr (by omega)⟩
    simp only [GENESIS_EPOCH, UInt64.toNat_add, UInt64.toNat_zero, UInt64.toNat_one] at two ⊢
    simp only [UInt64.toNat_ofNat] at two
    omega

/-- A call that confirms a walked root keeps the call invariant for that root.

The root covers honest heads from the call on, so from the next slot's start.

The start's recent historical root is below the root too, since the start is below it.

For a root of the current epoch, the start's checked origin serves if the start is of that epoch.

Otherwise the root is its own origin, checked by this call. -/
private theorem walk_invariant [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    {head : ForkChoiceNode} {slot : Slot} {start : Root} {source : BeaconState preset fork}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root start
      after.confirmedRoot)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later))
    (confirmedAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ((e.world n).state u).isOneConfirmed config head.root source
        (((e.world n).state u).tallyVotes source) member = .ok true)
    (startInv : CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start)
    (inputs : CallCheckpointInputs (e := e) 0 anchor.finalizedCheckpoint.root u n after head
      start after.confirmedRoot)
    (rootCovers : HonestHeadsCover (e := e) after.confirmedRoot (e.world n).time (limit + 1)) :
    CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n after.confirmedRoot := by
  obtain ⟨epoch, slot', rootEpoch, startEpoch, epochOk, slotOk', rootEpochOk, startEpochOk,
    recent, cases⟩ := checked
  have sameSlot : slot' = slot := Except.ok.inj (slotOk'.symm.trans slotOk)
  subst slot'
  obtain rfl := Store.getCurrentStoreEpoch_eq slotOk epochOk
  have rootAbove := Store.isAncestor_terminal_of_getAncestorRoots walked
    (by simp : after.confirmedRoot ∈ chain ++ after.confirmedRoot :: later)
  obtain ⟨startBlock, startHeld, -⟩ := found_of_blockEpoch startEpochOk
  have member : n ∈ events := List.mem_of_getElem? calls.1
  obtain ⟨callSlot, begin, callSlotOk, -, beginOk, atSlot⟩ := ctx.atSlots i n calls.1
  have sameCall : callSlot = slot := Except.ok.inj (callSlotOk.symm.trans slotOk)
  subst callSlot
  refine ⟨?_, ?_, ?_⟩
  · -- The root covers from the call on, so from the next slot's start.
    intro readSlot next following readOk nextOk followingOk
    have sameRead : readSlot = slot := Except.ok.inj (readOk.symm.trans slotOk)
    subst readSlot
    have nextNat := (addChecked_ok_iff.mp nextOk).2
    obtain ⟨time, timeOk, -, timeLe⟩ := exists_timeAtSlotMs_of_le (slot := slot) (last := next)
      (UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.toNat_one] at nextNat; omega))
      followingOk
    obtain rfl : time = begin := Except.ok.inj (timeOk.symm.trans beginOk)
    exact honestHeadsCover_mono rootCovers
      (by rw [atSlot]; exact UInt64.le_iff_toNat_le.mp timeLe) le_rfl
  · -- The start's historical root is below the root too.
    intro epoch readRootEpoch currentOk readRootOk _
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk currentOk
    obtain ⟨historical, historicalEpoch, epochStart, epochStartTime, above, historicalOk,
      historicalRecent, epochStartOk, epochStartTimeOk, cover⟩ :=
      startInv.2.1 _ startEpoch currentOk startEpochOk recent
    obtain ⟨_, found, -⟩ := found_of_blockEpoch historicalOk
    exact ⟨historical, historicalEpoch, epochStart, epochStartTime,
      Store.isAncestor_trans_of_lt ctx.preGloas startHeld found rootAbove above,
      historicalOk, historicalRecent, epochStartOk, epochStartTimeOk, cover⟩
  · intro epoch currentOk readRootOk
    obtain rfl := Store.getCurrentStoreEpoch_eq slotOk currentOk
    have rootSame : rootEpoch = computeEpochAtSlot preset slot :=
      Except.ok.inj (rootEpochOk.symm.trans readRootOk)
    by_cases startSame : startEpoch = computeEpochAtSlot preset slot
    · -- The start's checked origin is below the root.
      obtain ⟨k, before, origin, -, originOk, below, checkedOrigin, cover⟩ :=
        startInv.2.2 _ currentOk (startSame ▸ startEpochOk)
      obtain ⟨_, found, -⟩ := found_of_blockEpoch originOk
      exact ⟨k, before, origin, readRootOk, originOk,
        Store.isAncestor_trans_of_lt ctx.preGloas startHeld found rootAbove below,
        checkedOrigin, cover⟩
    · -- The root itself is the origin, checked by this call.
      have target : ((e.world n).state u).willCurrentTargetBeJustified config head.root =
          .ok true := by
        rcases cases with old | current
        · exact False.elim (old.2.1 rootSame)
        · exact current.2.1 rootSame startSame
      have forward := e.forwardReachable
        (fun x hx => (ctx.start x hx).symm ▸ Store.ForwardReachable.anchor ctx.anchored) n u
        ctx.caller
      have inside := not_start_of_confirmed forward ctx.slots
        (UInt64.le_of_eq ctx.anchorSlot) slotOk readRootOk (confirmedAll _ (by simp))
      obtain ⟨_, found, -⟩ := found_of_blockEpoch readRootOk
      exact ⟨n, le_rfl, after.confirmedRoot, readRootOk, readRootOk,
        Store.isAncestor_self found,
        Or.inr ⟨head, ctx.upToDate n member, currentOk, headOk, target, inputs.2.1,
          inputs.2.2.1 slot slotOk inside, slot, begin, slotOk, beginOk, atSlot⟩, rootCovers⟩

/-- The root that a confirming call stores, read from its accepted walk, is held from the call.

Every up-to-date honest store holds it from the call to `limit`, or evidence appears.

It needs the call's realized guard, and the source window's reserve over the adversary. -/
private theorem walk_holds [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot : Slot} {start : Root} {source : BeaconState preset fork}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (selects : ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot
      start)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root start
      after.confirmedRoot)
    (sourceOk : ((e.world n).state u).checkpointState
      after.currentEpochObservedJustifiedCheckpoint = .ok source)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later))
    (confirmedAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ((e.world n).state u).isOneConfirmed config head.root source
        (((e.world n).state u).tallyVotes source) member = .ok true)
    (obligations : CallObligations (e := e) 0 limit u n fcr after) :
    HonestHoldsFrom (e := e) after.confirmedRoot (e.world n).time limit ∨
      Bad (e := e) pre limit := by
  have rootMem : after.confirmedRoot ∈ chain ++ [after.confirmedRoot] := by simp
  have rootWalked : after.confirmedRoot ∈ chain ++ after.confirmedRoot :: later := by simp
  have current := ctx.upToDate n (List.mem_of_getElem? calls.1)
  -- The root's realized post-state, from the call's realized guard.
  obtain ⟨-, -, realized, -, members⟩ :=
    obligations head slot start source chain later headOk slotOk selects sourceOk walked
  obtain ⟨block, rootState, blockFound, stateFound, recent⟩ := realized _ rootMem
  have blockOk := Store.block_ok_iff.mpr blockFound
  -- The call's time is the start of its slot.
  obtain ⟨callSlot, begin, callSlotOk, -, beginOk, timeEq⟩ := ctx.atSlots i n calls.1
  rw [slotOk, Except.ok.injEq] at callSlotOk
  subst callSlot
  -- The caller's store is reachable, with a forward clock.
  have forwardWith := e.forwardReachableWith
    (fun a ha => (ctx.start a ha) ▸ Store.ForwardReachableWith.anchor ctx.anchored) n u
    ctx.caller
  have reached := forwardWith.reachable
  have anchorLe : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq ctx.anchorSlot
  -- The root is above the start, and the call is at most one epoch after the start.
  obtain ⟨rootBlock, startBlock, rootBlockOk, startBlockOk, aboveStart⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots walked (by simp) rootWalked
  rw [blockOk, Except.ok.injEq] at rootBlockOk
  subst rootBlock
  obtain ⟨epoch, checkedSlot, rootEpoch, startEpoch, epochOk, checkedSlotOk, -, startEpochOk,
    epochLe, -⟩ := checked
  have epochEq : computeEpochAtSlot preset slot = epoch :=
    (Store.getCurrentStoreEpoch_eq slotOk epochOk).symm
  have startEpochEq : computeEpochAtSlot preset startBlock.slot = startEpoch := by
    simpa [Store.getBlockEpoch, startBlockOk, bind, Except.bind, pure, Except.pure] using
      startEpochOk
  subst epochEq startEpochEq
  have startRoot := epoch_le_of_slot_le (preset := preset) startBlock.slot block.slot
    (UInt64.lt_iff_toNat_lt.mp aboveStart).le
  have callNear : (computeEpochAtSlot preset slot).toNat ≤
      (computeEpochAtSlot preset block.slot).toNat + 1 := by
    omega
  have recency : (computeEpochAtSlot preset slot).toNat ≤
      rootState.currentJustifiedCheckpoint.epoch.toNat + 2 := by
    omega
  -- The terms of the root's one-confirmation.
  have confirmed := confirmedAll _ rootMem
  obtain ⟨support, threshold, supportOk, thresholdOk, -⟩ :=
    Store.isOneConfirmed_eq_ok_true_iff.mp confirmed
  obtain ⟨readSlot, readBlock, parent, boost, first, last, maximum, discount, adversary,
    readSlotOk, readBlockOk, parentOk, boostOk, firstOk, lastOk, maximumOk, discountOk,
    adversaryOk⟩ := Store.computeSafetyThreshold_eq_ok thresholdOk
  rw [slotOk, Except.ok.injEq] at readSlotOk
  subst readSlot
  rw [blockOk, Except.ok.injEq] at readBlockOk
  subst readBlock
  obtain ⟨beforeBlock, parentParticipants, -, beforeOk, parentParticipantsOk, -, -⟩ :=
    Store.exists_stake_parentVotersOf_of_computeEmptySlotSupportDiscount blockOk parentOk
      firstOk discountOk
  -- The source window's reserve, at the reference store.
  obtain ⟨shift, -, -, reserveAll, -, -⟩ := members _ rootMem block parent first last
    beforeBlock boost maximum support discount adversary parentParticipants blockOk parentOk
    boostOk firstOk lastOk beforeOk maximumOk parentParticipantsOk supportOk discountOk
    adversaryOk
  obtain ⟨x, xJ, m, referenceSlot, finish, limitLe, xCurrent, referenceOk, finishOk⟩ :=
    ctx.reference
  have reserve := reserveAll x xJ m referenceSlot finish limitLe xCurrent referenceOk finishOk
  -- The reference store's last slot is no earlier than the call's.
  have lastLe : last ≤ finish := e.previousSlot_le_of_time_le ctx.start ctx.caller xJ
    (by omega) xCurrent slotOk referenceOk lastOk finishOk
  -- The range of the adversary and its committees.
  have lower := reached.parentsBelow anchorLe (ctx.absent u ctx.caller n nBound)
    after.confirmedRoot block parent blockFound (Store.block_ok_iff.mp parentOk)
  obtain ⟨startSlot, firstLe, startLe, startEpochLe, rangeOk⟩ :=
    Store.adversaryRange_start slotOk blockOk parentOk firstOk lastOk lower adversaryOk
  obtain ⟨weight, equivocation, -, equivocationOk⟩ :=
    Store.computeAdversarialWeight_eq_ok rangeOk
  obtain ⟨participants, participantsOk, -⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  have byzantine : ByzantineStakeAtMost (fun v => balanceAt source v.toNat)
      (Store.activeMembers source participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100 := by
    by_cases ordered : startSlot ≤ last
    · exact ⟨by norm_num, le_trans (Nat.le_add_right _ _)
        (reserve startSlot last participants firstLe ordered lastLe participantsOk)⟩
    · have empty : last < startSlot := by
        rw [UInt64.lt_iff_toNat_lt]
        rw [UInt64.le_iff_toNat_le] at ordered
        omega
      rw [Store.getCommitteesBetweenSlots_of_gt empty, Except.ok.injEq] at participantsOk
      subst participants
      have none : Store.activeMembers source ∅ = ∅ := by
        simp [Store.activeMembers]
      refine ⟨by norm_num, ?_⟩
      rw [none]
      simp [stake_empty]
  -- Lemmas 4 and 3: the honest supporters of the root carry positive stake.
  have descends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩
      ⟨after.confirmedRoot, .pending⟩ = .ok true :=
    (Store.parentRoot_of_getAncestorRoots walked blockOk).2.1
  have inside := forwardWith.supportersOf_mem_committees_of_near (balanceSource := source) anchorLe
    ctx.minLookahead (by have := ctx.exitWindow.lookahead; omega)
    (by have := ctx.ring; omega) slotOk blockOk startLe lastOk descends (by omega)
    participantsOk
  have noEquivocator : ∀ w ∈ J, ∀ v ∈ (e.start w).equivocatingIndices, v ∉ J := by
    intro w hw v member
    rw [ctx.start w hw, Store.getForkchoiceStore_equivocatingIndices ctx.anchored] at member
    simp at member
  have positive := e.lt_two_mul_honest_supportersOf_of_isOneConfirmed ctx.slots noEquivocator n
    ctx.caller (BeaconState.registryWithinLimit_of_lt ctx.preGloas source) slotOk blockOk
    parentOk boostOk firstOk lastOk maximumOk discountOk adversaryOk rangeOk participantsOk
    confirmed inside (reached.checkpointState_aligned ctx.sound ctx.maxAligned sourceOk)
    ctx.increment byzantine
  obtain ⟨readSlot, readSlotOk, blocksLe, -⟩ :=
    forwardWith.forwardReachable.slots_le_current ctx.slots anchorLe
  rw [slotOk, Except.ok.injEq] at readSlotOk
  subst readSlot
  have discountLe := UInt64.le_iff_toNat_le.mp
    (Store.computeEmptySlotSupportDiscount_le blockOk parentOk firstOk lastOk maximumOk
      discountOk (blocksLe _ _ blockFound))
  obtain ⟨v, supporter, honest⟩ : ∃ v ∈ ((e.world n).state u).supportersOf source
      ⟨after.confirmedRoot, .pending⟩, v ∈ J := by
    by_contra absent
    have empty : {v ∈ ((e.world n).state u).supportersOf source
        ⟨after.confirmedRoot, .pending⟩ | v ∈ J} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v member
      exact absent ⟨v, (Finset.mem_filter.mp member).1, (Finset.mem_filter.mp member).2⟩
    rw [empty, stake_empty] at positive
    omega
  -- The supporter's vote is a sent honest statement before the call slot, for a descendant.
  have vote : ∃ v ∈ J, ∃ k, (e.world k).time ≤ (e.world n).time ∧ ∃ m ∈ (e.world k).sent,
      ∃ data, (v, data) ∈ statements config checks anchorState anchorBlock m ∧
        data.slot < slot ∧
        ((e.world n).state u).isAncestor ⟨data.beaconBlockRoot, .pending⟩
          ⟨after.confirmedRoot, .pending⟩ = .ok true := by
    obtain ⟨message, supported, latest, -, supportedOk, voteDescends⟩ :=
      ((e.world n).state u).exists_of_voteCountsFor
        (Store.voteCountsFor_of_mem_supportersOf supporter)
    obtain ⟨attestation, sentMessage, inView, messageEq, signed, origin⟩ :=
      e.exists_signed_origin_of_latestMessages ctx.anchored ctx.start ctx.caller latest
    subst messageEq
    rw [Store.getSupportedNode_of_lt ctx.preGloas, Except.ok.injEq] at supportedOk
    subst supportedOk
    obtain ⟨readSlot, readSlotOk, past⟩ := origin.past
    rw [slotOk, Except.ok.injEq] at readSlotOk
    subst readSlot
    exact ⟨v, honest, n, le_rfl, sentMessage, e.view_subset_sent n u inView, attestation.data,
      signed, past, voteDescends⟩
  rcases Execution.rootHeld_of_honest_vote pre ctx.sync ctx.slots ctx.preGloas ctx.fits
      ctx.admitted ctx.prompt ctx.anchored ctx.sound ctx.anchorSlot
      ctx.anchorBoundary ctx.start ctx.bounded ctx.roots ctx.absent ctx.parameters ctx.genesis
      ctx.heldEarly ctx.enough ctx.terminal ctx.caller beginOk timeEq nBound blockFound
      stateFound recency vote with
    holds | collision | evidence
  · exact .inl holds
  · exact .inr (.inl collision)
  · exact .inr (.inr (.inr (.inr (.inr evidence))))

/-- The block parent of a root in a store, or the root itself when the store lacks it. -/
private def parentOrSelf (store : Store preset fork) (r : Root) : Root :=
  match store.block r with
  | .ok b => b.parentRoot
  | .error _ => r

/-- In a walk from a head down to a start, each member's parent is the member before it.

The first member's parent is the start. -/
private theorem parentOrSelf_of_walk {store : Store preset fork} {head start : Root}
    {members later : List Root}
    (walked : store.getAncestorRoots head start = .ok (members ++ later)) :
    ∀ i (h : i < members.length), parentOrSelf store members[i] =
      if _ : i = 0 then start else members[i - 1]'(by omega) := by
  intro i h
  have inAll : i < (members ++ later).length := by simp; omega
  have get : (members ++ later)[i] = members[i] := List.getElem_append_left h
  obtain ⟨b, -, found, -, -⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots walked (by simp) (List.getElem_mem inAll)
  have split : store.getAncestorRoots head start = .ok ((members ++ later).take i ++
      (members ++ later)[i] :: (members ++ later).drop (i + 1)) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
    exact walked
  rw [← get, show parentOrSelf store (members ++ later)[i] = b.parentRoot by
    simp [parentOrSelf, found], (Store.parentRoot_of_getAncestorRoots split found).1]
  rcases i with _ | j
  · simp
  · have hj : j < members.length := by omega
    simp [List.getLast?_take, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

/-- The last root of a walk's prefix descends from every member of that prefix. -/
private theorem root_descends_of_walk {store : Store preset fork} {head start root m : Root}
    {chain later : List Root}
    (walked : store.getAncestorRoots head start = .ok (chain ++ root :: later))
    (mem : m ∈ chain ++ [root]) :
    store.isAncestor ⟨root, .pending⟩ ⟨m, .pending⟩ = .ok true := by
  obtain ⟨rootBlock, -, rootFound, -, -⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots (member := root) walked (by simp) (by simp)
  rcases List.mem_append.mp mem with inChain | isRoot
  · obtain ⟨s, t, rfl⟩ := List.append_of_mem inChain
    have sub := Store.getAncestorRoots_of_append (older := s) (newer := t ++ root :: later)
      (by simpa using walked)
    exact (Store.parentRoot_of_getAncestorRoots (older := t) (newer := later) sub rootFound).2.2
  · rw [List.mem_singleton.mp isRoot]
    exact Store.isAncestor_self (Store.block_ok_iff.mp rootFound)

/-- Every member of an accepted walk is covered by honest heads from the call to the horizon.

Otherwise one of the five evidence alternatives holds.

The confirmed root is viable at each time it is covered, and each member below it then is too.

An induction on time and along the walk covers the members one by one. -/
private theorem walkMembers_cover [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    {pre : Run config checks g ⟨fork, anchorState⟩} {u : ValidatorIndex} {events : List ℕ}
    {firstSlot : Slot}
    (ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot)
    (good : Good (e := e) horizon limit)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {slot : Slot} {start : Root} {source : BeaconState preset fork}
    {chain later : List Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (selects : ((e.world n).state u).SelectsStart config after fcr.confirmedRoot head.root slot
      start)
    (checked : ((e.world n).state u).FastConfirmationChecked config after head.root start
      after.confirmedRoot)
    (sourceOk : ((e.world n).state u).checkpointState
      after.currentEpochObservedJustifiedCheckpoint = .ok source)
    (walked : ((e.world n).state u).getAncestorRoots head.root start =
      .ok (chain ++ after.confirmedRoot :: later))
    (confirmedAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ((e.world n).state u).isOneConfirmed config head.root source
        (((e.world n).state u).tallyVotes source) member = .ok true)
    (obligations : CallObligations (e := e) 0 limit u n fcr after)
    (startInv : CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start)
    (startCovers : HonestHeadsCover (e := e) start (e.world n).time (limit + 1))
    (inputs : CallCheckpointInputs (e := e) 0 anchor.finalizedCheckpoint.root u n after head
      start after.confirmedRoot)
    (holds : HonestHoldsFrom (e := e) after.confirmedRoot (e.world n).time limit)
    (onChainAll : ∀ member ∈ chain ++ [after.confirmedRoot],
      ∀ (block parent : BeaconBlock preset fork),
      ((e.world n).state u).block member = .ok block →
      ((e.world n).state u).block block.parentRoot = .ok parent →
      SourceOnParentChain ((e.world n).state u) after.currentEpochObservedJustifiedCheckpoint
        block.parentRoot parent) :
    (∀ m ∈ chain ++ [after.confirmedRoot],
      HonestHeadsCover (e := e) m (e.world n).time (limit + 1)) ∨ Bad (e := e) pre limit := by
  have upToDate := ctx.upToDate n (List.mem_of_getElem? calls.1)
  obtain ⟨slot', begin, slotOk', -, beginOk, timeEq⟩ := ctx.atSlots i n calls.1
  obtain rfl : slot = slot' := Except.ok.inj (slotOk.symm.trans slotOk')
  obtain ⟨sourceReads, -, recent, realizedHead, memberObligations⟩ :=
    obligations head slot start source chain later headOk slotOk selects sourceOk walked
  have reach := fun k w (hw : w ∈ J) =>
    e.reachable (fun a ha => (ctx.start a ha) ▸ Store.Reachable.anchor ctx.anchored) k w hw
  have maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := by
    have := ctx.exitWindow.lookahead
    omega
  -- The caller reads its head at each rollover, unless stores collide or historical evidence holds.
  have signed : JustifiedHonestlySigned (e := e) anchor.justifiedCheckpoint.epoch 0 limit :=
    ctx.anchorEpochOk ▸ ctx.signedAll
  have history : 2 ≤ preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := by
    have := ctx.ring
    omega
  rcases e.callRolloverRead_or_evidence ctx.sync ctx.slots history ctx.preGloas ctx.admitted
      ctx.fits ctx.prompt ctx.votes ctx.anchored ctx.start ctx.anchorSlot ctx.anchorBoundary signed
      ctx.roots ctx.absent ctx.bounded ctx.parameters ctx.genesis pre ctx.heldEarly ctx.enough
      ctx.terminal ctx.ceiling ctx.scoreFits ctx.fit ctx.caller n head.root with
    rollover | collision | evidence
  rotate_left
  · exact .inr (.inl collision)
  · exact .inr (.inr (.inl evidence))
  -- The root is viable at each covered time, unless stores collide or held-state evidence holds.
  by_cases collision : HonestCollision (e := e) limit
  · exact .inr (.inl collision)
  by_cases heldEvidence : HeldStateFinalityEvidence (e := e) pre limit
  · exact .inr (.inr (.inr (.inr (.inr heldEvidence))))
  by_cases cross : CrossStoreJustifiedEvidence (e := e) pre limit
  · exact .inr (.inr (.inr (.inr (.inl cross))))
  have rootViable : ∀ T, (e.world n).time ≤ T → T ≤ limit →
      HonestHeadsCover (e := e) after.confirmedRoot (e.world n).time T →
      RootViableAt (e := e) after.confirmedRoot T := fun T low high covers =>
    (e.rootViableAt_of_checked pre ctx.sync ctx.slots ctx.preGloas ctx.admitted
      ctx.fits ctx.prompt ctx.votes ctx.windows ctx.fit ctx.ring ctx.incrementPositive
      ctx.anchored ctx.sound ctx.anchorSlot ctx.anchorBoundary ctx.start ctx.anchorEpochOk
      ctx.bounded ctx.roots ctx.absent ctx.pinned ctx.signedAll
      good.quorum ctx.unslashed ctx.terminal ctx.anchorGenesis ctx.parameters ctx.genesis
      ctx.heldEarly ctx.enough ctx.included ctx.caller upToDate slotOk beginOk timeEq
      headOk rollover inputs walked recent realizedHead startCovers holds T low high
      covers).resolve_right (not_or.mpr ⟨collision, not_or.mpr ⟨heldEvidence, cross⟩⟩)
  -- The start's recent historical root, from the call invariant at the start.
  obtain ⟨epoch, -, -, startEpoch, epochOk, -, -, startEpochOk, recentStart, -⟩ := checked
  obtain ⟨historical, historicalEpoch, epochStart, epochStartTime, startBelow,
    historicalEpochOk, near, epochStartOk, epochStartTimeOk, historyCovers⟩ :=
    startInv.2.1 epoch startEpoch epochOk startEpochOk recentStart
  obtain ⟨_, historicalKnown, -⟩ := found_of_blockEpoch historicalEpochOk
  have walkedAll : ((e.world n).state u).getAncestorRoots head.root start =
      .ok ((chain ++ [after.confirmedRoot]) ++ later) := by
    simpa using walked
  -- An induction on time and along the walk.
  refine Execution.walk_covers (chain ++ [after.confirmedRoot])
    (parentOrSelf ((e.world n).state u)) (parentOrSelf_of_walk walkedAll) startCovers ?_
  intro T hT earlier m hm parentCovers
  by_cases early : T + 1 ≤ (e.world n).time
  · exact .inl fun _ low high => absurd high (by omega)
  have callerTime : (e.world n).time ≤ T := by omega
  have collisionAt : HonestCollision (e := e) T → HonestCollision (e := e) limit :=
    fun ⟨a, ha, b, hb, i, j, hi, hj, rest⟩ => ⟨a, ha, b, hb, i, j, hi.trans hT, hj.trans hT, rest⟩
  have memWalk : m ∈ chain ++ after.confirmedRoot :: later := by
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_append_left _ h
    · simp [List.mem_singleton.mp h]
  -- The member's reads, from its confirmation.
  obtain ⟨support, threshold, supportOk, thresholdOk, -⟩ :=
    Store.isOneConfirmed_eq_ok_true_iff.mp (confirmedAll m hm)
  obtain ⟨s, block, parent, boost, first, last, maximum, discount, adversary, sOk, blockOk,
    parentOk, boostOk, firstOk, lastOk, maximumOk, discountOk, adversaryOk⟩ :=
    Store.computeSafetyThreshold_eq_ok thresholdOk
  obtain rfl : slot = s := Except.ok.inj (slotOk.symm.trans sOk)
  obtain ⟨beforeBlock, participants, -, beforeOk, participantsOk, -, -⟩ :=
    Store.exists_stake_parentVotersOf_of_computeEmptySlotSupportDiscount blockOk parentOk
      firstOk discountOk
  obtain ⟨shift, margin, drift, reserveAll, late, newlyActive⟩ :=
    memberObligations m hm block parent first last beforeBlock boost maximum support discount
      adversary participants blockOk parentOk boostOk firstOk lastOk beforeOk maximumOk
      participantsOk supportOk discountOk adversaryOk
  obtain ⟨x, hx, mRef, referenceSlot, finish, referenceTime, referenceUpToDate, referenceSlotOk,
    finishOk⟩ := ctx.reference
  rw [show parentOrSelf ((e.world n).state u) m = block.parentRoot by
    simp [parentOrSelf, blockOk]] at parentCovers
  -- The member's near exit bound at time T, or a collision.
  rcases Execution.receiverWindowExitsNear_of_sourceOnParentChain ctx.anchored ctx.start
      ctx.anchorSlot ctx.positive ctx.exitWindow ctx.preGloas ctx.caller callerTime sourceOk
      parentOk firstOk (onChainAll m hm block parent blockOk parentOk) parentCovers
    with exits | collision
  swap
  · exact .inr (.inl (collisionAt collision))
  -- The member's walk relations in the caller's store.
  obtain ⟨-, startBlock, -, startFound, -⟩ :=
    Store.slot_lt_of_mem_getAncestorRoots walked (by simp) memWalk
  have startHeld := Store.block_ok_iff.mp startFound
  have headDescends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨m, .pending⟩ =
      .ok true := by
    obtain ⟨older, newer, split⟩ := List.append_of_mem memWalk
    exact (Store.parentRoot_of_getAncestorRoots (split ▸ walked) blockOk).2.1
  have historicalBelow := Store.isAncestor_trans_of_lt ctx.preGloas startHeld historicalKnown
    (parent_above startHeld walked hm blockOk) startBelow
  have rootAbove := root_descends_of_walk walked hm
  have membership := Execution.votersInHeadWindow_of_newlyActive ctx.anchored ctx.start
    (UInt64.le_of_eq ctx.anchorSlot) ctx.positive ctx.minLookahead maxLookahead ctx.ring
    (fun w hw k low high => newlyActive w hw k low (high.trans hT))
  -- Each member is viable wherever the root is.
  have viableAt : ∀ T', (e.world n).time ≤ T' → T' ≤ T →
      HonestHeadsCover (e := e) m (e.world n).time T' → RootViableAt (e := e) m T' := by
    intro T' low high _ w hw k nodes hd atTime ready receiverHead tree
    have rootCovers : HonestHeadsCover (e := e) after.confirmedRoot (e.world n).time T' :=
      fun t lo hi => earlier after.confirmedRoot (by simp) t lo (Nat.lt_of_lt_of_le hi high)
    have kLow : (e.world n).time ≤ (e.world k).time := by omega
    have kHigh : (e.world k).time ≤ limit := by omega
    have below : ((e.world k).state w).isAncestor ⟨after.confirmedRoot, .pending⟩
        ⟨m, .pending⟩ = .ok true :=
      Store.isAncestor_of_same_blocks (reach k w hw) ctx.preGloas
        (fun r b c hb hc => good.blocks u ctx.caller w hw n k nBound kHigh r b c hb hc)
        (Store.block_ok_iff.mp blockOk)
        ((reach n u ctx.caller).anchorSlot_le (UInt64.le_of_eq ctx.anchorSlot)
          (Store.block_ok_iff.mp blockOk))
        (holds w hw k kLow kHigh ready) rootAbove
    exact Store.viable_of_ancestor ctx.preGloas tree below
      (rootViable T' low (high.trans hT) rootCovers w hw k nodes hd atTime ready receiverHead
        tree)
  -- The member's step at time T.
  rcases Execution.honestHeadsCover_of_viableAt ctx.sync ctx.slots ctx.minLookahead maxLookahead
      ctx.ring ctx.preGloas
      (fun v hv w hw n k le => ctx.admitted v hv w hw n k (le.trans hT)) ctx.half
      (fun v hv s c d a b early le => ctx.votes v hv s c d a b early (le.trans hT)) ctx.fits
      (fun w hw s st a b le => ctx.prompt w hw s st a b (le.trans hT))
      (fun w hw k le => ctx.windows w hw k (le.trans hT)) membership
      ctx.anchored ctx.sound ctx.anchorSlot ctx.anchorBoundary ctx.start ctx.caller upToDate
      ⟨head, headOk, rfl⟩ slotOk beginOk timeEq blockOk parentOk sourceOk boostOk firstOk lastOk
      beforeOk maximumOk participantsOk (BeaconState.registryWithinLimit_of_lt ctx.preGloas source)
      (Store.Reachable.checkpointState_aligned ctx.sound (reach n u ctx.caller) ctx.maxAligned
        sourceOk)
      ctx.increment supportOk discountOk adversaryOk margin callerTime
      (fun w hw k hd st c f fi mx lo hi => sourceReads w hw k hd st c f fi mx lo (hi.trans hT))
      (fun w hw k hd st sc ss f fi mx smx lo hi =>
        drift w hw k hd st sc ss f fi mx smx lo (hi.trans hT))
      (reserveAll x hx mRef referenceSlot finish referenceTime referenceUpToDate referenceSlotOk
        finishOk)
      hx (hT.trans referenceTime) referenceUpToDate referenceSlotOk finishOk
      (fun w hw k ep le => ctx.bounded w hw k ep (le.trans hT))
      (fun w hw k le => ctx.roots w hw k (le.trans hT))
      (fun w hw k s le => ctx.unslashed w hw k s (le.trans hT))
      (fun w hw k c s le => ctx.ceiling w hw k c s (le.trans hT)) ctx.scoreFits
      ctx.parameters ctx.genesis pre (fun w hw k le => ctx.heldEarly w hw k (le.trans hT))
      (fun w hw k le => ctx.enough w hw k (le.trans hT))
      (fun w hw k le => ctx.terminal w hw k (le.trans hT)) headDescends
      historicalBelow epochOk historicalEpochOk near epochStartOk epochStartTimeOk
      (fun t lo hi => historyCovers t lo (by omega))
      (fun a ha i le => ctx.absent a ha i (le.trans hT)) parentCovers
      ctx.fit viableAt exits (fun w hw k ep st lo hi => late w hw k ep st lo (hi.trans hT))
    with covered | collision | historicalEvidence
  · exact .inl covered
  · exact .inr (.inl (collisionAt collision))
  · obtain ⟨w, hw, i, k, ik, hk, rest⟩ := historicalEvidence
    exact .inr (.inr (.inl ⟨w, hw, i, k, ik, hk.trans hT, rest⟩))

/-- One call of one honest validator keeps the call invariant, given it at every earlier call.

The call's stored root is its start, or a root on the walk from its head to that start.

The start is the stored root of the call before, the finalized root or the observed justified one.

Each walked member is covered from the call to the horizon, from the coverage of its parent.

The alternatives are a collision of two honest stores and four kinds of accountable-safety evidence.

The execution verifies signatures with BLS, as the pulled-up head state of the rule does. -/
private theorem Execution.callInvariant_step [DecidablePred (· ∈ J)] {Δ : ℕ}
    {anchor : Store preset fork} {limit : ℕ} {horizon anchorEpoch : Epoch}
    {g : ForkedBeaconState preset} (pre : Run config checks g ⟨fork, anchorState⟩)
    (bls : checks = .bls)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (exitWindow : preset.SeedLookaheadAtLeastThree)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ limit)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (long : 1 < preset.SLOTS_PER_EPOCH)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (votes : ValidatedDutyVotes (e := e) limit) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e limit) (windows : AssignmentWindowAgreement (e := e) limit)
    (fit : config.CommitteeWindowsFit preset)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (anchorEpochOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (roots : HeldBlockStateRootsNonzero (e := e) limit)
    (unslashed : HonestCountedStatesUnslashed (e := e) limit)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) limit)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (parameters : DirectSafety.Parameters preset) (genesis : Genesis config checks g)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) limit)
    (enough : HeldRunStakeFloor (e := e) pre horizon limit)
    (terminal : HeldTerminalStakeFloor (e := e) horizon limit)
    (absent : AnchorParentAbsent (e := e) limit)
    (pinned : JustifiedPinned (e := e) anchorEpoch 0 0 limit)
    (signedAll : JustifiedHonestlySigned (e := e) anchorEpoch 0 limit)
    (fusaka : .fusaka ≤ fork) (band : preset.IncrementWithinUpwardBand)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (capEq : preset.MAX_EFFECTIVE_BALANCE = preset.MIN_ACTIVATION_BALANCE)
    (capOrder : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (included : TargetIncluded (e := e) limit) (stale : StaleHeadVotersInWindow (e := e) limit)
    (reference : ∃ x ∈ J, ∃ m, ∃ referenceSlot finish : Slot, limit ≤ (e.world m).time ∧
      UpToDate config checks sources (e.world m).time ((e.world m).view x)
        ((e.world m).state x) ∧
      ((e.world m).state x).getCurrentSlot config = .ok referenceSlot ∧
      subChecked referenceSlot 1 = .ok finish)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    (confirmationEpoch : 2 ≤ computeEpochAtSlot preset firstSlot)
    (anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot)
    (upToDate : ∀ n ∈ events, UpToDate config checks sources (e.world n).time
      ((e.world n).view u) ((e.world n).state u))
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (nBound : (e.world n).time ≤ limit)
    (obligations : CallObligations (e := e) 0 limit u n fcr after)
    (earlier : ∀ i' < i, ∀ n' fcr' after',
      CallAt (e := e) u events (getFastConfirmationStore anchor) i' n' fcr' after' →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n'
        after'.confirmedRoot) :
    CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n after.confirmedRoot ∨
      HonestCollision (e := e) limit ∨ HistoricalDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreJustifiedEvidence (e := e) pre limit ∨
        HeldStateFinalityEvidence (e := e) pre limit := by
  have positive := fit.positive
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots
    omega
  have incrementPositive := band.1
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have ctx : StepCtx (e := e) pre Δ anchor limit horizon anchorEpoch u events firstSlot :=
    { bls, anchorGenesis, sync, slots, positive, minLookahead, exitWindow, ring, preGloas,
      admitted, half, long, window, maxAligned, incrementPositive, votes, fits, prompt,
      windows, fit, anchored, sound, anchorSlot, anchorBoundary, start,
      anchorEpochOk, increment, bounded, roots, unslashed, ceiling, scoreFits, parameters,
      genesis, heldEarly, enough, terminal, absent, pinned, signedAll, fusaka,
      band, withdrawDelay, capEq, capOrder, forkWindow, included, stale, reference, caller,
      confirmationEpoch, anchorEpochBefore, upToDate, atSlots }
  suffices goal : CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n
      after.confirmedRoot ∨ Bad (e := e) pre limit from goal
  -- Honest justified checkpoints agree, or the cross-store justified evidence holds.
  rcases e.selectedCheckpointsAgree_or_evidence anchored start anchorSlot roots absent parameters
      genesis pre heldEarly enough terminal with agree | evidence
  swap
  · exact .inr (.inr (.inr (.inr (.inl evidence))))
  -- Each store's finalized checkpoint is on the chain of each justified one, or evidence holds.
  rcases e.crossStoreFinality_or_evidence anchored start anchorSlot anchorBoundary slots bounded
      roots absent parameters genesis pre heldEarly enough terminal with finality | evidence
  swap
  · exact .inr (.inr (.inr (.inl evidence)))
  -- Honest stores agree on blocks, or two collide.
  rcases e.blocksAgree_or_collision limit with blocks | collision
  swap
  · exact .inr (.inl collision)
  -- The stake of each call's voters drifts by at most the call's reserve.
  have quorum : QuorumDriftWithin (e := e) horizon limit := by
    subst bls
    have maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := by
      have := exitWindow.lookahead
      omega
    exact e.quorumDriftWithin anchored start anchorSlot slots positive genesis pre preGloas
      fusaka forkWindow bounded maxLookahead band withdrawDelay ⟨UInt64.le_of_eq capEq, capOrder⟩
      (UInt64.le_of_eq capEq.symm)
  have good : Good (e := e) horizon limit := ⟨agree, finality, blocks, quorum⟩
  have anchorFacts := anchor_facts ctx
  have member : n ∈ events := List.mem_of_getElem? calls.1
  obtain ⟨head, slot, start0, headOk, slotOk, selects, result⟩ :=
    Store.onFastConfirmation_checked calls.2.2
  -- The selected start keeps the invariant and, for a walk, covers from the call on.
  have startFacts : (CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start0 ∧
      HonestHeadsCover (e := e) start0 (e.world n).time (limit + 1)) ∨
      Bad (e := e) pre limit ∨
      (start0 = ((e.world n).state u).finalizedCheckpoint.root ∧
        CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start0 ∧
        (((e.world n).state u).finalizedCheckpoint = anchor.finalizedCheckpoint →
          HonestHeadsCover (e := e) start0 (e.world n).time (limit + 1))) := by
    obtain ⟨base, baseCase, startCase⟩ := selects
    rcases startCase with ⟨rfl, _⟩ | ⟨rfl, replaces⟩
    · rcases baseCase with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact .inl (carried_facts ctx calls nBound earlier)
      · refine .inr (.inr ⟨rfl, finalized_invariant ctx good anchorFacts member nBound,
          fun same => ?_⟩)
        rw [same]
        exact (anchorFacts n member nBound).2
    · rcases observed_facts ctx good anchorFacts calls nBound slotOk replaces with facts | bad
      · exact .inl facts
      · exact .inr (.inl bad)
  rcases result with same | ⟨-, checked, source, chain, later, sourceOk, walked,
    confirmedAll⟩
  · -- No walk: the stored root is the selected start.
    rw [same]
    rcases startFacts with facts | bad | ⟨_, inv, _⟩
    · exact .inl facts.1
    · exact .inr bad
    · exact .inl inv
  -- A walk: the start's facts, then the walk's inputs, holding, coverage and invariant.
  have startBoth : (CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n start0 ∧
      HonestHeadsCover (e := e) start0 (e.world n).time (limit + 1)) ∨
      Bad (e := e) pre limit := by
    rcases startFacts with facts | bad | ⟨rfl, inv, covers⟩
    · exact .inl facts
    · exact .inr bad
    · exact .inl ⟨inv, covers (finalized_start_anchor ctx nBound checked)⟩
  rcases startBoth with ⟨startInv, startCovers⟩ | bad
  swap
  · exact .inr bad
  have inputs := walk_inputs ctx calls nBound headOk slotOk selects checked sourceOk walked
    confirmedAll obligations startInv
  rcases walk_holds ctx calls nBound headOk slotOk selects checked sourceOk walked
      confirmedAll obligations with holds | bad
  swap
  · exact .inr bad
  have onChainAll := sourceOnParentChain_of_walk anchored sound anchorSlot anchorBoundary start
    slots positive long preGloas window roots absent caller anchorEpochBefore atSlots calls nBound
    headOk slotOk selects checked walked
  rcases walkMembers_cover ctx good calls nBound headOk slotOk selects checked sourceOk walked
      confirmedAll obligations startInv startCovers inputs holds onChainAll with covers | bad
  swap
  · exact .inr bad
  exact .inl (walk_invariant ctx calls headOk slotOk checked walked confirmedAll startInv inputs
    (covers after.confirmedRoot (by simp)))

/-- Every event of a run of calls starts no later than the slot after the last event. -/
private theorem time_le_following {u : ValidatorIndex} {events : List ℕ} {firstSlot : Slot}
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {n : ℕ} {slot next : Slot} {following : UInt64}
    (lastEvent : events.getLast? = some n)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (nextOk : addChecked slot 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    {i m : ℕ} (event : events[i]? = some m) :
    (e.world m).time ≤ following.toNat := by
  have lastAt : events[events.length - 1]? = some n := by
    rw [← List.getLast?_eq_getElem?]; exact lastEvent
  obtain ⟨slotL, -, slotOkL, slotEqL, -, -⟩ := atSlots _ _ lastAt
  rw [slotOk] at slotOkL
  cases slotOkL
  obtain ⟨slotI, beginI, -, slotEqI, beginOkI, timeEqI⟩ := atSlots _ _ event
  have iLt : i < events.length := (List.getElem?_eq_some_iff.mp event).1
  have nextEq := (addChecked_ok_iff.mp nextOk).2
  have le : slotI ≤ next := UInt64.le_iff_toNat_le.mpr (by simp at nextEq; omega)
  obtain ⟨start, startOk, -, startLe⟩ := exists_timeAtSlotMs_of_le le followingOk
  rw [beginOkI] at startOk
  cases startOk
  rw [timeEqI]
  exact UInt64.le_iff_toNat_le.mp startLe

/-- The confirmed root of the last of consecutive calls of one honest validator covers honest heads.

Every up-to-date honest head descends from it, from the slot after the last call to the horizon.

The alternatives are a collision of two honest stores and four kinds of accountable-safety evidence.

The evidence is historical, cross-store direct-safety, cross-store justified or held-state finality.

Each call assumes its obligations, and the calls are at consecutive slots from the first slot.

An assumption on the run: the first slot's epoch is at least two and after the anchor state's.

The execution verifies signatures with BLS, as the pulled-up head state of the rule does.

An assumption on the run: the Byzantine stake is below two thirds in each state that counts votes.

It holds after the anchor's justified epoch, and buys the honest signer of each later justification.

An assumption on the run: the anchor's latest header is the anchor block's, with a zero state root.

The anchor store checks neither condition; the inclusion delay is positive on mainnet and minimal.

The maximum effective balances of the preset are aligned, as they are on mainnet and minimal.

No theorem derives the pinned justification of each call's epoch yet; its producer is planned. -/
theorem Execution.confirmedRoot_covers [DecidablePred (· ∈ J)] {Δ : ℕ} {anchor : Store preset fork}
    {limit : ℕ} {horizon anchorEpoch : Epoch} {g : ForkedBeaconState preset}
    (pre : Run config checks g ⟨fork, anchorState⟩) (bls : checks = .bls)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (exitWindow : preset.SeedLookaheadAtLeastThree)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) (admitted : BlocksAdmitted e 0 Δ limit)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (long : 1 < preset.SLOTS_PER_EPOCH)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (votes : ValidatedDutyVotes (e := e) limit) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e limit) (windows : AssignmentWindowAgreement (e := e) limit)
    (fit : config.CommitteeWindowsFit preset)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (anchorEpochOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (roots : HeldBlockStateRootsNonzero (e := e) limit)
    (unslashed : HonestCountedStatesUnslashed (e := e) limit)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) limit)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (parameters : DirectSafety.Parameters preset) (genesis : Genesis config checks g)
    (enough : HeldRunStakeFloor (e := e) pre horizon limit)
    (terminal : HeldTerminalStakeFloor (e := e) horizon limit)
    (absent : AnchorParentAbsent (e := e) limit)
    (pinned : JustifiedPinned (e := e) anchorEpoch 0 0 limit)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (delay : preset.InclusionDelayPositive)
    (byzantine : ByzantineCountedStake (e := e) anchorEpoch 0 limit)
    (fusaka : .fusaka ≤ fork) (band : preset.IncrementWithinUpwardBand)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (capEq : preset.MAX_EFFECTIVE_BALANCE = preset.MIN_ACTIVATION_BALANCE)
    (capOrder : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (included : TargetIncluded (e := e) limit) (stale : StaleHeadVotersInWindow (e := e) limit)
    (reference : ∃ x ∈ J, ∃ m, ∃ referenceSlot finish : Slot, limit ≤ (e.world m).time ∧
      UpToDate config checks sources (e.world m).time ((e.world m).view x)
        ((e.world m).state x) ∧
      ((e.world m).state x).getCurrentSlot config = .ok referenceSlot ∧
      subChecked referenceSlot 1 = .ok finish)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    (confirmationEpoch : 2 ≤ computeEpochAtSlot preset firstSlot)
    (anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot)
    (upToDate : ∀ n ∈ events, UpToDate config checks sources (e.world n).time
      ((e.world n).view u) ((e.world n).state u))
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    {last : FastConfirmationStore}
    (folded : (events.map fun n => (e.world n).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) (getFastConfirmationStore anchor) =
        .ok last)
    (obligations : ∀ i n fcr after,
      CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after →
      CallObligations (e := e) 0 limit u n fcr after)
    {n : ℕ} {slot next : Slot} {following : UInt64}
    (lastEvent : events.getLast? = some n)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (nextOk : addChecked slot 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (followingLe : following.toNat ≤ limit) :
    HonestHeadsCover (e := e) last.confirmedRoot following.toNat (limit + 1) ∨
      HonestCollision (e := e) limit ∨ HistoricalDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreJustifiedEvidence (e := e) pre limit ∨
        HeldStateFinalityEvidence (e := e) pre limit := by
  -- Honest stores hold only states before the next fork, from the horizon.
  have heldEarly := e.heldStatesBeforeUpgrade_of_bounded anchored start anchorSlot slots
    fit.positive forkWindow bounded
  -- Honest validators sign each justified checkpoint after the anchor's epoch.
  have afterAnchor : getCurrentEpoch anchorState ≤ anchorEpoch := by
    obtain ⟨_, -, -, -, anchorJustified, -⟩ := getForkchoiceStore_anchor anchored
    rw [← anchorEpochOk, anchorJustified]
    exact UInt64.le_refl _
  have signedAll := Execution.justifiedHonestlySigned anchored start anchorSlot anchorHeader
    anchorZero slots parameters delay genesis pre roots absent heldEarly bounded enough terminal
    afterAnchor byzantine
  by_cases bad : Bad (e := e) pre limit
  · exact .inr bad
  have timeLe : ∀ i m, events[i]? = some m → (e.world m).time ≤ limit := fun i m event =>
    Nat.le_trans (time_le_following atSlots lastEvent slotOk nextOk followingOk event)
      followingLe
  -- The call invariant holds at every call, by strong induction on the call's index.
  have invariant : ∀ i n fcr after,
      CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after →
      CallInvariant (e := e) 0 limit anchor.finalizedCheckpoint.root u n after.confirmedRoot := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i earlier =>
      intro n fcr after calls
      rcases e.callInvariant_step pre bls anchorGenesis sync slots minLookahead exitWindow ring
        preGloas admitted half long maxAligned votes fits prompt windows fit anchored anchorSlot
        anchorBoundary start anchorEpochOk increment bounded roots unslashed ceiling scoreFits
        parameters genesis heldEarly enough terminal absent pinned signedAll fusaka band
        withdrawDelay capEq capOrder forkWindow included stale reference caller confirmationEpoch
        anchorEpochBefore upToDate atSlots calls
        (timeLe i n calls.1) (obligations i n fcr after calls) (fun i' lt => earlier i' lt) with
        holds | evidence
      · exact holds
      · exact absurd evidence bad
  -- The last call is the last step of the run of calls.
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp lastEvent
  rw [List.map_append, List.foldlM_append] at folded
  cases prefixOk : (ys.map fun n => (e.world n).state u).foldlM
      (fun fcr store => store.onFastConfirmation config fcr) (getFastConfirmationStore anchor) with
  | error fault => simp [prefixOk, bind, Except.bind] at folded
  | ok fcr =>
    simp only [prefixOk, bind, Except.bind, List.map_cons, List.map_nil, List.foldlM_cons,
      List.foldlM_nil] at folded
    have callOk : ((e.world n).state u).onFastConfirmation config fcr = .ok last := by
      cases called : ((e.world n).state u).onFastConfirmation config fcr with
      | error fault => simp [called] at folded
      | ok after => simpa [called, pure, Except.pure] using folded
    have calls : CallAt (e := e) u (ys ++ [n]) (getFastConfirmationStore anchor) ys.length n
        fcr last := ⟨by simp, by simpa using prefixOk, callOk⟩
    exact .inl ((invariant _ _ _ _ calls).1 slot next following slotOk nextOk followingOk)

end EthLib.Consensus.Models.Network
