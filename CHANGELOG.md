# Changelog

This file lists the changes of each release that a caller of EthLib may need to act on.
The version is the same in `pyproject.toml` and `lakefile.lean`.

## 0.4.0

Not yet released.

### Proof additions

- `Execution.rootViable_of_checked_call` shows that the confirmed root of a call of the fast confirmation rule stays viable from the call up to `time` ([#2058](https://github.com/ethereum/EthLib/issues/2058), Theorem 3, for the confirmed root).
  At each up-to-date honest store whose fork choice returns a head, the root is in the filtered tree or below the justified block.
  The alternatives are a collision of two honest stores and accountable-safety evidence.
  Stores whose `getHead` returns an error are not covered, pending [#2060](https://github.com/ethereum/EthLib/issues/2060).
  `Execution.honestHeadsCover_of_checked_call` keeps the root on every up-to-date honest head chain over the same interval.
  It replaces the consistency and the leaf of `Execution.honestHeadsCover_of_signed_justification` with the rule's checks.
  It derives the honest signer from `ByzantineCountedStake anchorEpoch 0 time`, a wider bound than the call-epoch one of `Execution.honestHeadsCover_of_byzantine_bound`, and adds the premise `JustifiedPinned`.
  `Execution.rootInFilteredTree_of_checked` and `Execution.justified_comparable_of_checked` give the root's step at one time.
  They and `justified_descends_of_duty` may instead give `HonestCollision`, two honest stores that collide on a block, and the first two may give `CrossStoreJustifiedEvidence`.
  `Execution.blocksAgree_or_collision` splits that collision from the agreement of honest stores on the blocks they both hold, and `Execution.not_honestCollision_of_agree` rules it out under that agreement.
  `Store.findBlockCollision_held` places a collision's two blocks in the two stores, and `Store.findBlockCollision_valid` now reads it.
  `Execution.rootHeld_of_honest_vote` holds the root from the call on, from the honest vote that `Execution.honest_vote_of_caller_margin` finds behind the caller's margin.
  `Execution.heldFinality_or_evidence` reads a store's finalized checkpoint on a held state's justified chain, or gives `HeldStateFinalityEvidence`.
  `DelayFits.deadline_add_le`, `Store.ForwardReachable.finalized_add_two_le_or_anchor` and `Store.getCheckpointBlock_trans` are general steps.
  The new premises `CallCheckpointInputs`, `TargetChecked`, `AcceptedRealizedRecent`, `AcceptedRealizedHead`, `CallRolloverRead`, `JustifiedPinned`, `TargetIncluded` and `QuorumDriftWithin` are described in `SOUNDNESS.md`.
  `DirectSafety.AccountableOrHashEvidence` is the direct-safety bound on two tails or hash evidence on their runs, and the statements that spelled it out now name it.
  `quorumReserve` and `pinReserve` are the reserves that `QuorumDriftWithin`, `JustifiedPinned` and the reserved count of a call read, and `RootViableAt` is the viability of a root at one time.

- The checked-call proofs add these general facts.
  `SelectedCheckpointsAgree` says that honest justified checkpoints agree at each epoch, and `Execution.selectedCheckpointsAgree_or_evidence` derives it or returns evidence.
  `Execution.justified_eq_or_accountable` and `Store.Reachable.justified_eq_or_accountable` give two equal justified checkpoints of one epoch, or evidence.
  `Execution.held_finalized_read_or_accountable` reads an honest finality on a held state's justified chain, or gives evidence.
  `HonestHoldsFrom` says that honest stores hold a root over an interval, and `ReservedTargetVotes` is a call's honest count with its pin reserve.
  `quorumReserve_le_pinReserve` bounds the quorum reserve by the pin reserve.
  `includedVotes_votingSource_ge` lifts the voting sources above a block that holds a target's counted votes to that target.
  `boundary_le_of_duty` and `duty_after_call` place an honest duty in time.
  `DirectSafety.view_justified_fields` shows that a justified field of a view is the genesis checkpoint, or a quorum targets it.

- The store facts are `Store.getCheckpointBlock_walk`, the one walk of a checkpoint read, and `Store.held_of_isAncestor`.
  `Store.comparable_of_ancestors` and `Store.eq_of_isAncestor_antisymm` order two ancestors of one head.
  `Store.getCheckpointBlock_of_shared_origin` passes a checkpoint read to another store that agrees on its blocks.
  `Store.exists_leaf_above_mem_filterNodeTree`, `Store.isViableLeaf_eq_true`, `Store.filterNodeTree_cases` and `Store.filterNodeTree_sub` read the filtered tree.
  `Store.ForwardReachable.pulledUpHeadState_epoch`, `Store.ForwardReachable.votingSource_le_justified` and `Store.ForwardReachable.justified_le_of_pulledUp` bound the epochs that a store reads.
  `Store.Reachable.blockState_induction`, `Store.Reachable.justified_le_of_blockState`, `Store.Reachable.finalizedState_of_blockState`, `Store.Reachable.finalized_lt_justified_or_anchor`, `Store.Reachable.realized_le_source` and `Store.Reachable.unrealizedJustification_origin` read the held states.
  `DelayFits.start_add_lt_of_lt`, `slot_le_of_epoch_lt` and `exists_nextEpochStart_lt` are facts of the clock.

- The transition facts are in `Transition/IncludedTargetVotes.lean`, `Transition/ParticipationFrames.lean` and their neighbours.
  `processJustificationAndFinalization_justifies` and `advanceSlot_justifies` justify an epoch whose active, unslashed target voters (`UnslashedAt`) hold two thirds.
  `weighJustificationAndFinalization_justifies`, `processJustificationAndFinalization_totalActiveBalance` and `advanceSlot_total_of_last` are their steps.
  `advanceSlots_keepsVotes`, `processBlock_keepsVotes`, `keptVotes_trans` and `recentEpoch_eq` keep those votes inside an epoch.
  `PendingAtOwnEpoch` and `pendingAtOwnEpoch_stateTransition` keep each pending attestation at its own epoch.
  `advanceSlots_currentJustified_mono` and `stateTransition_currentJustified_mono` show that slots and blocks never lower the current justified epoch of an invariant state.
  `TargetFlagAt.of_processBlock` keeps a target flag through a block, read from `processBlock_participationKept`.
  `ParticipationKept`, `ParticipationKeptBelow`, `ParticipationKept.below` and `ParticipationKept.foldlM` are the participation-flag frames.
  `RunKept.getPendingAttestingIndices_eq` and `recordPendingAttestation_lists` read pending attestations.

- `advanceSlot_epochs` splits one slot into the end of an epoch or a step inside it, with the epochs on each side.
  `recentPending_advanceSlot` adds the two lists of pending attestations, and `recentPending_pendingFrame` keeps them across a frame.
  `TargetFlagsVoted.of_advanceSlot` and `PendingVoted.of_advanceSlot` read them, as does the proof of `Execution.rootViable_of_checked_call`.

- `mem_getUnslashedParticipatingIndices_of_recent_flag` places an active, unslashed validator with a flag among the participants of the current or the previous epoch.
  `mem_getUnslashedParticipatingIndices_of_flag` keeps its statement and is now its case of the previous epoch.

- `Store.onTick_slot_induction` passes a fact of a store at its slot through a forward tick, from each tick within a slot.
  `epoch_lt_of_offset_zero` places a slot at the start of its epoch in a later epoch than each earlier slot.
  The proofs of the justified and finalized ages of a forward-reachable store read them.

- `slotStart_le_of_slotAtTime` shows that each slot up to the slot at a time starts by that time.
  `nextSlotStart_le_of_slotAtTime` shows it for the slot after an earlier one.
  `slotStart_le_clock`, `DelayFits.deadline_add_le` and `duty_window_of_slot_le` read them.
  `Store.isAncestor_of_getCheckpointBlock_above` places a checkpoint read above a block at or before the epoch's first slot.
  `signerHead_of_duty` gives the head on which an honest duty's signer reads its target.

- `Execution.honestTargetVotes_signed_of_checked` shows that an accepted current-target test has honest signers with two thirds of the active balance ([#2058](https://github.com/ethereum/EthLib/issues/2058), Theorem 2).
  Each signer votes for the target before the start of the next epoch, unless two honest stores collide on a block.
  It assumes the honest count, honest heads above a block of the target's epoch until then, and the caller's head at that time.

- `genesis_offset_of_slot_start` and `slot_at_start_of_genesis_offset` show that a genesis offset below one slot duration keeps the slot read at every slot start.

- `quorum_of_current_target` names the honest voters of `HonestTargetVotes` when the two-thirds test on the current target passes.
  Three times their stake is at least twice the total active balance plus the margin of the count.

- `Store.Reachable.blockState_slot_eq` states that a known block's state is at the block's slot, when the anchor block is at the anchor state's slot.

- `le_computeStartSlotAtEpoch_of_isStartSlotAtEpoch` shows that a slot at the start of an epoch is at most the first slot of the epoch of each later slot.
  `HonestVoteData.target_read`, `Store.Reachable.getCheckpointBlock_anchor`, a step of `DutySupport.lean` and `Execution.honestTargetVotes_signed_of_checked` read it.

- `DirectSafety.accountable_safety_apriori` bounds the drift of accountable safety from the reference state alone.
  For two runs that finalize conflicting checkpoints, the unslashed stake at the shared state `x` is at most three times the accountable stake plus `2 * drift x high`, or the runs show `HashEvidence`.
  `drift x high` reads only numbers at `x` and the window to the later finalized epoch, so it needs no replay of the tails.
  It takes the premises of `source_safety`.
  When its guard fails, `drift` is the unslashed active stake at `x`, and the bound says nothing.

- `Execution.honestHeadsCover_of_historical_anchor` keeps a confirmed block on every honest head chain from the call to a horizon, by induction on time ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  It no longer assumes the root's own earlier coverage.
  It assumes the parent's coverage, the root's viability, the receivers' exits, and a late duty majority.
  The root's viability rules out honest justified checkpoints that conflict with the root, so it assumes the checkpoint-consistency half of safety.
  The alternatives are a block collision between honest stores and `HistoricalDirectSafetyEvidence`, which holds with no accountable key once the churn since the anchor is large enough.
  `Config.ProposerScoreFits` bounds the proposer boost so that the score fits in 64 bits; mainnet and minimal satisfy it.

- New lemmas derive the reads of the fast confirmation rule from a held head state ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  `Store.checkpointState_justified_of_getHead` shows that, before Gloas, a head with a viable node besides the justified block has read the justified state.
  `Store.getCommitteesBetweenSlots_exists` reads every committee window before the current slot, under `Config.CommitteeWindowsFit`.
  `Store.getCommitteesBetweenSlots_ok_of_slots` reads a window whose slots read and whose end has a checked successor.
  `getBeaconCommittee_exists` cuts a committee whose index is below the count of its slot, and `beaconCommitteeOf_ok_of_lt` does so for one shuffle.
  `Config.committeeWindowsFit_mainnet` and `Config.committeeWindowsFit_minimal` show that mainnet and minimal satisfy those bounds.
  `computeSlotAtTimeMs_le` bounds the slot at a time by the largest 64-bit integer divided by the slot duration.

- `Execution.mem_supportersOf_of_duty_epoch_or_accountable` and `Execution.isAncestor_getHead_of_duty_epoch_or_accountable` add accountable companions to the honest-duty results.
  They use a proved historical finalized-prefix family instead of assumed compatibility, while preserving the original theorems.
  They retain the network and duty conditions and require deposited genesis history, preset bounds, a fixed-fork horizon, stake floors and an absent anchor parent.
  The alternative is the reference-stake inequality with derived drift, or `DirectSafety.HashEvidence`, not an a priori drift bound.

- `Execution.honestHeadsCover_of_signed_justification` derives the late half of the root's viability inside the same induction ([#2656](https://github.com/ethereum/EthLib/issues/2656)).
  A justified checkpoint after the call's epoch descends from the root, because an honest validator signed a vote for it after the call.
  It takes `EarlyJustifiedConsistent`, `RootKeepsViableLeaf` and `JustifiedHonestlySigned` instead of `RootViable`.
  `Execution.honestHeadsCover_of_historical_anchor` keeps its statement.
  `slotStart_le_clock` is now public.

- `Execution.honestHeadsCover_of_byzantine_bound` derives the honest signer of the signed-justification headline ([#2656](https://github.com/ethereum/EthLib/issues/2656)).
  It takes `ByzantineCountedStake`, Byzantine stake below two thirds in each state that counts later votes, instead of `JustifiedHonestlySigned`.
  It also takes `Preset.InclusionDelayPositive` and two conditions on the anchor: its latest header is the anchor block's, with a zero state root.
  `Execution.justifiedHonestlySigned` is the derivation; `Execution.honestHeadsCover_of_signed_justification` keeps its statement.
  The votes behind a justified checkpoint are traced in `ForkChoice/JustifiedVotes.lean`: `Store.ForwardReachableWith.justified_counted`, `held_participation` and `counted_history`, and `Execution.exists_sent_of_votesBelow`.
  `processJustificationAndFinalization_exists_voter` names a voter of a fresh justification, among `quorumVoters`.
  `isValidIndexedAttestation_of_keys` and `processBlock_attestation_checked` carry a block's attestation check to the state of its target.
  `Store.ForwardReachableWith.pubkeysDistinct_of_blockState`, `countedRun_enoughStake` and `stake_activeKeys_eq` bound the stake where a store counts votes.
  `mapM_congr` is new and holds in any lawful monad, and `lt_size_of_mem_getActiveValidatorIndices` bounds active indices by the registry.
  `RunKept.getAttestingIndices_eq` keeps attesters along a run.
  `keys_advanceSlot`, `getAttestingIndices_eq_of_seed`, `Store.getAncestor_of_isAncestor` and `Store.exists_storeTargetCheckpointState` are now public.

- `HonestVoteData.target_read` reads the target of an honest vote from its voter's head, without the reads of a duty vote.
  It needs the target block held by some store reachable from the same anchor.
  The anchor store does not tie the anchor state's latest header to the anchor block, so a read at the anchor needs that block.
  `VoteAt.data_target` follows from it, and `Store.Reachable.lookahead_history_ancestor_of_held` is the walk it reads.

- `Store.Reachable.isViableLeaf_finalized` shows that each viable leaf of a reachable store descends from the finalized block, also at a genesis finalized epoch ([#1423](https://github.com/ethereum/EthLib/issues/1423)).
  Its checkpoint block at the finalized epoch is the finalized block.
  It asks that the anchor block is not after the anchor state and that its parent root names no known block.
  `Store.isViableLeaf_checkpointBlock` gives the checkpoint block that a viable leaf reads.

- `epochIfLast_cases` splits the epoch step of a slot.
  At an epoch boundary it is the epoch transition, and at any other slot it keeps the state.

- `VotersInHeadWindow` states that, between two times, each voter below a given parent block lies in each honest head's window after that parent ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  `VoteInHeadWindow` is the vote and the window that it reads.
  `Execution.votersInHeadWindow_of_newlyActive` derives it from `NewlyActiveVotersInHeadWindow`, which asks it only of a voter activated at the target epoch of a vote two epochs after that parent.
  `Store.mem_getCommitteesBetweenSlots_of_active`, `Store.ForwardReachableWith.active_or_newlyActive_of_voteOrigin` and `Store.ForwardReachableWith.epoch_le_of_checkpointState` are the general steps.
  `fits_of_shuffledCommittee` states that a cut committee has the number of indices times one past its position below `2^64`.
  `ReceiverWindowExitsNear` asks the receivers' exit bound only of receivers within two epochs of the parent.

### Changes that break callers

- In Lean, `Execution.honestHeadsCover_of_byzantine_bound` moves from `HistoricalSigners.lean` to `HistoricalCoverage.lean`, with the same statement, so that the checked-call headlines can read `Execution.justifiedHonestlySigned`.
  A caller that imports `HistoricalSigners.lean` alone imports `HistoricalCoverage.lean` instead.

- In Lean, `headState_epoch_le` moves from the fast-confirmation proofs to `Store.ForwardReachable.headState_epoch_le` in `ForkChoice/BlockStates.lean`, with the same statement.
  A caller writes `forward.headState_epoch_le` for a forward-reachable store `forward`.

- In Lean, the compressed encoding of a point of `G2` has its 96 bytes in its type ([#2189](https://github.com/ethereum/EthLib/issues/2189)).
  `G2.compress` and `G2.infinityBytes` are a `Vector UInt8 96`, and `G2.uncompress` takes one.
  A caller that holds bytes of another length reads them with `exactBytes? 96` and rejects `none`, as decompression did.
  `G2_POINT_AT_INFINITY` is a `BLSSignature`, and the precompile constant `KZG_SETUP_G2_MONOMIAL_1` is a `Vector UInt8 96`.
  `G2.size_compress` and `G2.uncompress_size_ne` are removed, since the type states the length.
  `packBytes_pointToSignature` becomes `pointToSignature_eq`, which states that a signature is the compressed point.
  `TrustedSetup.decodeG2_eq_ok` is new, and relates the decoder of a setup point to decompression.
  `G2.compress_uncompress`, `isOnTwist_of_uncompress`, `uncompress_injective`, `uncompress_valid`, `valid_of_uncompress` and `Security.decodeSignature_of_uncompress` take the encoding as a vector.
  `G2.uncompress_uncompressed`, `uncompress_infinity_sign_set`, `uncompress_infinity_nonzero_tail`, `uncompress_noncanonical_c1` and `uncompress_noncanonical_c0` take a vector, read the flags in its first byte, and drop the premise on the length.
  `G2.compress_congr`, `compress_eq_infinityBytes_iff`, `compress_inf`, `compress_zero`, `uncompress_infinityBytes`, `uncompress_compress` and `uncompress_compress_of_z_one` keep their meaning, and now take or equate vectors.
  `coreVerify_iff` takes the signature as a vector.
  `coreVerify_of_represents`, `pointToSignature_bytes` and `Security.encode_signature` state the signature as the bytes of the compressed point, `packBytes (G2.compress S)`.
  `Security.verify_iff` and `verify_iff_isDh` decompress the signature itself, with no conversion to bytes.
  `TrustedSetup.ofBytes_g2Monomial` states its fact through `TrustedSetup.decodeG2`.
  In the security proofs, `G2Sub.encode` is the bytes of the compressed point.
  No C export or Python function changes.

- In Lean, `infinitySignature` is removed, since it named the same constant as `G2_POINT_AT_INFINITY`.
  A caller writes `G2_POINT_AT_INFINITY`.
  No C export or Python function changes.

- In Lean, the historical-anchor theorems read the slot count of an epoch from `fit` ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  `Execution.honestHeadsCover_of_historical_anchor`, `Execution.honestHeadsCover_of_signed_justification` and `Execution.honestHeadsCover_of_byzantine_bound` drop `positive : 0 < preset.SLOTS_PER_EPOCH.toNat`, which `fit.positive` gives; their conclusions are unchanged.
  A caller drops the argument.

- In Lean, `processDepositRequest_ok` also gives the state after the request.
  It is the state before, with only the pending deposits and the start index of the requests changed.
  A caller that took the balances as `.2.2` takes `.2.2.1`, and a pattern with three parts gets a fourth.
  Nothing breaks in Python.

- In Lean, `FlagsKeptOrZero` is stronger.
  A zero byte of flags appears only at a position at or past the size of the registry before the step.
  So a step keeps the flags of each existing validator, or zeroes the byte of a new one.
  `FlagsKeptOrZero.trans` takes a new premise: the registry of the first state is no larger than that of the second.
  A caller passes that fact, for example from `Frame.registryGrows`.
  A match on the zero case, `old | rfl`, becomes `old | ⟨rfl, -⟩`.
  Nothing breaks in Python.

- In Lean, the historical-anchor theorems no longer assume the receivers' reads ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  `Execution.honestHeadsCover_of_historical_anchor`, `Execution.honestHeadsCover_of_signed_justification` and `Execution.honestHeadsCover_of_byzantine_bound` take `fit : config.CommitteeWindowsFit preset` instead of `reads`; their conclusions are unchanged.
  `Config.CommitteeWindowsFit` bounds the registry limit, the committees of an epoch, the clock and the seed lookahead, and requires an epoch to have a slot.
  A caller on mainnet or minimal passes `Config.committeeWindowsFit_mainnet` or `Config.committeeWindowsFit_minimal`.
  `HonestHeadReads` is removed.
  The receiver's justified state comes from `Store.checkpointState_justified_of_getHead`, and its committee windows from `Store.getCommitteesBetweenSlots_exists`.
  `Store.getCommitteesBetweenSlots_ok_of_slots` reads a window from its slots, `getBeaconCommittee_exists` cuts one committee, and `beaconCommitteeOf_ok_of_lt` bounds its position; all three are new.

- In Lean, the historical-anchor theorems assume less about recent votes and receiver exits ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  Each new statement implies the old one.
  `Execution.honestHeadsCover_of_historical_anchor`, `Execution.honestHeadsCover_of_signed_justification` and `Execution.honestHeadsCover_of_byzantine_bound` take `newVoters : NewlyActiveVotersInHeadWindow` in place of the common vote history, `history`, and `exits : ReceiverWindowExitsNear` in place of the exit bound for every receiver.
  `Execution.isAncestor_getHead_of_historical_anchor` and `ancestor_head_of_window_margin` take `membership : VotersInHeadWindow` in place of `history`.
  Both window premises name the parent of the tested block and hold only from the call's time.
  `ancestor_head_of_window_margin` also drops `minLookahead`, `maxLookahead` and `ring`, which now only the derivation of the window membership reads.
  A caller with the common vote history passes the window membership that it implies, or the corner premise.
  A caller with the old exit bound passes its restriction to receivers within two epochs of the parent.
  `VoteCommitteeCommonHistory` and `ReceiverWindowExits` are removed: no statement reads them any more.

- In Lean, the historical-anchor theorems no longer assume finality across honest stores ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  `Execution.source_surplus_or_historical_evidence`, `Execution.isAncestor_getHead_of_historical_anchor`, `Execution.honestHeadsCover_of_historical_anchor`, `Execution.honestHeadsCover_of_signed_justification` and `Execution.honestHeadsCover_of_byzantine_bound` drop their `residual` argument; their conclusions are unchanged.
  `receiver_fullMaximum_of_head_window` takes the receiver's own finalized checkpoint on its own justified chain, `finalizedRead`, instead of `compatible`, `bounded`, `slots` and `epochOk`, and loses its implicit `horizon` and `epoch`.
  `SelectedCheckpoint`, `FinalizedCheckpointCompatibility`, `ResidualFinalizedCheckpointCompatibility` and `compatibility_of_residual` are removed: no proof read them any more.

- The EVM errors `invalidJumpDest`, `outOfBoundsRead`, `invalidParameter`, `addressCollision` and `precompile` carry the values that their failed check compared.
  Each halt keeps its behaviour, and each error fires on the same inputs as before.
  The message of an EVM error names each value, as `(name := value)`, with the address of a collision in hex and a precompile by its number.
  In Lean, `Evm.EvmError.invalidJumpDest destination`, `outOfBoundsRead offset size available`, `invalidParameter immediate`, `addressCollision address` and `precompile address` take arguments.
  `stackUnderflow`, `stackOverflow`, `outOfGas`, `writeInStaticContext`, `invalidContractPrefix` and `revert` stay bare.

- The eth body, session, snap range and era1 errors, and the argument errors of the EVM exports, carry the values that their failed check compared.
  Each code keeps its meaning, and each error fires on the same inputs as before.
  The messages give the new values: `transactions do not have the transactions root of the header` becomes `transactions have the root 0x…, not the transactions root 0x…`, and `the sender must be 20 bytes` becomes `the sender must be 20 bytes, not 19`.
  The era1 and snap range errors print each value named, `(name := value)`, with hashes in hex, on one line: `blockCount 3 2` becomes `blockCount (counted := 3) (held := 2)`.
  In Lean, these constructors take arguments:
  - `Network.BodyError.wrongTransactionsRoot`, `wrongWithdrawalsRoot` and `wrongOmmersHash`, each with the header's value `expected` and the body's value `actual`, and `untypedTransaction first`, the first byte, or `none` for an empty string;
  - `Network.EthSessionError.beforeStatus id`, the ID of the message;
  - `Network.SnapRangeError.slimAccount hash` and `tooManyRanges ranges accounts`;
  - `History.Era1Error.blockNumber i expected actual`, `parentHash i expected actual`, `totalDifficulty i expected actual` and `accumulator expected actual`;
  - `Evm.Exports.ArgumentError.senderLength size` and `saltLength size`, and `readWord` takes the error as a function of the size.
  `ArgumentError.code_injective` concludes that the two errors come from one constructor, since errors with one code now differ in their size.
  `receiveEth_beforeStatus` and the created-address lemmas of the EVM exports state the new values in their errors.

- The trie, range, Merkle proof, account proof and state input errors carry the values that their failed check compared.
  Each code keeps its meaning, and each error fires on the same inputs as before.
  Their messages name each value, as `(name := value)`, with hashes and byte strings in hex and words in decimal, on one line.
  In Lean, these constructors take arguments:
  - `Trie.HexPrefixError.invalidFirstNibble nibble` and `nonZeroPadding nibble`;
  - `Trie.ProofError.missingNode hash`, the hash of the node the path needs, an `Option` that is `none` only when a walk runs out of its budget, which no walk does, `hashMismatch expected actual`, the reference and the hash of the node, `invalidReference size` and `unusedNodes count`;
  - `Trie.RangeError.unsorted index`, `beforeStart index` and `emptyValue index`, each the first entry, counted from 0, that breaks the rule;
  - `State.StateInputError.repeatedAddress address`, and `State.AccountProofError.slotMismatch index expected actual`, the word that the proof shows and the word of the answer.
  `Trie.TrieError.emptyValue` stays bare: the root does not depend on the order of the entries, and naming a key would make the error depend on it.
  `compactToNibbleList_invalidFirstNibble`, `compactToNibbleList_nonZeroPadding`, `verifySlot_eq_slotMismatch` and `verifyRange_eq` state the values in their errors.
  `ErrorArg` shows a `BitVec`, such as a `U256`, in decimal.

- The state accessor, shuffle and deposit tree errors carry the values that their check compared, and their codes keep their meaning.
  - `AccessorError.balanceOverflow` holds the total that reached 2^64, and `AccessorError.ssz` the error of the root.
  - `AccessorError.invalidPubkeys` holds the number of keys and the position of the first key that is not valid, if any.
  - `AccessorError.wrongSource` holds the epoch and root of the source, then those of the justified checkpoint.
  - `ShuffleError.noCommittee` holds the index of the committee, and `ShuffleError.overflow` the number of indices and that index.
  - `DepositTreeError.treeFull` holds the number of deposits, `missingFinalized` the level that finds no root, and `extraFinalized` the number of roots left over.
  - `DepositTreeError.rootMismatch` holds the deposit root, then the root that the finalized roots compute.
  The message of a deposit tree error is on one line, with roots in hex, as in `EthLib.Consensus.DepositTreeError.rootMismatch 0x00… 0xd7…`.
  `getPendingBalanceToWithdraw_eq_error_iff` names the total in the error, and `map_getRoot_pushLeaves` names the cap of the tree.

- The errors of the execution payload, the Gloas bid, envelope, parent requests and payload attestations carry the values that their check compared.
  `TransitionError.wrongPayloadParentHash`, `wrongPayloadRandao`, `wrongPayloadGasLimit`, `wrongPayloadBlockHash` and `wrongPayloadRequestsRoot` hold the value of the payload, then the value it must equal.
  `bidWrongParentHash`, `bidWrongParentRoot` and `bidWrongRandao` hold the value of the bid, then the value of the state; `bidRepeatsParentHash` holds the repeated hash, and `selfBuildBidPaid` the value of the bid.
  `envelopeWrongBlockRoot`, `envelopeWrongParentRoot` and `envelopeWrongBuilder` hold the value of the envelope, then the expected one; `invalidEnvelopeSignature` holds the builder and the block root.
  `invalidBidSignature` holds the builder and the slot, and `invalidExecutionPayload` the block hash of the payload.
  `tooManyBlobCommitments` holds the number of commitments and the limit.
  `payloadAttestationNotForParent` holds the block root of the attestation and the parent root; `invalidPayloadAttestation` holds the slot and the number of attesters.
  `parentRequestsNotEmpty` holds the number of requests, which the new `ExecutionRequests.count` gives, and `wrongParentRequestsRoot` the two roots.
  The codes do not change.
  `processParentExecutionPayload_of_empty_requests`, `processExecutionPayload_eq_error_of_prepareExecutionPayload` and `processBlockExecution_eq_error_of_prepareExecutionPayload` state these values.

- The Engine API errors carry the values that their failed check compared.
  Codes are unchanged, and the JSON-RPC error objects keep the messages and the `null` data that the Engine API fixes.
  The bindings messages, which print the error in Lean form, now end with these values; hashes and payload IDs print in hex.
  - `EngineError.unsupportedFork fork` carries the fork the method was asked to serve: that of the payload, of the attributes' block or of the stored build, or the node's fork for blobs; `none` when no fork is active.
  - `EngineError.invalidForkchoiceState safe finalized` carries the safe and finalized hashes of the forkchoice state.
  - `EngineError.tooLargeRequest count limit` carries the number of items asked for and the node's maximum.
  - `EngineError.unknownPayload id` carries the payload ID.
  - `PayloadError.wrongVersionedHashes expected actual` carries the expected hashes and those of the blob transactions.
  - `PayloadError.invalidTerminalBlock parent` carries the hash of the parent.
  - `GetPayloadError.wrongFork stored active` carries the stored fork and the configured one, and `blockValue value` the block value.
  - `Jwt.JwtError.secretLength size` carries the size of the secret, `compact count` the number of parts of the token, and `algorithm name` the algorithm the header names, or `none`.
  - The theorems on these errors state them with their fields: `forkchoiceUpdated_zero_after_transition`, `forkchoiceUpdated_eq_error_iff`, `checkAttributes_eq_error_of_unsupportedFork`, `checkRequestSize_eq_error_iff`, `bodiesByHash_eq_error_iff`, `bodiesByRange_eq_error_iff`, `getBlobsV1_of_fusaka`, `getPayload_eq_error_of_store_eq_none`, `getPayload_eq_error_of_activeFork_ne`, `getPayload_eq_error_of_acceptsGetPayloadFork_eq_false`, `getPayload_eq_error_of_blockValue_ge`, `newPayloadOnChain_of_not_terminal` and `issuedAt_eq_error_of_algorithm_ne`.

- The precompile errors carry the values that their failed check compared, and their message names each value on one line.
  Each code keeps its meaning, and each error fires on the same inputs as before.
  The message of a failed call no longer wraps: `PrecompileError.sha256\n  (Sha256Error.outOfGas 72 71)` becomes `PrecompileError.sha256 (Sha256Error.outOfGas (cost := 72) (gas := 71))`, with each name in full.
  A bare error inside another now prints in parentheses, as Lean's own printer does.
  In Lean, these constructors take arguments:
  - `AltBn128Error.invalidFieldElement value`, the coordinate at or above `p`, and `notOnCurve point` and `notInSubgroup point`, the bytes of the point read from the call data, with zeros past its end;
  - `Bls12381Error.invalidPadding padding`, the 16 bytes in front of the field element, `invalidFieldElement value`, and `notOnCurve point` and `notInSubgroup point`, the unpadded bytes of the point;
  - `PointEvaluationError.versionedHashMismatch expected actual`, the hash of the commitment and the hash of the call, `invalidCommitment commitment`, `invalidFieldElement value`, the value of `z` or `y`, and `invalidProof proof`.
  `PointEvaluationError.invalidTrustedSetup`, `proofRejected` and `Bls12381Error.notASquare` stay bare: the first is a constant, the second a verdict of the pairing check, and the third excluded by RFC 9380.
  `bytesToG1_invalidFieldElement` names the rejected coordinate in its error.

- The AES-GCM, ChaCha20-Poly1305 and ERC-2334 path errors carry the lengths and values that their failed check compared.
  Codes are unchanged; each message now ends with these values, and a failed tag comparison still carries nothing.
  - `Aes.Gcm.Error.tagLength declared actual` carries the declared tag length and the length of the tag, in bytes.
  - `Aes.Gcm.Error.shortTag`, `ivLength`, `textLength` and `aadLength` carry the length that failed, in bytes.
  - `ChaCha20Poly1305Error.counterExhausted counter length` carries the first block counter and the text length in bytes; the AEAD starts at the counter 1.
  - `ChaCha20Poly1305Error.aadTooLong length` carries the length of the additional data, in bytes.
  - `KeyPath.KeyPathError.invalidRoot root` carries the text before the first `/`, and `tooShort count` the number of segments after `m`.
  - `Gcm.checkLengths_shortTag`, `Gcm.encrypt_shortTag`, `Gcm.decrypt_shortTag` and `ChaCha20Poly1305.crypt_eq_error_of_counter_exhausted` state the error with its fields.
  - `Aes.Gcm.Error.code_injective` now concludes that two errors with one code share a constructor, `e₁.ctorIdx = e₂.ctorIdx`, as the KZG and secp256k1 forms do.

- The DER and e2store errors carry the values that their failed check compared.
  Codes are unchanged, and each error fires on the same inputs as before.
  - `Der.Error.truncated needed available` carries a lower bound on the bytes a value needs, exact once its length is read, and the bytes of the input.
  - `Der.Error.tag expected actual` carries the tag read, and the tag the reader expects, or `none` when no single tag is expected.
  - `Der.Error.length first` carries the first length octet, and `trailing count` the bytes left after the value.
  - `Der.Error.value` keeps no field: the content belongs to the caller, and the reader tracks no position in it.
  - `E2store.E2storeError.truncatedHeader offset available` and `truncatedData offset length available` carry the position of the record, the announced length of its data, and the size of the input.
  - `reservedNotZero first second` carries the two reserved bytes, `dataTooLong length` the length of the data, `noVersion type` the type of the first record, `versionData index` the position of the first Version record with data, and `indexSize size` the size of the index data.
  - `Der.validate_eq_error_tag` concludes `.tag none value.tag`.

- The errors of attestations, deposits, exits, withdrawals, BLS changes, the sync aggregate and the historical lists carry the values that their check compared.
  `TransitionError.wrongAttestationSource` holds the epoch and root of the source, then those of the justified checkpoint.
  `invalidAttestation` holds the slot of the attestation and the number of validators its indexed form names.
  `invalidDepositProof` holds the deposit index, the root of the deposit data and the deposit root.
  `invalidExitSignature` and `invalidBlsChangeSignature` hold the validator index and the signing root.
  `wrongWithdrawals` holds the first position at which the withdrawals differ, then the length of the payload's list and of the expected one.
  `invalidSyncAggregate` holds the slot of the signed block root, the number of signers and the signing root.
  `invalidSyncCommitteeKey` holds the key that fails to decode or fails key validation, and `unknownSyncCommitteeMember` the key that no validator holds.
  `tooManyPendingAttestations` holds the count and the limit; `registryFull`, `historicalRootsFull` and `historicalSummariesFull` hold the limit.
  The codes do not change.
  `appendHistoricalRoot_eq_error_iff`, `processHistoricalRootsUpdate_eq_error_iff` and `processHistoricalSummariesUpdate_eq_error_iff` state the limit in the error.

- `DirectSafety.same_epoch_histories` is removed, because nothing reads it.
  `DirectSafety.view_same_epoch` replaces it: pass the two quorum calls as `.inl` quorums of the realized views.
  `DirectSafety.accountable_justified_unique_terminal` covers its one use, in `accountable_justified_unique`.

- The transaction, inclusion and network-form errors carry the values that their failed check compared.
  Each code keeps its meaning, and each error fires on the same inputs as before.
  The messages of transaction and inclusion errors name each value, as `(name := value)`, with hashes and addresses in hex.
  For example, `nonceTooLow 3 1` becomes `nonceTooLow (expected := 3) (nonce := 1)`, and `insufficientGas 21000 0` becomes `insufficientGas (needed := 21000) (gas := 0)`.
  In Lean, these constructors take arguments:
  - `Transactions.TransactionError.nonceOverflow nonce`, the nonce of the transaction, or of the sender when a simulation skips the nonce check;
  - `Transactions.TransactionError.priorityFeeGreaterThanMaxFee priorityFee maxFee`;
  - `Transactions.TransactionError.invalidBlobVersionedHash index hash`, the first versioned hash with the wrong version;
  - `Transactions.InclusionError.senderNotEoa sender`;
  - `Transactions.NetworkError.versionedHashMismatch index expected actual`, the first commitment whose hash `expected` is not the versioned hash `actual`.
  `emptyTransaction`, `noBlobData` and `emptyAuthorizationList` stay bare, since each fires on an empty input.
  `invalidSignature` stays bare: it fires on a bad `v`, a bad y parity, `r` or `s` out of range, or a signature that recovers no key, and the transaction holds each of these values.
  `NetworkError.proofRejected` stays bare: the batch check of the proofs gives only a verdict.
  `checkSender_of_skipNonce` states the nonce `2^64 - 1` in its error.

- The TLS codec, TLS handshake, TLS crypto and libp2p TLS certificate errors carry the values their failed check compared.
  Each error fires on the same inputs as before, and codes are unchanged; each message now shows these values.
  - `Quic.Tls.Wire.Error.truncated` carries the bytes needed and available, `trailing` the count of bytes left, `duplicateExtension` the repeated extension type, and `messageType` the handshake type.
  - `Quic.Tls.Handshake.Error.missingExtension` and `unsupportedExtension` carry the extension type.
  - `Quic.Tls.Crypto.Error.group` carries the NamedGroup, and `signatureScheme` the SignatureScheme.
  - `Libp2p.Tls.TlsCertError.validity` carries the time and the validity bounds, `chain` the certificate count, and `duplicateExtension` and `criticalExtension` the OID bytes.
  - `Libp2p.Tls.authenticate_single`, `authenticate_empty`, `authenticateCertificate_validity`, `authenticate_validity` and `signedKey_critical`, and `Quic.Tls.encodeExtensions_duplicate`, state the fields of the error.
  - The new `Quic.Tls.repeatedKind`, `Libp2p.Tls.firstRepeated` and `Libp2p.Tls.criticalOid` compute these fields, and `repeatedKind_spec`, `firstRepeated_some` and `criticalOid_spec` show that each names a real repeated type, repeated OID or critical OID when its check fails.

- The QUIC integer, wire and packet protection errors carry the values their failed check compared.
  Each error fires on the same inputs as before, and codes are unchanged; each message now shows these values.
  - `Quic.Varint.VarintError.truncated` and `Quic.Wire.Error.truncated` carry the bytes needed and available.
  - `Quic.Wire.Error.connectionIdLength` carries the length and the maximum, `fixedBit` and `reservedBits` the first byte, and `version` the version.
  - `Quic.Wire.Error.packetNumber` carries the truncated number, its width in bytes and the expected number, and `protocolViolation` the frame type.
  - `Quic.Protection.Error.sample` carries the packet number offset and the packet size, `tagLength` the tag size, and `connectionId` the length of the original destination connection ID.
  - `Quic.Varint.decodeList_nil`, `decodeList_truncated`, `decode_empty`, `decode_truncated`, `decodeList_error_iff`, `decode_error_iff` and `Quic.Protection.sample_eq_error_of_short` state the fields of the error.

- The ENR, discv4 and discv5 errors carry the values their failed check compared.
  Each error fires on the same inputs as before, and codes are unchanged; each message now shows these values.
  - `Enr.EnrError.tooFewItems` carries the item count, and `unknownScheme` the value of the `id` pair.
  - The ENR messages of `repeatedKey`, `unsortedKeys` and `unknownScheme` show the keys and the scheme in hex.
  - `Discv4.Discv4Error.hashMismatch` carries the stored hash and the Keccak-256 hash of the bytes after it.
  - `Discv5.PacketError.protocolId` carries the first eight unmasked header bytes, `headerTruncated` the header bytes needed and available, `authdata` the flag and the authdata size, and `whoareyouMessage` the message size.
  - `Discv5.MessageError.fields` also carries the field count, and `invalid` the message type.
  - `Discv4.decode_hashMismatch` states both hashes of the error it returns.

- In Lean, the errors of era files, protocol bounds, light client update chunks, validator duties and proposer steps carry the values that their check compared, and their codes keep their meaning.
  - `EraError.noState` and `noStateIndex` take the type of the record that the check read, or `none` when the group ends; `stateIndex` takes the number of entries, the position the first one points at and the position of the state.
  - `EraError.genesisBlocks` takes the number of block records and whether an index of blocks is present, `noBlockIndex` the era, and `blockIndexRange` the first slot and the entries of the index, then those the era expects.
  - `BoundsError.notAtFork` and `topicNotAtFork` take the protocol or topic name and the fork, and `noRequest` the protocol; their messages do not change.
  - `ChunkError.truncated` takes the offset of the chunk, the length it needs and the length left, and `digestMismatch` also takes the expected digest.
  - `ValidatorDutyError.noMessages` takes the slot and the block root of the message to aggregate, and `pendingPayloadStatus` the slot of the vote and of the head block.
  - `ProposerError.noCommittee` takes the data of the aggregate.

  `attestationDataIndex_of_glamsterdam_of_ne` states the fields of `pendingPayloadStatus`.
  New `ToString` instances of `ValidatorDutyError`, `ProposerError` and `BoundsError` write each error with its values.
  The Python `ValidatorDutyError` and `ProposerError` carry that text in place of "validator duty failed with code N" and "proposer step failed with code N", such as "epoch 2 is after 1, the last epoch whose committees are known".

- The block, ommer and proof-of-work errors carry the values that their failed check compared.
  Each code keeps its meaning, and each error fires on the same inputs as before.
  The message of each error names each value, as `(name := value)`, and writes each hash, address and byte string in hex.
  It stays on one line, so `header invalid: EthLib.Execution.Blocks.BlockError.gasUsedAboveLimit` becomes `header invalid: EthLib.Execution.Blocks.BlockError.gasUsedAboveLimit (gasUsed := 30000001) (gasLimit := 30000000)`.
  The values that the errors already carried get names too: `wrongBaseFee 7 8` becomes `wrongBaseFee (expected := 7) (actual := 8)`.
  In Lean, these constructors of `Blocks.BlockError` take arguments:
  - `gasUsedAboveLimit gasUsed gasLimit`, `invalidGasLimit gasLimit parentGasLimit` and `timestampNotAfterParent timestamp parentTimestamp`;
  - `wrongNumber expected actual`, `extraDataTooLong size`, `nonzeroDifficulty difficulty`, `nonzeroNonce nonce` and `wrongOmmersHash ommersHash`;
  - `wrongParentHash expected actual`, whose expected hash is `none` only for a parent at a later fork than the header whose header has no RLP form;
  - `parentBeforeLondon parentFork`, `wrongFork active fork`, `ommersAfterParis count` and `wrongDaoExtraData extraData`;
  - `wrongTransactionsRoot`, `wrongStateRoot`, `wrongReceiptRoot`, `wrongBloom` and `wrongRequestsHash`, each with the header's value `expected` and the body's value `actual`;
  - `wrongWithdrawalsRoot` and `wrongBlockAccessListHash`, whose body value is an `Option`.
  `genesisNumber` and `noParent` stay bare: the number of the first is always 0, and the second fires on an empty recent chain.
  These constructors of `Blocks.OmmerError` take arguments:
  - `wrongOmmersHash expected actual`, `numberOutOfRange number blockNumber`, `parentMissing number` and `tooManyOmmers count`;
  - `duplicateOmmer hash`, `ommerInChain hash`, `ommerAlreadyIncluded hash`, `wrongAge hash age`, `parentNotRecent hash parentHash` and `siblingOfBlock hash`, each with the hash of the ommer;
  - `wrongDaoExtraData extraData`.
  `Blocks.PowError.wrongMixDigest expected actual` holds the mix digest of Ethash and that of the header, and `Blocks.PowError.resultAboveTarget result target` holds the result and the target.
  `buildPayload_eq_error_of_activeFork_ne` names the active fork and the fork of the build in its error.
  `Blocks.constructorFormat` moves to `EthLib.Execution.constructorFormat`, and `Transactions.Exports.oneLine` to `Blocks.Exports.oneLine`.

- In Lean, the errors of the fork choice, of weak subjectivity and of custody carry the values that their check compared, and their codes keep their meaning.
  - `ForkChoiceError.anchorStateMismatch` takes the state root of the anchor block and the root of the anchor state.
  - `futureBlock`, `attestationNotYetDue`, `ptcVoteNotCurrent`, `futureInclusionList` and `inclusionListTooOld` also take the current slot.
  - `blockNotAfterFinalized` also takes the first slot of the finalized epoch, and `targetEpochNotRecent` the current epoch.
  - `targetEpochMismatch` also takes the epoch of the slot, `targetNotCheckpointBlock` the root of the checkpoint block, and `terminalBlockHashNotActive` the activation epoch.
  - `futureVote` also takes the slots of the attestation and of the block, `notPreviousSlot` and `dependentBlockTooLate` the two slots they compared.
  - `invalidIndexedAttestation` takes the attestation data, and `notSlashable` the data of both attestations.
  - `invalidPayloadAttestation` and `invalidInclusionListSignature` take the validator index and the slot.
  - `invalidInclusionListSize` also takes the limit, and `emptyInclusionListTransaction` the position of the first empty transaction.
  - `WeakSubjectivityError.blockRootMismatch` takes the checkpoint root and the root that the state holds.
  - `CustodyError.outOfFuel` takes the number of groups found and the number asked for.

  `getForkchoiceStore_mismatch` and `validateTargetEpochAgainstCurrentTime_eq` state the fields of the error.
  New `ToString` instances of `ForkChoiceError` and `WeakSubjectivityError` write each error with its values.
  The Python `ForkChoiceError` and `WeakSubjectivityError` carry that text in place of the Lean `Repr` of the error, such as "fork choice: block slot 9 is after the current slot 8".

- The SSZ decoding errors carry the values that their failed check compared.
  Codes and rejection reasons are unchanged; the message `EthLib.Serialization.Ssz.Err.<name>` now ends with these values, in constructor order.
  - `Ssz.Err.offsetUnordered offset next` carries an offset and the smaller offset after it.
  - `Ssz.Err.offsetPastScope offset scope` carries the offset and the bytes of the budget.
  - `Ssz.Err.offsetUnaligned offset` and `offsetBelowTable offset` carry the first offset.
  - `Ssz.Err.truncated needed available` carries the end of the first field of the fixed part that overruns the budget, and the bytes of the budget.
  - `Ssz.Err.paddingBits byte` carries the last byte, whose bits above the last declared one are set.

- In Lean, the errors of the Builder API carry the values that their check compared, and their codes and rule names keep their meaning.
  - `ValidateBidError`: `inactiveBuilder` takes the builder index; `wrongSlot`, `wrongFeeRecipient`, `wrongParentRoot` and `wrongPrevRandao` take the expected value, then the value of the bid.
    `wrongParentHash` takes the parent hash of the bid, then the two hashes it may equal; `incompatibleGasLimit` takes the parent's gas limit, the bid's and the target; `cannotCoverBid` takes the builder index and the value.
  - `BidError`: `wrongParentHash` and `wrongFeeRecipient` take the expected value, then the header's; `badSignature` takes the builder key.
  - `RegistrationError`: `unknownValidator` and `badSignature` take the validator key, and `notEligible` the key and the current epoch.
    `clockOverflow` takes the clock and the lookahead, `tooFarInFuture` the timestamp, the clock and the lookahead, and `olderThanPrevious` the timestamp and the kept one.
  - `UnblindError.headerMismatch` takes the block hash of the blinded header, then that of the payload.

  `validateBid_zero_value` now states that no `cannotCoverBid` error, whatever its fields, comes from a bid of value zero.
  `processRegistration_exited` and `BlindedBeaconBlockBody.unblind_eq_headerMismatch_iff` state the fields of the error.

- The Noise, libp2p identity, multistream, gossip topic and subnet, and req/resp errors carry the values their failed check compared.
  Codes are unchanged; each message now shows these values.
  - `NoiseError.wrongPhase` carries the role and the number of messages handled, `truncated` the bytes needed and available, `messageTooLong` the size, and `frameLength` the declared and actual lengths.
  - `Libp2p.IdentityError.peerId` carries the first two bytes of the peer ID, or fewer when it is shorter.
  - `Multistream.MultistreamError.missingNewline` carries the last counted byte.
  - `Gossip.TopicError.forkDigest` carries the nine characters after `/eth2/`, or fewer where the string ends, and `name` the name.
  - `Gossip.SubnetError.epochOverflow` carries the epoch and the node offset, and `subnetOverflow` the two operands of the sum or product.
  - `ReqResp.ReqRespError.contextTruncated` carries the context bytes needed and available.
  - The req/resp messages of a varint or a framing error now end with the inner error.

- The secp256k1, secp256r1 and KZG errors carry the public values that their failed check compared.
  Codes are unchanged; each message now ends with these values.
  - `Secp256k1Error.coordinateTooLarge value` and `Secp256r1Error.coordinateTooLarge value` carry the coordinate, written as 32 bytes of hex in the message.
  - `Secp256k1Error.scalarOutOfRange value` carries the signature integer, `r` or `s`, written the same way; `r` is checked first.
  - `KzgError.commitmentIndexOutOfBounds index count` carries the first index past the list and the number of commitments.
  - `KzgError.cellIndexOutOfBounds index` carries the first cell index of 128 or more.
  - `KzgError.indicesNotAscending previous next` carries the first pair of neighbours whose second index is not larger.
  - `KzgError.notEnoughCells count` and `tooManyCells count` carry the number of cells given.
  - `KzgError.duplicateCommitments index` carries the position of the first commitment that repeats an earlier one.
  - The KZG theorems on these failures take the found index, as `find? … = some index`, in place of `any … = true`, and conclude the error with its fields.
  - `Base.hexNat width value` writes a number in hex behind `0x`, padded to `width` digits and never cut, for these messages.
  - `Base.any_eq_true_of_find?_eq_some` turns the found value back into the `any` that the definitions test.
  - Secret values stay out of the errors: `zeroPrivateKey`, `privateKeyTooLarge`, `unrecoverableNonce` and `noNonce` keep no fields.

- The Snappy, varint and protobuf errors carry the values their failed check compared.
  Codes are unchanged; each message now ends with these values, in constructor order.
  - `SnappyError.literalPastEnd` and `copyPastEnd` carry the bytes needed and the bytes left.
  - `SnappyError.copyOffsetZero` carries the output position of the copy.
  - `SnappyError.copyOffsetTooLarge` also carries the bytes written so far, after the offset.
  - `Snappy.FrameError.missingStreamIdentifier` carries the type of the first chunk, or `none` for an empty stream.
  - `Snappy.FrameError.headerTruncated` carries the bytes left, and `chunkPastEnd` the declared length and the bytes left.
  - `Snappy.FrameError.badStreamIdentifier` and `checksumTruncated` carry the length of the chunk data.
  - `Varint.VarintError.trailingBytes` carries the count of extra bytes, `overflow` the value, and `nonMinimal` the encoding length.
  - `Uvarint.UvarintError.tooLarge` carries the value.
  - `Protobuf.ProtobufError.truncated` carries the bytes needed and the bytes left.
  - A nested error now starts on a new line of the message when the longer message no longer fits one line.

- In Lean, `Base.ArithError.underflow` carries its operands, `underflow minuend subtrahend`, so a failed subtraction names the two values it compared.
  `Base.Uint64.subChecked a b` fails with `.underflow a b`.
  `overflow` and `divisionByZero` keep no fields.

- In Lean, `Base.Base64.Base64Error` names where the decoder stopped, counting the characters of the text from 0.
  `invalidChar position c` adds the position of the character, `invalidLength length` carries the length of the text, and `nonZeroPadBits position c` carries the last character and its position.
  `Base64.readSextet` takes the position of its character, and `Base64.decodeList` the position of its first character, as a new first argument; `Base64.decode` starts at 0.
  The ENR text decoder starts after the four characters of `enr:`, so its positions count the whole text.
  The lemmas `readSextet_encodeSextet`, `decodeList_encodeList`, `encodeSextet_of_readSextet` and `encodeList_decodeList` hold at every starting position, an implicit argument.

- In Lean, the errors of the light client carry the values that their check compared.
  Nineteen constructors of `LightClientError` gain fields, and their codes keep their meaning.
  - `invalidHeader` takes the slot of the header, and `unexpectedFinalizedHeader` the slot of the finalized header.
  - `untrustedHeader` takes the trusted root and the root of the header.
  - `invalidCurrentSyncCommitteeBranch`, `invalidFinalityBranch` and `invalidNextSyncCommitteeBranch` take the generalized index and the state root.
  - `tooFewParticipants` takes the count of signers and the minimum.
  - `slotsOutOfOrder` takes the current, signature, attested and finalized slots.
  - `unknownSignaturePeriod` takes the signature period, the store period and whether the store knows the next committee.
  - `irrelevantUpdate` takes the attested slot and the finalized slot of the store.
  - `unexpectedNextSyncCommittee` takes the aggregate key of the committee, and `conflictingNextSyncCommittee` the aggregate keys of the store's committee and the update's.
  - `invalidSignature` takes the signing root.
  - `finalizedPeriodMismatch` takes the finalized period and the store period.
  - `slotOverflow` takes the finalized slot and the timeout.
  - `beforeAltair` takes the epoch of the state and the Altair epoch, and `stateNotAtBlock` the slot of the state and of its latest block header.
  - `stateNotOfBlock` takes the block root of the state and the root it must equal, and `finalizedNotOfState` the finalized root of the state and the root of the given block.

  The new `ToString` instance of `LightClientError` writes each error with its values, such as "expected trusted block root 0x…, got header root 0x…".
  The Python `LightClientError` carries that message after "light client: ", in place of the Lean name of the constructor.

- The errors of the block header, the RANDAO reveal, the vote on the deposit contract, the slashings, the block signature and the state root carry the values that their check compared.
  `TransitionError.wrongParent` and `wrongStateRoot` hold the root of the block, then the root that the state gives.
  `invalidRandaoReveal` holds the proposer and the epoch, and `tooManyEth1Votes` the number of votes and the limit.
  `headerSlotsDiffer` and `headerProposersDiffer` hold the value of each header, and `sameHeaders` the slot and the proposer.
  `invalidHeaderSignature` holds the proposer and the signing root, and `invalidBlockSignature` the proposer and the slot.
  `notSlashableData` holds the source and target epochs of both attestations, `invalidIndexedAttestation` the position of the attestation, 1 or 2, and `noneSlashed` the number of validators in both.
  The message of a transition error is on one line and writes each root in hex behind `0x`, as in `EthLib.Consensus.TransitionError.wrongParent 0x00… 0x6a…`.
  A fork choice error that wraps a transition error writes it on one line too.
  The codes do not change.
  `processRandao_ne_invalidRandaoReveal` states that the step fails with an invalid reveal for no proposer and no epoch.

- In Lean, every node of a Merkle tree has a `Merkle.Position`, its level and its index, and the tree passes positions instead of a level and an index.
  The node hash has type `Position → α → α → m α`; it had type `Nat → Nat → α → α → m α`, with the level first.
  `Merkle.node hash leaves ⟨level, j⟩`, `Merkle.siblings hash leaves p n`, `Merkle.ordered p` and `Merkle.climb hash p current siblings` take a position; `Merkle.root` and `Merkle.path` keep their arguments.
  `Merkle.node hash leaves level j` becomes `Merkle.node hash leaves ⟨level, j⟩`, and the recursion on the level is `Merkle.node.go`.
  A position names its `parent`, `sibling`, `left` and `right` children and its `ancestor` `k` levels up, and `EthLib.Cryptography.Proofs.Merkle.Position` proves how they relate.
  `Merkle.div_two_div_pow` moves to that module, under the same name.
  The searches `Merkle.findCollision`, `Merkle.findSecondPreimage` and `Merkle.climbPairs` take the starting position instead of a level and an index.
  `Merkle.Collision` and `Merkle.SecondPreimage` hold one `position` field, the position of the node they attack, instead of a level and an index.
  `Merkle.findCollision_valid` concludes `c.position = p.ancestor (k + 1)` in place of the level and index equations.
  `Merkle.SecondPreimage.Valid` also requires the position to be above the leaves, where the node has children.
  `Merkle.findSecondPreimage_valid` states that this node is a strict ancestor of the starting position, with `Position.IsAncestor`.
  In the random oracle model, `Merkle.RandomOracle.NodeInput R` is `Position × R × R`, so the domain of the node oracle changes.
  `Merkle.RandomOracle.nodeHash` and `Merkle.RandomOracle.queryNode` take a position.
  The agreement hypotheses of `Merkle.node_congr`, `path_congr` and `climb_congr`, and of the XMSS and SPHINCS+ lemmas built on them, quantify over positions.
  The query lemmas of `EthLib.Cryptography.Proofs.QueryAvoidance` take a position and a node hash of a position.
  The node hashes of XMSS, SPHINCS+, FORS and the VRF take a position and compute the same bytes.
  The XMSS, SPHINCS+ and FORS nodes and the SSZ climb still take a level or height and an index, and build the position.
  Lemmas about climbs from a leaf state its positions as `(⟨0, j⟩ : Position).ancestor n` and its `sibling`, `left` and `right`, in place of `⟨n, j / 2 ^ n⟩`.
  `Position.ancestor_mk_zero` and the `_mk` lemmas of the position module convert between the two forms.
  `XmssSecurity.Concrete.CacheReplay.div_pow_succ` is removed; `Merkle.div_pow_div_two` states the same fact.
  To migrate a node hash, read `p.level` and `p.index` where it read the level and the index.

- In Lean, ten general lemmas that [#2647](https://github.com/ethereum/EthLib/pull/2647) made public move into the namespaces of the objects they describe ([#2648](https://github.com/ethereum/EthLib/issues/2648)).
  Statements are unchanged; use the new names.
  - `active_of_mem_voters` becomes `Store.active_of_mem_voters`.
  - `slot_mem_range_of_voteOrigin` becomes `Store.slot_mem_range_of_voteOrigin`.
  - `exists_voteOrigin_of_mem_supporters` and `previousBlockSlot_le_previousCurrentSlot` become `Store.ForwardReachableWith.exists_voteOrigin_of_mem_supporters` and `Store.ForwardReachableWith.previousBlockSlot_le_previousCurrentSlot`.
  - `data_eq_of_signed_of_target_epoch`, `latest_slot_floor_of_signed_rank`, `mem_supportersOf_of_latest_signed`, `latest_eq_of_rank_eq`, `notSlashed_checkpointState` and `previousSlot_le_of_time_le` get the prefix `Execution.`.

- In Lean, `Store.isAncestor_of_same_blocks` no longer takes the hypothesis that the receiver holds the ancestor ([#2648](https://github.com/ethereum/EthLib/issues/2648)).
  Remove the `targetKnown` argument, which came after `sourceKnown`.
  The walk from the tip in the receiver reaches the ancestor, so the conclusion is unchanged.

- In Lean, the theorems of the `Toolchain` proof modules move to sub-namespaces, and the theorems that repeat them are removed ([#2627](https://github.com/ethereum/EthLib/issues/2627)).
  `Base.Toolchain.mkObj_eq`, `isNull_eq`, the `isNull` theorem of each constructor, and `getArr?_eq`, `getStr?_eq`, `getNat?_eq`, `getBool?_eq` and `getObjVal?_eq` move to `Base.Toolchain.Json`.
  `Base.Toolchain.compare_eq` becomes `Base.Toolchain.String.compare_eq`, and `filterM_eq`, `filterAuxM_nil` and `filterAuxM_cons` move to `Base.Toolchain.List`.
  `EthLib.Base.Proofs.Toolchain.Repr` is removed; import `EthLib.Base.Proofs.Nat` and use `Base.digitChar_eq` in place of `Base.Toolchain.digitChar_eq`.
  `Serialization.JsonRpc.isNull_str` and `isNull_arr` are removed; use `Base.Toolchain.Json.isNull_str` and `isNull_arr`.
  `Tls13.size_toUTF8` is removed; use `String.toUTF8_eq_toByteArray` and `String.size_toByteArray`.
  Statements are unchanged.
  The `isNull` theorems on `Json.null`, `bool`, `str`, `arr`, `obj` and `mkObj` are now `@[simp]` rules, so `simp` can close goals that it left open before.
  Each entry of `scripts/check_layers_baseline.txt` now starts with the label of the rule that it allows.

- In Lean, the Python conversion laws and properties move from `EthLib.Base.Exports.Proofs.PyValue` to `EthLib.Base.Proofs.Exports.PyValue` ([#2630](https://github.com/ethereum/EthLib/issues/2630)).
  Update imports for `pyExport_items` and the hexadecimal conversion theorems; their statements are unchanged.
  `EthLib.Base.Exports.PyValue` imports the law instances at compile time, and `pyExport` keeps the same law constraints.
  The Python extension links only runtime dependencies and preserves C exports and runtime initializers as public native symbols.
  The linker hides EthLib's compile-time and legacy initializers and discards their unused sections.
  C callers that initialize the extension through an `initialize_EthLib_*` symbol must use the corresponding `runtime_initialize_EthLib_*` symbol or import the Python module.

- In Lean, the honest-duty supporter and head theorems use `VotesInSlots` for one complete epoch, including their accountable companions.
  For `Execution.mem_supportersOf_of_duty_epoch` and its accountable companion, pass the scoped votes after the epoch and slot binders, before `beginOk`.
  For `Execution.isAncestor_getHead_of_duty_epoch` and its accountable companion, include the scoped votes inside the `margin` existential, after the time bounds and before the stake inequality.
  For `Execution.exists_voteAt_of_duty_interval`, bind `begin`, `last` and `slot` before the scoped votes, and supply `beginTime` and `endTime` after `fits`.
  `VotesInSlots` couples `VoteAt` and `VoteCommittees` on the same witness; the latter requires the committee check only after successful target-cache reads.
  Conclusions and the existing unbounded `Votes` definition are unchanged.

- In Lean, the compressed encoding of a point of `G1` has its 48 bytes in its type ([#2189](https://github.com/ethereum/EthLib/issues/2189)).
  `G1.compress` returns a `Vector UInt8 48`, and `G1.uncompress`, `G1.keyValidatePoint` and `G1.keyValidate` take one.
  A caller that holds bytes of another length reads them with `exactBytes? 48`, now in `EthLib.Base`, and rejects `none` as decompression did.
  `G1.size_compress` and `keyValidatePoint_size_ne` are removed, since the type states the length.
  `G1.uncompress_ok_cases` no longer states the size, and `uncompress_ok_cases_bytes` and `uncompress_eq_zero_or_bytes` state its facts on the bytes of the input.
  `TrustedSetup.decodeG1` and `TrustedSetup.decodeG2` decode one point of a setup, and the theorems on decoded setups state their facts through them.
  `Signatures.keyMessagePair` is the pair of one key and one message in the core aggregate verification.
  `coreVerify_iff` takes the key as a vector, and `packBytes_pointToPubkey` and `packBytes_skToPk` become `pointToPubkey_eq` and `skToPk_eq`.
  `SyncDrawable.keys` states key validation of each key as a vector.
  No C export or Python function changes.

- In Lean, `EthLib.Execution.Exports.Proofs.Evm` and `EthLib.Execution.Exports.Proofs.Trie` move to `EthLib.Execution.Proofs.Exports.Evm` and `EthLib.Execution.Proofs.Exports.Trie` ([#2630](https://github.com/ethereum/EthLib/issues/2630)).
  Declaration names and statements are unchanged; update the imports.
  Consumers that received these theorems through an `Exports` root must import the relevant proof module or `EthLib.Execution.Proofs`.

- In Lean, `Evm.Call.TransferLog` becomes `Evm.TransferLog`, and the XMSS security modules `XmssSecurity.Scan.*` move to `XmssSecurity.Proof.Scan.*` ([#2629](https://github.com/ethereum/EthLib/pull/2629)).
  The import checker now finds a cycle between directories through imports at any depth, and these moves break the two such cycles that remained.
  Declaration names, namespaces and statements are unchanged; update the imports.

- In Lean, specification modules keep only the theorems that their definitions and instances need, plus persistent `@[simp]` rules ([#2628](https://github.com/ethereum/EthLib/pull/2628)).
  55 theorems move to the matching `Proofs` modules.
  In Base, two move from `Base.BigEndian` to `Base.Proofs.BigEndian`, five from `Base.Except` to `Base.Proofs.Except`, and one from `Base.Hex` to `Base.Proofs.Hex`.
  In Cryptography, twelve move from `Cryptography.Montgomery` to `Cryptography.Proofs.Montgomery.Core`, and one each from `Hash.Scrypt` and `Sphincs.Tree` to `Proofs.Hash.Scrypt` and `Proofs.Sphincs.Tree`.
  The XMSS and SPHINCS+ constants follow: ten move from `Xmss.Constants` to `Proofs.Xmss.Constants`, and twenty-one from `Sphincs.Constants` to `Proofs.Sphincs.Constants`.
  In Execution, one moves from `Evm.Step` to `Proofs.Evm.Step`, and in Serialization, one from `Ssz.Typed.Rooted` to `Proofs.Ssz.Typed.Rooted`.
  The SSZ export proofs `EthLib.Serialization.Exports.Proofs.Ssz` become `EthLib.Serialization.Proofs.Exports.Ssz`, and `EthLib.Serialization.Exports` no longer imports them.
  Declaration names and statements are unchanged; add the `Proofs` imports.

- Fork-choice replay returns a nonempty list of handler outcomes for each input step ([#2622](https://github.com/ethereum/EthLib/pull/2622)).
  An admitted block's first outcome reports admission; the rest report its attestations and attester slashings, in order.
  Carried operations run only for an admitted block, so a rejected block gives one outcome, its error.
  Each successful handler commits independently, and a failed carried operation does not stop later calls.
  An invalid payload verdict applies its removal after the step, even a rejected one, and after the carried operations of an admitted block.
  Other inputs have one outcome.
  This changes `fork_choice`, `forkChoice`, `replayForkChoice` and `replayForkChoiceConfirming`.
  Every export that takes fork-choice steps replays blocks this way.
  Callers must inspect each nested outcome, not treat the input as one atomic operation.
  The public `runForkChoiceStep` block branch now performs bare admission only; its type is unchanged.
  `Store.onBlockWithVotes` and its nine wrapper-only lemmas are removed; call the spec handlers separately.

- In Lean, `Models.Network.Handles.block` calls `Store.onBlock` without processing carried operations ([#2622](https://github.com/ethereum/EthLib/pull/2622)).
  The `blockAttestation` and `blockAttesterSlashing` constructors process them separately.
  Each requires the enclosing signed block in the view and its root among the blocks of the receiving store, so carried operations run only for an admitted block.
  Update case analyses of `Handles` to cover both constructors and their two new premises.
  This changes `forkChoice` executions and `UpToDate`, and transitively `Prompt` and `VoteAt`, even where their signatures are unchanged.
  `BlocksAdmitted` requires only bare `onBlock` success, with its other conditions unchanged.

- In Lean, modules move so that no two directories of a layer import each other ([#2617](https://github.com/ethereum/EthLib/pull/2617)).
  In Execution, `Evm.Call.Delegation`, `Evm.Machine.Errors`, `Blocks.Log` and `Fees.BlobGas` become `Evm.Delegation`, `Evm.Errors`, `Evm.Log` and `Transactions.BlobGas`.
  In Serialization, `Ssz.Codec.Error` becomes `Ssz.Error`, and the proof modules `Proofs.Ssz.Type.Bounds`, `DefaultLaws` and `FitsLaws` move to `Proofs.Ssz.Codec`.
  In Consensus, the proof module `Models.Network.ForkChoice` becomes `Proofs.ForkChoiceNetworkModel`.
  In Cryptography, the XMSS `Unforgeability` modules move to `Security.XmssSecurity`, with `Statement` renamed `ConcreteStatement`, and the SPHINCS+ security modules regroup under `Forgery`, `GraphView`, `HiddenOracle`, `PreparedRun`, `RefinedForgery`, `ScanSigner` and `SmallBudget`.
  Declaration names, namespaces and statements are unchanged; update the imports.

- The QUIC and TLS codecs use packed byte arrays for byte strings, as [Shared types](ARCHITECTURE.md#shared-types) requires ([#2616](https://github.com/ethereum/EthLib/pull/2616)).
  In Lean, packet-header fields, frame payloads, TLS byte fields and transcripts use `ByteArray` in place of `List UInt8`.
  `Varint`, `Packet`, `Frame` and TLS `encode` and `decode` use `ByteArray` at their byte boundaries.
  Use `.size` for a byte length and `.data.toList` only when calling the internal list readers.
  In Python, these fields use `bytes` in place of `list[int]`; convert an existing byte list with `bytes(value)` and write an empty byte string as `b""`.
  Collections of messages, extensions, key shares and ALPN protocol names remain lists.
  Encoded wire bytes and rejection codes are unchanged.

- In Lean, the proof modules `FastConfirmationCommittees`, `FastConfirmationConfirmedRoot`, `FastConfirmationIndicators`, `FastConfirmationSets` and `FastConfirmationSupporters` move under `EthLib.Consensus.Proofs.ForkChoice.FastConfirmation` as `Committees`, `ConfirmedRoot`, `Indicators`, `Sets` and `Supporters` ([#2566](https://github.com/ethereum/EthLib/pull/2566)).
  The declarations of the former `FastConfirmation` module move to `FastConfirmation.Basic`, and importing `FastConfirmation` still provides them and all five leaves.
  Declaration namespaces and statements are unchanged.

- `ssz.get_generalized_index` names a field of a container only by its name ([#2480](https://github.com/ethereum/EthLib/issues/2480)).
  A position given for a field is refused with the error for an unknown field.
  In addition, a path takes `__active_fields__` and `__selector__`, the mixed-in nodes of a progressive container and of a union.

- In Python, `consensus.api_post` and `consensus.api_gossip_event` return the data of each event as its JSON text, instead of the parsed value ([#2515](https://github.com/ethereum/EthLib/pull/2515)).
  This is the `data` field of the Beacon API event stream, and the form that the fork choice events already return.
  A caller that needs the value applies `json.loads` to that text.

- In Lean, the SSZ exports read a Python value directly, without writing it as JSON first ([#2475](https://github.com/ethereum/EthLib/issues/2475)).
  In Lean, `valueOfJson` becomes `valueOf`, `jsonOfValue` and `jsonOfValues` become `pyOfValue` and `pyOfValues`, and `descOf`, `tagged`, `optionalNat`, `pair` and `readValue` take a `PyValue`.
  Bytes given as `bytes` are taken as they are, instead of being written as hex and read back.
  Nothing breaks in Python: every input gives the same result or the same error as before.

- In Lean, the shuffle, custody, keystore and discv5 callers of SHA-256 keep the digest as a `Vector UInt8 32` ([#2189](https://github.com/ethereum/EthLib/issues/2189)).
  `Shuffle.bucketBits` and `Keystore.passwordChecksum` return one, and `Shuffle.bitAt` and `DataAvailability.firstUInt64` take one.
  A caller that needs the bytes applies `packBytes`, and `Sha256.packBytes_hash32` gives back the byte-array digest.
  The keystore checksum theorems compare the checksum with `store.checksum` directly, and `checksumVector` is removed: use `passwordChecksum`.
  Nothing breaks in Python.

- The execution RPC answers `eth_simulateV1` with its simulated blocks ([#2108](https://github.com/ethereum/EthLib/issues/2108)).
  The results of the calls are not yet in the blocks.
  In Lean, `fillHeader`, `outputChecks_fillHeader` and `runBody_fillHeader` move from `EthLib.Engine` to `EthLib.Execution.Blocks`, and `SimulateChoices` gains `gasCap`.
  Nothing breaks in Python.

- In Lean, the block environment gains the field `blobGasPrice` ([#2108](https://github.com/ethereum/EthLib/issues/2108)).
  A simulation sets the base fee per blob gas with it, and its default `none` keeps the price of the excess blob gas.
  Supply that field in positional constructors, or use structure notation with its default.
  The checks and the run of a transaction, and the simulation overrides of a body, take optional lifted rules.
  A simulation can skip the nonce check and lift the gas caps of EIP-8037 with them.
  The sender check gains a flag for the nonce check.
  Nothing breaks in Python.

- In Lean, the transaction environment gains the field `precompiles` ([#2108](https://github.com/ethereum/EthLib/issues/2108)).
  It gives the address of the precompile that a call to each address runs.
  Its default `some` keeps each precompile at its own address, so a real block is unchanged.
  Supply that field in positional constructors, or use structure notation with its default.
  The checks of a transaction, its run and the body of a block take optional simulation overrides.
  A simulation can give the sender in place of the signature, and that sender may have code.
  The sender check gains a flag for that case.
  Nothing breaks in Python.

- The execution RPC checks the requests of `eth_simulateV1` before their blocks run ([#2107](https://github.com/ethereum/EthLib/issues/2107)).
  In Lean, `call_unknown` requires the method name to differ from `eth_simulateV1`.
  Nothing breaks in Python: `rpc.apply_overrides` gives the state root after the account overrides of one block.

- The execution RPC serves `eth_getBlockAccessList` and `debug_getRawBlockAccessList` ([#2106](https://github.com/ethereum/EthLib/issues/2106)).
  In Lean, `BlockRecord` gains the optional field `accessList` for the retained list.
  Supply that field in positional constructors, or use structure notation with its `none` default.
  `Follows` requires each retained list to equal the execution builder's list.
  `call_unknown` requires the method name to differ from both access-list method names.
  Nothing breaks in Python: `rpc.serve` takes the new optional argument `pruned_access_lists` for block numbers whose lists are unavailable.
  `rpc.encode_block_access_list` encodes a JSON list as its EIP-7928 RLP bytes.

- In Lean, `Frame` gains the field `slashed`, after `pubkeysDistinct` ([#1451](https://github.com/ethereum/EthLib/issues/1451)).
  A validator slashed before a step, at a registry position, is slashed after it at the same position.
  A proof that builds a `Frame` with an anonymous constructor adds that field.
  `frame_setValidatorAt_of_whole`, `frame_setValidator_of_whole` and `frame_setValidator` take a new premise `old.slashed = true → validator.slashed = true` after the proof of the key.
  A caller passes `id` when the new validator copies the flag of the old one, and `fun _ => rfl` when it is slashed.
  `initiateValidatorExit_balances_eq_and_pendingConsolidations_eq` moves to `Consensus/Proofs/Transition/PendingConsolidations.lean`, which `BalanceDrift.lean` imports publicly.

- In Lean, the results on slashed flags state them at each position of the registry, through `slashedFlagAt state position`, the read `(state.validators.data[position]?).map (·.slashed)` ([#2187](https://github.com/ethereum/EthLib/issues/2187)).
  From Gloas the registry has no limit in its type, so a position may lie beyond every `ValidatorIndex`.
  A proof whose goal spells out the read unfolds the name first, as in `simp only [slashedFlagAt] at h`.
  `slashedFlag_initiateValidatorExit` is renamed `slashedFlagAt_initiateValidatorExit`, and it takes a `position : Nat` in place of an index.
  The second conjunct of `slashValidator_slashedFlag` holds at each position other than `slashedIndex.toNat`.
  A caller that read either at an index `i` reads it at `i.toNat`.
  The new `slashedFlag_eq_of_slashed` turns equal flags there into equal values of `slashedFlag` at `i`.
  `slashIfSlashable_ok` and `foldlM_slashIfSlashable` gain a last conjunct: no slashed flag changes at a position other than that of their index, or that none of their indices names.
  A pattern that takes them apart needs a fourth component.
  `UpgradeFrame` gains the field `slashed`, since each upgrade keeps every slashed flag.
  `ElectraKept` gains the same conjunct, so a pattern that takes it apart needs a fourth component too.
  `UpgradeFrame.trans_blockFrame` takes the new premise `slashed`: the steps after the upgrade keep every slashed flag.
  A block frame alone may slash, so it cannot give the field.
  Compose the block frames of the steps first, and pass their slashed flags once.
  `slashedFlagAt_processProposerSlashing` and `slashedFlagAt_processAttesterSlashing` state that a slashing changes flags only at the positions that it names.
  `slashedFlagAt_foldlM` states the same for a fold of such steps.
  `slashed_setValidatorAt` is renamed `slashedFlagAt_setValidatorAt`.
  `foldlM_ok_invariant_of_mem` moves to `Base/Proofs/MapM.lean`, in the namespace `EthLib.Base`.

- `engine_forkchoiceUpdated` checks that the most recent block of proof of work on the chain of the head is terminal, as step 3 of the method and step 2 of payload validation of Paris require.
  A head whose chain fails the check is `INVALID`, with the zero hash, and the head does not change.
  Once the known finalized block is a payload of the tree, a zero safe or finalized hash gives `-38002`.
  The latest valid hash of an invalid head is zero when its latest valid block is of proof of work.
  In Lean, `KnownPayload` has the new field `powTotalDifficulty`, `none` for a payload, so its anonymous constructor takes a fifth value.
  `forkchoiceUpdated` takes a `TransitionConfiguration` first, and `forkchoiceUpdatedCall` takes one after the chain configuration.
  `forkchoiceUpdated_valid`, `forkchoiceUpdated_of_belowFinalized`, `forkchoiceUpdated_valid_none_iff`, `forkchoiceUpdated_of_invalid`, `forkchoiceUpdated_of_onChain` and `forkchoiceUpdated_eq_error_iff` state the terminal block check.
  `forkchoiceUpdated_valid`, `forkchoiceUpdated_of_onChain` and `forkchoiceUpdated_eq_error_iff` also state the rule on zero hashes, and `forkchoiceUpdated_of_invalid` answers `latestValidHash` in place of `latestValid`.
  In Python, a block of the tree of `engine.forkchoice_updated` may carry `totalDifficulty` and `parentTotalDifficulty`.
  The function takes the required keyword-only argument `terminal_total_difficulty`, as `engine.new_payload_on_chain` does.
  A tree with no block of proof of work passes the check whatever that value, which must be below `2^256`.
  The native `engine_forkchoice_updated` takes that value after the finalized block.
- `engine_newPayload` on a chain checks that a parent of proof of work is a terminal block, as step 2 of payload validation of Paris requires.
  A parent that fails the check makes the payload `INVALID`, with the zero hash and the new reason code 407.
  In Lean, `PayloadError` has the new constructor `invalidTerminalBlock`, with that code.
  `newPayloadOnChain` takes two new arguments before the chain: a `TransitionConfiguration`, and the total difficulty of the last block of the chain.
  Its theorems take both values, and `newPayloadOnChain_of_stateTransition_ok`, `newPayloadOnChain_of_stateTransition_error` and `newPayloadOnChain_of_buildPayload` take the hypothesis that the parent passes the check.
  In Python, `engine.new_payload_on_chain` takes the required keyword-only arguments `terminal_total_difficulty` and `total_difficulty`, and the native `engine_new_payload_on_chain` takes them after the recent blocks.
  A last block from Paris on passes the check, so then any total difficulty, and any terminal total difficulty below `2^256`, do.
- In Lean, the bound on the extra data of an Engine payload is the named constant `Execution.Blocks.MAX_EXTRA_DATA_BYTES`, in place of the literal `32`.
  The statements of `anyPayload_executionPayloadJson`, `payloadV4_executionPayloadV4Json`, `payloadOfBlock_extraData` and `newPayloadParams_json` change only by that name, and so do `payloadOfBlock` and `anyPayload`.
  The constant is `32`, so a proof that used `omega` on the bound first unfolds it, as in `simp only [MAX_EXTRA_DATA_BYTES]; omega`.
- In Lean, `EpochFrameLaws` now extends `EpochStepLaws`, which holds every law except those for a new validator and for the queue of pending deposits.
  The theorems that need neither law moved from the `EpochFrameLaws` namespace to the `EpochStepLaws` namespace, with the same statements, and they now take the smaller structure.
  Dot notation on a value of either structure still finds them; a full name such as `EpochFrameLaws.processSyncAggregate` becomes `EpochStepLaws.processSyncAggregate`.
- In Lean, `processEpoch_split_of_lt_altair` moved from the `EpochFrameLaws` namespace to the `EpochStepLaws` namespace, with the same statement, and it now takes the smaller structure.
  Dot notation on an `EpochFrameLaws` value still finds it.
  A call by the full name `EpochFrameLaws.processEpoch_split_of_lt_altair laws` becomes `EpochStepLaws.processEpoch_split_of_lt_altair laws.toEpochStepLaws`.
- In Lean, the JSON readers and writers of the base types moved from `EthLib.Engine.Json` to `EthLib.Serialization.JsonRpc`, with their theorems.
  They are `hexValue`, `hexDigits`, `bytesOf`, `bytes`, `fixed`, `address`, `quantity`, `bytesMax`, `uint64`, `paramsArray`, `array`, `fields`, `hasExactly`, `field`, `dataJson`, `quantityJson`, `listJson` and `optionJson`.
  Their namespace is now `EthLib.Serialization.JsonRpc`.
  The readers among them return `Read`, an alias of `Except String`, in place of `Except EngineError`, and reject an input with a reason.
  An Engine decoding lifts that reason to `EngineError.invalidParams`, through `Engine.Json.lift` and its `MonadLift` instance, so every Engine decoder returns what it returned before.
  `withdrawal` and `withdrawalJson`, with their theorems, moved to `EthLib.Execution.Rpc`.
  The Python bindings are unchanged.

- In Lean, `DirectSafety.EnoughStake run high` requires the stake floor only at epoch calls whose current epoch is at most `high + 1`.
  The floor reaches one epoch past the finalized epoch of `b` in `accountable_safety`, and one epoch past `j.epoch` in the other three direct safety endpoints.
  Move `j` (and `k` for `accountable_justified_unique`) before the stake premises.
  An existing unbounded floor proof adapts as `fun call _ => oldEnough call`.
  Pass a target-epoch bound as the new `within` argument of `quorum_count`.
  Remove the `starts` argument from `accountable_safety` and `accountable_safety_justified`, but keep it for `accountable_justified_unique`.
  `conflict` and `ordered` imply the removed bound on the slot of `x`, so the theorems cover the same runs as before.
  The drift horizon in the conclusion of `accountable_safety` is the finalized epoch of `b`, not the larger of the two finalized epochs; `ordered` makes them equal.

- In Lean, the direct safety endpoints bound the unslashed active stake at `x`, `unslashedKeys x.state`, in place of `activeKeys x.state` ([#2187](https://github.com/ethereum/EthLib/issues/2187)).
  `Accountable` takes the shared prefix and the two tails, `shared left right`, in place of the two full runs, and `accountableKeys` takes them in place of the two full runs and the reference state.
  Slashing evidence counts only in the tails; double votes still count over the full runs, and proposer slashings in the tails still count.
  `accountableKeys` keeps only the unslashed keys active at `x`.
  `recentKeys` keeps only unslashed keys, `referenceLoss` sums over `unslashedKeys x`, and `referenceGain` subtracts the support of `unslashedKeys x`.
  So `boundaryStake`, and through it `stateDrift` and `derivedDrift`, count only unslashed recent stake.
  `Run.slashed_evidence` holds for a run from any state, with no `genesis` argument, and concludes `SlashedAt x.state v.pubkey ∨ run.SlashingEvidence v.pubkey`.
  `SlashedAt` names the predicate that `referenceLoss` stated inline before.
  `verifiedConflict_of_accountable` takes `shared left right` and concludes `VerifiedConflict (shared.append left) (shared.append right) key`.
  Pass `shared left right` where a caller passed `shared.append left`, `shared.append right` and `x`.
  `DirectSafety.accountable_safety_justified_terminal` and `Store.Reachable.finalized_ancestor_or_accountable` change the same way: their stake alternative bounds the unslashed active stake, at `x` or at the anchor state, by `accountableKeys` of the shared prefix and the two tails.
  The new Lean declarations are `DirectSafety.SlashedAt`, `DirectSafety.unslashedKeys`, `DirectSafety.EpochCall.pubkeysDistinct` and `Run.pubkeysDistinct`.
  `Run.pubkeysDistinct` gives distinct keys at the end of a run from genesis; `EpochCall.pubkeysDistinct`, `view_quorum_count` and `view_voters_recent` read it.

- In Lean, `DirectSafety.HashEvidence objects` is stated through the searches `findMessageCollision` and the new `findZeroRoot`, in place of a bounded existential ([#2187](https://github.com/ethereum/EthLib/issues/2187)).
  No C export or Python function changes, and every theorem that mentions `HashEvidence` keeps its statement.
  `hashEvidence_iff` proves that the new body is equivalent to the old one, for every list of objects and with no hypothesis.
  `findZeroRoot_valid` and `findZeroRoot_eq_none_iff` say what the new search returns and when it fails.
  The two bodies are not definitionally equal.
  A proof that unfolds `HashEvidence` to take it apart first rewrites with `hashEvidence_iff`, or applies `hashEvidence_iff.mp`.
  A proof that builds the evidence as an `Or` of the old form applies `hashEvidence_iff.mpr`.

- In Lean, `DirectSafety.slashingLimits` counts only the indices that are slashable at the operation.
  It still reads every index with `getValidator`, so its errors are unchanged.
  It then keeps the validators for which `isSlashableValidator` holds at the current epoch, the test of `slashIfSlashable`.
  An attester slashing pays nothing for an index that is already slashed, so its limits no longer count one.
  So every value derived from it can only decrease.
  These are the `creditLimit` and `debitLimit` of the `.slashings` events, and through `fundingCredit (.slashings)` the values `activeStakeWindow`, `consolidationRate` and the right side of `departure_charges_le_funded_window`.
  `residualCredit` and `sourceDrift` read the same limits, so they can only decrease too.
  A call on one proposer that is not slashable now gives zero limits.
  The replay of a successful proposer slashing is unchanged, since `processProposerSlashing` requires the proposer to be slashable.
  Every theorem statement is unchanged.

- In Lean, the four rules by which one justification step finalizes a checkpoint have one definition, `FinalizationStepRule state after checkpoint` ([#2187](https://github.com/ethereum/EthLib/issues/2187)).
  The bits come from the state after the step, the epoch and the justified checkpoints from the state before it.
  `weighJustificationAndFinalization_finalized` states its second disjunct as `FinalizationStepRule state after after.finalizedCheckpoint`, with the same unfolded body.
  `DirectSafety.FinalizationRule call checkpoint` is `FinalizationStepRule call.cached call.weighed checkpoint`, with the same unfolded body.
  A proof that took either apart by name first unfolds `FinalizationStepRule`.
  No C export or Python function changes.

- `verify_kzg_proof` checks its inputs in the order of EIP-4844: the commitment, `z`, `y`, then the proof.
  When more than one input is invalid, the first in that order gives the error.
  Before, it checked the proof second, so an input with an invalid `z` and an invalid proof raised the error of the proof.
  It now raises the error of `z`.
  The verdicts are unchanged, and so are the errors of an input with at most one invalid argument.

- In Lean, `verifyBlobKzgProof_binding` states its hypotheses as EIP-4844 converts the commitment and the proof.
  It takes the raw bytes, the values that `bytesToKzgCommitment` and `bytesToKzgProof` return, and the points that `uncompressG1` decodes from them.
  A caller that holds `validateKzgG1Point b = .ok C` gets the two new hypotheses from `bytesToKzgCommitment_of_validateKzgG1Point` and `uncompressG1_of_validateKzgG1Point`.
  The same holds for the proof, with `bytesToKzgProof_of_validateKzgG1Point`.
  The C exports and the Python functions are unchanged.

- Along a chain from genesis, the public keys of the validators stay a prefix and stay distinct ([#1421](https://github.com/ethereum/EthLib/issues/1421)).
  No C export or Python function changes.
  In Lean, `Frame` and `UpgradeFrame` gain the fields `pubkeysPrefix` and `pubkeysDistinct`.
  They bring back the key-keeping fact that [#1950](https://github.com/ethereum/EthLib/pull/1950) removed for [#1908](https://github.com/ethereum/EthLib/issues/1908), where it was named `KeysKept`.
  `validatorKeys` lists the keys of the registry and `PubkeysDistinct` says that they have no repeat.
  `validatorKeys_prefix_and_distinct_of_chainSteps` states, for a run of steps, that the keys of its first state are a prefix of the keys of its last state.
  It also states that distinct keys stay distinct.
  `validatorKeys_prefix_and_distinct_of_genesis_chainSteps` states both along a chain from genesis.
  `frame_addValidatorToRegistry` takes a proof that the key is not in the registry, and `EpochFrameLaws.addValidatorToRegistry` takes it too.
  `frame_setValidatorAt_of_whole`, `frame_setValidator_of_whole`, `EpochFrameLaws.setValidator` and the `setValidatorAt` field of `EpochFrameLaws` take the old validator and a proof that the state holds it at that position.
  They also take a proof that the new validator keeps the key of the old one.
  `frame_setValidator`, `EpochFrameLaws.setValidator_of_sameBalance` and `EpochFrameLaws.setValidatorAt_of_sameBalance` take the proof of the key.
  `applyPendingDeposit_cases` decomposes a pending deposit.
  `addValidatorToRegistry_slot` states that adding a validator keeps the slot.

- In Lean, the gossip message ID has its length in its type.
  `Gossip.messageId` returns `Vector UInt8 20` in place of a `ByteArray`.
  A caller that needs a `ByteArray` takes `Base.packBytes (messageId fork topic data)`.
  `messageId_size` is removed, since the type states the length.
  `messageId_of_ok` and `messageId_of_error` state the ID as `(Sha256.hash32 input).take 20`.
  The new `packBytes_messageId_of_ok` and `packBytes_messageId_of_error` state their former equations, through `Base.packBytes`.
  The C export `eth_gossip_message_id` and the Python `gossip.message_id` are unchanged.

- Slashing-protection imports use EIP-3076's minimal strategy ([#1963](https://github.com/ethereum/EthLib/issues/1963)).
  Import compacts both the held record and the file: each key keeps its greatest block slot and its greatest source and target epochs, taken independently, without signing roots.
  So a repeat of any message held before the import is refused, and so is a block at or before the slot limit, or a vote with a source before the source limit or a target at or before the target limit.
  The keys of the record come out in byte order.
  The JSON format and the C and Python signatures are unchanged.

- A checkpoint of a fork-choice store comes from the anchor, a held state or its pull-up ([#1423](https://github.com/ethereum/EthLib/issues/1423)).
  No C export or Python function changes.
  In Lean, `Store.Reachable.justified_origins` and `Store.Reachable.finalized_origins` state this for a reachable store.
  In the new module `Consensus.Proofs.ForkChoice.CheckpointAncestry`, `Store.Reachable.finalized_ancestor_or_accountable` gives three cases for the finalized checkpoint of the store.
  It is at or before the anchor epoch, or it is on the chain of the justified checkpoint at the first slot of its epoch.
  Otherwise two runs from the anchor to held states of the store bound the accountable stake, or show hash evidence.
  It asks that every block was imported with the setting of the signature checks of the run from genesis, as `Store.BlockStatesFromParents`, which `Store.ForwardReachableWith.blockStatesFromParents` gives.
  The drift of its bound counts from the anchor, so the bound loosens as the justified epoch moves away from the anchor epoch.
  `DirectSafety.TerminalView` reads the checkpoints of the last state of a run, or of one justification step on it, as fork choice runs it.
  `DirectSafety.accountable_safety_justified_terminal` states direct accountable safety for two such views, and like the theorems it extends it asks no bound on the fork of either run.
  `DirectSafety.accountable_safety_justified` is its case without a step, and its statement is unchanged.
  The other new Lean declarations are `TerminalView.state`, `TerminalView.enough`, `TerminalQuorum`, `TerminalQuorum.source`, `TerminalQuorum.voters`, `TerminalQuorum.currentEpoch_le`, `ViewQuorum`, `ViewQuorum.source`, `ViewQuorum.target`, `ViewQuorum.voters`, `ViewQuorum.state`, `ViewQuorum.eq_inl_of_realized`, `view_field_crossing`, `view_finalized_quorums`, `view_quorum_attestations`, `view_quorum_count`, `view_quorum_target_binding`, `view_conflicting_fields_quorums`, `view_voters_recent`, `checkpoint_binding_prefixes` and `hashObjects_append_subset`, all in `DirectSafety`, and `Store.ancestorRoots_of_parent`, `Store.updateCheckpoints_unrealizedJustifications` and `Store.updateUnrealizedCheckpoints_unrealizedJustifications`.
  The new `Store.SameCheckpoints` says that two stores have the same justified, finalized, unrealized justified and unrealized finalized checkpoints.
  `Store.SameCheckpoints.refl`, `.justified`, `.finalized`, `.unrealizedJustified` and `.unrealizedFinalized` read it; a caller that names these projections does not depend on the order of the four checkpoints.
  `Store.storeTargetCheckpointState_frame`, `Store.onAttestation_frame`, `Store.onAttesterSlashing_frame`, `Store.recordBlockTimeliness_frame` and `Store.updateProposerBoostRoot_frame` end with two new conjuncts.
  They state `Store.SameCheckpoints` of the store and the result, and that the unrealized justifications are unchanged.
  `Store.onTickPerSlot_frame` ends with a new conjunct: a store `moved`, the store itself or `updateCheckpoints` with its unrealized checkpoints, has `Store.SameCheckpoints` with the result, and the unrealized justifications are unchanged.
  `Store.computePulledUpTip_frame` ends with a new conjunct: the held state of the tip and the result of its justification and finalization.
  The conjunct also gives a store `moved` with `Store.SameCheckpoints` of the result, built from that result, and the unrealized justifications with that result's current justified checkpoint added for the tip.
  A pattern that destructures the four checkpoints destructures them in one nested pattern.
  A caller that destructures one of these seven results adds one pattern, and only if its last pattern named the old last conjunct.
  A pattern that ends in `-` needs no change.
  A projection of the old last conjunct gains `.1`.
  So `.2.2` of `Store.onAttestation_frame` and `Store.onAttesterSlashing_frame` becomes `.2.2.1`, and `.2.2.2.2` of `Store.onTickPerSlot_frame` becomes `.2.2.2.2.1`.
  The `.2.2.2` of the other four frames becomes `.2.2.2.1`.
  The new `Store.catchUp_preserves` states that catch-up keeps each property of the store that every tick within a slot keeps.
  It composes preservation over the individual tick steps.
  `Store.catchUp_frame`, `Store.catchUp_ordered` and the catch-up step of `Store.onTick_checkpointStates_latestMessages` now read it, with unchanged statements.
  The new `Store.onTick_ok` splits a tick into the slot of its time, the catch-up to that slot and one tick within it.
  `Store.onTick_frame`, `Store.getCurrentSlot_onTick`, `Store.onTick_ordered`, `Store.onTick_checkpointStates_latestMessages` and `Store.exists_getCurrentSlot_onTick_ge` now read it, with unchanged statements.
  The new `Store.Reachable.linked_of_unknown` gives the links of a reachable store whose anchor parent is unknown, and `Store.Reachable.parentsBelow` keeps its statement.

- The theorem that a block leaves its header as the latest block header holds at every fork ([#2061](https://github.com/ethereum/EthLib/issues/2061)).
  In Lean, `latestBlockHeader_processBlock` drops its `gloas` argument, and its conclusion is unchanged.
  Callers remove that argument.

- The cumulative churn bounds also hold for idle queues ([#1451](https://github.com/ethereum/EthLib/issues/1451)).
  In Lean, `churnQueue_foldlM_le` drops its `first` argument, and `computeExitEpochAndUpdateChurn_foldlM_le` and `computeConsolidationEpochAndUpdateChurn_foldlM_le` drop their `open_` argument.
  Callers remove that argument.
  The exact `_spend` equalities keep it.
- A req/resp payload now fails when bytes follow the chunk that completes its declared length.
  A reader must reject any bytes that remain after it has read the declared number of SSZ bytes.
  The decoder read the whole Snappy stream.
  So it accepted chunks after the one that completes the length, if they add no bytes: padding, reserved skippable chunks, a second stream identifier or an empty data chunk.
  With a declared length of 0, the reader now reads the stream identifier alone, so any chunk after it fails too.
  `reqresp.decode_payload` and `reqresp.decode_response_chunk` raise `ReqRespError` with the message "N bytes follow the last chunk of the payload", and the C exports return the new error code 10.
  In Lean, `decodePayload` reads the stream with the new `Snappy.readFrames`, which stops at the chunk that completes the declared length and returns the bytes after it.
  `Snappy.readChunks` is its chunk loop, and the new module `Networking.Proofs.Snappy.Read` proves their properties.
  `ReqRespError` gains the constructor `trailingBytes`.
  The last conjunct of `decodePayload_ok` and `decodePayload_eq_ok_iff` is now `Snappy.readFrames … = .ok (d.data.toList, [])` in place of `Snappy.decodeFrames … = .ok d`.
  `decodeFramesList_of_readFrames` gives the list form of the old conjunct, and the new `decodePayload_append_ne_ok` proves that bytes appended to a payload that decodes make it fail.
- The leanXMSS signing lemmas over a map of monads now derive, from the monad laws, that the map keeps `map` ([#1385](https://github.com/ethereum/EthLib/issues/1385#issuecomment-6722640861)).
  `findCodeword_map_monad`, `otsSign_map_monad`, `signLayer_map_monad` and `signDerived_map_monad` require `LawfulMonad` instances for both monads instead of an explicit `map_map` argument.
  Drop that argument at each call.
  `Sphincs.Unforgeability.map_monad_map` moves to `HashSig.map_monad_map`, so leanXMSS and leanSPHINCS share one proof that such a map keeps `map`.
- From Gloas, the discount for empty slots of the fast confirmation rule also counts the votes for the pending node of the parent ([#1368](https://github.com/ethereum/EthLib/issues/1368), [#1458](https://github.com/ethereum/EthLib/issues/1458)).
  A parent has three nodes from Gloas: a pending one, and a full and an empty one for the two answers on its payload.
  The discount counted only the votes for the full or the empty node that the block builds on.
  It counts the votes for that node and for the pending node, and the votes for the other of the two stay out.
  A vote cast in the slot of the block it names supports the pending node of that block.
  A member of the committees of the empty slots can hold such a vote for the parent, and the discount missed it.
  Before Gloas the parent has only its pending node, and the discount keeps its value.
  No signature of a C export or Python function changes.
  From Gloas the threshold can be lower, so a `fast_confirmation` step of `fork_choice` can confirm a block sooner.
  In Lean, `Store.getNodeSupportBetweenSlots` takes a list of nodes in place of a node, and counts a vote for any of them.
  `getNodeSupportBetweenSlots_le` takes that list too.
- The block supply bound and the Glamsterdam equality now follow from the exact block supply equation ([#1902](https://github.com/ethereum/EthLib/issues/1902)).
  No C export or Python function changes.
  In Lean, `supply_systemCall`, `supply_systemCall_join`, `supply_startSystemCalls`, `supply_blockRequests` and `applyTransactions_supply` are gone from `EthLib.Execution.Proofs.Blocks.Supply`.
  The new `SystemCallBurns.total_eq_zero_of_glamsterdam`, `StartSystemCallsBurns.total_eq_zero_of_glamsterdam`, `TransactionsBurns.total_eq_zero_of_glamsterdam`, `RequestsBurns.total_eq_zero_of_glamsterdam`, `BlockRequestsBurns.total_eq_zero_of_glamsterdam` and `BodyBurns.total_eq_zero_of_glamsterdam` in `EthLib.Execution.Proofs.Blocks.Burn` prove that the certified losses are 0 from Glamsterdam.
  `withdrawnWei`, `rewardWei`, `createdWei`, `burnedWei` and the supply lemmas of the DAO transfer, the withdrawals and the rewards move to `EthLib.Execution.Proofs.Blocks.Burn`, with the same names.
  `EthLib.Execution.Proofs.Blocks.Burn` no longer imports `EthLib.Execution.Proofs.Blocks.Supply`, so import the latter for `headerBurnedWei`, the `applyBody_supply` theorems and the `stateTransition_supply` bounds.
- From Gloas, the rewards and penalties and the inactivity updates of an epoch now fail where a registry position of 2^64 or more would become a validator index ([#1883](https://github.com/ethereum/EthLib/issues/1883)).
  The specification builds a `ValidatorIndex` for each position when it applies the deltas, and for each eligible validator when it lists the eligible indices.
  EthLib took such a position modulo 2^64, so it credited the balance, or updated the inactivity score, of another validator.
  Before Gloas the registry stays within its limit, which is below 2^64, so nothing changes there.
  No C export or Python function changes.
  In Lean, `applyDeltas_eq_ok_iff` now reads the balance at the position itself, not at the position modulo 2^64, and adds the condition that the position is below 2^64.
  `applyAllDeltas_balances`, `foldlM_applyAllDeltas_balances` and `processRewardsAndPenalties_balances_of_altair` no longer take a bound on the size of the registry.
- The FFG chain theorems now derive that the block of each justified checkpoint is in the chain of the block of its recent epoch from the order of the roots at consecutive slots, instead of assuming it ([#1420](https://github.com/ethereum/EthLib/issues/1420)).
  No C export or Python function changes.
  In Lean, the field `chain` of `SlackStepBounds` becomes `links`, which asks the map from roots to blocks to keep in order the roots of consecutive slots (`rootLinks`).
  `SlackChainInvariant` gains the field `roots`, a `RootsAbove` fact that the new `FfgRoots.lean` keeps along each chain step.
  The new `ChainRoot` orders the roots by the links of the states that genesis reaches, and `slackJustifiedCheckpoints_chainRoot_of_chainSteps` uses it, so it asks no order hypothesis.
  The new `recentJustified` names the justified checkpoint of a recent epoch, and `RootsAbove.le_of_getBlockRoot` gives the order that justification reads; `RootsAbove.of_chainStep`, `RootsAbove.of_initializeBeaconStateFromEth1` and `toChainRoot` are new too.
  New shared lemmas: `getBlockRootAtSlot_ok_iff`, `getBlockRootAtSlot_exists`, `getBlockRootAtSlot_between` and `getBlockRootAtSlot_congr` (`Accessors.lean`), `advanceSlot_previousJustified`, `processBlock_blockRoots`, `processUpgrades_slot` and `processUpgrades_blockRoots`.
- From Gloas, the pending deposits of an epoch now fail at every deposit they read to a key whose first validator sits at a registry position of 2^64 or more ([#1883](https://github.com/ethereum/EthLib/issues/1883)).
  The specification builds a `ValidatorIndex` from that position before it tests the validator, so it fails there.
  EthLib failed only when it credited such a deposit, and missed the deposit to a validator that exits and is not withdrawn, and the deposit beyond the churn.
  Before Gloas the registry stays within its limit, which is below 2^64, so nothing changes there.
  No C export or Python function changes.
  In Lean, `depositTargetStatus` now returns an `Except AccessorError (Bool × Bool)`.
  The fields `stops`, `used`, `appliedFilter` and `movedFilter` of `PassPendingDepositsFacts`, and `processPendingDeposits_postponed`, test that result.
  The new field `statusOk`, and a new conclusion of `processPendingDeposits_postponed`, say that the status of each deposit read succeeds.
  The new `addValidatorToRegistry_size_lt` says that a new validator joins a registry of fewer than 2^64 validators.
- The FFG theorems on the beacon chain now take their votes from the attestations that blocks apply, instead of from any data that some signature verifies on ([#1888](https://github.com/ethereum/EthLib/issues/1888)).
  Under the BLS checks a verifying signature exists for every data that a registered key can sign, so the old votes did not say who voted.
  No C export or Python function changes.
  In Lean, `SignedVote`, `TargetFlagsSigned` and `PendingSigned` are gone, with their lemmas, `voteFrame_processOperations` and the two `of_stateTransition` lemmas of the flags and the pending attestations.
  The new `attestationVotes` and `blockVotes` name the votes that an attestation and a block cast, and `TargetFlagsVoted` and the new `PendingVoted` take a set of such votes.
  `VoteFrame` drops its configuration, its signature checks and its field `signed`, and `voteFrame_processAttestation` and `voteFrame_processBlock` give the votes of the step by name; the latter takes the preset bound `apart`.
  The slot and upgrade lemmas of the flags and the pending attestations no longer take a bound on the registry.
  The link and slack theorems of `FfgJustification.lean` and `FfgSlack.lean` take the vote set and a hypothesis that the votes of the model hold it, with no slot condition.
  `SlackChainInvariant` drops its configuration, its signature checks and its field `known`, takes the vote set, and uses its votes in the model; `SlackStepHypotheses` replaces `contains` by `applied`, on the new `blockStepVotes`.
  `runVotes` drops its argument `block` and now holds the beacon votes that the block steps of a run cast, so a caller wraps it in `ffgVotes block`.
  `ForkVersionsKnown` is gone with its lemmas, and `initializeBeaconStateFromEth1_target` becomes `JustifiedEarly.of_initializeBeaconStateFromEth1`, which gives only the equal justified checkpoints.
  `TargetFlagAt.of_flagsKeptOrZero` moves to `Upgrade.lean`.
- The theorem that an attestation keeps the registry and the RANDAO mixes now holds at every fork ([#1888](https://github.com/ethereum/EthLib/issues/1888)).
  No C export or Python function changes.
  In Lean, `processAttestation_registry` drops its argument `before : fork < .altair`, so a caller removes it.
- From Gloas, builder deposits, exits and onboarding, ejections, slashing penalties, attestation committee counts and active-validator reads now fail where a position of 2^64 or more would become a 64-bit index ([#1883](https://github.com/ethereum/EthLib/issues/1883)).
  Such a position used to wrap modulo 2^64, so the step read or wrote another validator or builder.
  The registry updates, the slashing penalties, the effective-balance updates and the genesis activations read and write each validator at its plain position, as the specification indexes the registry with a Python integer.
  No C export or Python function changes.
  In Lean, `addBuilderToRegistry` now returns an `Except TransitionError`; bind its result, and pass a successful return to `builderBalanceSum_addBuilderToRegistry`.
  The new `getValidatorAt`, `getBalanceAt` and `BeaconState.setValidatorAt` read and write at a plain position, and `getValidator_eq_getValidatorAt`, `getBalance_eq_getBalanceAt` and `setValidator_eq_setValidatorAt` relate them to the index forms.
  `EpochFrameLaws` replaces its `setValidator` field by a `setValidatorAt` field, and the theorem `EpochFrameLaws.setValidator` gives the index form; `EpochFrameLaws.setValidatorAt_of_sameBalance`, `frame_setValidatorAt_of_whole`, `activeStep_setValidatorAt` and `sameSizes_setValidatorAt` are new.
  `KeysKept`, `Frame.keysKept` and `UpgradeFrame.keysKept` are gone, as no theorem read them ([#1908](https://github.com/ethereum/EthLib/issues/1908)); `advanceSlot_keys` becomes `advanceSlot_kept`, without the key conjunct.
  The setter laws of `EpochFrameLaws` and the frame lemmas of validator writes no longer take a key equality, and the `_of_whole` forms no longer take the old validator.
  `activeKept_processEpoch`, `activeKept_processBlock`, `activeKept_advanceSlot`, `ChainStep.activeKept`, `activeKept_of_chainSteps`, `processBlock_attestationSplit`, `voteFrame_processBlock`, `committeesKept_processBlock`, `committeesKept_advanceSlot`, `RunKept.committeesKept`, `slackJustifiedCheckpoints_chainRoot_of_chainSteps`, `slackFinalized_chainRoot_of_chainSteps` and `processEffectiveBalanceUpdates_effectiveBalance` drop their registry-size argument.
  `SlackStepBounds` drops its field `small`, and the field `RunKept.active` no longer takes a registry bound.
  `getTotalActiveBalance` reads the checked active indices.
  The new `getActiveValidatorIndicesChecked` converts each active position with `ofNatChecked`, as the specification builds each index, and the new `getCommitteeCountPerSlotChecked` also converts their count.
  `getActiveValidatorIndicesChecked_eq_ok_iff` replaces `getActiveValidatorIndices_eq_mapM_ofNatChecked`, and `getTotalActiveBalance_ne_indexOutOfRange` drops its registry bound.
  New lemmas on the checked read: `getActiveValidatorIndicesChecked_ok`, `_of_size_le`, `_of_within`, `_of_attesterShuffle`, `_error` and `_eq_error`, `lt_of_getActiveValidatorIndicesChecked_ok`, `sorted_of_getActiveValidatorIndicesChecked_ok`, `mem_iff_of_getActiveValidatorIndicesChecked_ok` and `ActiveKept.getActiveValidatorIndicesChecked_eq`.
  New lemmas on the checked count: `getCommitteeCountPerSlotChecked_of_within` and `getCommitteeCountPerSlotChecked_ok`; in `Base`, `ofNatChecked_toNat`, `mapM_ofNatChecked_eq_ok_iff` and `mapM_ofNatChecked_error`.
  `getValidatorAt_eq_ok_iff`, `getBalanceAt_eq_ok_iff` and `committeePositions_ne_nil` are new.
  The new `committeeCountOf` gives the committee count for a number of active validators, so the checked count converts the length of the checked list without a second pass over the registry.
  `CommitteesKept.of_seed` also takes the equality of the checked active indices of the two states.
  `proposerCandidates` takes the checked active indices instead of the epoch, and `proposerCandidates_spec` places each candidate among them.
  `getEligibleValidatorIndices_sorted`, `getEligibleValidatorIndices_ok` and `processInactivityUpdates_scores` drop their registry bound: the new `getEligibleValidatorIndices_fits` bounds each eligible position of a successful computation, and the new `validatorPositions_sorted_of_fits` sorts positions under such a bound.
  The new `depositTargetStatus_ne_indexOutOfRange` states that the status of a deposit target never fails on an index, through the new `getElem?_toNat_eq_of_ofNatChecked`.
  `exists_mem_getBeaconCommittee` takes a successful checked active-index read, and `attestationCommitteesSize_of_attesterShuffle` takes a successful checked committee-count read.
  `attestationCommitteesSize_cons` includes that count check on its right side.
- From Gloas, a deposit, a withdrawal or consolidation request, or a sync aggregate now fails where a registry position of 2^64 or more would become a validator index ([#1883](https://github.com/ethereum/EthLib/issues/1883)).
  Such a position used to wrap modulo 2^64, so a deposit at 2^64 validators overwrote validator 0.
  The step now fails with the accessor error `arith overflow`, as the specification fails to build a `ValidatorIndex` there.
  Before Gloas the registry holds at most 2^40 validators, so nothing changes there.
  No C export or Python function changes.
  In Lean, the new `Base.Uint64.ofNatChecked` converts a natural number to a `UInt64`, and fails with an overflow at 2^64 or more.
  `getIndexForNewValidator` now returns an `Except AccessorError ValidatorIndex`, and `queueConsolidation` takes the index of the source in place of its position.
  `addValidatorToRegistry_validators_eq_push`, `addValidatorToRegistry_push`, `activeStep_addValidatorToRegistry` and the deposit theorems of `Proofs.Transition.Operations` and `Proofs.Transition.EpochPending` no longer take a bound on the size of the registry.
  The fields `used`, `appliedFilter` and `movedFilter` of `PassPendingDepositsFacts` no longer take a bound either.
  `frame_queueConsolidation`, `sameSizes_queueConsolidation` and `payloadInputs_queueConsolidation` take the index of the source in place of its position.
- The exact change of the supply of ether across a transaction is now proved at every fork, with the burns of SELFDESTRUCT and the deleted balances as terms fixed by the run ([#1793](https://github.com/ethereum/EthLib/issues/1793)).
  No C export or Python function changes.
  In Lean, the rules of a relation of frames split in two: `OrdinaryStepRules` holds the rules of every write but SELFDESTRUCT, and `StepRules` extends it with the rule of SELFDESTRUCT.
  The lemmas `sameContext`, `refl` and `lift`, and those of SSTORE, TSTORE, the calls, the creations and the instructions that send a message, move from the `StepRules` namespace to `OrdinaryStepRules`.
  So a qualified name changes, while the dot notation on a `StepRules` value still works.
  `OrdinaryStepRules.instruction` takes a proof that the opcode is not SELFDESTRUCT, and `StepRules.instruction` is gone; `StepRules.step` covers every instruction.
  The new `OrdinaryStepRules.step` concludes that a step either runs SELFDESTRUCT, as the new `RunsSelfdestruct` says, or keeps the relation.
  `runTransaction_eq_ok` now concludes `TransactionRun`, a definition that unfolds to the same seven equations, and `TransactionRun.unique` proves that its values are fixed by the transaction and its output.
  The new `processMessage_frame_byKind` runs the induction over messages for any fact about the frame of a call, and `processMessage_rel_byKind` keeps its statement and now follows from it.
- The fork choice now rejects an attestation whose committees are not those of its slot, a step of the safety proof of the fast confirmation rule ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  It runs the committee check of block processing in the state of the target, with one aggregation bit for each member of the committees.
  Before Electra the index must be below the count of committees of the slot.
  From Electra each index of the committee bits must be below that count, each of those committees must have a bit set, and the index of the attestation must be 0 before Gloas.
  Before, a committee index past that count named a committee of a later slot of the same epoch, or none, so a validator could vote for a slot before its own.
  Gossip validation and block processing already rejected such an attestation.
  The rejection is the fork choice error `transition`, which carries the error of the check, such as `committeeIndexOutOfRange`; a failed shuffle is now reported there too.
  No signature of a C export or Python function changes, but an `attestation` step of `fork_choice` now rejects these attestations, and so does a `block` step that carries one.
- The safety threshold of the fast confirmation rule now fails when the discount for empty slots exceeds the weight of the committees since the parent ([#1832](https://github.com/ethereum/EthLib/issues/1832)).
  It fails with the new fork choice error `supportDiscountAboveMaximum`, of code 53, where it used to return half of what was left, or 0.
  A block at or before the current slot never reaches that error, and a proof shows it.
- The theorems on the four system contracts of EIP-4788, EIP-2935, EIP-7002 and EIP-7251 now hold from Glamsterdam too, with the state gas meter of EIP-8037 ([#1861](https://github.com/ethereum/EthLib/pull/1861)).
  No C export or Python function changes.
  In Lean, each `systemCall_set` and `systemCall_dequeue`, with its `spec_set` or `spec_dequeue`, no longer requires a fork before Glamsterdam.
  The one-counter gas premises of `spec_set` and `spec_dequeue` are multiplied by `storageGasScale fork`, which is 1 before Glamsterdam and 5 from it.
  `RequestQueue.sstore_writes` and `RequestQueue.sstore_then` change the same way, and their continuation must hold with up to 22,100 gas times that factor less.
  The SSTORE rules `sstoreStep_eq`, `sstoreG`, `sstore` and `sstore_of_account` of the EVM logic now hold from Berlin at every fork.
  They charge `sstoreTotalCost`, the price and the state gas of the write, where they charged `sstoreCost`.
  Before Glamsterdam, `sstoreTotalCost_of_lt` turns that charge back into the price.
  `SystemContract.systemCall_of_spec` and `SystemContract.systemCall_of_writesStorage` no longer require a fork before Glamsterdam, and take a proof that the code passes `SupportedCode` from Glamsterdam.
- Each fork upgrade now gives one upgrade frame, and the invariant across the upgrade follows from it ([#1841](https://github.com/ethereum/EthLib/pull/1841) and [#1851](https://github.com/ethereum/EthLib/pull/1851)).
  `UpgradeFrame` now also keeps the finalized checkpoint, and it carries the balance count and the exit order of the validators.
  So a caller that builds one supplies the three new fields, and `UpgradeFrame.of_carried` takes the finalized checkpoint and the number of balances as new premises.
  `UpgradeFrame`, its constructors, `UpgradeFrame.invariant` and the frame of each upgrade are in `EthLib.Consensus.Proofs.Transition.Upgrade`, and `upgradeFrame_upgradeNext` is in `EthLib.Consensus.Proofs.Transition.ForkBoundary`.
  `upgradeFrame_carryFields` no longer takes a proof that the fork is at least Altair.
  `Invariant.of_carried` is gone; `UpgradeFrame.invariant` replaces it.
  No statement of an invariant theorem changes, and no C export or Python function changes.
- The fast confirmation rule now weighs the committees of a range of slots exactly, in place of an average per slot ([#1828](https://github.com/ethereum/EthLib/issues/1828)).
  Each active member of the committees counts once, by its effective balance in the source of balances, and a range with a whole epoch still weighs the total active balance.
  The average did not bound a given committee, so the rule could confirm a block that an attack then reorgs.
  The rule can now confirm fewer blocks, or more, than before, and some pinned fast confirmation vectors expect the old answers.
  `estimateCommitteeWeightBetweenSlots`, `adjustCommitteeWeightEstimateToEnsureSafety` and `COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR` are gone; the new `Store.computeCommitteeWeightBetweenSlots` replaces them, and takes the head and the source of balances.
  `Store.computeCommitteeWeightAndMembers` also returns the members it reads, and `Store.getEquivocationScoreOf` weighs the equivocators of a given set.
  No C export or Python function changes.
- A contract creation now fails at an address with non-empty storage, at every fork, as [EIP-7610](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification) asks ([#1823](https://github.com/ethereum/EthLib/issues/1823)).
  Before, such a creation wiped the storage and ran the init code.
  It now fails exactly like a creation at an address with code or a nonce, as [EIP-684](https://eips.ethereum.org/EIPS/eip-684#specification) asks: a creation transaction ends with `addressCollision`, and CREATE or CREATE2 takes the gas of the message and pushes 0.
  So a block with such a creation can now have another gas used, another state root, or be rejected.
  From Glamsterdam, CREATE or CREATE2 that collides gets back the state gas of the new account that it paid, as [EIP-8037](https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-new-accounts) asks of a collision.
  Only a target with storage but no nonce, code or balance paid any.
  `accountDeployable` also requires empty storage, through the new `accountHasStorage`.
  The rules `createKind_stored`, `create_stored` and `create2_stored` take a new hypothesis: no fact of a slot gives the new address a word other than zero.
  The new theorems `accountHasStorage_eq_true_iff`, `accountDeployable_eq_true_iff` and `accountDeployable_congr` state the rule.
- The Engine API now models `engine_getPayloadV1` to `engine_getPayloadV6` ([#1848](https://github.com/ethereum/EthLib/pull/1848)).
  `EngineError` has a new constructor, `unknownPayload`, with code 38001, so an exhaustive match on it needs a new case.
  A store of completed builds holds the result of the payload build, its blobs bundle, the override flag and, from Glamsterdam, the block access list.
  The returned payload must give back the stored block hash, with the stored requests and access list.
  From version 3 the commitments of the bundle must hash to the blob hashes of the block, in order, and its proofs must verify.
  The C export `eth_engine_get_payload` takes the configuration, the store and the request.
  Each entry of the store holds the payload ID, the fork and the four results of `eth_engine_build_payload`.
  Then come the network forms of the blob transactions, the flag and the access list.
  In Python, `engine.get_payload` takes the configuration, the store, the method and its parameters.
  The payload ID has one type, `PayloadId`, which the forkchoice update also returns.
  The network check of a blob transaction now runs `validateBlobs` on its lists, so `countsMatch` is `blobCountsMatch` on its fields.
- The forkchoice update now checks the timestamp of payload attributes, on an applied valid head ([#1479](https://github.com/ethereum/EthLib/issues/1479)).
  A known payload holds the number and the timestamp of its block, so `KnownPayload` has two new fields, `number` and `timestamp`.
  `forkchoiceUpdatedCall` takes the chain configuration first, and returns the attributes at the fork of their timestamp.
  Attributes of a fork that the version does not take now give code 38005, `unsupportedFork`.
  Version 1 takes Paris, version 2 Paris and Shapella, version 3 Dencun to BPO5, and version 4 Glamsterdam.
  Version 2 with the structure of version 1 from Shapella, or of version 2 before it, gives code 38003.
  So do attributes whose timestamp is not above that of the head.
  The C export `eth_engine_forkchoice_updated` takes the configuration first, and each payload of the tree needs `number` and `timestamp`.
  In Python, `engine.forkchoice_updated` takes the configuration first.
- The forkchoice update now models `engine_forkchoiceUpdatedV4`, and it checks the structure of the payload attributes on an applied valid head ([#1478](https://github.com/ethereum/EthLib/issues/1478)).
  Attributes that fit no structure of the version now give code 38003, `invalidPayloadAttributes`, where any object gave code 0 before.
  Attributes that fit still give code 0, since no payload build is specified.
  A wrong number of parameters now has the reason `params: got N, expected 2`, or `2 or 3` for version 4, in place of `params: not 2 values`.
  `forkchoiceUpdatedParams` takes the version first and returns the attributes as JSON, or `none`, in place of a flag.
  `EngineError` has a new constructor, `invalidPayloadAttributes`, with code 38003.
- `MIN_REQUEST_LIMIT`, the fewest versioned hashes that `engine_getBlobs` must take in one request, is now `MIN_BLOBS_REQUEST_LIMIT`.
  Its value stays 128, and no C export or Python function changes.
- The optimistic store now holds its head as a fork choice node, a root and the status of its payload, in place of the root of the head block ([#1475](https://github.com/ethereum/EthLib/issues/1475)).
  From Gloas, the optimism of the head reads the payload that the status names, so it can fail as a payload chain does, and it returns an `Except`.
  The C export `eth_consensus_is_optimistic_node` takes the code of that status after the head root: 0 empty, 1 full and 2 pending.
  In Python, `consensus.is_optimistic_node` takes it as the keyword `head_payload_status`, 2 by default, so a call before Gloas gets the same answer as before.
  The latest verified ancestor now takes a fork choice node; before Gloas it reads only the root.
  The C export `eth_consensus_latest_verified_ancestor` takes the code of the status after the root, and `consensus.latest_verified_ancestor` takes it as the keyword `payload_status`, 2 by default.
  The latest verified ancestor and the optimistic node now run at Gloas.
  The theorem `latestVerifiedAncestor_of_glamsterdam` now states the Gloas answer, no longer a failure.
  The optimistic node then fails when the head is not optimistic, since its second case is not yet specified.
- `compute_min_epochs_for_block_requests` now takes the fork, and from Gloas it applies a formula derived from the [weak subjectivity period of EIP-8061](https://eips.ethereum.org/EIPS/eip-8061#weak-subjectivity-period).
  Before, every fork got the Phase 0 value: 33024 epochs on mainnet, where Gloas asks for 14299.
  `Config.computeMinEpochsForBlockRequests` takes the fork as a new argument.
  The C export `eth_consensus_compute_min_epochs_for_block_requests` reads the configuration and the fork as a pair, as `eth_consensus_gossip_topics` does.
  In Python, `consensus.compute_min_epochs_for_block_requests` takes the fork first, then the configuration, `mainnet` by default.
- `NoiseError` now gives its own code to each failure of the local identity secret, of signing and of the saved remote message, in the libp2p Noise handshake ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  Before, a failure of the secret or of signing had code 9, the code of an invalid remote identity.
  An identity secret that is 0, or at least the secp256k1 group order, now gives code 11, `identitySecret`.
  A failure of ECDSA signing with that secret gives code 12, `signing`.
  Completion of a state whose saved remote message is missing, or does not match the state, gives code 13, `savedRemote`.
  Before, such a state gave the error of the failed step: code 1, 3, 4, 6, 7, 8 or 9.
  Code 9 now means only a remote identity that fails to authenticate.
- The libp2p Noise handshake gives the identity secret, the chaining key and the handshake hash their own types, apart from the type of the X25519 keys ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  The secp256k1 identity secret of `writeLibp2p` and `makePayload` is a scalar `Secp256k1.Fn`, in place of 32 bytes.
  `Libp2p.publicKey` and `Libp2p.sign` take that scalar too, and the exports read it from 32 big-endian bytes whose value must be below the group order.
  The chaining key and the handshake hash of `SymmetricState` have the types `ChainingKey` and `HandshakeHash`, and `hkdf2` takes a `ChainingKey`.
  The C exports and the Python functions keep their signatures: they take the secret and return the chaining key and the hash as 32 bytes.
  `writeLibp2p` now rejects a zero identity secret before every other check, on every message, message 1 included.
  The C export `eth_noise_libp2p_write`, and `noise_libp2p_write` in Python, give code 11 for a secret of 0 or at least the group order.
  Before, a write at step 0 ignored the secret: message 1 succeeded, and a responder writing out of turn got code 1, `wrongPhase`, or code 10, `firstMessageExtensions`.
- The libp2p Noise state now stores the authenticated remote, in place of the encrypted remote message and the state before it ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  Completion returns that remote with the transport ciphers, and reads no message.
  It returns `Remote × CipherState × CipherState`.
  `Libp2pState.remoteMessage` is now `Libp2pState.remote`, a `Remote` with the static key, the identity point, the signature and the extensions.
  `AuthenticatedRemote`, `RemoteInfo` and `remoteInfo` are removed, and `authenticatePayload` returns a `Remote`.
  `writeLibp2p` no longer runs completion after message 3.
  The Python state of `noise_libp2p_*` holds the remote as `(static_key, public_key, signature, extensions)`, or `None`, in place of the saved message and its state.
  Completion checks that the stored remote has the remote static key of the handshake, and no longer verifies its signature.
  Code 13, `savedRemote`, now means that at completion the state holds no remote, or one whose static key is not the remote static key of the handshake.
  `readLibp2p_authenticates` now concludes that the new state stores the authenticated `Remote`.
  The theorems `complete_authenticates` and `complete_peerId` are replaced by `complete_ok` and the `Produced` theorems, and `authenticatePayload_decode` by `authenticatePayload_ok`.
  The C exports and Python functions that take a libp2p state, to write, read or complete, also give code 13 when the stored public key does not decode.
- `ethlib.networking.noise` now exports short typed wrappers in place of the raw `noise_*` names of the extension ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  `noise_initialize` is now `initialize`, `noise_cipher_encrypt` is `cipher_encrypt`, `noise_libp2p_complete` is `libp2p_complete`, and so on; `libp2p_write` takes `extensions=None` by default.
  The package also exports the type aliases of its states, `CipherState`, `HandshakeState`, `Remote`, `Libp2pState`, `Identity` and `Completion`, which `lake exe gen-bindings` writes from Lean, and `NoiseError`.
  The extension methods keep their names and signatures.
- A chain configuration now holds the address of its deposit contract, and the deposit requests of a block come from that address ([#1486](https://github.com/ethereum/EthLib/issues/1486)).
  Before, every chain read deposits from the mainnet address, so a chain with another deposit contract, such as Sepolia, got no deposit request.
  The configuration that the exports read as JSON, or as a Python `dict`, must give `depositContractAddress`: `0x` and forty hex digits, or 20 bytes in Python.
  A configuration without it is rejected with `config: no depositContractAddress`.
  `depositRequests`, the C export `eth_block_deposit_requests` and `blocks.deposit_requests` in Python take the address first.
- The output of the VRF tree at index `i` now hashes the index before the secret: `keccak256(PQ_VRF_OUTPUT | LE32(i) | s)` ([#1652](https://github.com/ethereum/EthLib/pull/1652)).
  Every output changes, for every root, index and seed.
  Roots and openings are unchanged, so an existing opening still verifies, but returns a different output.
  `verify`, `verifyBytes` and `evaluate` keep their arguments, and `outputHash` takes the index.
  Before, one secret placed at every leaf gave every index the same output, which the holder could choose.
  A new `mixOutput`, the C export `eth_vrf_mix` and `vrf.mix` in Python hash an output with randomness.
  A selection must compare that mixed value, with randomness revealed after the root is registered.
- `engine_forkchoiceUpdated` now applies step 2 of its specification ([#1018](https://github.com/ethereum/EthLib/pull/1018)).
  The execution layer may know a finalized block from an earlier update.
  A valid head below that block is answered `VALID`, and the forkchoice state is not checked.
  The Lean function and the C export `eth_engine_forkchoice_updated` take that block as a new argument, between the tree and the request.
  The C export reads it as JSON text: a block hash, or `null` for none.
  In Python, `engine.forkchoice_updated` takes it as the keyword `finalized`, `None` by default, so a call without it gets the same answer as before.
- `engine_forkchoiceUpdated` with payload attributes now answers a syncing head, an invalid head and a head below the known finalized block, since no payload build begins there ([#1018](https://github.com/ethereum/EthLib/pull/1018)).
  A request that would select a new head with payload attributes is still refused with code 0, because the build is not specified.
- The shuffle errors of `ConsensusError` now have the codes 201 to 204, in place of 1 to 4 ([#1087](https://github.com/ethereum/EthLib/pull/1087)).
  The custody errors already had the codes 1 to 3 in the same class, so a code did not name one error.
  A caller that tests `code == 1` for an index at or past the count now tests `code == 201`.
  The new code 204 is a count above 2^40.
- `compute_shuffled_index` and `compute_shuffled_permutation` now fail for a count above 2^40, as the consensus specification does ([#1072](https://github.com/ethereum/EthLib/pull/1072) and [#1087](https://github.com/ethereum/EthLib/pull/1087)).
  Before, the index wrapped a bucket number that does not fit in 4 bytes and returned a value.
- The C export `eth_engine_forkchoice_updated` now rejects a tree of known payloads that names one block hash twice, with code 0 ([#1102](https://github.com/ethereum/EthLib/pull/1102)).
  Before, it answered from the first entry of that hash and ignored the second.
- The Ethash exports, the CRC-32 and CRC-32C exports and the precompile price now take and return typed values ([#1516](https://github.com/ethereum/EthLib/pull/1516)).
  A number crosses as a Python `int`, and the proof-of-work function returns its mix digest and its result as a pair.
  The C exports take the tuple of their arguments as one value, as `eth_consensus_fork_choice` does.
  In Python, an argument that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError` before.
  Examples are a `str` given for bytes and a `bool` given for an `int`.
  A negative number raises `ValueError`, where it raised `OverflowError`.
  An address of 2^64 or more has no precompile, so its price raises `PrecompileError`, where it raised `OverflowError`.
- The EVM word and memory exports, the CREATE address, the fee exports and the block difficulty now take and return typed values ([#1524](https://github.com/ethereum/EthLib/pull/1524)).
  `eth_evm_word_op` takes the opcode and a list of at most three operands, each an `int` below 2^256.
  `eth_evm_extend_memory` replaces `eth_evm_extend_memory_cost` and `eth_evm_extend_memory_expand_by`, and returns the price and the growth as a pair.
  Each range is a pair of two words.
  The base fee and the fake exponential now return a result that can fail, as every typed export does.
  The error codes 101 and 102 of `EvmError` are gone, since no export reads the lengths of operands or ranges now.
  In Python, an argument that Lean cannot read raises the error class of the method with code 0.
  Examples are an operand, a range word or an opcode out of range, more than three operands, a `bool` given for an `int` and `bytes` given for a fork name.
  Before, these raised `OverflowError`, `ValueError`, `TypeError` or `AttributeError`.
  A negative number raises `ValueError`, where it raised `OverflowError`.
- The transaction check, the check against a block, the settlement and the run now take and return typed values ([#1529](https://github.com/ethereum/EthLib/pull/1529)).
  The C exports `eth_tx_check`, `eth_tx_check_in_block`, `eth_tx_settle` and `eth_tx_run` take the tuple of their arguments as one value.
  They return tuples where they returned fixed-width bytes or an RLP list.
  In Python, `Run.accounts` holds each nonce, balance and storage value as an `int`, where they were the bytes of RLP scalars.
  Each account and each storage slot is a tuple, where it was a list.
  An argument that Lean cannot read raises `TransactionError` with code 0, where some raised `TypeError` or `OverflowError`.
  Examples are a chain ID of 2^64 or more, a `bool` given for an `int` and `bytes` given for a fork name.
  A negative number raises `ValueError`, where it raised `OverflowError`.
- The header checks, the genesis block, the typed RLP decoder and the hex-prefix encoding now take typed values ([#1542](https://github.com/ethereum/EthLib/pull/1542)).
  The C exports `eth_block_validate_header`, `eth_block_check_header`, `eth_genesis_block`, `eth_rlp_decode_as` and `eth_trie_hex_prefix` take the tuple of their arguments as one value.
  The header checks take the blob schedules as pairs of four integers, and return `None`.
  `eth_genesis_block` takes the fields of the header as one tuple, and `eth_trie_hex_prefix` takes a list of nibbles.
  `eth_rlp_decode_as` returns the value itself, such as an `int`, a `bool` or `None` for a contract creation.
  A new export, `eth_pow_chain_forks`, writes the RLP form of the forks of a chain, which `chain_forks` returns.
  In Python, an argument that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
  Examples are `bytes` given for a fork name or for the kind of `rlp.decode_as`, and an `int` given for the `is_leaf` flag.
  A nibble of 16 or more raises `TrieError` with code 0, where one of 256 or more raised `OverflowError`.
  A negative number raises `ValueError`, where some raised `OverflowError`.
- Every typed export reads a pair, such as a memory range or a blob schedule, from a Python list as from a tuple ([#1542](https://github.com/ethereum/EthLib/pull/1542)).
- The networking exports that returned JSON text, packed records or joined bytes now return typed values ([#1547](https://github.com/ethereum/EthLib/pull/1547)).
  These are the discv5 key derivation, packet, message, WHOAREYOU and handshake exports, the fork identifier, the consensus entries and `eth` entry of a record, the RLPx answer and the req/resp response chunk.
  Their C exports take the tuple of their arguments as one value, and return a typed value where they returned bytes.
  Two new exports, `eth_fork_id_schedule` and `eth_fork_id_encode`, write the RLP schedule and fork identifier that `forkid.schedule` and `forkid.encode` return.
  `forkid.encode` now requires a 4-byte hash and a next fork below 2^64, as the fork identifier types them.
  The discv5 `dict` results keep their keys and values, in the order of the packet rather than sorted.
  In Python, an argument of the right Python type that Lean rejects raises the error class of the method with code 0, where some raised `TypeError`, `OverflowError` or `AttributeError`.
  Examples are a block number of 2^64, `bytes` given for a fork name, and `str` given for bytes.
  A negative number raises `ValueError`, where it raised `OverflowError`, and a value that cannot cross, such as a `bytearray`, still raises `TypeError`.
  `rlpx.SECRETS_SIZE` is now read from Lean.
- The consensus presets, configurations and parameters, and the active fork of a configured chain, now take and return typed values ([#1548](https://github.com/ethereum/EthLib/pull/1548)).
  The C exports `eth_consensus_preset`, `eth_consensus_config`, `eth_consensus_parameters` and `eth_active_fork` take the tuple of their arguments as one value.
  The first three return a `dict`, where they returned JSON text.
  An integer in that `dict` is an `int`, where it was a string of decimal digits.
  `eth_active_fork` takes the chain configuration as a `dict` with the keys of its JSON form, and returns the name of the fork or `None`.
  In Python, an argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
  An example is `bytes` given for a name.
  A timestamp or a block number of 2^64 or more given to `chain.active_fork` raises `ChainError` with code 0, where it raised `OverflowError`.
  A `bool` given there raises `ChainError` with code 0, where it read as 0 or 1.
  A negative number raises `ValueError`, where it raised `OverflowError`.
- A replacement of a 64-bit value of a consensus configuration may now be an `int`, where it had to be a string ([#1548](https://github.com/ethereum/EthLib/pull/1548)).
- The Engine API exports, the block state transition and the check of an `eth_getProof` answer now take typed values in place of JSON text ([#1549](https://github.com/ethereum/EthLib/pull/1549)).
  The C exports `eth_engine_new_payload`, `eth_engine_forkchoice_updated`, `eth_engine_prepare_execution_payload`, `eth_engine_new_payload_on_chain`, `eth_state_transition` and `eth_trie_verify_account_proof` take the tuple of their arguments as one value.
  A configuration, a request or an answer crosses as the Python value of its JSON, and the first three return the value of the JSON of their answer.
  `eth_engine_new_payload_on_chain` returns the status with the header and the accounts in RLP, or `None` twice, where it returned an RLP list.
  `eth_trie_verify_account_proof` returns `None` for an absent account, or one bool for each slot, and Lean reads the patterns of the fields of the answer, where Python read them.
  In Python, `bytes` inside one of these values now crosses as `0x` hex text, where `json.dumps` refused it.
  A `float`, a negative `int` or a `dict` key that is not a `str` raises `TypeError` or `ValueError`, where `json.dumps` wrote it.
  An argument of the right Python type that Lean rejects raises the error class of the method with code 0, where some raised `TypeError`.
  Examples are `str` given for the state, and `1` given for `check_seal`.
  A field of an `eth_getProof` answer that is missing or out of its pattern raises `TrieError` with code 0, where it raised `KeyError` or `ValueError`.
- On a free-threaded build of CPython, such as 3.14t, importing the extension now leaves the GIL disabled ([#1372](https://github.com/ethereum/EthLib/issues/1372)).
  Threads may call the exports at the same time, and a list that another thread changes during a call is read as a snapshot.
- The consensus gossip and req/resp lists, the subscribed subnets and the SSZ root exports now take and return typed values ([#1551](https://github.com/ethereum/EthLib/pull/1551)).
  The C exports `eth_consensus_gossip_topics`, `eth_consensus_reqresp_protocol_ids`, `eth_consensus_reqresp_parse_protocol_id`, `eth_consensus_reqresp_request_bounds`, `eth_consensus_reqresp_response_bounds` and `eth_consensus_compute_subscribed_subnets` take the tuple of their arguments as one value.
  So do `eth_consensus_ssz_static`, `eth_consensus_reqresp_message`, `eth_consensus_merkle_proof` and `eth_pq_keys_ssz`.
  A list comes back as a list, the subscribed subnets as a list of `int`, and a pair as a tuple, where each came back as JSON text.
  The three SSZ exports return the root and the bytes as a pair, where they returned the two joined.
  `eth_consensus_merkle_proof` returns the node and the list of its siblings, and `eth_consensus_compute_subscribed_subnets` takes the node ID as an `int`.
  In Python, a node ID of 2^256 or more, or an epoch or a generalized index of 2^64 or more, raises the error class of the method with code 0, where it raised `OverflowError`.
  A `bool` given for one of them raises the same error, where it read as 0 or 1.
  A negative number raises `ValueError`, where it raised `OverflowError`.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
- The custody exports, the shuffle, the matrix, the shape check of a data column sidecar and the sidecars of a block now take and return typed values ([#1552](https://github.com/ethereum/EthLib/pull/1552)).
  The C exports `eth_consensus_get_custody_groups`, `eth_consensus_compute_columns_for_custody_group`, `eth_consensus_compute_shuffled_permutation`, `eth_consensus_compute_shuffled_index` and `eth_consensus_get_validators_custody_requirement` take the tuple of their arguments as one value.
  So do `eth_consensus_verify_data_column_sidecar`, `eth_consensus_compute_matrix`, `eth_consensus_recover_matrix` and the two exports of the sidecars of a block.
  A list of groups, columns or positions comes back as a list of `int`, where it came back as JSON text.
  A node ID crosses as an `int`, a validator index as an `int`, and a configuration replacement as a `dict`.
  The blobs and the matrix entries cross as a list of bytes, where they crossed joined in one byte string.
  The sidecars come back as a list of bytes, where they came back as the SSZ encoding of a list.
  A row of cells crosses as a pair of lists, and a row with another count than 128 cells and 128 proofs raises `SszError` with code 0.
  In Python, a node ID of 2^256 or more, or a count, group or index of 2^64 or more, raises the error class of the method with code 0.
  A `bool` or a `str` given for one of these numbers raises the same error.
  Before, these cases raised `OverflowError` or `TypeError`, or read a `bool` as 0 or 1, and for a validator index they raised `struct.error`.
  A negative number raises `ValueError`.
  A seed, a blob, a matrix entry, or a cell or proof of a row, of the wrong length, raises the error class of the method with code 0 and the message `expected N bytes, got M`.
  A `bytearray` or a `memoryview` given for bytes raises `TypeError`, where some were read as bytes.
- The consensus transition exports now take typed values ([#1556](https://github.com/ethereum/EthLib/pull/1556)).
  These are the block operations, the epoch steps, the slots and the state transitions of one block or of several blocks.
  They are also the upgrades, the rewards and penalties, the genesis exports and the weak subjectivity exports.
  Their C exports take the tuple of their arguments as one value, in the order they had.
  A configuration replacement crosses as a `dict`, where it crossed as JSON text, and any other value raises the error class of the method with code 0.
  In a replacement, a negative `int` or a `float` raises `ValueError` or `TypeError` from the converter, and `bytes` crosses as `0x` hex.
  The names of the kinds of deltas and of the forks of the blocks cross as `str`.
  The deposits of the genesis cross as a list of bytes, one deposit each, where they crossed joined in one byte string.
  A hash of the Eth1 block of another length than 32 bytes raises `TransitionError` with code 0 and the message `expected 32 bytes, got N`, where the message began with `input rejected`.
  Every argument is read before the names, so an argument that Lean cannot read is reported before an unknown preset.
  In Python, a slot count or an Eth1 timestamp of 2^64 or more, or a negative one, raises an error, where it was read modulo 2^64 without one.
  The times of weak subjectivity of 2^64 or more raise the error class of the method with code 0, where they raised `OverflowError`.
  A negative number raises `ValueError`.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where it raised `TypeError`.
  Examples are `bytes` given for a name and `str` given for a state.
  A `bool` given for a slot count, and `1` or `None` given for `verify`, now raise the same error, where they were read as 0 or 1 or by truthiness.
  The limits of the converter, 2^29 bytes and 2^22 values in one call, now apply to the states and the blocks.
- The honest validator exports that take a state, and the optimistic sync exports of the ancestor and the payload verdicts, now take and return typed values ([#1558](https://github.com/ethereum/EthLib/pull/1558)).
  These are the committee, proposer, sync committee and PTC assignments, the sync committee subnets and the upcoming proposal slots.
  They are also the signature of a duty, the construction of an attestation and of a single attestation, the Eth1 vote, the pending deposit count and the new state root.
  The others are the latest verified ancestor and the two payload verdicts.
  Their C exports take the tuple of their arguments as one value, in the order they had, and a configuration replacement as a `dict`, as the transition exports do.
  The committee assignment comes back as a tuple of the committee, its index and its slot, or `None`, where it came back as JSON text.
  The PTC assignment comes back as an `int` or `None`, and the sync committee subnets and the upcoming proposal slots as a list of `int`, where they came back as JSON text.
  The Eth1 chain crosses as a list of pairs of a timestamp and the SSZ bytes of the Eth1 data, where each block crossed as 80 packed bytes.
  Eth1 data of another length than 72 bytes raises `ProposerError` with code 0, after the fork and the state are read, where it raised `ValueError`.
  The optimistic roots cross and come back as a list of 32-byte roots, where they crossed joined in one byte string.
  A root of another length than 32 bytes raises the error class of the method with code 0 and the message `expected 32 bytes, got N`.
  Before, the message was `a root is 32 bytes, not N` or `a list of roots is 32 bytes each, not N`, and it came after the checks of the name and the fork.
  In Python, an epoch, an index or a timestamp of 2^64 or more raises the error class of the method with code 0, where it raised `OverflowError`, or `struct.error` for an Eth1 timestamp.
  A negative number raises `ValueError`, where it raised `OverflowError` or `struct.error`.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
  An example is `bytes` given for a name or a duty.
  A `bool` given for an index, and `1` or `None` given for `verify`, now raise the same error, where they were read as 0 or 1 or by truthiness.
  A `bytearray` or a `memoryview` given for an optimistic root or for the Eth1 data of a block raises `TypeError`, where it was read as bytes.
- The light client exports that take a configuration now take and return typed values ([#1559](https://github.com/ethereum/EthLib/pull/1559)).
  These are the sync, the light client header of a block, the checks of the proofs of an update, the ranking of two updates, the bootstrap, the update and the fork digest.
  Their C exports take the tuple of their arguments as one value, in the order they had, and a configuration replacement as a `dict`, as the transition exports do.
  The steps of a sync cross as tuples, `("update", fork, slot, data)`, `("force", slot)` and `("upgrade", fork)`, where they crossed packed in one byte string.
  The sync returns, for each step, the pair of the finalized and the optimistic header, each a tuple of a slot and two roots, where it returned 144 bytes for each step.
  The light client header of a block comes back as the pair of the root and the bytes, where the two came back joined.
  An unknown finalized block of an update is `None`, where it was empty bytes; in Python, empty bytes still stand for it.
  A root of another length than 32 bytes raises the error class of the method with code 0 and the message `expected 32 bytes, got N`, where it said `a root has 32 bytes`.
  In Python, a step of an unknown kind raises `LightClientError` with code 0, where it raised `ValueError`.
  A slot of a step of 2^64 or more raises `LightClientError` with code 0, and a negative one `ValueError`, where it raised `OverflowError`.
  An epoch of the fork digest of 2^64 or more raises `SszError` with code 0, and a negative one `ValueError`, where both were read modulo 2^64.
  A `bool` given for a slot or an epoch raises the error class of the method with code 0, where it was read as 0 or 1.
  A `bytearray` or a `memoryview` given for the data of an update raises `TypeError`, where it was read as bytes.
  Every argument is read before the names, so a root of the wrong length is reported before an unknown preset or a fork before Altair.
  The limits of the converter, 2^29 bytes and 2^22 values in one call, now apply to the states, the blocks and the steps.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
- The gossip validation export now takes and returns typed values ([#1561](https://github.com/ethereum/EthLib/pull/1561)).
  Its C export takes the tuple of its arguments as one value, in the order it had, and a configuration replacement as a `dict`, as the transition exports do.
  The blocks after the anchor cross as tuples of a kind, a payload status or `None`, the SSZ bytes and an optional envelope, where they crossed packed in one byte string.
  An envelope of `None` means no envelope, as empty bytes still do.
  A payload status of 255 is now a status, where it meant none; only `None` means none.
  The messages cross as tuples of a time, a subnet, the SSZ bytes and an optional topic, where they crossed packed in one byte string.
  A topic of a message may now be longer than 255 bytes in UTF-8, where it raised `ValueError`.
  The finalized checkpoint crosses as a pair of an epoch and a root, or `None`, where it crossed as 40 bytes, and the topic as a `str`.
  Each outcome comes back as a pair of `valid`, `ignore` or `reject` and its reason or `None`, where it came back packed in one byte string.
  In Python, a block or a message of another length than three or four items raises `ForkChoiceError` with code 0.
  Before, a shorter one raised `ValueError`, and a longer one was read without its extra items.
  A time, a subnet or an epoch of 2^64 or more raises `ForkChoiceError` with code 0, and a negative one `ValueError`, where it raised `OverflowError`.
  A kind or a payload status of 256 or more raises `ForkChoiceError` with code 0, where it raised `ValueError`.
  A `bool` given for one of these numbers, and `1` or `None` given for `verify`, raise the same error, where they were read as 0 or 1 or by truthiness.
  A `bytearray` or a `memoryview` given for the bytes of a block, an envelope or a message raises `TypeError`, where it was read as bytes.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError` or `AttributeError`.
  A root of the finalized checkpoint of another length than 32 bytes raises `ForkChoiceError` with code 0 and the message `expected 32 bytes, got N`, where the message was `the finalized checkpoint is not 40 bytes`.
  Every argument is read before the names, and the limits of the converter, 2^29 bytes and 2^22 values in one call, now apply.
- The generic SSZ exports now take and return typed values ([#1563](https://github.com/ethereum/EthLib/pull/1563)).
  The C exports `eth_ssz_serialize`, `eth_ssz_deserialize` and `eth_ssz_hash_tree_root` take the tuple of their arguments as one value.
  A type and a value cross as the Python values of their tagged form, such as `{"uint": 2}` and `{"uint": 258}`, where they crossed as JSON text.
  `eth_ssz_deserialize` returns the value as a `dict`, where it returned JSON text.
  In Python, `bytes` inside a type or a value now crosses as `0x` hex, where `json.dumps` refused it.
  A `float` or a `dict` key that is not a `str` raises `TypeError`, and a negative `int` raises `ValueError`, where each raised `SszError` with code 0.
  Data that is not `bytes` raises `SszError` with code 0, where it raised `TypeError`.
  The converter reads an argument nested at most 64 levels below it, where 256 SSZ levels were read.
  So a value of more than 31 `seq` or `union` levels raises `ValueError`, and so does a type of more than 32 `vector` or `list` levels or more than 21 `container` levels.
  A value that `deserialize` returns past these bounds, or past the converter budget, cannot be given back to `serialize`.
- The active fork of mainnet and of Hoodi, the seal hash, the proof-of-work check, the gossip message ID and the recent blocks of a chain now cross as typed values ([#1571](https://github.com/ethereum/EthLib/pull/1571)).
  The C exports `eth_mainnet_active_fork`, `eth_hoodi_active_fork`, `eth_pow_seal_hash`, `eth_pow_check` and `eth_gossip_message_id` take the tuple of their arguments as one value.
  A fork crosses as its name, a `str`, where it crossed as UTF-8 bytes, and the active fork comes back as a `str` or `None`, where it came back as bytes.
  `eth_state_transition` and `eth_engine_new_payload_on_chain` take the recent blocks as a list of tuples, where they took one RLP list.
  Each tuple is the fork name, the header in RLP form and the list of the RLP forms of its ommers.
  In Python, `mainnet_active_fork` and `hoodi_active_fork` raise `ChainError` with code 0 for a block number or a timestamp of 2^64 or more.
  They raise `ValueError` for a negative one, where both raised `OverflowError`.
  A `bool` given there raises `ChainError` with code 0, where it was read as 0 or 1.
  A recent block whose header or ommer does not decode raises `BlockError` from `state_transition` and `EngineError` from `new_payload_on_chain`, with code 0, where it raised `RlpError`.
  A fork name given as `bytes` to `seal_hash`, `check_proof_of_work` or `message_id` raises the error class of the method with code 0.
- A Python value of a list or a `dict` with many items no longer overflows the stack when an export reads it as JSON or writes JSON as a Python value ([#1563](https://github.com/ethereum/EthLib/pull/1563)).
  Every export that reads a typed value as JSON, or returns JSON as a typed value, reads and writes the items in a loop.
- The converter of typed values now passes up to 2^22 values in one call, where it passed 1,000,000, so that the longest `ssz_generic` vectors of consensus-spec-tests cross ([#1563](https://github.com/ethereum/EthLib/pull/1563)).
- A chain configuration that the exports read as JSON is now rejected, with code 0, when a fork by block number comes after a fork by timestamp ([#1110](https://github.com/ethereum/EthLib/pull/1110)).
  EIP-6122 requires the forks by timestamp to be scheduled at or after the forks by block.
- leanSPHINCS now hashes with the layout of FIPS 205 ([#1555](https://github.com/ethereum/EthLib/pull/1555)).
  For the same seed and message, `key_gen` and `sign` now return a different key and signature.
  `verify` checks the new layout, so keys and signatures made with 0.3.0 must be made again.
  The sizes are unchanged: a 32-byte seed, a 32-byte public key and a 7740-byte signature.
  The public key is now `PK.seed` then the root, 16 bytes each, in place of the root then the public parameter.
  The Python constant `sphincs.PUBLIC_PARAM_LEN` and the C export `eth_sphincs_const_public_param_len` are removed.
- The gossip topics of Heze are now those of Gloas followed by `inclusion_list` ([#1469](https://github.com/ethereum/EthLib/issues/1469)).
  `consensus.gossip_topics` and `consensus.gossip_topic_bound` now answer at `hegota`, where they raised `ConsensusError`.
  The error of code 304 is gone, since every fork now has a list of topics, and no other error takes that code.
  In Lean, `Config.gossipTopics` returns a `List GossipTopic`, where it returned an `Option`.
- The gossip bounds of four topics are now held to the size limits that the networking specification sets on their messages ([#1610](https://github.com/ethereum/EthLib/issues/1610)).
  `consensus.gossip_topic_bound` answers the limit for `beacon_aggregate_and_proof`, `attester_slashing` and `execution_payload_bid` from `glamsterdam`, and for `inclusion_list` at `hegota`, where it answered the payload cap of 10485760 bytes.
  On mainnet the limits are 16829, 2097616, 196932 and 41112 bytes, and that of a bid is 196934 bytes at `hegota`.
  In Lean, `topicBound_eq` now takes a topic without a size limit, and `decodePayload_message` a message within the size limit of its topic.
- Data column sidecars on gossip and in responses, and inclusion lists in responses, are now held to the size limits of the networking specification ([#1618](https://github.com/ethereum/EthLib/issues/1618)).
  From `glamsterdam`, `consensus.gossip_topic_bound` answers 44072 bytes on mainnet and 18920 on minimal for `data_column_sidecar_{subnet_id}`, where it answered the payload cap of 10485760 bytes.
  `consensus.reqresp_response_bounds` answers (56, 44072) on mainnet and (56, 18920) on minimal for `data_column_sidecars_by_range` and `data_column_sidecars_by_root`, and (152, 41112) for `inclusion_lists_by_indices` at `hegota`.
  Their largest length was the payload cap of 10485760 bytes.
  The limit of a sidecar is its size with a cell and a proof for each blob of the largest blob limit.
  In Lean, `GossipTopic.sizeLimit` now takes the configuration, and the gossip `sizeLimit_ne_none_iff` names the data column sidecar topics.
  From `glamsterdam`, `decodePayload_message` at a sidecar topic now needs a message within the size limit of the topic.
  `responseBounds_eq` now takes a protocol without a size limit, and `decodeResponseChunk_response` a value within the size limit of its protocol.
- The rules that a transaction must pass alone now reject a transaction whose type the fork does not have, with `unsupportedType` and the type ([#1779](https://github.com/ethereum/EthLib/issues/1779)).
  Before, only decoding rejected it, so a block built in Lean could run a type-4 transaction before Pectra, or a type-3 transaction before Dencun.
  `validateTransaction` checks the type first, and the inclusion check and `checkTransaction` call it, so they reject such a transaction too.
  The exports decode each transaction at its fork first, so their answers do not change.
  In Lean, `validateTransaction_eq_ok_iff` ends with the new conjunct `tx.fork ≤ fork`, and `checkInclusion_fork_le` derives it from a passing inclusion check.
  `processTransaction_nonce_lt` no longer takes the hypothesis `tx.fork ≤ fork`.
- `processBlock_split_of` is removed.
  Its reader `processBlock_split` now reads `processBlock_operationsInput` and `OperationsInput.step_of`, and `processBlock_attestationSplit` reads `processBlock_folds`.
  In Lean, a caller that needs a step across the parts of a block before its operations takes the `OperationsInput` that `processBlock_operationsInput` gives.
  It applies `OperationsInput.step_of` to it with the same step arguments.
  The block then continues with `processOperations`, as before.
  No C export or Python function changes.
- A validator write in the epoch laws must keep the slashed flag ([#1421](https://github.com/ethereum/EthLib/issues/1421)).
  No C export or Python function changes.
  In Lean, the `setValidatorAt` field of `EpochFrameLaws` takes a proof of `validator.slashed = old.slashed`, after the proof of the key.
  `EpochFrameLaws.setValidator`, `EpochFrameLaws.setValidator_of_sameBalance` and `EpochFrameLaws.setValidatorAt_of_sameBalance` take the same proof, after the proof of the key.
  A caller passes `rfl` when the write leaves the flag alone, and an instance of the laws takes one more argument.
- The place where a block checks an indexed attestation now also covers the two attestations of an attester slashing ([#1421](https://github.com/ethereum/EthLib/issues/1421)).
  No C export or Python function changes.
  In Lean, `AttestationSite` gains the constructor `slashing`, and a proof that eliminates an `AttestationSite` handles that case too.
  `blockVotes_verified` and `blockStepVotes_verified` keep their statements, so the site that they give may now be either case.
  `AttestationSite.frame` gives the frame from the input of the operations to the state of the check, in both cases.
- The decompositions of a block and of its operations now name the steps after the attestations ([#1421](https://github.com/ethereum/EthLib/issues/1421)).
  No C export or Python function changes.
  In Lean, `processBlock_operationsInput` ends with a new conjunct for the step after the operations.
  From Altair the sync aggregate takes the state after the operations to the state after the block, and before Altair the two are equal.
  A caller that destructures its result adds one pattern at the end.
  The new `processOperations_folds_of` gives the three folds of the operations and a step of any relation across the operations after them.
  `processOperations_folds` is its case for `BlockFrame`, with the same statement.
- An SSZ type path that selects a compatible union option which the union does not declare fails with `badDeclaration` ([#2190](https://github.com/ethereum/EthLib/issues/2190)).
  Before, `Desc.resolveStep` returned the default type, a Boolean, when a union had fewer options than selectors.
  A well-formed union has one option per selector, so its paths resolve as before.
  No C export or Python function changes.
  In Lean, `resolveStep_compatibleUnion` takes the selected child and a proof of `options[slot]? = some child`, and concludes with that child.
  `union_options_share_one_tree` quantifies over that child in the same way.
  `resolveStep_compatibleUnion_of_wellFormed` gives the child for a well-formed union.
- In Lean, the hash of a message to elements of `Fp2` has its count in its type ([#2210](https://github.com/ethereum/EthLib/pull/2210)).
  `hashToFieldFp2` returns `Vector (Fp2 F) count`, where it returned an `Array`, so a caller that needs an array takes `.toArray`.
  The elements, the errors and the points of the hash to `G2` are the same.
  `map_hashToFieldFp2` maps with `Vector.map`, and `hashToFieldFp2_eq_spec` states the same equation over the vector.
  `hashToG2` no longer takes an `Inhabited` instance.
  `map_hashToG2` no longer takes the two instances, or the hypothesis that the map sends the default to the default.
  No C export or Python function changes.
- In Lean, the RLP decoder reads only bytes inside its input ([#2211](https://github.com/ethereum/EthLib/pull/2211)).
  `readPrefix`, `decodeItem`, `decodeItems` and `decodeItemsFrom` take a proof of `stop ≤ input.size`, which `omega` supplies by default.
  `readBigEndian` takes a proof of `pos + k ≤ input.size`.
  The proof helper `readItem` takes the same bound as `decodeItem`, also supplied by `omega` by default.
  `readPrefix_short`, `decodeItemsFrom_eq` and `decodeItems_eq` take the same bound, and `decodeItem_of_readItem` takes it as an implicit argument.
  `decode` keeps its type, the inputs it accepts, its values and its errors.
  No C export or Python function changes.
- In Lean, the reader of an `eth_getProof` answer moves into the specification ([#2099](https://github.com/ethereum/EthLib/issues/2099)).
  `accountProofOfJson`, `storageProofOfJson` and `proofNodes` move from `EthLib.Engine.Exports` to `EthLib.Execution.Rpc`, in `Execution/Rpc/Proof.lean`.
  They keep their types and their errors.
  No C export or Python function changes.
- The chain view serves `eth_getProof`, with the answer that `AccountProof.ofState` builds from the state after the block.

- `eth_config` reports the current, next and last scheduled configurations from Dencun through Glamsterdam.
  As EIP-7910 says, the report leaves out a future fork after Glamsterdam, and `next` and `last` are null when no supported fork remains.
  A fork at a block after genesis is never a next or last configuration.
  In Lean, `ChainView` adds `genesis` and `mergeForkBlock` for the fork checksum.
  Supply both fields in positional constructors, or use structure notation with their `none` defaults.
  `call_unknown` also requires that the method name differ from `eth_config`.
  The configuration given to `rpc_serve` takes the optional keys `mergeForkBlock`, `genesisHash` and `genesisTime`.
  It rejects a malformed value of these keys, one of the genesis pair without the other, and a genesis pair that disagrees with block zero.
  The C and Python function signatures stay the same.

## 0.3.0

Released on 2026-11-06.

0.2.0 had Python bindings for BLS and KZG only.
In 0.3.0, the package `ethlib` has a subpackage for each layer of EthLib:

- `ethlib.cryptography`: `aes`, `bls`, `crc32`, `crc32c`, `ethash`, `hmac`, `kdf`, `keccak`, `kzg`, `secp256k1`, `secp256r1`, `sha256`, `sphincs`, `vrf` and `xmss`
- `ethlib.serialization`: `rlp` and `ssz`
- `ethlib.networking`: `devp2p`, `discv4`, `discv5`, `enr`, `forkid`, `gossip`, `reqresp`, `rlpx`, `snappy` and `varint`
- `ethlib.execution`: `blocks`, `evm`, `fees`, `network`, `pow`, `transactions` and `trie`, with `ethlib.precompiles`, `ethlib.state` and `ethlib.chain`
- `ethlib.consensus` and `ethlib.engine`, for the consensus layer and the Engine API

The sections below list the changes that a caller of 0.2.0, or of master before this release, may need to act on.

### Typed errors in the Python bindings

A failed call into the Python bindings now raises an exception that carries the code and the message of the Lean error ([#310](https://github.com/ethereum/EthLib/pull/310)).
Before, most failures raised a bare `RuntimeError` or `ValueError` with the name of the operation, and the Lean message went to standard error.

The new module `ethlib.errors` defines one exception class for each primitive, such as `KzgError` or `BlsError`.
Each class derives from `EthLibError`, which has two attributes:

- `code`, an integer that names the kind of failure;
- `message`, the text of the Lean error.

Each class also derives from the class that the same failure raised before: `RuntimeError`, `ValueError` or both.
So a caller that catches `RuntimeError` or `ValueError` still catches it.
A caller that parsed the text of an old message must now read `message`.
A message no longer starts with the name of the operation.

The Lean type of each error defines its codes, one for each constructor, from 1.
When one Python class carries several Lean error types, the second type takes its codes from 101, the third from 201, and so on.
A theorem for each error type shows that two errors with one code come from one constructor.

Code 0 means a failure that has no Lean error code.
Examples are an unknown fork name and an input that the export reads before the specification runs.
No Lean error type uses code 0.
Some checks on the type or the length of an argument run in C first, and raise `TypeError` or `ValueError` with no code.

The C signatures of the fallible exports change too.
Each one returns the code and the message of its error, in place of a Lean `IO` error.

### Precompiles

The module `ethlib.precompiles` reaches every precompile by its address, at a fork named by the caller.
`run(fork, address, data, gas)` returns the output, and `price(fork, address, data)` returns the gas that the call charges ([#459](https://github.com/ethereum/EthLib/pull/459)).
A failed call raises `PrecompileError`, whose code names the precompile.

Before the release, master also had the modules `ethlib.precompiles.ecrecover`, `modexp`, `sha256` and `ripemd160`, with the classes `EcrecoverError`, `ModexpError` and `Sha256PrecompileError`.
They are removed, and 0.3.0 does not have them.
A caller of `modexp.modexp(data, gas)` now calls `run(fork, 0x05, data, gas)`, and a caller of `modexp.gas_cost(data)` calls `price(fork, 0x05, data)`.

### Other changes that break callers

- The KZG operations take the trusted setup as an argument and no longer run in `IO` ([#235](https://github.com/ethereum/EthLib/pull/235)), and their byte inputs are typed ([#346](https://github.com/ethereum/EthLib/pull/346)).
- leanXMSS replaced XMSS, with two layers of height 16 ([#134](https://github.com/ethereum/EthLib/pull/134)), and hashes with Keccak-256 in place of BLAKE2s ([#138](https://github.com/ethereum/EthLib/pull/138)).
- The C exports moved into a Lean library of their own, so Lean code that imported them changes its imports ([#119](https://github.com/ethereum/EthLib/pull/119)).
- An integer argument out of its range raises `OverflowError`, as Python's own conversions to a C integer do ([#718](https://github.com/ethereum/EthLib/pull/718)).
  Before, an integer outside [0, 2^64), an EVM opcode above 255 and the range checks of the Python wrappers raised `ValueError`.
  A caller that caught `ValueError` for such an argument now catches `OverflowError`.
- `consensus.verify_data_column_sidecar` takes the signed block before the configuration, in the order of its native export ([#729](https://github.com/ethereum/EthLib/pull/729)).
