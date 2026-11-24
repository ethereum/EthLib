# Changelog

This file lists the changes of each release that a caller of EthLib may need to act on.
The version is the same in `pyproject.toml` and `lakefile.lean`.

## 0.4.0

Not yet released.

### Proof additions

- In Lean, `readP256_eq_ok_iff` in `EthLib.Networking.Proofs.Libp2p.Tls` says that the libp2p TLS reader of a P-256 key accepts exactly a SubjectPublicKeyInfo of 26 fixed octets (RFC 5480 §§2.1.1, 2.1.1.1, 2.2), then octets that the uncompressed decoder accepts, and returns their point ([#4261](https://github.com/ethereum/EthLib/pull/4261)).
  So it refuses another key type or curve, another parameter form, a long length form, an unused bit and a trailing octet.
  `size_of_readP256_eq_ok` derives that such a SubjectPublicKeyInfo has 91 octets.
  The proof reads public lemmas of `EthLib.Serialization.Proofs.Der` on a short value and on the values that a SEQUENCE holds; `Proofs.Der.size_eq_length` is public too.
  No statement changes.

- In Lean, `Secp256r1.decodeUncompressed_eq_some_iff` in the new module `EthLib.Cryptography.Proofs.Secp256r1.Encoding` says that the uncompressed decoder of SEC 1 v2 §2.3.4 accepts exactly the bytes `04 ‖ x ‖ y` of the affine points `(x, y)` on the curve, and returns that point ([#4260](https://github.com/ethereum/EthLib/pull/4260)).
  So it refuses the octet `00` of `O`, every prefix other than `04`, every length other than 65 bytes, a coordinate of `p` or more, and a pair off the curve.
  No statement changes.

- At every fork, the simulated logs that a message starts with change nothing else that it computes ([#3584](https://github.com/ethereum/EthLib/issues/3584)).
  The new module `EthLib.Execution.Proofs.Evm.Call.SimulatedLogsErase` defines `Evm.prependSimulatedLogs`, `Evm.eraseSimulatedLogs` and `StepResult.prependSimulatedLogs`.
  `step_prependSimulatedLogs` says that a step from any frame with logs in front of its simulated logs gives the same result with them in front, so no step reads them.
  `processMessage_prependSimulatedLogs` and `processCreateMessage_prependSimulatedLogs` say that logs put in front of the simulated logs at the start stay in front at the end, and nothing else changes.
  `processMessage_eraseSimulatedLogs`, `processCreateMessage_eraseSimulatedLogs` and `Transactions.processMessageCall_eraseSimulatedLogs` say that two runs that differ only in their starting simulated logs end alike but for them.
  No statement changes.

- `Xmss.chainStarts` builds the 58 chain starts with `Vector.flatMap` over the 29 derivations, and `Xmss.Internal.digit` reads a digit with one shift and `% 4` ([#4255](https://github.com/ethereum/EthLib/pull/4255)).
  The new lemma `Xmss.getElem_cast_flatMap_halves` in `EthLib.Cryptography.Proofs.Xmss.Ots` gives chain `i` as half `i mod 2` of derivation `floor(i / 2)`.
  The statements of `Xmss.chainStarts_seedPrf` and `XmssSecurity.Bridge.halves_eq` follow the new body of `chainStarts`.
  Both functions keep their values, and `Xmss.digit_val` keeps its statement.

- `registryLifecycle_processParentExecutionPayload` (`Transition/RegistryLifecycle.lean`) states that, from Gloas, successful processing of the parent payload preserves each existing validator's index and any assigned activation and exit epochs ([#4243](https://github.com/ethereum/EthLib/issues/4243)).
  `registryLifecycle_processBlock` in the same file, `block_balances` in `Transition/BlockCredits.lean` and the signed-conflict slashing theorem in `DirectSafety/Includable.lean` read it.
  It replaces two copies of the same proof.

- In Lean, `getPendingAttestingIndices_lt` in `EthLib.Consensus.Proofs.Transition.EpochJustification` says that each attester of a pending attestation is in the registry, at every fork.
  It was a private Phase 0 lemma of the upgrade to Altair.
  The totality of the unslashed signers and the upgrade to Altair read it ([#4253](https://github.com/ethereum/EthLib/pull/4253)).

- `registryLifecycle_processOperations` (`Transition/RegistryLifecycle.lean`) says that the operations of a block keep the lifecycle of the registry.
  `registryLifecycle_processBlock` and the effective-balance fall read it.

- `Run.registryWithinLimit_of_room` (`ForkChoice/BlockRuns.lean`) bounds, at every fork, the registry at the end of a run that starts at the anchor and stays at the anchor's fork.
  From Gloas, a run that ends within the horizon keeps its registry within the limit, given the anchor's registry room.
  Before Gloas, the type bounds it.
  `Execution.quorumDriftWithin` reads it at the counting state.
  `registryWithinLimit_of_anchorRoom` (`ForkChoice/BlockRuns.lean`) is the arithmetic that it shares with `Store.ForwardReachable.registriesWithinLimit_of_room` and the confirmed-root proof.
  A registry at an epoch within the horizon fits the anchor's room if it grew by at most one epoch of pending deposits per epoch.

- In Lean, the payload of the parent has a balance ledger from Gloas, and its old validators read at both ends are later.
  `BlockLedger.ledger_processParentExecutionPayload` changes no balance outside a set of converted validators.
  That set has no more members than a payload can carry consolidation requests; no balance rises, and only a conversion lowers one.
  `BlockLedger.lives_processParentExecutionPayload` says that an old validator read at both ends is later at the end, and that a new validator is not activated.
  `BlockCredits.block_balances` reads them.

- The fresh-slot facts of a change of an account, of new code and of a record of a read are now shared lemmas ([#4235](https://github.com/ethereum/EthLib/issues/4235), second part).
  `TransactionState.freshSlots_modifyState`, `freshSlots_setCode` and `freshSlots_recordAccountRead` in `EthLib.Execution.Proofs.State.FreshSlots` are new public lemmas, taken from private copies in `EthLib.Execution.Proofs.Transactions.StateGasUsed`.
  The new lemma `StateGasMeter.stateGasUsed_absorb_sub` in `EthLib.Execution.Proofs.Evm.Gas.StateGas` gives the net state gas of any merge of a child, and `stateGasUsed_absorb` now follows from it.
  The new lemma `StateGasMeter.stateGasUsed_charge` there proves that a charge of execution gas keeps the net state gas, in place of three proofs by hand in the slot-surplus proofs.
  No statement changes.

- The rebuild proof of a message and the proof that a message pays for its slots take each nonce or code they keep from the proof that every message keeps them ([#4235](https://github.com/ethereum/EthLib/issues/4235), first part).
  `KeepsNonceOrCodeFrame`, `KeepsNonceOrCodeCall` and `KeepsNonceOrCodeCreate` in `EthLib.Execution.Proofs.Evm.Call.NonceOrCode` are now public.
  The new lemmas `stepRules_keepsNonceOrCodeFrame`, `keepsNonceOrCodeFrame_step`, `keepsNonceOrCodeCall_rollbackOnError` and `keepsNonceOrCodeCreate_depositCode` there state the rule of each step, call and creation.
  `keepsNonceOrCode_setCode_of_not_hasNonceOrCode` in `EthLib.Execution.Proofs.Evm.Call.NonceOrCodeWrites` proves that new code at an account with neither a nonce nor code keeps each nonce or code; the rebuild proof of a delegation uses it.
  `EthLib.Execution.Proofs.Evm.Call.Rebuild` now imports `EthLib.Execution.Proofs.Evm.Call.NonceOrCode`.
  No statement changes.

- Each fact that a write of a transaction state keeps each nonce or code now has one proof ([#4144](https://github.com/ethereum/EthLib/issues/4144)).
  The new module `EthLib.Execution.Proofs.Evm.Call.NonceOrCodeWrites` holds `HasNonceOrCode`, `KeepsNonceOrCode` and the lemma of each write, below both the rebuild property and the theorems on messages.
  None of them needs the rebuild property of the state.
  `keepsNonceOrCode_setStorage`, `_setTransientStorage`, `_touchAccount`, `_createEther`, `_setAccountBalance`, `_depositCode` and `_startState` are new, and `keepsNonceOrCode_of_getAccountOptional` and `keepsNonceOrCode_rollbackOnError` are now public.
  The `RebuildState` lemmas of the same writes keep their statements, and take their second half from these.
  `EthLib.Execution.Proofs.Evm.Call.NonceOrCode` no longer imports `EthLib.Execution.Proofs.Evm.Call.Rebuild`.

- `processTransaction_gasLeft_le_of_glamsterdam` proves that from Glamsterdam the execution gas left and the reservoir left of a transaction are at most its gas limit less its intrinsic gas, so its gas used before the refund never floors at zero ([#4038](https://github.com/ethereum/EthLib/issues/4038)).
  `processMessageCall_stateGasUsed_nonneg` proves that the net state gas of the message of a transaction is at least 0, for a message that runs at its recipient from a state with no fresh slot, with no other hypothesis on the state before the transaction.
  SOUNDNESS.md ("Transaction gas") no longer records this as a gap.

- `processMessage_messagePays` and `processCreateMessage_messagePays` prove that from Glamsterdam every call whose code runs at an account with a nonce or code, and every creation at an address with neither, pays for the fresh slots it counts (`MessagePays`), whether or not it ends with an error ([#4038](https://github.com/ethereum/EthLib/issues/4038), sixth part).
  A message that fails rolls back its state gas to the floor of its meter, and its counted slots to those of its start, with no hypothesis on the state.
  `accountDeployable_of_create_step` is now public.

- `paysSlots_messageInstruction` proves that from Glamsterdam each call and creation pays for the fresh slots it counts (`PaysSlots`), given that each message it sends pays (`MessagePays`) ([#4038](https://github.com/ethereum/EthLib/issues/4038), fifth part).
  `paysSlots_step` gives the same for every step of a running frame whose code, when not empty, runs at an account with a nonce or code.

- `slotSurplus` is the net state gas of a frame of EIP-8037, less the state gas of a new slot for each fresh slot of an account with a nonce or code ([#4038](https://github.com/ethereum/EthLib/issues/4038), fourth part).
  `PaysSlots` relates two frames when the second failed (it stops with an error, and its meter rolled back unless it reverted), or when, without an error, its surplus did not drop; it is a preorder (`PaysSlots.refl`, `PaysSlots.trans`).
  `paysSlots_instruction` proves that from Glamsterdam each instruction that gives the next frame keeps it, from a running frame whose current account has a nonce or code.
  `MessagePays` states what a message must pay for its slots, from the floor of its meter.

- `keepsNonceOrCode_processMessage` and `keepsNonceOrCode_processCreateMessage` prove that from Spurious Dragon every call and creation lowers no nonce and keeps a nonce or code wherever an account has one, with no hypothesis on the state ([#4038](https://github.com/ethereum/EthLib/issues/4038), third part).
  `processMessage_rebuildState` and `processCreateMessage_rebuildState` also need the rebuild property of the state, a code condition at the target or a deployable target, and a value condition.
  `stepRules_keepsNonceOrCode` gives the same for each step, at every fork.

- `nonceOrCodeFreshSlots` counts the fresh slots of the accounts with a nonce or code, the only accounts where code runs ([#4038](https://github.com/ethereum/EthLib/issues/4038), second part).
  `sstoreStateGas_sub_sstoreStateRefill_of_hasNonceOrCode` proves that from Glamsterdam a storage write at such an account pays for them: its state gas net of its refill is the state gas of a new slot times their change.
  The count stays through a read, a write of transient storage, a change that keeps the nonce and the code, a move of ether, a touch, a nonce rise or new code at an account that already has a nonce or code, and the start of a creation at an account with none.
  A rollback on the same block that keeps the created accounts restores the count of its snapshot, when each account created since had no nonce or code there (`nonceOrCodeFreshSlots_restoreTxState`).

- `TransactionState.freshSlots` is the finite set of slots whose word was zero before the transaction and is not zero now, by `mem_freshSlots` ([#4038](https://github.com/ethereum/EthLib/issues/4038), first part).
  A transaction with no write has none (`freshSlots_ofBlock`), and a storage write adds or removes only its own slot (`freshSlots_setStorage`, `card_freshSlots_setStorage`).
  `sstoreStateGas_sub_sstoreStateRefill` proves that from Glamsterdam the state gas of a storage write, net of its refill, is the state gas of a new slot times the change in the number of fresh slots.

- `Schedule.Bounded` checks that every fork of a fork identifier schedule is below `2^64`, as EIP-2124 and EIP-6122 hold each fork as a `uint64` ([#3855](https://github.com/ethereum/EthLib/issues/3855)).
  `readSchedule_bounded` proves that the schedule reader of the exports returns only such schedules, and `mainnet_bounded` that mainnet is one.
  For such a schedule, `checksumInput_eq_iff` proves that the checksum input holds each fork whole, and `forkId_next_toNat` that `FORK_NEXT` holds the next fork whole.

- `processTransaction_stateGas_le_of_glamsterdam` proves that from Glamsterdam the state gas that a transaction adds to its block is at most the gas it used before its refund, so subtracting it for the execution gas of the block never floors at zero ([#3851](https://github.com/ethereum/EthLib/issues/3851)).

- `length_transactions_lt_of_checkBlock` proves that from Fusaka a block that passes its checks has fewer than `2^32 - 1` transactions, so every position of its block access list fits 32 bits ([#3849](https://github.com/ethereum/EthLib/issues/3849)).
  `applyBody_nonceChanges_le` proves that the body records no nonce above `2^64 - 1` when the state before it meets EIP-2681, so every nonce of the list fits 64 bits.
  `one_le_lengthPrefix_size`, `one_le_encode_size`, `joinEncodings_size_ge` and `encode_list_size_gt` bound the size of an RLP encoding from below.

- In Lean, `Base.hexValue?_toUpper` and `Base.hexBytesFrom?_map_toUpper` state that a hex digit, and a run of hex digits, decode the same in uppercase ([#3837](https://github.com/ethereum/EthLib/issues/3837)).
  The SSZ JSON codec uses them for its case rule.

- At a state where the facts of a chain hold, an attester slashing of one validator by two signatures on a double or surround vote succeeds at its turn in a block within the limits ([#3431](https://github.com/ethereum/EthLib/issues/3431)).
  Otherwise the validator is already slashed there.
  A slashing that succeeds leaves the validator slashed, with its key, in the state right after it.
  `DirectSafety.signedConflict_attesterSlashing_accepted_at` (`DirectSafety/Includable.lean`) states it for a key whose validator is activated and not yet withdrawable at the epoch of a state of a run.
  The pair of votes is a `DirectSafety.VotePairAt`, and the result is conditional on the inclusion of the slashing and on the success of the steps before it.
  The block is at a strictly later slot in the epoch of that state or the next, at the same fork, and the slots up to it advance successfully.
  In the next epoch, three requirements apply.
  The block's epoch is at most the first epoch of the chain plus its number of epochs.
  `SignersAtEnds` holds for the slots up to the block.
  The signer epoch is the epoch before that state's, or epoch 0 itself when that state is in epoch 0.
  At the last slot of the epoch of that state, after its roots are cached, the signers of the signer epoch hold at most the current total active balance of the cached state.
  That balance is the total active balance of the epoch of that state.
  Before Altair, the signers are the unslashed attesters of the pending attestations of the signer epoch that match the source.
  From Altair, for each participation flag, the unslashed validators active in the signer epoch that set it hold at most that balance; the bound is per flag, not on their union.
  The comparison is required only when those reads succeed.
  No fact of a chain gives that comparison.
  The chosen validator, if unslashed in that state, has a withdrawable epoch recorded in that state after the block's epoch.
  `slashValidator_ok_of_block` (`Totality/ChainBlock.lean`) states that slashing succeeds at that turn, at the state that `SlashingTurn` (`Transition/Invariants.lean`) describes.
  `SlashRoom` with `slashValidator_ok_of_room` (`Totality/SlashValidator.lean`) gives a room that suffices for slashing to succeed.
  `slashingTurn_kept` there states that the steps from the operations to that turn keep the frame, activity and the proposer.
  `slashingTurn_exits`, `slashingTurn_supply_le` and `slashingTurn_slashed_le` bound the exits, the supply and the slashed balances at that turn.
  `initiateValidatorExit_total_of_electra` states that an exit succeeds from Electra within bounds on the exit queue, the churn and the exit epochs.
  `run_of_advanceSlotsAcross` (`Transition/Trace.lean`) states that slots that advance a state across forks are a run.
  `slashings_initiateValidatorExit` states that an exit keeps the slashed balances.
  `forkVersions_eq_of_fork` states that two states at one fork, on chains from one genesis, hold the same versions.
  `DirectSafety.mem_keysAt_epoch_of_within` is `DirectSafety.mem_keysAt_epoch` with the registry limit in place of a fork before Gloas; `DirectSafety.mem_keysAt_epoch` keeps its statement.
  Some earlier private declarations are now public, with unchanged statements: `ExitsBelow`, `initiateValidatorExit_exists_ok`, `activeStep_operationsInput`, `RunBounded.size_le`, and `getBeaconProposerIndex_of_kept`, which moves from `Transition/BlockLedger.lean` to `Transition/BalanceDrift.lean`.
  `upgradeNext_forkVersions` and `forkVersion_of_lt_altair` move from `BeaconApi/Config.lean` and are public in `Transition/ForkVersions.lean`, outside the `BeaconApi` namespace.
  `getBeaconProposerIndex_slashDebit` (`Transition/BalanceDrift.lean`) is new: the exit, the slashed mark, the slashings write and the debit of a slashing keep the proposer that an earlier state reads.
  `DirectSafety.genesisValidatorsRoot_chainSteps` (`DirectSafety/Signatures.lean`) is new: steps of a chain keep the genesis validators root.
  `effectiveBalanceSum_eq_of_effectiveKept` (`Totality/SupplyBlock.lean`) is new: a step that keeps the size of the registry and each effective balance keeps their sum.

- `Store.getAncestor_pending_root` and `Store.isAncestor_of_getAncestor_root` (`ForkChoice/Store.lean`) are new.
  The first says that a walk from any node to a slot reaches the same root from that node's pending node.
  The second says that a walk from a pending start to a known block's slot that reaches that block's root gives descent to its pending node.

- `Store.isAncestor_getHeadFrom_of_sibling_bound` (`ForkChoice/PayloadGhost.lean`) shows that, from Gloas, the head walk from a node of the path descends from a viable target node.
  Below each node from that start to the target, the child toward the target must outweigh every viable rival that is not a payload decision of the previous slot.
  When any distinct viable rival exists, that child must also have positive weight.
  `Store.siblingBound_of_majority` gives that bound from a target whose votes exceed half the sum of the stake and the boost.
  `Store.getHeadFrom_of_visited` shows that, from Gloas, a head walk passing a node ends where the walk from that node ends.

- `Store.isAncestor_getHead_root` (`ForkChoice/Ghost.lean`) shows that the head's ancestry at a pending node reads only the head's root, at every fork.
  `Store.getCheckpointBlock_walk_root` (`ForkChoice/Store.lean`) shows that a checkpoint read is the root of a walk back to the first slot of the epoch, at every fork.
  `HonestRegistriesWithinLimit` and `Execution.honestRegistries_of_room` (`ForkChoice/FastConfirmation/HistoricalStatements.lean`) are now public, unchanged: from Gloas, honest registries stay within the limit while the stores' epochs stay bounded.

- `Store.HeadWeightAtMost` (`ForkChoice/HeadTotality.lean`) bounds the stake of every set of validators of a state that are active or known to equivocate: the weights that the weak-head test reads.
  `CheckpointHeadWeightCeiling` (`ForkChoice/FastConfirmation/HonestHeads.lean`) asks it of every honest justified state up to a time.
  It is the Gloas head endpoint's stake bound, restricted to the validators that the weak-head test reads.
  `Store.headWeightAtMost_of_effectiveBalanceSum_le` derives it from a bound on the registry's effective-balance sum.
  `Execution.honestHeadsExist_or_evidence_of_gated` gives honest heads at every fork, from the pre-Gloas premises before Gloas and the Gloas ones, gated, from Gloas.
  It takes the active-stake ceiling and the seed bound at every fork.

- `Store.getCheckpointBlock_of_descendant` (`ForkChoice/Store.lean`) shows that an ancestor of a tip reads the tip's checkpoint block, at an epoch whose first slot is at or before the ancestor.
  It is the converse of `Store.getCheckpointBlock_of_isAncestor`.
  `Store.isPreviousSlotPayloadDecision_eq_false` (`ForkChoice/Head.lean`) shows that a pending node, or a node of a block not from the previous slot, is no payload decision of the previous slot.

- `Store.isAncestor_getSupportedNode` (`ForkChoice/Head.lean`) shows that a supported node descends from a pending node exactly as the vote's block does, at every fork.

- `Store.weight_add_weight_add_stake_le_stake_withBoost_of_isChild` (`ForkChoice/SiblingCap.lean`) bounds two sibling nodes and a set supporting neither by a window plus one boost, for any tree and view of the store's votes.
  `Store.weight_add_weight_add_stake_le_stake_withBoost` is now its case for sibling blocks.

- `honestRegistries_of_gated` (`ForkChoice/FastConfirmation/HistoricalStatements.lean`) gives the honest registry bound at every fork from its Gloas form; before Gloas the type of the registry bounds it.

- `Store.FullParentsVerified` (`ForkChoice/PayloadGhost.lean`) says that, from Gloas, each held block that builds on a held full parent finds the parent's payload verified.
  `Store.Reachable.fullParentsVerified` (`ForkChoice/StoreEntries.lean`) proves it for a reachable store that holds no block at the anchor's parent root.
  `Store.onBlock_validateParentPayload` (`ForkChoice/Handlers.lean`) shows that a new block the handler accepts passed the check of its parent's payload.

- In Lean, the laws of a four-word Montgomery field are proved once in `Word64.Montgomery`, from the laws of its sum, difference and product that an instance of `Word64.Montgomery.Laws` gives ([#3827](https://github.com/ethereum/EthLib/issues/3827)).
  They are the bridge `toMont` to the shared field on eight limbs with its laws, `toFin_val_eq`, the read-back laws `toFin_zero` to `toFin_ofFin`, and the new `ofFin_toFin`.
  The helpers `element_ext`, `mont_ext`, `modulus_odd` and `eq_of_radix_mul_mod` are public there.
  Both base fields, of secp256r1 and of secp256k1, are instances; the secp256k1 product law that its instance reads is public as `Secp256k1.Montgomery.mul_val_words`.

- The secp256r1 double scalar multiplication of verification runs in Montgomery form on four words ([#3796](https://github.com/ethereum/EthLib/issues/3796)).
  `Secp256r1.Point.mulAdd_eq_jacobian` states that it equals the shared Jacobian chain on `Fp`, for every input.
  `Secp256r1.Montgomery.toFin_embedding` states that reading the four-word form back into `Fp` keeps the operations and is one to one.
  `Word64.Raw.val_injective` and `Word64.Raw.bit_iff` state that four words are determined by their integer, and that a bit read from them is a bit of it.
  `Word64.add4_spec` and `Word64.sub4_spec` give the integer of a four-word sum with its carry, and of a difference with its borrow.
  The word lemmas that were private in the secp256k1 field and that both fields use are public in `Word64`: `mulHigh_spec`, `add_with_carry`, `mac_spec`, `sub_split`, `yes_le_one`, `lowValue_lt`, `value_low_of_top_zero`, `rawOfNat_val`, and in the proofs `value_wide`, `val_narrow` and `wide_narrow`.

- `Store.ForwardReachable.registriesWithinLimit_of_room` (`ForkChoice/CheckpointBlocks.lean`) bounds registries from Gloas.
  A forward store whose epoch is within a horizon keeps its held and justified registries within the limit.
  The anchor's registry must leave room up to that horizon.
  The anchor state must satisfy the state invariant, and the anchor block must be at or before its slot.

- `Store.VotesHaveOrigins.exists_attestation_of_voteCountsFor` (`ForkChoice/VoteOrigins.lean`) works in a store whose latest votes have attestation origins.
  There a counted vote for a known node comes from an attestation at or after its block's slot.
  `Store.VotesHaveOrigins.slot_lt_of_voteCountsFor` adds that the block is before the current slot.

- `Store.filterNodeTree_root_ancestor` (`ForkChoice/PayloadGhost.lean`) holds at every fork.
  If parents have lower slots and filtering from a start node succeeds, each returned node's block root descends from the start's block root.

- `Store.boostScoreOfGloas_le_boostScore` (`ForkChoice/PayloadGhost.lean`) bounds the score of the boost from Gloas by the boost score of the LMD-GHOST model.

- `Store.getNodeChildren_ok_of_known` (`ForkChoice/Head.lean`) shows that the children of a node can be computed when the store holds its block.

- `Store.getSupportedNode_exists` (`ForkChoice/Head.lean`) shows that a vote for a held block supports a node of the store, at every fork.

- `PinDrift.Internal.total_band_of_setting` is public, in `PinDriftBound/Setting.lean`.
  In the pin's setting, take a pre-Gloas state on a run from the finalized state, by R's next epoch.
  When both total active balance reads succeed, each total is at most three halves of the other.

- `DirectSafety.exitChurnLimit_total` is public: it gives the total active balance read by a successful exit churn limit before Gloas.
  `ExitCharges` reads it for the pin reserve, and `BlockFold` reads it for the deposit churn bound.

- The proof of the pin reserve bound separates the estimates for balances, exits and rewards into modules.
  The helpers shared by these modules are public in the `PinDrift.Internal` namespace.
  The bound's statement and import path are unchanged.

- `Run.nil_append` drops an empty prefix, and `Run.snoc_append_eq` puts the split of a run before its final prefix step instead of after it.
  `PinDriftBound` reads both to split event replays.

- `Run.split_at_flip` cuts a run at a step that gains a property, and `ChainStep.epoch_le_succ` bounds one step's epoch increase by one.
  `PinDriftBound` reads them to locate changes along a run.

- `Run.cross_split` cuts a run at the slot that leaves a given epoch, and `Run.exists_epoch_split` cuts it at a state in a given epoch.
  `PinDriftBound` reads both, and `Run.split_next` follows from `Run.cross_split` with its statement unchanged.

- `Run.blockCount_le_epochs` bounds the blocks of a run by the slots of the epochs it touches.
  `PinDriftBound` reads it to count sync committee debits and credits.

- `Run.mem_balancePath_split` locates a balance-path state at a run boundary or inside a slot step before upgrades.
  `PinDriftBound` reads it to bound balances along the path.

- `ceil_div_le` bounds a rounded-up natural-number quotient by its numerator.
  `PinDriftBound` reads it for a rounded balance bound.

- `floor_add_ceil_le`, `rounded_add_ceil_le`, `rounded_add_floor_le` and `floor_le_of_lt` bound natural-number quotients and amounts rounded to an increment.
  `PinDriftBound` reads them to bound sums and compare balances.

- `signers_elsewhere_of_unseated` says that no member of a sync committee takes the position of a validator whose key the committee lacks, regardless of the member's participation bit.
  `processSyncAggregate_proposer` reads it, and the pin's bound on a position that a sync aggregate moves reads it in `PinDriftBound`.

- `Step.eq_slot_of_crossing` says that a step of a run that crosses an epoch is a slot step, and gives the step as that slot.
  `DirectSafety.Apriori.Internal.slot_of_crossing` now follows from it, and its statement is unchanged.
  The pin's drift bound, the penalty segments and the active-stake ceiling read it where a step leaves its epoch.

- `DirectSafety.Apriori.Internal.segment_slot_cases` splits a segment of a run that starts in an epoch: it stays in its epoch, or it ends with the slot of the epoch boundary after an inner run.
  `segment_events_cases` builds on it, and the pin's credit scan of a segment reads it.

- `DirectSafety.Apriori.Internal.segment_events_cases` splits the events of a segment of a branch that starts in an epoch.
  The segment stays in its epoch, or it ends with the slot of the epoch boundary after an inner run, and it gives the epoch passes of that run by their source.
  The cohort's penalties in `Penalties` and one key's pass debits in the pin's drift bound read it.

- `PinTerms` names the terms of `pinReserve`, `PinTerms.total` is their weighted sum, and `pinTerms` computes them from a call's state, its ancestor and the finalized block's state.
  `pinReserve` is `(pinTerms config state ancestor finalizedState).total`.
  Through `pinTerms`, it reads the churn of the a priori drift bound.
  The pin's drift bound in `PinDriftBound` reads the terms one by one.

- `PinTerms.capAt`, `PinTerms.dueAmount` and `PinTerms.exitedSlashable` read a key's cap, its due partial withdrawals and its exit from a state, as `pinTerms` does.
  `PinTerms.syncEnvelope` and `PinTerms.wide` are bounds that `pinTerms` computes from a total.
  `joiningStake` is the stake joining the active set, which `quorumReserve` and `pinTerms` both read, with `quorumReserve`'s value and statement unchanged.
  The pin's drift bound in `PinDriftBound` reads them at other states and totals.

- `ConsolidationQueueRise.Appends` says that the queue of pending consolidations only grows at its end inside a block, and `ConsolidationQueueRise.appendStep_processBlock` proves it for a block from Altair, with the frame and the registry lifecycle.
  `riseStep_processBlock` now follows from it.
  The pin's `block_step` reads it.

- `Execution.justifiedSigned_at` generalizes `Execution.justifiedHonestlySigned` to one receiver and any set of signers.
  A store's justified checkpoint after an epoch has a signer in a set `p`.
  This holds when the quorum voters outside `p` hold less than two thirds of the total in each state that the store counts in.
  `justifiedHonestlySigned` is its instance with `p` the honest set, and its statement is unchanged.
  The pin's reader takes `p` to be the voters of a call.

- `setting_runs_of_call` is public: it gives the runs and epochs of the pin's setting, for one call and one counting state.
  The finalized block's state is reached from genesis, and a split state from it.
  Runs from the split state reach the pulled-up state of the call and the counting state.
  The pin's reader reads it.

- `Run.slashed_withdrawable_eq` says that a validator that is slashed, with an assigned exit, keeps its withdrawable epoch along a run.
  The pin's floors read it for the keys that the counting branch slashes before the split.

- `Run.withdrawable_eq_exit_delay` says that a validator reached from genesis, if it is not slashed, has no withdrawable epoch before its exit is assigned.
  After the exit is assigned, its withdrawable epoch is exactly the withdrawal delay after it.
  It extends `Run.exit_withdrawable_delay` with the upper bound, and the pin's floors read it for the keys that the counting branch exits.
  The private invariant `ActivationExitOrder.Holds` gains the upper bound as a fifth conjunct.
  The new `Holds` implies the old one, so each reader of the old four conjuncts is unchanged.

- `hysteresis_of_run_slot` says that a slot step of a run from genesis ends within the bands of hysteresis.
  The step must reach the first slot of an epoch.
  It composes the epoch transition with the upgrades of the slot, which keep the bands because every effective balance is at most its cap.
  `run_boundaryEpoch` and the pin's charge lemmas read it.

- `DirectSafety.Apriori.Internal.FloorTrace.run_potential_floor_slash` is public: a key unslashed at the start of a run keeps its balance within the closed form of a slash, over one more epoch.
  The pin's `segment_potential_slash` reads it for the floor of a key that the counting run slashes.

- `Run.exit_activated` says that a validator with an assigned exit, in a run from genesis, has reached its activation epoch.
  It lets a reader of `Step.slashed_activated` discharge its `exited` premise.
  The private invariant `ActivationExitOrder.Holds` gains it as a sixth conjunct.
  The new `Holds` implies the old one, so each reader of the old five conjuncts is unchanged.

- `DirectSafety.Apriori.Internal.perIncrement_exists` is public: the base reward per increment exists at a positive total when the scaled factor fits.
  The pin reads it to show that its base reward per increment is at least four.
  The pin's preset facts include `fits`, that the scaled base reward factor fits in a `Gwei`, which both presets meet.
  They also include `activation`, that the activation balance is at most the largest effective balance before Electra, which both presets meet.
  The pin reads `activation` for the bands of hysteresis through a chain of upgrades.

- `DirectSafety.Apriori.Internal.run_cuts_of_additive` sums a bound over the one-epoch segments of a branch, for any quantity that adds over `Run.append`.
  `run_cuts_le` is its instance for the cost of the replayed events.
  The pin's proposer-credit bound reads it for the credits of the block steps.

- `processBlockHeader_proposer` is public.
  It says that a block's header step reads the proposer of the block at the state before it.
  The pin's gross-credit count reads it for the proposer of a block step.

- `DirectSafety.Apriori.Internal.activeStake_eq_of_same_epoch` says that the effective balances active in an epoch sum the same at two states of one epoch of a run.
  `activeStake_same_epoch` and the pin's proposer-credit bound read it.

- `Run.pendingConsolidation_targets` says that each pending consolidation of a state of a run from genesis has its target in the registry.
  A request finds its target by pubkey in the registry, which only grows.
  The pin reads it to exclude a created key that only a consolidation funds.

- `DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax` says that a key's effective balance at a state of a run from genesis is at most the largest one its credentials allow.
  The pin's floors read it.

- `slashedFlagAt_advanceSlot` says that advancing one slot keeps each slashed flag; `Step.slashed_activated` reads it.

- `Step.slashed_activated` says that a key which a step newly slashes was activated by the epoch of the step's start, from Electra.
  A key that has begun to exit before the step must be activated, as a hypothesis, and a block never appends a slashed key.
  The pin's closure of the created keys reads it.

- `Step.new_validators_unassigned` says that a step from Electra and before Gloas leaves every validator it appends with no activation or exit epoch; the pin's `created_first_state` reads it.

- A signing root in one domain type is never one in another, unless SHA-256 collides on the signing data ([#3433](https://github.com/ethereum/EthLib/issues/3433)).
  `computeSigningRoot_ne_or_collision_of_domain_ne` states it for two different domains, and `computeSigningRoot_ne_or_collision_of_domainType_ne` for two domain types at any fork versions and chains.
  `signingDataMessages` names the inputs of the node hash in the signing data of an object root and a domain.

- In Lean, `payloadInputs_processExecutionRequests` (PayloadInputs.lean) shows that from Electra to Fulu the requests of the execution layer in a block keep the inputs of a payload.

- A double or surround vote of signed direct safety, with a signature by the key alone on each data, gives an attester slashing that a state accepts exactly when it can slash the validator, when the state reads the fork versions of the signatures and the validator is slashable there ([#3431](https://github.com/ethereum/EthLib/issues/3431)).
  `processAttesterSlashing_eq_slashValidator_of_single` shows that a slashing whose two attestations name one validator, with both signatures verifying in the domains the state reads and the validator slashable there, returns what slashing that validator returns.
  `processAttesterSlashing_single_eq_slashValidator` and its run form apply it to `singleAttesterSlashing`, built from the two signed data of direct safety and two given signatures by the key alone, at a state that reads their fork versions and where the validator is slashable.

- Direct accountable safety has a one-third form, for the accountable keys and for the keys that signed conflicting objects ([#3429](https://github.com/ethereum/EthLib/issues/3429)).
  `derivedDrift_eq_zero_of_stableKeys` shows that the drift of a tail is zero when its unslashed active keys stay those of `x` not slashed since, with their effective balances, and no unslashed key leaves the active set at an epoch boundary (`StableKeys`).
  `accountable_safety_third` and `accountable_safety_signed_third` then bound the unslashed active stake at `x` by three times the stake of those keys, or the hashes show evidence.
  In both, the keys must stay stable up to one epoch past the later finalized epoch.

- On a chain whose digests name their forks, the digest of each update or bootstrap of a valid light client response names the fork of its epoch ([#2642](https://github.com/ethereum/EthLib/issues/2642)).
  `forkOfDigest_of_isValidLightClientUpdatesByRangeResponse` and `forkOfDigest_of_isValidLightClientBootstrapResponse` state it.
  `isValidLightClientUpdatesByRangeResponse_iff_without_count` shows that the updates check needs no bound of its length by the count.

- `Unforgeability.Bridge.unforgeable_capped` charges the SPHINCS signer's counter searches apart from the adversary's queries ([#3375](https://github.com/ethereum/EthLib/issues/3375)).
  An adversary with at most `q` hash calls of its own and `r` signing requests forges with probability at most `(q + cappedCalls (2^22) r + 1) / 2^127`.
  `cappedCalls T r` charges each request `470595 + 3 T` calls and one request `3 * 2^32` more; at `2^30` requests the floor drops from about `2^-63.4` to `2^-73.4`.
  `forgeAdvantage_le_capped` states the bound for every cap `1 <= T <= 2^32`, and `unforgeable` and `unforgeable_adversary` are unchanged.
  `HashSig.prEvent_failedSearch_le` bounds, in the random oracle model, the chance that some search fails its first `T` trials, whoever queried them.
  `hashCost` names the cost of a query, and `countedOracle_eq` and `experiment_eq` state the counted game as the random oracle with that cost; `countedOracle_cost` is removed, and `hashCost_eq` replaces it.
  The bridge's budget transfers are proved once for any computation, so the kernel replay of `Count`, `AdversaryCalls` and the new modules stays within a few GB.

- `VoteAt.validatePayloadVote_or_collision` shows that from Gloas a receiver passes the payload check of an honest duty vote for a block it holds ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  Both stores start at the anchor store, and the receiver reads the vote at least the delay after its deadline.
  For each envelope in its view that the receiver accepts, the receiver's store must already mark the block root verified.
  Otherwise two honest stores at bounded times collide.
  `Execution.reachable_of_start` shows that the store of any validator that is reachable from the anchor at the start stays reachable, and `Execution.reachable` now follows from it.

- `Execution.honestHeadsExist_or_evidence_of_gloas` shows that from Gloas an up-to-date honest store has a head ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  Otherwise two honest stores collide, or direct-safety evidence holds.
  It is the Gloas companion of `Execution.honestHeadsExist_or_evidence`, which keeps its statement.
  `CheckpointHeadWeightCeiling` bounds each honest store at each event up to time `last` where the justified-state lookup succeeds.
  Take any set of validators each active at that state's current epoch or known to that store to equivocate.
  Their effective balances in that state add up to at most the cap.
  `AnchorRegistryRoom` asks the anchor's registry to leave room for the pending deposits of each epoch up to the horizon.

- The Gloas head endpoint adds these facts.
  `Store.Reachable.validators_size_le_of_gloas` bounds the registry of each held block state and checkpoint state from Gloas by the anchor's registry and the epochs since the anchor.
  `advanceSlots_validators_size_le`, `processSlots_validators_size_le` and `stateTransition_validators_size_le` bound the validators that runs of slots and a block from Gloas add.
  `Store.ForwardReachableWith.registered_of_shared_checkpoint` gives each validator active in a held block state an index in a state processed to a checkpoint that both blocks read.
  Both blocks must read one checkpoint at or past that state's finality.
  `Store.updateCheckpoints_finalizedCheckpoint` states that replacing the checkpoints keeps the finalized checkpoint or adopts the given one.

- `Execution.payloadVerified_of_partiallySynchronous` delivers, from Gloas, a payload that an honest sender verified ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  It reaches each honest receiver that holds its block state, at least the delay after the sender's event and after stabilization.
  For each envelope in its view that the receiver accepts, the receiver's store must already mark the block root verified.
  Otherwise bounded honest stores collide; those may be any honest stores, not only the two that start at the anchor.
  `Store.onTick_payloads`, `Store.onBlock_payloads`, `Store.onAttestation_payloads` and `Store.onAttesterSlashing_payloads` show that those handlers keep the verified payloads.
  `HonestCollision`, `Execution.blocksAgree_or_collision` and `Execution.not_honestCollision_of_agree` move from `FastConfirmation/HistoricalStatements.lean` to `BlockAgreement.lean`, with their statements unchanged.

- `Store.getNodeChildren_held` shows that the children of a held node can be computed at every fork, when the store's parents sit below their children (`ParentsBelow`).
  Each child is held and lower in rank.

- `Store.isPayloadVerified_of_getHead` shows that from Gloas a full head of a store has its payload verified by that store.

- `VoteAt.accepted_at_next_slot_of_payloadVote` accepts a held duty vote at the next slot at every fork, or names a collision of bounded honest stores ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  From Gloas it takes the receiver's check of the payload status that the vote names.

- `Execution.blocks_of_partiallySynchronous_of_anchorSlot` delivers a block at every fork, when from Gloas the anchor block is not after the anchor state ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  It needs partial synchrony, the sender's read of the receiver's finalized checkpoint, and a receiver that admits the delivered blocks.
  Otherwise bounded honest stores collide.
  From Gloas the payload of a full parent reaches the receiver through `Execution.payloadVerified_of_partiallySynchronous`.

- `Store.getHead_exists_of_gloas` shows that from Gloas the head of a store that the handlers build can be computed ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  It is the Gloas twin of `Store.getHead_exists`.
  The store must hold its justified state, in which each set of validators active or known to the store to equivocate weighs at most `2 * 10^17` Gwei (`Store.HeadWeightAtMost`).
  `HeldRegistriesWithinLimit` asks each held block state to have its registry within the limit.
  `ActiveEquivocatorsRegistered` asks each equivocator active in a held block's state, at that block's epoch, to have a place in the justified state.
  `Config.HeadWeightsFit` bundles the slot length and the reorg threshold that the head reads need, and `Config.headWeightsFit_mainnet` and `Config.headWeightsFit_minimal` prove it.

- The Gloas head adds these facts.
  `Store.Reachable.payloadInclusionListSatisfaction_isSome` gives, from Heze, the inclusion-list answer of each verified payload of a reachable store.
  `getBeaconCommittees_nodup` shows that the committees of one slot together repeat no member.
  `advanceSlot_validators_size_le` bounds the validators that one slot adds, and `foldlM_validators_size_le` the validators that a fold adds.

- `Xmss.Cost` and `Sphincs.Cost` state the hash calls of key generation, signing and verification ([#3334](https://github.com/ethereum/EthLib/issues/3334)).
  XMSS bounds key generation and signing on every path: at most `13434881` and `8616804556` calls.
  Under a fixed answer function, XMSS key generation makes exactly `13434881` calls.
  leanSPHINCS counts the calls under a fixed answer function.
  Key generation makes exactly `264193`, signing at most `12885372483`, and verification at most `491`, exactly `491` when it accepts.
  `HashSig.length_queriesWith_node` and `HashSig.length_queriesWith_ofFnInOrder_const` count the calls of shared loops.
- `Unforgeability.Bridge.unforgeable_adversary` bounds a SPHINCS forgery by the adversary's own hash calls ([#3336](https://github.com/ethereum/EthLib/issues/3336)).
  An adversary with at most `q` hash calls of its own and `r` signing requests forges with probability at most `(q + schemeCalls r) / 2^127`.
  `schemeCalls r` bounds the calls of key generation, of `r` requests and of verification, about `2^63.7` at the model's cap of 1,182,000,000 requests.
  `HasAdversaryQueryBound` reads both counts from `adversaryExperiment`, the game with a counter on the adversary's hash calls.
  `mem_support_counted_iff` now holds for a game with any result type, not only a Boolean one.

- XMSS signing builds the bottom tree once, for both the key's path and the root its top key signs ([#3395](https://github.com/ethereum/EthLib/pull/3395)).
  `Xmss.signDerived_eq_path_node` proves that every signature stays the same, byte for byte, for every hash function.
  `Merkle.build` computes every node under a position, with the calls of the node there, in the same order.
  The signing bound drops from `8630239231` to `8616804556` calls, and a request's bound `requestQueries` from `2^33 + 615 * 2^16` to `2^33 + 410 * 2^16 + 204`.
  `Cost.signCalls_eq`, `isQueryBoundP_signDerived`, `isQueryBoundP_signWith` and `lifetimeQueries_eq` state the new constants.

- leanSPHINCS signing builds each tree once: the top tree, the two lower trees and the 24 FORS trees ([#3401](https://github.com/ethereum/EthLib/pull/3401)).
  Each build gives both the path of a key and the root that the layer above signs.
  `signWith_eq_recompute` proves that every signature stays the same, byte for byte, for every hash function.
  `signDerived` now takes `PK.seed` and the built top tree, `signLayer` takes the key's built tree, and `forsSign` also returns the FORS public key.
  The signing bound drops from `939499 + 3 * 2^32` to `470595 + 3 * 2^32` calls, and so does `signCalls` in `schemeCalls`.
  `Cost.signCalls_eq` and `hashCalls_signWith_le` state the new constants, and `unforgeable_adversary` keeps its 127 bits.

- `Xmss.Unforgeability.forgeAdvantage_le_adversaryBudget` bounds an XMSS forgery by the adversary's own calls ([#3335](https://github.com/ethereum/EthLib/issues/3335)).
  An adversary with at most `qH` calls of `H` and `r` signing requests (`HasAdversaryBudget`) forges with probability at most `gameQueries qH r / 2^127`.
  `gameQueries qH r` adds upper bounds on the calls of key generation, of `r` requests and of the verification.
  `forgeAdvantage_le_lifetime` takes `r <= 2^32`, and its constant `lifetimeQueries` is `2^65 + 410 * 2^48 + 204 * 2^32 + 205 * 2^16 + 385`.
  `unforgeable` is unchanged.

- `quorumDrift_le_quorumReserve` bounds the drift of a fast-confirmation call's quorum by `quorumReserve` ([#2058](https://github.com/ethereum/EthLib/issues/2058)).
  It compares the call's pulled-up state with a later state in the target's epoch or the next, from Fulu.
  It takes the counting state's registry within the limit, which the type of the registry gives before Gloas.
  `Execution.quorumDriftWithin` builds those runs from the stores and proves `QuorumDriftWithin` with BLS checks.
  The anchor state is reached by a run with BLS checks from a genesis built from deposits, and an epoch has at least one slot.
  `Execution.rootViable_of_checked_call` takes the same genesis and run for any signature checks; this theorem fixes them to BLS.
  The other premises are the anchor store and slot, and positive slot durations.
  The preset keeps the bands of hysteresis, its seed lookahead covers at least one epoch, and the withdrawal delay is at least one epoch.
  The preset meets `CapOrder` and the new `ActivationWithinMaxEffective`, which together make `MAX_EFFECTIVE_BALANCE` equal `MIN_ACTIVATION_BALANCE`.
  `ActivationWithinMaxEffective.mainnet` and `ActivationWithinMaxEffective.minimal` show that it holds on both presets.
  No separate headline discharges `QuorumDriftWithin`: a caller with BLS checks from Fulu composes `Execution.quorumDriftWithin` with `Execution.rootViable_of_checked_call` or `Execution.honestHeadsCover_of_checked_call`, passing the anchor's registry room from Gloas.
  `Execution.heldStatesBeforeUpgrade_of_bounded` derives their premise `HeldStatesBeforeUpgrade` from the horizon and `HonestStoreEpochsBounded`.
  `effectiveRise_le` bounds the rise of the active effective balances over an epoch end, and `effectiveFall_le` the fall of a voter's.
  `Run.balanceCorrections_of_same_epoch` bounds the balances along a branch inside one epoch.

- `processProposerSlashing_balanceDown` says that a proposer slashing does not raise the balance of any index other than the proposer's, and keeps `getBeaconProposerIndex`.
  It needs the mixes to span more than the seed lookahead plus two epochs.
  The pin's gross credit count reads it for each recorded pass of a block.

- `processAttesterSlashing_balanceDown` says that an attester slashing does not raise the balance of any index other than the proposer's, and keeps `getBeaconProposerIndex`.
  It needs the mixes to span more than the seed lookahead plus two epochs.
  The pin's gross credit count reads it for each recorded pass of a block.

- `processAttestation_balanceDown` says that an attestation does not raise the balance of any index other than the proposer's, and keeps `getBeaconProposerIndex`.
  It needs the mixes to span more than the seed lookahead plus two epochs.
  The pin's gross credit count reads it for each recorded pass of a block.

- `DirectSafety.selected_deposit_le` says that a balance event credits a set of keys, none of them withdrawable before it, at most the gains of the keys that are not withdrawable.
  For a deposit event from Electra, that sum is its funding credit.
  The pin's bound on the deposits credited to the active keys of the counting run reads it, in `deposit_each_le`.

- `FloorTrace.step_general_or_fulu` and `FloorTrace.run_of_le_cap_or_fulu` extend the per-key floor trace to a key with no activation epoch, from Fulu.
  They also accept a different guard in place of the final key's exit.
  It is that the withdrawable epoch of the key at the start of the step is past the call's epochs.
  The existing statements are the cases with the exit guard.
  `FloorTrace.run_of_le_cap_general` takes the same guard and covers an activated key or a branch from Fulu.
  `processUpgrades_eq_of_window` states that the upgrades from Fulu up to before Gloas leave the state as it is.
  The pin's drift bound reads them for keys that are not yet active.

- `FloorTrace.run_effective_origin` says where a key's effective balance after a run from Fusaka comes from.
  It is its value at the start, or an update set it at most to the balance at the last state where it changed.
  The run splits at that state, with the effective balance constant after it and aligned.
  The stay step of the pin's counting-branch floor reads it.

- `FloorTrace.effective_aligned` says that a key's effective balance at a state of a run from genesis is a whole number of increments.
  The pin's drift bound reads it.

- `hysteresis_of_crossing_slot` says that a slot step to a later epoch, from Fusaka before Gloas, leaves the state within the bands of hysteresis.
  `DirectSafety.Apriori.Internal.slot_of_crossing` says that a step that ends in a later epoch is a slot step.
  The pin's claim about the keys that are pending at the start of an epoch reads them.

- `processEpochAltair_credentials` says that an epoch from Altair keeps the withdrawal credentials of each validator in the registry before it.
  `processEffectiveBalanceUpdates_owned` says that the pass of the effective balances finds a balance at each position of its registry.
  The pin's balance bound for a key that switches to compounding on the counting branch reads both.

- `compoundingKept_beforeConsolidations` says that the operations of a block before its consolidation requests keep whether each validator compounds.
  It covers the slashings, attestations, deposits, exits and BLS changes, and the deposit and withdrawal requests, from Fulu before Gloas.
  `ledger_depositWithdrawalRequests` says that the deposit requests and then the withdrawal requests of a payload move no balance and keep the credentials.
  `ledger_processConsolidationRequest` says that a consolidation request converts at most one validator and moves no other balance.
  `recordBalance_single` says that a recorded operation that succeeds runs its action at the input state and appends one event with its source, states and limits.
  The pin's balance bound for a key that switches to compounding reads these four lemmas.

- `run_partial_queue_net` bounds the partial cost of a run plus the due entries left in its queue.
  The pin's bound on the penalties and partials of a key on the pulled-up branch reads it.

- `Run.deposit_credit_le_funding` bounds what a deposit event of a run credits the keys recent at the run's end by the event's funding credit.
  The pin's deposit-queue bound for the keys that vote on the pulled-up branch reads it.

- `processRegistryUpdates_withdrawableEpoch_of_unassigned_late` says what registry updates do to the withdrawable epoch of a key with no exit.
  They keep it, or set it after the current epoch, the seed lookahead and the withdrawal delay.
  The existing `processRegistryUpdates_withdrawableEpoch_of_unassigned` is its weaker case.
  The pin's drift bound reads it for the keys that registry updates eject before the pending consolidations.

- `Step.consolidation_withdrawable` says what a step does to the withdrawable epoch of a key before its pending consolidations.
  The key keeps the withdrawable epoch it had at the start of the step, or has one set after the next epoch.
  It takes a step with a positive withdrawal delay.
  The pin's drift bound reads it for the source of a pending consolidation.

- `Run.departure_charge_site` splits a run at the step that assigns the exit of a departure charge, with the validator before and after that step.
  The pin's drift bound reads it for the activation of a key whose exit a counting state charges.

- `Run.exit_activation_gap` shows that an assigned exit in a run from genesis comes at least the seed lookahead and one epoch after the activation.
  The pin's drift bound reads it.

- `Run.eligibility_le_finalized` shows that a validator with an assigned activation in a run from genesis was eligible by the finalized epoch.
  The pin's drift bound reads it.

- `preActivation_waiting` shows that each validator put back into the activation queue at an upgrade has no activation epoch.
  The exit-order walk, `queues_preActivation_fold` in the churn bounds and `balanceDrift_preActivation_excludes` in the balance drift read it.

- The quorum drift bound adds these facts of runs.
  `Run.blockCount` counts the blocks of a run, `Run.blockCount_append` adds them over two runs, and `Run.blocks_le_slots` bounds them by one per slot.
  `run_of_stateTransition` and `run_of_processSlots` give a run for one block or for the slots before it, when the slot is before the next fork.
  `Run.split_next` splits a run that ends one epoch after it starts at the slot where its epoch changes.
  `Run.induction_of_same_epoch` inducts over a run inside one epoch, and `advanceSlotAcross_of_same_epoch` shows such a slot only caches the slot.
  Inside one epoch, `Run.fork_eq_of_same_epoch` keeps the fork, `Run.currentSyncCommittee_eq_of_same_epoch` the keys of the sync committee, and `Run.effectiveKept_of_same_epoch` each effective balance.
  `Run.induction_of_same_period` inducts over a run inside one period of epochs, and `Run.induction_of_same_epoch` is its instance for one epoch.
  `Run.currentSyncCommittee_eq_of_same_period` keeps the keys of the current sync committee inside one period of the committee rotation.
  Their readers are the count of the keys that a branch credits, and the bound on the sync-seat holders that a branch debits, in the pin reserve bound.
  `Run.currentSyncCommittee_eq_nextSyncCommittee_of_next_period` makes the keys of the current committee, one period later, the keys of the next committee at the start.
  The pin's seat count reads it to bound the debited sync-committee seats of the two branches.
  `pending_deposit_rises` bounds the positions whose balance the pending-deposit pass raises by the deposits that it may read, and `pending_deposit_bound` is its projection.
  `Step.slot_deposit_site` says that a deposit event of a slot step is the pending-deposit pass at some state with matching sizes and ordered exits.
  The registry of that state keeps its assigned epochs to the end of the slot.
  The slot ends an epoch, and it records at most one deposit event.
  Their reader is the count of the keys that a branch credits, in the pin reserve bound.
  `Run.withdrawableKept_of_same_epoch` and `withdrawableKept_processRegistryUpdates` keep `WithdrawableKept` inside an epoch and through the registry updates.
  `Genesis.invariant` gives the invariant of a genesis built from deposits, and `Run.invariant` keeps it along a run.
  `syncRewards_bounds` bounds the sync rewards at a position.
  They do not raise it without a signer or a paid proposer there, and do not lower it without an unsigned member there.
  The pin's drift bound reads it for the keys that hold no seat.

- Its transition facts are in `Transition/BlockLedger.lean`, `Transition/BlockCredits.lean`, `Transition/BranchLedger.lean`, `Transition/EffectiveRise.lean`, `Transition/EffectiveFall.lean`, `Transition/EpochReads.lean` and their neighbours.
  The ledger of a block's balances is in `BlockLedger`, its proposer and deposit credits in `BlockCredits`, and the tally of an epoch's blocks in `BranchLedger`.
  The helpers of the first two are public in the namespaces `BlockLedger` (such as `BlockLedger.Ledger` and `BlockLedger.Lives`) and `BlockCredits` (such as `BlockCredits.Kept` and `BlockCredits.lt_size_of_isActiveAt_recent`).
  The generic pieces sit with their kind: `getBeaconProposerIndex_congr` and `proposerSearch_congr_validators` in `Accessors`, `WithdrawableKept` in `RegistryLifecycle`, and `withdrawableKept_processRegistryUpdates` in `PendingConsolidations` next to the registry-update lemma it reads.
  `payloadInputs_addValidatorToRegistry` and `payloadInputs_processDeposit` are in `PayloadInputs`, and the `actualBalanceAt_*` step lemmas and the hysteresis lemmas are in `BalanceDrift`.
  The growth of the queue of pending consolidations inside an epoch is in `PendingConsolidations`, as `ConsolidationQueueRise.QueueFrom`, `ConsolidationQueueRise.Grows`, `ConsolidationQueueRise.RiseStep` and `ConsolidationQueueRise.riseStep_processBlock`.
  `Array.findIdx?_of_prefix` is in `Base/Proofs/List.lean`.
  `Hysteresis` puts each effective balance within the bands of its balance.
  `processEffectiveBalanceUpdates_hysteresis` establishes it, `Hysteresis.of_data` carries it to a state with the same validators and balances, and `Hysteresis.upgrade` keeps it across upgrades.
  `EpochTrace.through_effectiveBalances` splits an epoch trace after the effective-balance updates.
  `activeBalanceTotal` is the active effective balance as a natural number, and `getTotalActiveBalance_toNat` makes it the value of a successful read.
  `syncRewardAt` is the participant reward of the sync committee as a natural number, and `syncParticipantReward_toNat` makes it the value of a successful read.
  `syncSeats` counts the seats of a validator in the current sync committee, and `syncSeats_eq_length` equates it with the length of the beacon API's `BeaconApi.syncSeats`.
  `activeFilter_eq` and `activeSum_eq` keep the active positions and their effective balances between two registries, and `seats_eq` keeps `syncSeats`.
  `Store.Reachable.nonempty_run_of_blockState` gives a run from the anchor state to each held state, with the store's setting of the checks.
  `getBaseReward_congr` reads the same base reward for two validators with the same effective balance, in one state or in two.
  `processRewardsAndPenalties_balance_le_of_inactivityUpdates` bounds each balance after the rewards pass, given a bound on each base reward.
  `processOperations_floor` bounds the balance of an unslashed validator through the operations of a block from Fulu.
  The balance stays at least the smaller of its balance and its effective balance before them.
  `actualBalanceAt_increaseBalance` and `actualBalanceAt_decreaseBalance` change the balance at one index and keep every other, and `actualBalanceAt_push` reads an appended balance.
  `passPendingConsolidations_balanceNotLowered_of_waiting` keeps the balance of a source that cannot yet leave, and `queueConsolidation_queued` records the exit epoch and the queue entry of a consolidation.
  `processBlock_currentSyncCommittee` keeps the current sync committee across a block.
  `Transition/PartialWithdrawalQueue.lean` holds the step facts of the queue of pending partial withdrawals that the departure queue and the drift bound share.
  `departureQueues` and its step lemmas move there from `DirectSafety/DepartureQueue.lean` and become public, with unchanged statements except the changes below.
  Three only drop their pre-Gloas binder; `withdrawals_departureQueues`, `blockExecution_departureQueues` and `getExpectedWithdrawals_partials` also change their conclusions.
  `PartialsSame` says that two states hold the same queue, and `PartialsSame.of_queues` reads it from equal departure queues.
  `flagSumOf` states the flag sums of `SupplyBlock` for any base reward, and `recentFlagSum` adds both recent epochs; `flagRewardWeight` keeps its value.
  `flagSumOf_le` bounds a flag sum by 54 base rewards per position, and `flagSumOf_foldlM_addAttesterFlags` raises it by at least the numerator its attesters gain.
  `processAttestation_keepsFlag` keeps each flag an attestation finds, and `flags_exit` and `flags_processExecutionRequests` keep both lists of flags.
  `processSlots_pendingPartialWithdrawals` keeps the queue of pending partial withdrawals across slot steps from Altair.
  `hysteresis_of_advanceSlot` and `hysteresis_of_processSlots` put a state at the first slot of an epoch within the bands of hysteresis.
  `Store.ForwardReachableWith.relation_of_checkpointPrefix_with` composes a relation that needs to hold only for transitions with the store's checks.
  `runScore_le_start` bounds the inactivity score of a key along a run by its start score plus a bias for each epoch.
  The pin's bound on the penalty of one rewards pass at a state reads it.

- Some earlier private declarations are now public, with unchanged statements.
  They are the flag frames `flags_operationsInput`, `flags_proposerSlashing`, `flags_attesterSlashing`, `flags_increase`, `flags_decrease`, `flagsBelow_add` and `flagsBelow_deposit`.
  They are also `flagValue`, `flagValue_le`, `isActiveAt_of_getAttestingIndices` and `withdrawnFrom_split`.
  They are also `StepKeeps.refl`, `StepKeeps.trans`, `StepKeeps.of_validators` and fifteen `stepKeeps_*` step lemmas, of setValidator, decreaseBalance, initiateValidatorExit, slashValidator and the block operations.
  They are also `effectiveKept_setValidator`, `effectiveKept_decrease`, `effectiveKept_exit`, `effectiveKept_requests` and `balanceDrift_upgrades_upper` (its pre-Gloas binder is dropped below).
  They are also `Unassigned`, `UnassignedFrom`, `unassignedFrom_size`, `UnassignedKept` and `UnassignedKept.processDeposit`.
  `DirectSafety.total_active_congr` moves from `DirectSafety/DepartureQueue.lean` to `Transition/BalanceDrift.lean`, with its name unchanged; its pre-Gloas binders are dropped below.
  `DirectSafety.queueCarry_le_of_run` bounds the exit and consolidation capacity that the queues carry at the end of a run from a state of a run from genesis.
  `DirectSafety.Run.departureCharges_epoch_ge_start` bounds the exit epoch of each departure charge of a run from Electra from below.
  The bound is the epoch of the start, plus one epoch and the seed lookahead.
  `DirectSafety.departureCharges_run_indices` shows that the departure charges of a run name each registry index at most once.
  The pin's drift bound reads it for its exit-queue terms.
  `sync_bounds_combined` bounds a sync aggregate's credits plus debits by the committee size times a reward and its share.
  PinDriftBound's sync-debit bound reads it.
  `DirectSafety.Apriori.Internal.replayRewards_passes` gives the four passes of deltas that the rewards replay runs from Altair, after the first epoch.
  `DirectSafety.Apriori.Internal.replayDeltas_flows` bounds what one pass of deltas debits and credits at one position.
  `DirectSafety.Apriori.Internal.rewardCredit` is the credit of one reward event at a position, the sibling of `penaltyDebit`.
  The pin's per-key epoch reward bound reads all three.

- `queueConsolidation_steps` states the steps of queueing a consolidation once ([#2334](https://github.com/ethereum/EthLib/issues/2334)).
  The churn call writes only the churn left and the earliest consolidation epoch.
  The source then gets its exit and withdrawable epochs, and the consolidation joins the queue.

- `Execution.confirmedRoot_covers` covers the last confirmed root of consecutive calls of the fast confirmation rule by one honest validator ([#1458](https://github.com/ethereum/EthLib/issues/1458), Theorem 1).
  That root is on every up-to-date honest head from the next slot to a horizon.
  The alternatives are a collision of two honest stores and four kinds of accountable-safety evidence: historical, cross-store direct-safety, cross-store justified and held-state finality.
  It covers executions whose honest stores verify signatures with BLS (`checks = .bls`), because the specification's pulled-up head state processes slots with BLS checks.
  Each call assumes `CallObligations`, with `MemberObligations` for each member of its walk.
  `CallObligations` does not include the caller's head read at each rollover: `Execution.callRolloverRead_or_evidence` derives `CallRolloverRead` from the theorem's other premises.
  `MemberObligations` states each window reserve at `exitReserveNear`, the reserve that the exit bound of the walk's receivers gives.
  The run assumes `JustifiedPinned`, `ByzantineCountedStake`, `TargetIncluded` and `StaleHeadVotersInWindow`; `SOUNDNESS.md` describes them.
  With `Preset.InclusionDelayPositive` and two conditions on the anchor, the theorem derives the signed justification inside, through `Execution.justifiedHonestlySigned`.
  It derives `HeldStatesBeforeUpgrade` through `Execution.heldStatesBeforeUpgrade_of_bounded`, from its horizon and `HonestStoreEpochsBounded`, so it does not take it.
  It takes `CapOrder` and `ActivationWithinMaxEffective`, which it passes to `Execution.quorumDriftWithin`.
  Its proof is a private step: one call keeps the call invariant, given the invariant at every earlier call.
  `CallAt` names one call in a run of calls by one validator.
  `FastConfirmation/ConfirmedCalls.lean` holds the walk of a call and the call invariant; the helpers that the step reads are public in its `ConfirmedCalls` namespace.
  `FastConfirmation/ConfirmedCallStep.lean` holds the step and the theorem.
  The step reads these new or newly public lemmas:
  - `Store.viable_of_ancestor` passes viability from a root to its ancestors.
  - `Store.held_of_isAncestor` now gives the held block at the root of any ancestor node, not only of a pending one.
  - `Store.Reachable.finalized_known` gives the block of a reachable store's finalized checkpoint; steps of `RootViability.lean` and `RootHeld.lean` read it too.
  - `Execution.walk_covers` covers a walk of roots from its start and a step, and `honestHeadsCover_mono` shrinks the interval of a coverage.
  - `Execution.honestHeadsCover_of_viableAt` is the induction behind the historical-anchor headlines, with the root's viability given per time.
    Its window reserve and its receivers' exits read one reserve value; the headlines pass `exitReserve`.
  - `Execution.rootViableAt_of_checked` gives that viability for the root of a checked call.
  - `Execution.currentSlot_le_of_time_le` orders the current slots of honest stores at ordered times; `Execution.previousSlot_le_of_time_le` keeps its statement and reads it.
    Both are in `ForkChoice/VoteDelivery.lean`; `Execution.previousSlot_le_of_time_le` moves there from `FastConfirmation/HistoricalTransport.lean`.
  - `Store.ForwardReachable.justified_origins_epoch`, `Store.ForwardReachable.pulledUp_le_unrealized`, `Store.Reachable.justified_epoch_le_unrealized` and `Execution.unrealizedJustified_epoch_le_of_le` bound the justified checkpoints of a store.
    `Store.onBlock_pulledUp` gives the pull-up of a block that the store adds, which their block steps read.
  - `Store.adversaryRange_start` and `Store.ForwardReachableWith.supportersOf_mem_committees_of_near` read the adversary's range of a block and its committees; `Store.ForwardReachableWith.supportersOf_mem_committees` now reads the second.
  - `Store.updateCheckpoints_justifiedCheckpoint`, `Store.onTick_unrealizedJustifiedCheckpoint` and `Store.onBlock_unrealized_epoch_le` are the store steps of the justified bounds above.
    `Store.updateCheckpoints_unrealizedJustifiedCheckpoint` and `Store.onTick_justifiedCheckpoint_of_unrealized` are now public, with their statements unchanged.
  - `Execution.crossStoreFinality_or_evidence` puts one honest store's finalized checkpoint on another's justified chain at that epoch or later, or gives `CrossStoreDirectSafetyEvidence`.
    `Execution.finalized_read_or_accountable` is its step for one pair of stores.
  - `Execution.anchor_stateRoot_nonzero` shows that an honest held copy of the anchor block has a nonzero state root.
  - `Store.getCheckpointForBlock_eq_ok_iff` reads the checkpoint of an epoch in a chain as that epoch and its checkpoint block.
  - `computeStartSlotAtEpoch_le_of_epoch_le`, `Store.getCurrentStoreEpoch_eq`, `Store.getCheckpointBlock_of_ancestor_epoch` and `Store.getCheckpointBlock_self` read the clock and the checkpoint reads of a store.
  - `Store.Reachable.anchor_le_finalized`, `Store.ForwardReachable.block_epoch_le_current`, `Store.ForwardReachable.justified_before_current`, `Store.ForwardReachable.unrealizedJustification_epoch_le` and `Store.ForwardReachable.votingSource_epoch_le` bound the epochs that a store holds.
  - `Execution.isAncestor_of_le` keeps an ancestor test at every later event, and `Execution.anchor_unrealized_le` bounds an honest store's unrealized justified epoch below by the anchor store's.
    `Execution.getBlockEpoch_of_le` keeps the epoch read of a held block at every later event.
  - `Store.parentRoot_of_getAncestorRoots` and `Store.isAncestor_terminal_of_getAncestorRoots` in `ForkChoice/AncestorRoots.lean` read a walk of roots.
    Each root has the root before it as parent, or the terminal block; the head descends from it, and it descends from the terminal block.
    `Store.isAncestor_parentRoot_of_isAncestor` passes descent from a known block to its parent.
  - `Store.not_isOneConfirmed_of_slot_eq_current` shows that a held block at the current slot is not one-confirmed in a forward store.
  - `Store.unrealizedJustification_found` reads an unrealized justification as its stored entry.
  - `isStartSlotAtEpoch_eq`, `isStartSlotAtEpoch_next_eq_false` and `computeStartSlotAtEpoch_of_isStartSlotAtEpoch` read the start test of a slot as its remainder by the epoch length.

- `Execution.rootViable_of_checked_call` shows that the confirmed root of a call of the fast confirmation rule stays viable from the call up to `time` ([#2058](https://github.com/ethereum/EthLib/issues/2058), Theorem 3, for the confirmed root).
  At each up-to-date honest store, the root is in the filtered tree or below the justified block.
  The alternatives are a collision of two honest stores and accountable-safety evidence.
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
  The new premises `CallCheckpointInputs`, `TargetChecked`, `AcceptedRealizedRecent`, `AcceptedRealizedHead`, `CallRolloverRead` (derived by the headlines), `JustifiedPinned`, `TargetIncluded` and `QuorumDriftWithin` are described in `SOUNDNESS.md`.
  `DirectSafety.AccountableOrHashEvidence` is the direct-safety bound on two tails or hash evidence on their runs, and the statements that spelled it out now name it.
  `quorumReserve` and `pinReserve` are the reserves that `QuorumDriftWithin`, `JustifiedPinned` and the reserved count of a call read.
  `RootViableAt` is the viability of a root at one time.

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

- `exitReserveNear` is the active source stake already scheduled to exit within three epochs of the source, the reach of a confirmation's near window.
  `Preset.SeedLookaheadAtLeastThree` asks for a seed lookahead of at least three epochs, so that activity is fixed three epochs ahead.
  `Execution.receiverWindowExitsNear_of_sourceOnParentChain` in `FastConfirmation/ReceiverExits.lean` reads it, since the near window reaches three epochs past the source.
  `Preset.seedLookaheadAtLeastThree_mainnet` and `Preset.seedLookaheadAtLeastThree_minimal` show that both presets satisfy it.
  Under it, no other source stake leaves by then, in any later state that keeps the source's fixed activity.
  `exitReserve` keeps its value, and no theorem orders the two values.
  `SourceWindowReserveWith`, `WindowExitBoundWith` and `ReceiverWindowExitsNearWith` take the reserve as an argument.
  `SourceWindowReserve`, `WindowExitBound` and `ReceiverWindowExitsNear` are their instances at `exitReserve`, with their statements unchanged.
  `Execution.isAncestor_getHead_of_historical_anchor_with` and `Execution.source_surplus_or_historical_evidence_with` take one reserve value for the window reserve and the exit bound.
  The theorems without `_with` keep their statements and read them.

- `Execution.receiverWindowExitsNear_of_sourceOnParentChain` proves `ReceiverWindowExitsNearWith` at `exitReserveNear` when the call's balance source is on the parent's chain (`SourceOnParentChain`), or names a block collision between honest stores.
  The checkpoint's epoch is at most two epochs before the parent's, and the preset satisfies `Preset.SeedLookaheadAtLeastThree`.
  Each near receiver's head state keeps the source's activity three epochs ahead, so each full epoch of its window is bounded by `exitReserveNear`.

- `Store.Reachable.blockState_slot_eq` states that a known block's state is at the block's slot, when the anchor block is at the anchor state's slot.

- `le_computeStartSlotAtEpoch_of_isStartSlotAtEpoch` shows that a slot at the start of an epoch is at most the first slot of the epoch of each later slot.
  `HonestVoteData.target_read`, `Store.Reachable.getCheckpointBlock_anchor`, a step of `DutySupport.lean` and `Execution.honestTargetVotes_signed_of_checked` read it.

- `DirectSafety.accountable_safety_apriori` bounds the drift of accountable safety from the reference state alone.
  For two runs that finalize conflicting checkpoints, the unslashed stake at the shared state `x` is at most three times the accountable stake plus `2 * drift x high`, or the runs show `HashEvidence`.
  `drift x high` reads only numbers at `x` and the window to the later finalized epoch, so it needs no replay of the tails.
  It takes the premises of `source_safety`.
  When its guard fails, `drift` is the unslashed active stake at `x`, and the bound says nothing.

- `Execution.honestTargetVotes_of_byzantineStakeAtMost` derives the honest target-vote count, `HonestTargetVotes`, from a bound on Byzantine stake ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  It assumes `TargetCountBounds`, which is stated for the pulled-up state of the head.
  That state has at most the threshold share of Byzantine stake in the committees of the epoch so far.
  The honest validators of the slots still to come hold the share that the rule counts for them.
  They hold a third of the margin on top of it.
  For a head whose block is two or more epochs before the current epoch it also assumes `StaleHeadVotersInWindow`.
  `HonestTargetVotes` and `quorum_of_no_conflicting_checkpoint` keep their statements.
  `le_activityFixedEpoch` is now public, for `TargetCount.lean`.

- `Execution.honestHeadsCover_of_historical_anchor` keeps a confirmed block on every honest head chain from the call to a horizon, by induction on time ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  It no longer assumes the root's own earlier coverage.
  It assumes the parent's coverage, the root's viability, the receivers' exits, and a late duty majority.
  The root's viability rules out honest justified checkpoints that conflict with the root, so it assumes the checkpoint-consistency half of safety.
  The alternatives are a block collision between honest stores and `HistoricalDirectSafetyEvidence`.
  The latter holds with no accountable key once the churn since the anchor is large enough and a justified root fails to read an earlier finalized root.
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
  When the next slot starts an epoch it is the epoch transition, and at any other slot it keeps the state.

- `getTotalActiveBalance_bounds` bounds a total active balance below by one increment.
  It bounds it above by the larger of one increment and the sum of the effective balances.

- `processEpoch_registryCut` splits an epoch at its registry updates: the three stages before them, the registry updates, then the rest of the epoch.

- Six epoch and deposit steps keep the inputs of a payload: `payloadInputs_applyPendingDeposit`, `payloadInputs_processInactivityUpdates`, `payloadInputs_processRegistryUpdates`, `payloadInputs_passPendingDeposits`, `payloadInputs_passPendingConsolidations` and `payloadInputs_processHistoricalSummariesUpdate`.

- `roundToIncrement_share_bounds` bounds a share of a total, raised to the least churn and rounded down to an increment.
  When the least churn is at least one increment, so is the share, and the share is at most the least churn plus the total.

- `epochs_le_div_add_one` bounds the epochs that hold an amount plus less than one churn, when the churn is at least one increment.
  They are at most the amount in increments, plus one.

- `processWithdrawals_of` carries a relation across the withdrawal step.
  It holds when the relation holds of the state to itself and across the expected withdrawals.

- `effectiveKept_parentPayload` states that the payload of the parent keeps the size of the registry and each effective balance in it.

- `EpochBaseLaws` and `EpochFrameBaseLaws` are the laws of the epoch steps without a write of the RANDAO mixes or of the lookahead of proposers.
  So a relation that keeps both can satisfy them.
  `EpochStepLaws` and `EpochFrameLaws` extend them with those two laws, and have the same fields by name.
  `payloadInputsLaws` gives the frame base laws for `PayloadInputs`.
  `payloadInputs_epochPrefix` states that the stages of an epoch before the RANDAO reset keep the inputs of a payload.

- `VotersInHeadWindow` states that, between two times, each voter below a given parent block lies in each honest head's window after that parent ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  `VoteInHeadWindow` is the vote and the window that it reads.
  `Execution.votersInHeadWindow_of_newlyActive` derives it from `NewlyActiveVotersInHeadWindow`, which asks it only of a voter activated at the target epoch of a vote two epochs after that parent.
  `Store.mem_getCommitteesBetweenSlots_of_active`, `Store.ForwardReachableWith.active_or_newlyActive_of_voteOrigin` and `Store.ForwardReachableWith.epoch_le_of_checkpointState` are the general steps.
  `fits_of_shuffledCommittee` states that a cut committee has the number of indices times one past its position below `2^64`.
  `ReceiverWindowExitsNear` asks the receivers' exit bound only of receivers within two epochs of the parent.

- `ChainStep.exit_assigned_activated` states that, from Electra, a chain step assigns an exit only to a validator that is activated at the step's start epoch.
  The pin's drift bound reads it to show that a key whose exit starts on a run was activated before its exit.

- `upgradeNext_validators_of_electra` states that, from Electra, an upgrade keeps the validators as the same sequence.
  The pin's drift bound reads it for the registry along a slot step, and `ChainStep.exit_assigned_activated` reads it for the upgrades of a slot.

- `LookaheadActive` says that, from Fulu, each entry of the proposer lookahead of a state is active in its epoch.
  Position `k` is `k / SLOTS_PER_EPOCH` epochs after the current epoch.
  `Run.lookaheadActive` states it along every run from genesis that ends before Gloas, when `MAX_SEED_LOOKAHEAD` is above `MIN_SEED_LOOKAHEAD`.
  `LookaheadActive.proposer_active` states that a proposer read from a state that holds it is active in the epoch of the state.
  The pin's whistleblower and sync bounds read it to show that a validator that exited before the finalized epoch proposes no block.

- `processBlock_proposerLookahead` states that a successful block leaves the proposer lookahead unchanged.
  `processEpoch_lookahead_cut` states that, from Fulu, an epoch draws its new last epoch of proposers from a state just before that draw.
  That state has the slot and the lookahead of the epoch's start, and the registry of the epoch's end.
  `Run.lookaheadActive` reads both.

- Up-to-date honest stores before Gloas have a head ([#2060](https://github.com/ethereum/EthLib/issues/2060), for pre-Gloas forks).
  `Store.getHead_exists` computes the head of a store that the handlers built from its anchor, under the anchor conditions of the handlers.
  The store holds its justified state, that state has at most `2 * 10^17` Gwei of active stake, and the proposer boost fits that cap.
  `Execution.honestHeadsExist_or_evidence` shows `HonestHeadsExist`: every up-to-date honest store has a head.
  The alternatives are a collision of two honest stores and `HistoricalDirectSafetyEvidence`.
  `Execution.callRolloverRead_or_evidence` derives `CallRolloverRead` with the same alternatives.
  The store holds its justified state because an honest vote for that checkpoint reaches it by the next slot (`VoteAt.accepted_at_next_slot`), and `Handles.checkpointStates_of_found` keeps it.
  `Store.getAttestationScore_eq_of_checked`, `Store.stake_supportersOf_eq_sum`, `Store.isAncestor_ok_of_orphans_le` and `Store.onAttestation_eq_of_reads` are the steps that existing proofs now share.
  `Execution.genesisTimeMs_eq_of_honest` and `Execution.getCurrentSlot_of_slot_start` read an honest receiver's genesis time and its slot at a slot start.
  `Store.nextSlotStart_le_clock` in `ForkChoice/ForwardClock.lean` shows that the slot after one before the current slot exists and starts by the store's clock.

- `FloorTrace.balance_floor_general` says that a trace from an account keeps the floor, less the penalty of a slash if the trace holds one.
  The pin's epoch floor and its floor of a slashed key read it.

- `FloorTrace.run_potential_floor_once` says that the potential floor of a run whose effective balance starts above its balance is charged once.
  The pin's segment potential reads it.

- `runScores_le` says that on a branch from Altair, each inactivity score of a state is at most the start score plus the bias for each epoch of the branch.
  It holds at the positions that the branch adds as well.
  The pin's cross-branch bound on a key's leak reads it.

- `scoresKept_processBlock` says that a block keeps the inactivity score at each position of the registry before it.
  Each score after the block, at every position, was there before it or is zero.
  The step of the branch's score bound reads it, in `runScores_le`.

- `scoresKept_processEpochAltair` says the same of the epoch pass from Altair: it keeps the score at each position of the registry before it.
  It needs no premise on the deposits or the consolidations.
  The step of the branch's score bound reads it too.

- `addValidatorToRegistry_keeps` says that, from Altair, a new validator at the end of the registry keeps each validator, the consolidations, and the balance and score at each position that holds a validator.
  The new validator takes the score zero.
  The block's proof that the balance is not raised reads it.

- `slot_events_no_withdrawals` says that a slot records no withdrawal event.
  The pin's partial-debit bound of a key reads it.

- `PartialCost` says that a cost function charges a withdrawals event at most the amounts of the queued partial withdrawals that a filter selects, and every other event nothing.
  The pin reads it for the partial debits of one key and of all keys.

- `departure_charges_le_window_electra_cap` says that, from Electra, the departures of a window spend only carry-in capacity and eligible epochs.
  If the exit churn limit at each step of the run is at most `exitCap`, the exit queue adds at most `exitCap` for each epoch of the window.
  The pin's queue-window bound reads it.

- `ScheduledEligibleBalanceElectra` says that, from Electra, an eligible key that is not yet active keeps its activation reserve.
  `run_eligible_balance` states it for the state at the end of a run.

- `run_eligible_balance` says that a key without an activation epoch keeps its effective balance funded at the end of a run from genesis.
  From Electra, the eligible keys that are not yet active also keep their activation reserve.
  The pin's bounds on a key's funding at the start of a run and at the first state of a created key read it.

- `PinPresetFacts` is public: the preset facts that the pin's drift bound needs.
  Each field is a fact about the preset alone, and a deployed preset has it.
  Its fields bound the increment, the largest effective balance, the bands, the slashings vector, the slashing and whistleblower quotients, the reward factor and the seed lookahead, and include `activation : ActivationWithinMaxEffective preset`.
  The one divisor fact the pin reads is `syncPeriod : preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0`.
  Facts that follow from its other fields are not fields.
  A preset's witness proves each field, as `PinPresetFacts.mainnet` and `PinPresetFacts.minimal` do.

- `PinPresetFacts.mainnet` is public: the mainnet preset has the preset facts of the pin.

- `PinPresetFacts.minimal` is public: the minimal preset has the preset facts of the pin.

- `PinDrift.Setting` is public: the setting of the pin's drift bound for one call.
  It holds the runs from genesis to the finalized state, the split state, the pulled-up state and the counting state, with the fork bounds.

- `PinDrift.le_pinReserve` is public: under a `PinDrift.Setting`, it bounds the drift of the quorum from the call's pulled-up state to a counting state.
  It takes the setting and the two total active balances.

- `PinGuarded` is public: the a priori guard at a call's finalized state, for the head that each honest store selects, within the withdrawal delay from that state.

- `justifiedPinned_of_setting` is public: the voters of a call pin the justified checkpoints of the call's epoch.
  It assumes no bound on finality lag: past the withdrawal delay the reserve already covers three times the voters' stake.

- `justifiedPinned_of_setting.mainnet` is `justifiedPinned_of_setting` on the mainnet preset, with the preset premises proved.

- `justifiedPinned_of_setting.minimal` is `justifiedPinned_of_setting` on the minimal preset, with the preset premises proved.

- `DirectSafety.Apriori.Internal.applyPendingDeposit_absent_balances` says that a pending deposit to a key that no validator has raises no balance inside the registry.
  It changes nothing, or appends one validator with its balance.
  The pin's deposit bound reads it.

- `DirectSafety.Apriori.Internal.except_dite_bind` moves a fork-conditional replay before its common continuation.
  The pin's credit bound reads it.

- `DirectSafety.Apriori.Internal.penaltyDebit_sum_zero_of_free` says that events with no penalty or inactivity source debit no key as a penalty.
  The pin's segment penalty bounds read it.

- `DirectSafety.Apriori.Internal.single_balanceEvents` reads the events of one step as the events of the one-step run.
  The pin's step bounds read it.

- `DirectSafety.Apriori.Internal.balance_le_pathCredits` says that the balance at the end of a path of states is at most the balance at its start and the increases between its states.
  The pin's step bounds read it.

- `DirectSafety.Apriori.Internal.recordFold_plain` says that a recorded fold ends at the state of the fold of its actions.
  `PinDriftBound` reads it in `blockReplay_proposer_credits` and `block_flip_balance`.

- `add_le_of_lt_of_aligned` says that a whole number of increments above another is at least one increment above it.
  The pin's effective-balance bounds read it.

- `Models.Network.voters_sum_le` says that a sum over some voters of a function of their positions is at most its sum over those positions.
  The pin's drift bound reads it.

- `activationLe_of_active` and `activationLe_of_slashable` say that an active or slashable validator was activated at or before the epoch.
  `ActivationExitOrder` reads both for its exit, slashing and consolidation steps, and `ValidatorStep` reads the first.
  `PinDriftBound` reads `activationLe_of_active` for active voters.

- `DirectSafety.Apriori.Internal.keys_debits_le` says that the debits of one event over a set of keys are at most its debits over the registry.
  The pin's debit bounds read it.

- `DirectSafety.Apriori.Internal.slashing_credits_le` says that uniform per-index bounds over the step inputs of a run pay all its slashing credits only once.
  The pin's whistleblower terms read it.

- `Internal.minimum_cap` says that the withdrawal cap of a validator is at least the maximum effective balance before Electra.
  It needs the activation balance and the compounding cap in order.
  The pin's floors for keys that upgrade read it.

- `balanceDrift_epoch` says that an epoch keeps every existing effective balance until its effective-balance update.
  Registry updates and pending deposits before it keep existing effective balances, and the stages after it keep the validators and the balances.
  The pin's floor of a key's effective balance reads it.

- `rounded_mono` in `Base.Proofs.Nat` says that rounding down to a multiple of an increment preserves order.
  `EffectiveFall` and `InactivityLeakVoterRun` use it for their rounding bounds, and the pin uses it for its effective-balance bounds.

- `Internal.assigned_of_active` is moved to `Transition.ActiveKept` and says that an active validator has an assigned activation epoch.
  `ValidatorStep`, `PinDriftBound.CreditBudgets` and `PinDriftBound.PreviousEpochRise` use it.

### Changes that break callers

- The signed-conflict slashing theorem of [#3431](https://github.com/ethereum/EthLib/issues/3431) now also covers a block in the epoch after the state of the run, including a block at the first slot of an epoch ([#4243](https://github.com/ethereum/EthLib/issues/4243)).
  Write `x` for the state of the run at which the block applies.
  `DirectSafety.signedConflict_attesterSlashing_accepted_at` (`DirectSafety/Includable.lean`) takes, for each block, a bound of one epoch in place of the hypothesis that the block is in the epoch of `x`.
  It also takes a premise for a block in the next epoch, under the guard that the block's epoch is after the epoch of `x`.
  That premise bundles the three requirements listed in the #3431 entry on the attester slashing at its turn.
  The block's epoch is at most the first epoch of the chain plus its number of epochs.
  `SignersAtEnds` holds for the slots up to the block.
  The chosen validator, if unslashed at `x`, has its withdrawable epoch recorded at `x` after the block's epoch.
  A caller with the old hypothesis `sameEpoch` can pass `sameEpoch.le.trans (Nat.le_succ _)` for the bound, and `fun crossing => absurd crossing (by omega)` for the guarded premise.

- In Lean, two lemmas are removed that restated another lemma with an added `fork < .glamsterdam` argument ([#4297](https://github.com/ethereum/EthLib/pull/4297)).
  `effectiveKept_block` restated `effectiveKept_processBlock`, which holds at every fork, and ignored the argument.
  `BlockLedger.validators_processBlockExecution` restated `processBlockExecution_validators`, which holds from Bellatrix, where the execution part of a block exists, at every later fork.
  Migration: call `effectiveKept_processBlock` and `processBlockExecution_validators` without the pre-Gloas argument.
  The implicit states of `processBlockExecution_validators` are named `state` and `after`, so a call that wrote `(s := s) (t := t)` writes `(state := s) (after := t)` or omits them.

- In Lean, the leanXMSS addresses take the name the specification gives them: `Xmss.CallSite` is now `Xmss.Address` ([#4278](https://github.com/ethereum/EthLib/pull/4278)).
  The old `Xmss.Address`, an abbreviation for the 16 bytes as `Lanes2`, is removed, and `Address.encode` now returns `Lanes2`.
  `CallSite.tau`, `.mu`, `.hi`, `.lo`, `.encode`, `.encode_injective`, `.toNat_encode_lo`, `.bytes_encode` and `.ne_msg_of_hi` become `Address.tau` and so on, with the same statements.
  Migration: replace `CallSite` with `Address`, and a type `Address` that meant the 16 bytes with `Lanes2`.

- In Lean, the leanXMSS tweakable hash, its input and the derivations from the seed take a call site instead of a 16-byte address ([#4277](https://github.com/ethereum/EthLib/pull/4277)); [#4267](https://github.com/ethereum/EthLib/pull/4267) added the call sites.
  `Xmss.CallSite` has one constructor for each address of the specification, and `CallSite.encode` gives its address, as two lanes.
  `CallSite.encode_injective` says that two distinct call sites never share an address.
  `Xmss.th`, `Xmss.thInput` and `Xmss.seedPrf` take a `CallSite`, `Xmss.SeedPrf` reads one, and `Xmss.Unforgeability.PrfInput` holds one; every hash input keeps its bytes.
  The definitions and lemmas that took an address now take a call site, and `thInput_inj` now concludes that the call sites are equal.
  `th_isQueryBoundP_otherLayer` in `EthLib.Cryptography.Proofs.Xmss.SignatureFailure` takes a call site whose `hi` carries the layer, in place of the four raw fields.
  The new `CallSite.ne_msg_of_hi` says that a call site whose `hi` carries one layer is not a message call site of the other layer.
  `encodeAddress`, `AddressType`, `AddressType.code`, `addrPrf`, `addrChain`, `addrLeaf`, `addrNode`, `addrParam`, `addrRnd` and `addrMsg` are removed.
  So are `encodeAddress_inj`, `encodeAddress_ne_of_type_ne`, `AddressType.code_injective`, `addrPrf_inj`, `addrChain_inj`, `addrLeaf_inj`, `addrNode_inj`, `addrRnd_inj`, `addrMsg_inj`, `encodeAddress_ne_addrMsg`, `addrPrf_ne_addrRnd`, `addrParam_ne_addrRnd` and `Unforgeability.toList_encodeAddress`.
  `toNat_encodeAddress_lo` and `bytes_encodeAddress` become `CallSite.toNat_encode_lo` and `CallSite.bytes_encode`.
  In `Xmss.Unforgeability`, `toList_addrChain`, `toList_addrLeaf`, `toList_addrMsg`, `toList_addrRnd`, `toList_addrNode`, `toList_addrPrf` and `toList_addrParam` become `toList_encode_chain`, `toList_encode_leaf`, `toList_encode_msg`, `toList_encode_rnd`, `toList_encode_node`, `toList_encode_prf` and `toList_encode_param`.
  Migration: write `.chain layer e mu` where a call read `addrChain layer e mu`, and `(CallSite.chain layer e mu).encode` where it needs the bytes.
  For `addrChain_inj` and the others, rewrite with `CallSite.encode_injective.eq_iff` and the constructor's `injEq`.

- From Glamsterdam, a system call starts with the accessed addresses of a transaction from the system address to its contract, with no access list ([#4071](https://github.com/ethereum/EthLib/issues/4071)).
  So the beneficiary, the precompiles, the system address and the contract start warm in that call; up to BPO5 it still starts with no access.
  In Lean, the new `Blocks.systemSubstate` gives that start, and `systemSubstate_of_lt_glamsterdam` and `systemSubstate_of_glamsterdam` in `EthLib.Execution.Proofs.Blocks.SystemCall` state it.
  `systemCall_of_glamsterdam` now runs the message from `systemSubstate env target` in place of `Substate.empty`; `systemCall_of_lt_glamsterdam` keeps its statement.
  `SystemCallBurns` in `EthLib.Execution.Proofs.Blocks.Burn` reads the same start in place of the empty substate.
  The new `Transactions.startAccessedAddressesOf` takes an access list, and `startAccessedAddresses` reads it with the access list of the transaction, with the same value.
  `mem_systemSubstate_accessedAddresses` lists the addresses that start accessed from Glamsterdam.
  Migration: rewrite with `systemSubstate_of_glamsterdam` where a proof read the empty substate from Glamsterdam, and with `systemSubstate_of_lt_glamsterdam` where it reads `SystemCallBurns` before Glamsterdam.

- The signed-conflict slashing theorem of [#3431](https://github.com/ethereum/EthLib/issues/3431) now covers a key whose validator has exited but is not yet withdrawable ([#4243](https://github.com/ethereum/EthLib/issues/4243)).
  `DirectSafety.signedConflict_attesterSlashing_accepted_at` (`DirectSafety/Includable.lean`) takes `lifetime` in place of `member : key ∈ activeKeys x.state`.
  `lifetime` gives a validator of `x` with the key that is activated and not yet withdrawable at the epoch of `x`.
  Unlike membership in `activeKeys`, `lifetime` still holds after the validator's exit epoch, until its withdrawable epoch.
  Unlike slashability, it does not require the validator to be unslashed.
  An already slashed active validator was covered before too, since activity ignores the slashed flag; an exited one was not.
  For a validator already slashed at the turn, the left disjunct holds, as before.
  A caller with `member` builds `lifetime` with `DirectSafety.mem_keysAt_epoch_of_within`, from the registry limit and the order of exits that `holds` gives.
  That lemma is in `EthLib.Consensus.Proofs.DirectSafety.ChurnBounds`, which the caller must import itself.
  The registry limit is `(RunBounded.size_le holds.bounded).trans (holds.run conditions within).load.1`, and the order of exits is `holds.invariant.exitsOrdered`.

- `dnsdisc.resolve` refuses a list whose root of links reaches a node record, even when the root of records also reaches it.
  EIP-1459 says that a record "may only appear in the `enr-root` subtree".
  It gave the list, and skipped the record under the root of links, since the walk took a hash met in either subtree as read.
  In Lean, `walk` and `walkCollision` track each hash with its subtree, in a `List (Subtree × Hash)` in place of a `List Hash`.
  A branch under both roots is now read in each subtree, so the hashes below it take from the budget in each.
  A list near its budget can now end with too many entries.
  `records_of_resolve` and `links_of_resolve` in `EthLib.Networking.Proofs.DnsDisc` state that each entry that a subtree of a resolved list reaches is a branch or a leaf of that subtree.

- The signed-conflict slashing theorem of [#3431](https://github.com/ethereum/EthLib/issues/3431) now also states that the slashing leaves the validator slashed ([#4244](https://github.com/ethereum/EthLib/issues/4244)).
  In `DirectSafety.signedConflict_attesterSlashing_accepted_at` (`DirectSafety/Includable.lean`), the right disjunct also gives the validator at the index in the state right after the slashing.
  That validator still has the key and is slashed.
  A caller that destructured the disjunct as `⟨after, ok⟩` now writes `⟨after, _, ok, _⟩`, where the first `_` is that validator.
  The old disjunction follows from the new one by `.imp id fun ⟨after, _, ok, _⟩ => ⟨after, ok⟩`.
  The left disjunct is unchanged: it covers a validator already slashed at the turn, and the theorem says nothing more about that case.

- In Lean, `getUnslashedAttestingIndices_exists_ok` in `EthLib.Consensus.Proofs.Transition.Totality.Justification` drops its premise that the registry stays within its limit, which its proof did not read.
  Committee membership alone puts each signer in the registry, by `getPendingAttestingIndices_lt`.
  Migration: delete the `within` argument ([#4253](https://github.com/ethereum/EthLib/pull/4253)).

- In Lean, `Execution.blocks_of_partiallySynchronous` is removed; its one reader, the confirmed-root step, now reads `Execution.blocks_of_partiallySynchronous_of_anchorSlot`.
  Migration: use `Execution.blocks_of_partiallySynchronous_of_anchorSlot` (added earlier in 0.4.0), passing `fun gloas => absurd gloas (Nat.not_le_of_lt preGloas)` for `anchorSlot` and `start v honest` and `start u receiver` for the two starts.

- In Lean, the confirmed root of a run of fast-confirmation calls covers honest heads from Gloas too, and keeps its Fulu floor.
  `Execution.confirmedRoot_covers` takes `room`, `weights` and `supply`, gated on Gloas, instead of `preGloas`.
  They are the anchor's registry room, the head-weight bundle, and the head-weight ceiling of honest justified states.
  `CallsCtx` drops its field `preGloas`, and `StepCtx` carries `room`, `weights` and `supply`.
  `sourceOnParentChain_of_walk`, `Execution.honestTargetVotes_of_byzantineStakeAtMost` and `Store.viable_of_ancestor` drop their pre-Gloas binder.
  `Execution.receiverWindowExitsNear_of_sourceOnParentChain` takes `within`, the registry of the source within the limit, instead of `preGloas`.
  Migration: pass `room`, `weights` and `supply` each as `fun g => absurd g (Nat.not_le_of_lt preGloas)`, delete the other arguments, and pass `within := source.validators.bound preGloas`.

- In Lean, the quorum drift of a call is bounded from Gloas too, and keeps its Fulu floor.
  `quorumDrift_le_quorumReserve` takes `within` at the counting state instead of `early`.
  `Execution.quorumDriftWithin` takes `room`, the anchor's registry room from Gloas, instead of `early`.
  `setting_runs_of_call` drops `early`.
  Migration: pass `within := BeaconState.registryWithinLimit_of_lt early state` and `room := fun g => absurd g (Nat.not_le_of_lt early)`, and delete the argument of `setting_runs_of_call`.

- In Lean, `effectiveRise_le` and `effectiveFall_le` bound the effective-balance rise and fall from Gloas too, and keep their Fulu floor at `P`.
  They take `within`, the registry of the counting state within the limit, instead of `early`.
  From Gloas the type of the registry does not give it.
  Migration: pass `within := y.state.validators.bound early`.

- In Lean, the sync-key lemmas hold through Gloas, still from Altair at both ends, and `depositCarry_processBlock` holds at every fork.
  Their conclusions are unchanged.
  `Run.currentSyncCommittee_eq_of_same_period`, `Run.currentSyncCommittee_eq_nextSyncCommittee_of_next_period`, `Run.currentSyncCommittee_eq_of_same_epoch` and `depositCarry_processBlock` drop their pre-Gloas binder.
  Migration: delete the argument.

- In Lean, the block and ledger lemmas behind the quorum reserve extend through Gloas, and their existing lower fork bounds remain.
  These drop their pre-Gloas binder (`DirectSafety.total_active_congr` drops two, `before` and `after`), with the same conclusion: `DirectSafety.total_active_congr`, `Run.effectiveKept_of_same_epoch`, `hysteresis_of_run_slot`, `balanceDrift_upgrades_upper`, `balanceDrift_upgrades_active`, `BlockLedger.ledger_processBlockExecution`, `BlockLedger.ledger_processProposerSlashing`, `BlockLedger.ledger_processAttesterSlashing`, `processOperations_floor`, `BlockCredits.block_balances`, `Run.withdrawableKept_of_same_epoch`, `Run.balanceCorrections_of_same_epoch`, `Run.effectiveBalance_capped`, `Run.pendingConsolidationsOrdered`, `Run.pendingConsolidation_invariant`, `ConsolidationQueueRise.appendStep_processBlock`, `ConsolidationQueueRise.riseStep_processBlock`, `SamePendingQueue.blockExecution`, `applyWithdrawals_departureQueues`, `attestation_departureQueues` and `slashValidator_departureQueues`.
  Migration: delete the arguments.

- In Lean, lemmas whose proofs read no upper fork bound drop it, with the same conclusion.
  `Run.effectiveAt_le_of_same_epoch` drops `early : y.fork < .pectra`; the other 23 drop a bound below Gloas.
  They are `ReservedReplay.fresh_not_initial`, `effectiveAt_le_withdrawalMax`, `step_same_epoch_effective`, `run_same_epoch_effective`, `Run.effectiveAt_le_of_same_epoch`, `Run.pendingConsolidations_apart`, `Run.pendingConsolidation_targets`, `Run.pendingConsolidation_sources`, `Run.retired_validator`, `run_slashed_exit_assigned`, `Run.newly_slashed_initial_exited_unwithdrawable`, `Run.newly_slashed_withdrawableEpoch`, `Run.slashed_withdrawableEpoch_mono_epoch`, `Run.slashed_withdrawable_eq`, `Run.compounding_of_exit_assigned`, `Run.validatorCap_mono`, `pass_kept`, `epochPrefix_slashedSpan`, `cap_le_cap_of_run`, `effective_le_cap_at`, `capCeil_path`, `slashed_waits`, `newly_slashed_unwithdrawable` and `effectiveAt_le_capMax`.
  Migration: delete the `early` argument.

- In Lean, `Run.induction_of_same_epoch` and `Run.induction_of_same_period` induct over runs through Gloas.
  `Run.induction_of_same_epoch` drops `early` and the pre-Gloas hypothesis of its block callback.
  `Run.induction_of_same_period` drops `early` and the pre-Gloas hypotheses of both callbacks.
  Migration: delete `early`; a callback that used the hypothesis keeps it through the motive `fun z pre => z.fork < .glamsterdam → motive z pre`, and the caller applies the result to `early`.

- In Lean, `Internal.CapStep.run` holds through Gloas, and keeps the invariant of the transition.
  It drops `early`; its `AssignedPartials` and `UnassignedEligibleBalance` conjuncts are proved before Gloas only, and now take it as a hypothesis.
  Migration: write `.2.1 early` for `.2.1` and `.2.2.2 early` for `.2.2.2`; `.1` and `.2.2.1` are unchanged.

- In Lean, the withdrawal step and the execution part of a block state their departure queues by the payload of the parent.
  From Gloas a block whose parent has no payload pays no withdrawals.
  `withdrawals_departureQueues` and `blockExecution_departureQueues` drop `early`.
  They conclude with a clause for a full parent or for a fork from Electra through before Gloas, and a clause for an empty parent.
  Migration: before Gloas, take the second half of the first clause; the second clause needs Gloas.

- In Lean, `getExpectedWithdrawals_partials` reads the partial withdrawals after the prior ones.
  From Gloas the queued builder withdrawals come first, so the read starts after them.
  It drops `early` and concludes with the prior withdrawals and the start index.
  Migration: before Gloas, the first clause gives no prior withdrawals and the state's next withdrawal index.

- The TLS 1.3 key schedule names its Main Secret as [RFC 9846 §7.1](https://www.rfc-editor.org/rfc/rfc9846#section-7.1) does, where it kept the Master Secret of RFC 8446 ([#4242](https://github.com/ethereum/EthLib/issues/4242)).
  In Python, the field `master` of `KeySchedule` is now `main`; the tuple keeps its order, so positional reads are unchanged.
  The key `master` of `TrafficSecrets`, in the negotiated part of a handshake state, is now `main`, so a state saved with the old key no longer reads back.
  In Lean, `masterSecret` is now `mainSecret`, the field `KeySchedule.master` is now `KeySchedule.main`, and the theorem `masterSecret_ok` is now `mainSecret_ok`.
  The statement of `keySchedule_eq_ok_iff` follows the new names.

- A completed TLS 1.3 client now silently ignores every 1-RTT NewSessionTicket, whatever its body, as [RFC 9846 §4.7.1](https://www.rfc-editor.org/rfc/rfc9846#section-4.7.1) requires of a client without resumption ([#4241](https://github.com/ethereum/EthLib/issues/4241)).
  It parses only the message type and length, so it no longer checks the ticket's fields, its extension placement or the early_data value of RFC 9001 §4.6.1.
  `client_step` now returns the unchanged state for such a ticket, where it raised `TlsStepError` with decode_error (`0x132`), illegal_parameter (`0x12f`) or PROTOCOL_VIOLATION (`0x0a`).
  A post-handshake CertificateRequest or KeyUpdate still fails as before.
  In Lean, the new theorem `clientStep_ticket` states that a completed client keeps its state for any framed ticket at the 1-RTT level.

- A TLS 1.3 hello whose legacy_version is not `0x0303` now fails with protocol_version, as RFC 9846 §§4.2.2 to 4.2.4 ask, where it failed with illegal_parameter ([#4234](https://github.com/ethereum/EthLib/issues/4234)).
  `decode_message` and `transcript` raise `TlsHandshakeError` with the new local code 8, `legacyVersion`, where they raised code 4, `constant`.
  `client_step` and `server_step` raise `TlsStepError` with the QUIC code `0x146`, where they raised `0x12f`.
  In Lean, `Wire.Error` has the new constructor `legacyVersion`, which the step layer maps to `protocolVersion`.

- The TLS 1.3 codec takes two floors of [RFC 9846](https://www.rfc-editor.org/rfc/rfc9846), which obsoletes RFC 8446 ([#4234](https://github.com/ethereum/EthLib/issues/4234)).
  A ClientHello extension block may have 7 bytes, a lone supported_versions extension, as RFC 9846 §4.2.2 and the verified [erratum 8423](https://www.rfc-editor.org/errata/eid8423) of RFC 8446 say, where the codec asked for 8.
  A CertificateRequest extension block may be empty, as RFC 9846 §4.4.2 says, where the codec asked for 2 bytes.
  `encode_message` and `decode_message` now accept both, where they raised `TlsHandshakeError` with the local code 2.
  The handshake steps still require signature_algorithms in a CertificateRequest, so an empty block now gives missing_extension in place of decode_error.

- A QUIC 0-RTT packet that carries a RETIRE_CONNECTION_ID frame now fails with PROTOCOL_VIOLATION, as the verified [erratum 7365](https://www.rfc-editor.org/errata/eid7365) of RFC 9000 asks ([#4222](https://github.com/ethereum/EthLib/issues/4222)).
  The erratum corrects Table 3 of §12.4 to allow the frame in 1-RTT packets only, as the end of §12.5 already said.
  `decode_frame` on a 0-RTT packet now raises `QuicError` with the local code 9 for frame type `0x19`, where it returned the frame.
  In Lean, `Frame.allowed` of a RETIRE_CONNECTION_ID frame is false for 0-RTT, so `Frame.decode` rejects it there.

- In Lean, the shared Jacobian scalar multiplication of short Weierstrass curves works over any field, and `G_2` of alt_bn128 uses it ([#4092](https://github.com/ethereum/EthLib/issues/4092)).
  `ShortWeierstrass.Point.mulBits` takes a point over any field `F`, with maps between `F` and its representation, where it took `Fin m`.
  The new `ShortWeierstrass.Point.toCoords` gives the Jacobian form of a point over any field, and `toJacobian` is that form over `Fin m`.
  `Jacobian.ofAffine` is gone: `toCoords` gives `(x, y, 1)`.
  `AltBn128.Point2.mulBits` is the shared multiplication over `Fp2`, with one inverse at the end where the affine rule took one at each step.
  The new theorems `Jacobian.Coords.double_spec`, `add_spec`, `toPoint_mulBits` and `toPoint_mulAdd` state the group law of the forms of a nonsingular curve, over any field in which `2` is not zero.
  `ShortWeierstrass.Point.toPoint_mulBits_field` and `isOnCurve_mulBits_field` state that the shared multiplication computes `k P`, on the curve, over any such field and in any representation.
  The chains also stay on the curve, by `Jacobian.Coords.onCurve_mulBits`, `onCurve_mulAddAux` and `onCurve_mulAdd`, and the joint chain computes `k P + l Q` by `toPoint_mulAddAux`.
  Bridges relate forms over `Fin m` to their values in `ZMod m` (`Jacobian.onCurve_iff`, `Jacobian.toPoint_eq` and the `Jacobian.map_*` lemmas), and points to forms over any field (`ShortWeierstrass.Point.toCoords_spec` and `ofCoords_spec`).
  `Jacobian.Coords.Embedding.id` states that the identity is a change of representation.
  The formulas over `Fin m`, `Jacobian.double_eq_formula` and `Jacobian.add_eq_formula`, are gone, with the numeral lemmas `Jacobian.toZ_two`, `toZ_three`, `toZ_four` and `toZ_eight` that only they used ([#4117](https://github.com/ethereum/EthLib/issues/4117)).
  The forms over any field keep their formulas, `Jacobian.Coords.double_eq_formula` and `add_eq_formula`.
  `AltBn128.fp2_two_ne_zero` states that `2` is not zero in `Fp2`, for the group law of the twist and for the lines of the pairing.
  The theorems about forms over `Fin m`, about the prime-field curves and about `G_2` keep their statements, and now follow from these.
  No value changes for points on the curve, the only points that ECPAIRING passes to the multiplication of `G_2`.

- In Lean, the points of `G_2` on the alt_bn128 twist are the shared short Weierstrass points over `Fp2` ([#4061](https://github.com/ethereum/EthLib/issues/4061)).
  `AltBn128.Point2` is now `ShortWeierstrass.Point Fp2`, through the new instance `AltBn128.instTwistParams` with `a = 0` and `b2`.
  Its sum, negation and curve test are those of the shared rule, so `AltBn128.Point2.add` and `AltBn128.Point2.isOnCurve` are gone.
  Dot notation still finds `p + q` and `p.isOnCurve`, and `-p` is new.
  `Point2.infinity` and `Point2.affine` keep their names, as abbreviations of the shared constructors.
  `Fp2` gets the numerals `2` and `3` of the rule, as `AltBn128.instOfNatTwo` and `AltBn128.instOfNatThree`.
  The generic extension gets `0` and `1` in its specification module instead of its proofs.
  No value changes, and the theorems about `G_2`, the pairing and ECPAIRING keep their statements.

- In Lean, the readers of byte fields move from Base to Networking, next to their only users, the QUIC and TLS wire formats and Protobuf ([#3841](https://github.com/ethereum/EthLib/issues/3841)).
  The modules `EthLib.Base.ByteReader` and `EthLib.Base.Proofs.ByteReader` are now `EthLib.Networking.Encoding.ByteReader` and `EthLib.Networking.Proofs.Encoding.ByteReader`, and the namespace `EthLib.Base.ByteReader` is now `EthLib.Networking.Encoding.ByteReader`.

- In Lean, base32 moves from Base to Networking, next to its only user, node discovery by DNS ([#3841](https://github.com/ethereum/EthLib/issues/3841)).
  The modules `EthLib.Base.Base32` and `EthLib.Base.Proofs.Base32` are now `EthLib.Networking.Encoding.Base32` and `EthLib.Networking.Proofs.Encoding.Base32`, and the namespace `EthLib.Base.Base32` is now `EthLib.Networking.Encoding.Base32`.
  The string forms `Base32.encode` and `Base32.decode`, which nothing used, are gone with their theorems `Base32.decode_encode` and `Base32.encode_of_decode`.
  `Base32.decodeList_encodeList` and `Base32.encodeList_of_decodeList` state the same bijection on lists of characters.

- In Lean, NFKD normalization moves from Base to Cryptography, next to the EIP-2335 keystore, its only user ([#3840](https://github.com/ethereum/EthLib/issues/3840)).
  The modules `EthLib.Base.Unicode` and `EthLib.Base.Unicode.Data` are now `EthLib.Cryptography.Unicode` and `EthLib.Cryptography.Unicode.Data`, and the namespace `EthLib.Base.Unicode` is now `EthLib.Cryptography.Unicode`.
  `EthLib.Base` no longer imports them.
  The Unicode License of the table is now `EthLib/Cryptography/Unicode/LICENSE`.

- In Lean, three list lemmas of Base give way to the Batteries lemmas they repeat ([#3839](https://github.com/ethereum/EthLib/issues/3839)).
  `Base.forall₂_of_mapM_ok` and `Base.mapM_ok_of_forall₂` are the two directions of `List.mapM_eq_ok_iff_forall₂`.
  `Base.forall₂_of_mapM_some` is the forward direction of `List.mapM_eq_some_iff_forall₂`.
  The module `EthLib.Base.Proofs.FoldlM` is gone: `Base.foldlM_exists_ok_of_distinct` is now in `EthLib.Base.Proofs.MapM`, unchanged.

- In Lean, the big-endian conversions of other layers are defined through `Base.bytesToNat` and `Base.natToBytes` ([#3838](https://github.com/ethereum/EthLib/issues/3838)).
  The reading side covers RLP scalars, AES counter blocks and the size in an RLPx frame header.
  The writing side covers AES counter blocks, `I2OSP` of hash to curve, that frame size, RPC storage keys and the counter of a discv5 nonce.
  No value changes.
  `Rlp.ofBigEndian_lt` and `Rlp.foldl_bigEndian_lt` are gone: `Base.bytesToNat_lt` gives the bound.
  `Execution.Rpc.getElem_natToBytes` moves to `Base.getElem_natToBytes`.
  `Rlp.ofBigEndian_nil` and `Rlp.ofBigEndian_append_singleton` state the reading of no bytes and of a byte appended at the end.

- In Lean, the four counts of the expected withdrawals are `UInt64`, as the source types them ([#3858](https://github.com/ethereum/EthLib/issues/3858)).
  The parts still count on natural numbers, and a count of `2^64` or more fails, as the increment of a `uint64` count that reaches it would; no reachable value changes.
  The updates of the queues and of the sweep of builders take the counts as `UInt64`, and the sweep of builders adds its count with no wrap.
  Theorems that use a count as a list length take its `toNat`, among them `getExpectedWithdrawals_bounds`, `getExpectedWithdrawals_parts`, `getExpectedWithdrawals_partials` and `applyExpectedWithdrawals_builderQueues`.
  `liftCount_ok_iff` states when a count converts.

- In Lean, the fewest epochs over which a node serves blocks returns an `Except ArithError Epoch`, and fails where its `uint64` arithmetic overflows or, from Gloas, divides by zero ([#3857](https://github.com/ethereum/EthLib/issues/3857)).
  Before Gloas the sum wrapped, and from Gloas the result was truncated to 64 bits and a zero denominator gave 0.
  From Gloas the product `3 * CHURN_LIMIT_QUOTIENT_GLOAS * CONSOLIDATION_CHURN_LIMIT_QUOTIENT` now fails at `2^64`, where it was computed on natural numbers.
  `computeMinEpochsForBlockRequests_toNat` states that a result is the count on natural numbers.
  The mainnet and minimal values are unchanged.

- In Lean, the gossipsub parameters take the slot duration and the slots per epoch as `UInt64`, and fail with an overflow when two epochs in milliseconds reach `2^64`, as the `uint64` arithmetic of the source does ([#3856](https://github.com/ethereum/EthLib/issues/3856)).
  They return an `Except ArithError`, and the mesh and message cache theorems take the success as a hypothesis.
  `gossipsubParameters_isOk_iff` states when they succeed, and `gossipsubParameters_seen_ttl` that the lifetime of a seen message ID is then two epochs in whole seconds.
  In Python, `gossip.router.parameters` raises `GossipError` with `two epochs in milliseconds are not below 2^64` there, where it returned a lifetime from the unbounded product.
  It also refuses a slot duration or a slots per epoch outside the 64-bit range.

- The block checks and the state transition of the execution layer give their block errors through the shared conversion ([#3605](https://github.com/ethereum/EthLib/issues/3605)).
  No error code changes, but some messages change in Python.
  `blocks.validate_size`, `blocks.validate_header` and `blocks.check_header` give `block invalid: ` and the short name of the block error, with any inner error still named in full, such as `block invalid: wrongDifficulty (expected := 131072) (actual := 0)`.
  They gave `block invalid: ` or `header invalid: `, then the full Lean name, such as `EthLib.Execution.Blocks.BlockError.wrongDifficulty`.
  `blocks.state_transition` and `rpc.serve`, which reads the blocks of a chain, give `block invalid: encoding (…)` for a block that does not decode, in place of `block rejected: …`.
  A transaction of the body that does not decode keeps its message, `transaction N does not decode: …`, which the block error instance now gives.
  In Lean, the messages and the instances of the transaction, inclusion, EVM abort and block errors move to the new module `Execution.Exports.Errors`, with their names unchanged.

- In Lean, `eth_sendRawTransaction` and `eth_simulateV1` fail with an internal error when the excess blob gas of the next or simulated block is `2^64` or more, where they truncated it to 64 bits ([#3850](https://github.com/ethereum/EthLib/issues/3850)).
  `childExcessBlobGas` computes the excess blob gas that a parent gives to a child at a number and a time, and the Engine's `builtExcessBlobGas` and `ChainView.nextExcessBlobGas` are instances of it.
  `ChainView.nextBlobSchedule` gives the schedule of the next block.
  `ChainView.nextEnvironment` takes a proof that the next excess blob gas is below `2^64`, and so does `baseFeeOf_nextEnvironment`.
  `checkBlock_simulateBlock` and `stateTransition_of_simulateBlock` no longer take a bound on the parent's excess plus blob gas.
  `simulateBlock_eq_error_of_excess` states the failure.

- `dnsdisc.parse_entry` and `dnsdisc.resolve` give code 8, a refused node record, for a record whose RLP encoding fails, in place of code 0 ([#3605](https://github.com/ethereum/EthLib/issues/3605)).
  The message stays `record has no RLP encoding`, and every export that encodes a record now gives it.
  The encoder fails only for a payload of `2^64` bytes or more, so no record of a test reaches this failure.

- In Lean, GASPRICE, NUMBER, DIFFICULTY, GASLIMIT, BASEFEE and BLOBBASEFEE abort the execution with the new error `EvmError.wordOverflow` when the number they push is `2^256` or more ([#3848](https://github.com/ethereum/EthLib/issues/3848)).
  They pushed the number modulo `2^256`, a value that no source gives; execution-specs fails there with an error that is not an exception of the EVM.
  The new step `readNumber` reads such a number; `EvmError.aborts` is true on the new error, and the trace text of the error is `value above a word`.
  `environmentStep_blobbasefee` takes the hypothesis that the blob base fee is below `2^256`, and `environmentStep_blobbasefee_of_le` states the abort above it.
  `BlockEnvironment.WordsFit` and `WordsFit` state that the numbers of an environment fit words.
  `step_aborts_state`, `processMessage_eq_error`, `processCreateMessage_eq_error`, `processMessageCall_eq_error`, `processTransaction_eq_error`, `applyBody_aborted`, `stateTransition_aborted` and `stateTransition_eq_error_invalid` take that bound as a new hypothesis.
  `errorsMeet_stateTransition` and `errorsMeet_stateTransition_of_plain` ask the body to meet the property only in the environments that the header gives, one for each list of recent hashes, where they asked it in every environment.
  `env_of_step_eq_child` states that a message a step sends has the environment of its frame.
  `push_of_readNumber` and `push_of_readNumberG` are the program-logic rules of an instruction that reads a number.
  `readNumber_pays`, `MeterRules.readNumber_keeps`, `readFrame_of_readNumber`, `readNumber_sameContext` and `memory_readNumber` carry the facts of an instruction that reads the frame over to it.
  Migration: pass a proof that the numbers of the block, and the gas price of the transaction, are below `2^256`.

- In Lean, `Blocks.Exports.oneLine` moves to `EthLib.Exports.oneLine`, beside the shared conversion of export errors ([#3605](https://github.com/ethereum/EthLib/issues/3605)).
  The exports that printed an error on one line by hand use it, and their messages stay the same.

- The optimistic sync, slashing protection, Keymanager API, Builder API, ENR, DNS discovery and execution JSON-RPC exports turn their errors into a code and a message through the shared conversion ([#3605](https://github.com/ethereum/EthLib/issues/3605)).
  No error code changes, but some messages change in Python.
  The optimistic sync exports give their fork choice error after `optimistic sync: `, in place of `optimistic sync failed with code N`.
  Slashing protection and the Keymanager API give their error on one line, in place of `slashing protection failed with code N` and `keymanager value rejected with code N`.
  That form is the full Lean name of the constructor and its arguments, such as `EthLib.Consensus.SlashingProtectionError.slashableBlock 100`, with roots as hex behind `0x`.
  The Builder API gives a failed step of the transition on one line, as the other consensus exports do.
  `dnsdisc.verify_root` gives `root does not have the fields e=, l=, seq= and sig=, in that order` for a text that is no root, in place of `text is not a root`.

- In Lean, the nonce of a set-code transaction is `UInt64`, and the other kinds keep a nonce of 256 bits ([#3846](https://github.com/ethereum/EthLib/issues/3846)).
  So a set-code transaction with a nonce of `2^64` or more fails at decoding, with `scalarTooLarge`, where the rule of EIP-2681 refused it with `nonceOverflow`.
  `Transaction.nonce` still returns a `U256`, and gives the 64-bit nonce unchanged.
  `typedFields` takes the nonce as a `Nat`.
  The JSON reader of transactions reads the nonce of type 4 as a 64-bit quantity.
  `GenericTransaction.toTransaction` refuses a type 4 nonce of `2^64` or more with `nonce: too large`, through the new `callUint64`.
  `exists_toTransaction_eq_ok_iff` gains the conjunct `tx.kind = 4 → nonce < 2 ^ 64`.
  Migration: read `tx.nonce.toNat` of a `SetCodeTransaction` where a natural number is needed.
  `eth_simulateV1` answers a set-code call with such a nonce with -32602 and `transaction: nonce: too large`, where it answered -32603.
  In Python, `transactions.check`, `tx_hash`, `recover_sender` and `intrinsic_gas` report `decoding: field 1: scalarTooLarge <nonce> 64` for such a transaction.

- The configuration reader of the exports refuses an activation, by block or by time, of `2^64` or more, as the reader of a client configuration file already refused such a time ([#3854](https://github.com/ethereum/EthLib/issues/3854)).
  `Base.ACTIVATION_BOUND` is that bound, `2^64`: the fork identifier of EIP-2124 and EIP-6122 hashes each fork block and time as a `uint64`.
  The file reader, the export reader and `eth_config` all read it, and the doc of the file reader's error now cites the fork identifier instead of a block's time.
  In Python, every export that reads the JSON form of a chain configuration fails with code 0 and `an activation is not below 2^64` on such an activation; `eth_config` no longer sees one.
  The schedule reader of the fork identifier exports refuses a fork value or a merge fork block of `2^64` or more, with code 0.

- In Lean, the attestation and sync committee rewards of the Beacon API fail with code 500 when a signed amount does not fit the `Int64` of the response types ([#3853](https://github.com/ethereum/EthLib/issues/3853)).
  The amounts stay unbounded integers, and the responses check them once, with `int64Fits` and the `fits` of each answer type, before they write the answer.
  `attestationRewardsResponse_ok` and `syncCommitteeRewardsResponse_ok` gain a conjunct: every amount of an answer fits.
  Migration: a proof that destructures the conclusion of either lemma takes one more component.

- In Lean, an Engine node keeps the number and the time of each known block unbounded, as its header holds them, and the build of a payload fails on an excess blob gas of `2^64` or more ([#3852](https://github.com/ethereum/EthLib/issues/3852)).
  `KnownPayload.number` and `KnownPayload.timestamp` are `Nat`, so a block with a time of `2^64` or more no longer wraps to a small time in the check that the attributes come after the head.
  `checkAttributes` compares the head's time with the `toNat` of the attributes' time, and `checkAttributes_eq_ok_iff`, `checkAttributes_eq_error_of_unsupportedFork`, `checkAttributes_eq_error_of_wrong_structure` and `checkAttributes_eq_error_of_not_after_head` state the checks on `Nat`.
  The statements on the JSON of the attributes of a forkchoice update, `forkchoiceUpdatedCall_payloadAttributesJson` and its forms for Glamsterdam and Hegotá, read the times the same way.
  `buildPayload` fails with the new block error `excessBlobGasOverflow`, of code 257, when `builtExcessBlobGas`, the excess that the parent gives, is `2^64` or more; `buildPayload_eq_error_of_excessBlobGas_overflow` states it.
  The refusals after that check, `buildPayload_eq_error_of_hash_eq_error`, `_of_runBody_eq_error`, `_of_checkBlock_eq_error` and `_of_outputChecks_eq_error`, take the hypothesis that the excess is below `2^64`.
  `buildPayload_of_buildPayloadOnChain` and the refusals of `buildPayloadOnChain` give the head with the parent's number and time unconverted.
  In Python, `engine.build_payload` builds on a parent whose number is `2^64` or more, where it refused it with code 0.
  A parent whose time is `2^64` or more now fails with `-38003`, since the time of the attributes is a 64-bit number and cannot come after it.
  `engine.forkchoice_updated` reads the numbers and times of its tree of known blocks unbounded.
  Migration: read a known block's number and time as natural numbers, and pass the bound on the excess to the refusal lemmas.

- In Lean, the SSWU map of BLS12-381 `G1` reads the square root of the base field as an option, and the wrapper `sqrtOrError` is removed ([#4009](https://github.com/ethereum/EthLib/pull/4009)).
  The map gives the same points and fails with the same error.
  `Fp.sqrtOrError_eq` and `map_sqrtOrError` are removed.
  Migration: use `BaseField.sqrt`, with `Fp.baseField_sqrt` and `BaseField.Hom.map_sqrt`.

- In Lean, BLS12-381 `G2 F` is an abbreviation of `G1 (Fp2 F)`, and the operations of `G1` ask for the field operations alone ([#4007](https://github.com/ethereum/EthLib/pull/4007)).
  `G2` runs the formulas of `G1`, with mixed addition, and gives the same points.
  `G2.zero`, `G2.neg`, `G2.add` and `G2.mul` are aliases of the operations of `G1`; `G2.double`, `G2.mulNat`, `G2.toAffine`, `G2.isInfinity` and `G2.projectiveEq` are removed, and a caller writes field notation such as `p.double`.
  The group law is proved once in `G1.Law`, and the theorems of `G1Group` and `G2Group` keep their statements; `G1.doubleSpec`, `G1.addSpec`, `G1.double_eq_doubleSpec` and `G1.add_eq_addSpec` are removed.
  `G1.map` takes a `FieldOps.Hom`, which `BaseField.Hom` extends, so a caller writes `G1.map f.toHom`; `G2.map f` is `G1.map (Fp2.hom f)`.
  `FieldOps.Embedding` moves to `Proofs/BaseField`, `Fp.embedding` to `FpZMod`, and the fuel ladder `mulNatAux` of `G1Order` to `CurveMap`, over any base field.

- In Lean, the target and the maximum of a blob schedule are `UInt64`, as EIP-7892 types them, and the update fraction stays `Nat` ([#3845](https://github.com/ethereum/EthLib/issues/3845)).
  `BlobSchedule` gains the bound `maxBlobGas_lt`: the blob gas of the maximum, `GAS_PER_BLOB * max`, is below `2^64`.
  `GAS_PER_BLOB` moves to `EthLib.Base`, and `Fees.BlobBaseFee` exports it under its old name.
  `BlobSchedule.ofNat?` builds a schedule from three natural numbers when they meet its bounds.
  `ofNat?_isSome_iff` states when it builds one, `target_toNat_of_ofNat?`, `max_toNat_of_ofNat?` and `baseFeeUpdateFraction_of_ofNat?` what it holds, and `ofNat?_toNat` the round trip.
  The reader of a configuration file, the configuration reader of the exports and the blob schedules of the header check build their schedules with it.
  So they refuse a target or a maximum of `2^64` or more, and a maximum of `2^47` or more, whose blob gas reaches `2^64`.
  The statements on the excess blob gas read the target and the maximum through `UInt64.toNat`: `calcExcessBlobGas_of_lt`, `calcExcessBlobGas_eq_sub`, `calcExcessBlobGas_of_lt_fusaka`, `calcExcessBlobGas_of_below`, `le_calcExcessBlobGas_of_below`, `calcExcessBlobGas_le`, `excessBlobGasGrowth`, `excessBlobGasGrowth_succ`, `excessBlobGas_le_of_checkHeader`, `excessBlobGasGrowth_of_eq` and `blobGasUsed_le_of_stateTransition`.
  In `excessBlobGas_le_of_stateTransition`, the hypothesis that the maximum never falls compares the two maximums as `UInt64`.
  `getObjVal_configObject_blobSchedule` writes the target and the maximum as the JSON numbers of their `toNat`.
  The C export `execution_blob_schedule` returns the same integers, now typed as 64-bit.
  Migration: read `s.target.toNat` and `s.max.toNat` where a natural number is needed, and build a schedule from numbers with `BlobSchedule.ofNat?`.
  In Python, `blocks.validate_header` and the configuration readers of `chain` refuse a blob schedule whose maximum is `2^47` or more.
  The message of the two readers that are not the file reader becomes `a blob schedule needs target ≤ max, 0 < max, 0 < update fraction and a blob gas of max below 2^64`.

- In Lean, the KZG trusted setup decodes its hex strings with the reader of Base, and its own copy is removed ([#3837](https://github.com/ethereum/EthLib/issues/3837)).
  `TrustedSetup.nibble?`, `TrustedSetup.hexToBytesAux` and `TrustedSetup.hexToBytes?` are removed, and the decoders of the setup give the same results.
  `SetupLagrange.coords_of_encodes`, `SetupTorsion.modulus_smul_eq_zero`, `TrustedSetup.hexListToBytes_mem` and `TrustedSetup.hexListToBytes_getElem` state `Base.hexBytes? s.toList` where they stated `TrustedSetup.hexToBytes? s`.
  In `SetupTorsion`, `nibble?_eq` becomes `hexValue?_eq` and `hexToBytesAux_eq` becomes `hexBytesFrom?_eq`, on the Base readers, and `byte_eq` states `16 * a + b` in place of `a <<< 4 ||| b`, for any two numbers, with no bound.
  Migration: write `Base.hexBytes? s.toList` for `TrustedSetup.hexToBytes? s`.

- In Lean, the SSZ JSON codec reads hex with the readers of Base, and its own copies are removed ([#3837](https://github.com/ethereum/EthLib/issues/3837)).
  `Ssz.hexDigit` and `Ssz.hexBytesFrom` are removed, and `Ssz.hexBytes` reads its digits with `Base.hexBytes?`, with the same results.
  The lemmas `Ssz.hexDigit_toUpper`, `Ssz.hexBytesFrom_map_toUpper`, `Ssz.hexBytesFrom_eq` and `Ssz.hexBytes_cons` are removed.
  Migration: use `Base.hexValue?_toUpper` and `Base.hexBytesFrom?_map_toUpper`; the two loop lemmas have no replacement, so unfold `Ssz.hexBytes` and reason on `Base.hexBytesFrom?`.

- In Lean, `Execution.honestTargetVotes_signed_of_checked` holds at every fork.
  It no longer takes `preGloas : fork < .glamsterdam`; it takes `registries`, gated from Gloas, in its place: every honest held block state up to `time` has its registry within the limit.
  Migration: before Gloas, pass `fun gloas => absurd gloas (Nat.not_le_of_lt preGloas)`; from `HonestRegistriesWithinLimit`, pass its first half.
  The new statement implies the old one.

- In Lean, `Execution.rootInFilteredTree_of_checked` holds at every fork.
  It no longer takes `preGloas : fork < .glamsterdam`; it takes `room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon` after `inHorizon`.
  Migration: before Gloas, drop `preGloas` and pass `fun gloas => absurd gloas (Nat.not_le_of_lt preGloas)` for `room`.
  The new statement implies the old one.

- In Lean, `includedVotes_votingSource_ge` holds at every fork and no longer takes `preGloas : fork < .glamsterdam`.
  Migration: a caller drops that argument.
  The new statement implies the old one.

- In Lean, `Store.isAncestor_iff`, `Store.comparable_of_ancestors`, `Store.eq_of_isAncestor_antisymm`, `Store.isAncestor_of_getCheckpointBlock_above` and `Store.isAncestor_of_blockTree_ancestor` hold at every fork and no longer take `before : fork < .glamsterdam`.
  `signerHead_of_duty` and `justified_descends_of_duty` (`ForkChoice/FastConfirmation/DutyWindows.lean`) no longer take `preGloas : fork < .glamsterdam`.
  `Store.ForwardReachableWith.weight_add_weight_add_stake_le_withBoost` and `Store.ForwardReachableWith.weight_add_weight_le_withBoost` no longer take `before : fork < .glamsterdam`.
  Migration: a caller drops that argument.
  The new statements imply the old ones.

- In Lean, `Store.Reachable.realized_le_source` and `Store.getCheckpointBlock_of_shared_origin` hold at every fork and no longer take `before : fork < .glamsterdam`.
  Migration: a caller drops that argument.
  The new statements imply the old ones.

- In Lean, `Store.exists_leaf_above_mem_filterNodeTree` holds at every fork.
  It no longer takes `before : fork < .glamsterdam`; it takes `verified : ∀ gloas : .glamsterdam ≤ fork, store.FullParentsVerified gloas` in its place.
  Migration: before Gloas, pass `fun gloas => absurd gloas (Nat.not_le_of_lt before)`; for a reachable store, pass `fun gloas => reachable.fullParentsVerified absent gloas`.
  The new statement implies the old one.

- In Lean, `Execution.rootHeld_of_honest_vote`, `Execution.justified_comparable_of_checked` and `Execution.latest_eq_of_rank_eq` hold at every fork and no longer take `preGloas : fork < .glamsterdam`.
  From Gloas the rank of a latest vote is its slot.
  Migration: a caller drops that argument.
  The new statements imply the old ones.

- In Lean, `receiver_fullMaximum_of_head_window` holds at every fork.
  It no longer takes `early : fork < .glamsterdam`; it takes `registries : .glamsterdam ≤ fork → HonestRegistriesWithinLimit time` after `ceiling`.
  Migration: before Gloas, pass `fun gloas => absurd gloas (Nat.not_le_of_lt early)`.
  The new statement implies the old one.

- In Lean, `Store.getHead_exists_of_gloas` no longer takes `supply : effectiveBalanceSum state ≤ 2 * 10 ^ 17`.
  It takes `heads : store.HeadWeightAtMost (2 * 10 ^ 17) state` in its place, and derives the active-stake bound from it.
  `Execution.honestHeadsExist_or_evidence_of_gloas` takes `heads : CheckpointHeadWeightCeiling (2 * 10 ^ 17) last` in place of `supply : CheckpointRegistryStakeCeiling (2 * 10 ^ 17) last`.
  Migration: derive `heads` from the old bound with `Store.headWeightAtMost_of_effectiveBalanceSum_le`, pointwise for the ceiling.
  The new statements imply the old ones.

- In Lean, `CheckpointRegistryStakeCeiling` (`ForkChoice/FastConfirmation/HonestHeads.lean`, added earlier in 0.4.0) is removed: after the change of `Execution.honestHeadsExist_or_evidence_of_gloas` it had no reader.
  Migration: state `CheckpointHeadWeightCeiling` instead; a bound on each honest justified state's effective-balance sum implies it, by `Store.headWeightAtMost_of_effectiveBalanceSum_le`.

- In Lean, `Execution.callRolloverRead_or_evidence`, `Execution.honestHeadsCover_of_checked_call` and `Execution.rootViable_of_checked_call` hold at every fork and no longer take `preGloas : fork < .glamsterdam`.
  They take `room`, `weights` and `supply` gated from Gloas as their last arguments, and `Execution.callRolloverRead_or_evidence` also a gated `fit`.
  Their `supply` has the type `CheckpointHeadWeightCeiling (2 * 10 ^ 17) _`, the bound that the Gloas head endpoint now reads.
  Migration: drop `preGloas` and pass `fun gloas => absurd gloas (Nat.not_le_of_lt preGloas)` for each gated argument.
  The new statements imply the old ones.

- In Lean, `Store.checkpointState_justified_of_getHead` holds at every fork.
  It no longer takes `before : fork < .glamsterdam`; it takes `justifiedEarly`, which from Gloas asks that the justified block be older than the previous slot.
  Migration: before Gloas, drop `before` and pass `fun gloas => absurd gloas (Nat.not_le_of_lt before)`.
  The new statement implies the old one.

- In Lean, `Execution.rootViableAt_of_checked` and `Execution.honestHeadsCover_of_viableAt` hold at every fork.
  They no longer take `preGloas : fork < .glamsterdam`; they take `room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon` as their last argument.
  Migration: drop `preGloas` and pass `fun gloas => absurd gloas (Nat.not_le_of_lt preGloas)` as `room`.
  The new statements imply the old ones.

- In Lean, `Execution.honest_vote_of_caller_margin` holds at every fork and no longer takes `preGloas : fork < .glamsterdam`.
  `Execution.source_surplus_or_historical_evidence_with` and `Execution.isAncestor_getHead_of_historical_anchor_with` hold at every fork; they no longer take `preGloas` and take `registries : .glamsterdam ≤ fork → HonestRegistriesWithinLimit time` as their last argument.
  Migration: drop `preGloas`; before Gloas, pass `fun gloas => absurd gloas (Nat.not_le_of_lt preGloas)` as `registries`.
  The new statements imply the old ones.

- In Lean, `ancestor_head_of_window_margin` holds at every fork.
  It no longer takes `before : fork < .glamsterdam`; it takes `registries`, gated from Gloas, as its last argument: every honest justified state read up to `last` has its registry within the limit.
  From Gloas the head walk is cut at the parent's pending node and read with `Store.isAncestor_getHeadFrom_of_sibling_bound`.
  Migration: before Gloas, drop `before` and pass `fun gloas => absurd gloas (Nat.not_le_of_lt before)`; from `HonestRegistriesWithinLimit`, pass its second half.
  The new statement implies the old one.

- In Lean, `Store.isAncestor_head_pending` moves from `EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic` to `EthLib.Consensus.Proofs.ForkChoice.Store`.
  Its name and statement are unchanged.
  Existing imports remain sufficient; for a direct import of the lemma, use `EthLib.Consensus.Proofs.ForkChoice.Store`.

- In Lean, `Store.getNodeChildren_held` moves from `EthLib.Consensus.Proofs.ForkChoice.HeadTotality` to `EthLib.Consensus.Proofs.ForkChoice.Ghost`.
  Its name and statement are unchanged.
  Existing imports remain sufficient; for a direct import of the lemma, use `EthLib.Consensus.Proofs.ForkChoice.Ghost`.

- In Lean, the IPv6 reader of the builder API reads hex digits with the reader of Base, and its own copy is removed ([#3837](https://github.com/ethereum/EthLib/issues/3837)).
  `BuilderApi.hexDigitValue?` is removed, and `BuilderApi.mem_hexGroup` now states that each character of a group has a value under `Base.hexValue?`, a byte.
  Migration: write `Base.hexValue?`, and read its value with `UInt8.toNat`.

- In Lean, the light client checks with the shared assertion of Base, and its own copy is removed ([#3837](https://github.com/ethereum/EthLib/issues/3837)).
  `LightClientError.require` and its lemma `LightClientError.require_ok` are removed.
  Migration: write `Base.ensure` and `Base.ensure_ok_iff`, the same definition and lemma for any error type.

- In Lean, the module `EthLib.Base.Length` is removed, and its declarations move to `EthLib.Networking.Snappy` with the same definitions ([#3836](https://github.com/ethereum/EthLib/issues/3836)).
  They are `hasAtLeast`, `hasAtLeast_iff`, `decideLeLength` and `decideLengthLt`.
  Migration: import `EthLib.Networking.Snappy.Block` and use the new namespace.

- In Lean, three unused pieces of Base are removed ([#3835](https://github.com/ethereum/EthLib/issues/3835)).
  The `LawfulBEq ByteArray` instance of `Base/Bytes.lean` goes, since Lean core gives one.
  The lemma `Base.byteArray_set_eq_set!` goes.
  The module `EthLib.Base.Proofs.Toolchain.OrdString` goes, with its lemma `Base.Toolchain.String.compare_eq`.
  Migration: unfold `ByteArray.set!` where the lemma was used, and use `Std.compare_eq_of_lt_iff` for the order on strings.

- The leanXMSS security proof plays the game whose signer keeps its key, and the proofs no longer write out the note's stateless signer.
  `Proofs/Xmss/Reference.lean` is removed, with `statelessSignWith`, `statelessSign`, `statelessKeyGenWith`, `signDerived`, `signLayer` and `publicKeyOf`.
  The stateless games `statelessGameCore`, `statelessExperiment`, `statelessForgeAdvantage`, `statelessReasonRun` and `statelessSigningFailure` are removed, and so is `forgeAdvantage_eq_statelessForgeAdvantage`.
  `Unforgeability.HasHashQueryBound` counts the calls of `experiment`, the game with the kept key, and `gameCore_eq_realGame` proves that this game is the real game of the proof.
  `unforgeable`, `forgeAdvantage_le_adversaryBudget`, `forgeAdvantage_le_lifetime`, `reasonForgeAdvantage_le`, `reasonForgeAdvantage_le_add`, `signingFailure_le` and `reasonForgeAdvantage_le_bounded` keep their text.
  `Unforgeability.requestQueries` is `2^33 + 205 * 2^16 + 407`, so `lifetimeQueries_eq` is `2^65 + 205 * 2^48 + 407 * 2^32 + 205 * 2^16 + 385`.
  `Xmss.SecretKey.Reachable.signWith_fst` takes `hs` and `hpp`, which name the scheme seed and the parameter, and writes the note's signature out.
  `Xmss.SecretKey.Reachable.sign_fst` is removed: `sign_eq` and `signWith_fst` state what `sign` computes.
  `Xmss.Internal.keyGenFrom` is key generation from the scheme seed, which `keyGenWith` calls after the seed hash.
  `Xmss.SecretKey.Reachable.signWith_eq_ok` replaces `statelessSign_eq_ok`, and `keyGenWith_fst` states the public key as the top tree's root and `P`.
  `Xmss.Internal.signRootWith`, `cacheTreeWith`, `fetchTreeWith` and `signWithTrials` take the derivations `prf`; `signWith` and `sign` pass those of the key's seed and compute the same bytes.
  The helpers of the stateless signer in `Correctness`, `Cost`, `QueryBound`, `MapMonad`, `SignatureFailure` and `Unforgeability` are removed, such as `verifyWith_statelessSignWith`, `prEvent_statelessSignWith_error_le` and `isQueryBoundP_signDerived`.
  `layerRoot_signLayer` becomes `layerRoot_of_otsSign`, and `Cost.isQueryBoundP_signRootWith`, `isQueryBoundP_cacheTreeWith` and `isQueryBoundP_fetchTreeWith` take a bound on the derivations.
  Migration: state a budget on the calls of `experiment`; read a signature's layers from `signWith_eq_ok`.

- In Lean, `Secp256r1.Montgomery` and `Secp256k1.Montgomery` are now abbreviations of `Word64.Montgomery Fp.modulus`, a four-word Montgomery element written once for any modulus ([#3827](https://github.com/ethereum/EthLib/issues/3827)).
  In each curve, the fields `raw` and `lt` and the `DecidableEq` instance are those of `Word64.Montgomery`, so `a.raw` and `a.lt` still read the same.
  Each curve's zero, one, `readRaw`, `montgomerySquare` and `rawOne` move to `Word64.Montgomery`; the one and `montgomerySquare` read the words that the curve's instance of `Word64.Montgomery.Constants` gives.
  Each curve's `ofFin`, `toFin` and `toMont` stay, now as abbreviations of the shared conversions, so `simp` and `unfold` reach the shared definitions through them.
  Every public theorem of both fields keeps its statement.
  A value whose type reads `Word64.Montgomery Fp.modulus` no longer reaches a curve's own functions, such as `square`, by dot notation.
  Migration: write `Word64.Montgomery.readRaw`, `Word64.Montgomery.montgomerySquare` and `Word64.Montgomery.rawOne`, and `Word64.Montgomery.mk` and `Word64.Montgomery.mk.injEq` for the constructor; call a curve's own functions by their full names.

- In Lean, the 64-bit word primitives and the integers of four and five words move from `Secp256k1.Montgomery` to the neutral `Word64` module, which the secp256r1 field shares.
  Each moves from `EthLib.Cryptography.Secp256k1.Montgomery.X` to `EthLib.Cryptography.Word64.X`, with its statement unchanged, for `X` in `wordRadix`, `mulHigh`, `yes`, `Pair`, `mac`, `plus`, `minus`, `plus_spec`, `minus_spec`, `Words64`, `Words64.val`, `lowValue`, `value`, `Raw`, `Raw.fromWords`, `Raw.words`, `Raw.val`, `Raw.val_eq`, `Raw.fromWords_val`, `rawOfNat`, `rawToNat` and `rawToNat_eq`.
  The proof helpers `join`, `wide` and `narrow` move the same way, from `Proofs/Secp256k1/Montgomery.lean` to `Proofs/Word64.lean`.
  Inside `Secp256k1.Montgomery`, an `export` keeps the short names `wordRadix`, `mulHigh`, `yes`, `Pair`, `mac`, `plus`, `minus`, `plus_spec`, `minus_spec`, `Words64`, `lowValue`, `value`, `Raw`, `rawOfNat`, `rawToNat` and `rawToNat_eq`.
  Migration: write the new full names, or `open EthLib.Cryptography.Word64` for the members of `Raw` and `Words64`.

- In Lean, the secp256r1 `Fp`, `Fn`, `Fp.modulus`, `Fn.modulus`, `Fp.inv`, `Fn.inv` and their `NeZero` instances move from `Secp256r1/Curve.lean` to `Secp256r1/Field.lean`, with unchanged full names.
  `Secp256r1.Curve` no longer publicly imports `Secp256k1.Field`.
  Migration: import `Secp256k1.Field` directly where it is needed.

- In Lean, `Store.isAncestor_getHead_of_duty_support` holds at every fork.
  It no longer takes `before : fork < .glamsterdam`; it takes `early : .glamsterdam ≤ fork → ∃ current, store.getCurrentSlot config = .ok current ∧ block.slot < current` after `known`.
  Migration: before Gloas, drop `before` and pass `fun gloas => absurd gloas (Nat.not_le_of_lt before)` for `early`.
  The new statement implies the old one.

- In Lean, `rootFinal_or_justified_covers` holds at every fork and no longer takes `preGloas : fork < .glamsterdam`.
  Migration: a caller drops that argument.
  The new statement implies the old one.

- In Lean, `Execution.isAncestor_getHead_of_duty_epoch` and `Execution.isAncestor_getHead_of_duty_epoch_or_accountable` hold at every fork.
  They no longer take `preGloas : fork < .glamsterdam`; they take `room : .glamsterdam ≤ fork → AnchorRegistryRoom preset anchorState horizon` after `inHorizon`.
  Migration: before Gloas, drop `preGloas` and pass `fun gloas => absurd gloas (Nat.not_le_of_lt preGloas)` for `room`.
  The new statements imply the old ones.

- In Lean, `Store.voteCountsFor_eq_false_of_slot_eq_current` is removed.
  Migration: use `Store.VotesHaveOrigins.slot_lt_of_voteCountsFor` with `forward.votesHaveOrigins`, which gives `block.slot < current` for a counted vote.

- In Lean, `HeldRegistriesWithinLimit` moves from `EthLib.Consensus.Proofs.ForkChoice.HeadTotality` to `EthLib.Consensus.Proofs.ForkChoice.BlockRuns`.
  Its name and statement are unchanged.
  Existing imports remain sufficient; for a direct import of the definition, use `EthLib.Consensus.Proofs.ForkChoice.BlockRuns`.

- In Lean, `VoteAt.recorded_at_next_slot` holds at every fork.
  It no longer takes `preGloas : fork < .glamsterdam`; it takes `anchorSlot : .glamsterdam ≤ fork → anchorBlock.slot ≤ anchorState.slot` after `sync`, and concludes `(LatestMessage.ofAttestation attestation).rank ≤ message.rank`.
  Migration: before Gloas, pass `fun gloas => absurd gloas (Nat.not_le_of_lt preGloas)` for `anchorSlot`, and read the rank as the target epoch through `LatestMessage.ofAttestation_rank_of_lt`.

- In Lean, `Execution.latest_rank_of_voteAt` holds at every fork, no longer takes `preGloas : fork < .glamsterdam`, and concludes `(LatestMessage.ofAttestation attestation).rank ≤ message.rank`.
  Migration: a caller drops that argument, and before Gloas reads the rank as the target epoch through `LatestMessage.ofAttestation_rank_of_lt`.

- In Lean, `Execution.mem_supportersOf_of_latest_signed`, `Execution.mem_supportersOf_of_duty_interval_core`, `Execution.mem_supportersOf_of_duty_epoch` and `Execution.mem_supportersOf_of_duty_epoch_or_accountable` hold at every fork and no longer take `preGloas : fork < .glamsterdam`.
  Migration: a caller drops that argument.
  The new statements imply the old ones.

- In Lean, `Store.isAncestor_trans_of_lt` is renamed `Store.isAncestor_trans` and holds at every fork.
  It no longer takes `before : fork < .glamsterdam`.
  Migration: a caller takes the new name and drops that argument.
  The new statement implies the old one.

- In Lean, `Store.getCheckpointBlock_of_isAncestor`, `Store.getCheckpointBlock_of_ancestor_epoch`, `Store.isAncestor_of_same_blocks` and `Store.isAncestor_of_parent` hold at every fork and no longer take `before : fork < .glamsterdam`.
  Migration: a caller drops that argument.
  The new statements imply the old ones.

- In Lean, `Store.getAncestor_of_isAncestor` moves from `EthLib.Consensus.Proofs.ForkChoice.CommitteeAgreement` to `EthLib.Consensus.Proofs.ForkChoice.Store`.
  Its name and statement are unchanged.
  Existing imports remain sufficient; for a direct import of the lemma, use `EthLib.Consensus.Proofs.ForkChoice.Store`.

- In Lean, the eth messages Transactions, BlockHeaders and PooledTransactions keep each transaction and header as `Rlp.Encoded`: its item, and the bytes it was read from ([#3766](https://github.com/ethereum/EthLib/issues/3766)).
  The wire hash, the hash of a header, the PooledTransactions check, the BlockHeaders check and the session read those bytes, so they never run the recursive RLP encoder on what a peer sent.
  `Message.ofItem` takes the bytes of the item as a last argument, and the new `Message.kept_of_decode` states that each kept slice is the encoding of its item.
  `wireHash`, `headerHash` and `Message.transactionHashes` no longer fail, so `PoolError.rlp` (code 301) and `EthSessionError.transaction` (code 705) are removed; the codes stay unused.
  Migration: build an `Rlp.Encoded` from an item and its encoding; `checkPooled_eq_ok_iff`, `receiveEth_receivedTxs` and `run_no_resend` state the hashes as `txs.map wireHash`.
  `ofItem_toItem` takes the bytes and asks that each kept slice encode its item; `ofItem_eq_ok_iff` asks that the bytes encode the item, and concludes that each kept slice encodes its own.
  `checkHeaders`, `followsIn`, `followAll` and `isStart` take `Rlp.Encoded` headers, and `followsIn_eq_ok_iff` and `headerParent_of_checkHeaders` state the parent hash as an equation instead of `∃ p`.
  `ofItem_blockRangeUpdate_eth68`, `ofItem_unequalLengths` and `messageCount_le_iff_unknownId` take the bytes too, and `answers_of_requestId`, `sublist_of_checkPooled` and `numbers_of_checkHeaders` take the new types.
  New: `Rlp.listEncodings`, `Rlp.splitItems`, `Rlp.Encoded.zip`, `Message.payloadEncodings`, `Message.kept`, `Message.Kept`, and the theorems `listEncodings_of_encode`, `Encoded.zip_eq_ok_iff`, `zip_listEncodings_eq_ok_iff` and `wireHash_networkForm`.

- In Lean, the check of a block body, the checks of block access lists in eth and snap, and the sizes of partial receipts read the bytes each item was read from ([#3826](https://github.com/ethereum/EthLib/issues/3826)).
  So none of them runs the recursive RLP encoder on what a peer sent.
  `checkBody`, `checkTransactions`, `checkOmmers`, `transactionValues` and `transactionBytes` take `Rlp.Encoded` items; `checkGasLimits` and `checkWithdrawals` still take items.
  `Message.blockAccessLists` and `SnapMessage.blockAccessLists` hold `Rlp.Encoded` access lists, and `accessListsAnswer` takes them.
  `SnapMessage.ofItem` takes the bytes of the item as a last argument, as `Message.ofItem` does.
  `Message.payloadEncodings` moves to `Rlp.payloadEncodings`, with the same definition.
  Migration: build an `Rlp.Encoded` from an item and its encoding.
  The body theorems that compare or complete bodies ask that each body keep its own encoding: `checkBody_binding`, `checkTransactions_binding`, `checkOmmers_binding`, `transactionValues_injective` and `transactionBytes_injective`.
  `checkBody_complete` states the check for every encoding of the body, `checkOmmers_hash` states the hash of the kept bytes, and `TransactionsBound` and `OmmersBound` take `Rlp.Encoded`.
  `accessListsAnswer_eq_true_iff`, `of_accessListsAnswer` and `accessListsResponse_eq_true_iff` state the hash of the kept bytes; `Message.kept_of_decode` and the new `SnapMessage.kept_of_decode` state that those bytes are the encoding.
  The other body theorems take `Rlp.Encoded` items: `checkOmmers_tooMany`, `checkOmmers_nil`, `checkOmmers_of_valid` (which drops its encoding hypothesis), `checkBody_eq_ok`, `checkBody_gasLimit_le`, `checkTransactions_eq_ok_iff`, `transactionBytes_bytes`, `transactionBytes_bodyItem` and `mapM_transactionBytes`.
  `checkBody_unexpectedWithdrawals`, `checkBody_missingWithdrawals`, `checkBody_tooManyOmmers` and `checkBody_tooManyOmmers_shapella` ask that the body bytes encode the body.
  `Message.kept` and `Message.Kept` now cover access lists, so `Message.ofItem_toItem` and `Message.ofItem_eq_ok_iff` speak of them too.
  The snap theorems `ofItem_toItem`, `ofItem_eq_ok_iff`, `ofItem_snap2_trieNodes`, `ofItem_snap1_accessLists` and `messageCount_le_iff_unknownId` take the bytes, as the eth ones do.
  New: `Rlp.Encoded.parts`, `SnapMessage.kept`, `SnapMessage.Kept`, `receiptSizes`, and the theorems `Encoded.parts_eq_ok_iff`, `Encoded.item_of_parts`, `Encoded.parts_of_encode`, `payloadEncodings_of_encode`, `transactionBytes_list` and `receiptSizes_eq_ok_iff`.

- In Lean, the SHA-256 sizes name their unit: `Sha256.BLOCK_SIZE` is now `Sha256.BLOCK_SIZE_BYTES`, and `Sha256.LENGTH_SIZE` is now `Sha256.LENGTH_SIZE_BYTES`.
  The new `Sha256.DIGEST_SIZE_BYTES` is the 32-byte digest size of FIPS 180-4 §1.
  `HASH_LEN` of HKDF, PBKDF2 and Concat KDF, and `OUTPUT_BYTES` of the SHA-256 precompile, are defined as that size.
  Their values are unchanged.
  The hash to `G2` reads that size for `b_in_bytes`.
  A proof that unfolds one of them to the literal 32 also unfolds `Sha256.DIGEST_SIZE_BYTES`.
  `HashToCurve.sha256BlockSize` and `HashToCurve.sha256OutputSize` are removed; a caller uses `Sha256.BLOCK_SIZE_BYTES` and `Sha256.DIGEST_SIZE_BYTES`.

- In Lean, `HashToCurve.fp2` is now `Bls.Fp2.ofNats`, and its lemma `map_fp2` is now `map_ofNats`.
  `G2.generator`, `G2.bTwist` and `HashToCurve.Bprime` are written with it, with the same values.
  A proof that unfolds one of them to its two coordinates also unfolds `Fp2.ofNats`.

- In Lean, the step of a call builds its calling frame with the new `Evm.callerFrame` and its message with the new `Evm.callMessage`.
  `genericCall` no longer empties the return data, since `callerFrame` does; the step computes what it computed before.
  `callStep_child_of_routes`, `callStep_child`, `callStep_call`, `callStep_staticcall` and `callStep_value` state one equation on these two values instead of 23 conjuncts.
  A caller reads one field with a lemma such as `gas_callMessage` or `memory_callerFrame`; each closes by `rfl`.

- In Lean, `vectorSlices_eq` and `listSlices_eq` are removed ([#3747](https://github.com/ethereum/EthLib/pull/3747)), because they restated the whole body of the SSZ slicers.
  A caller unfolds `vectorSlices` or `listSlices`; on the offset-table path it also rewrites with the new `zipWith_extract_eq`, which turns the final `zipWith` into a map over the zipped offsets and spans.

- In Lean, `Valid.transactionReceipt_blockReceipts` takes the block that the lookup returns, and no longer asks that it be canonical.
  The lookup reads only canonical blocks, so the hypotheses `i < v.canonical.length` and the block `v.canonical[i]` are gone; a caller passes the lookup's result as is.

- In Lean, the Snappy preamble reader takes the value of the shared varint reader, and keeps no loop of its own.
  `Snappy.readPreambleAux` and `Snappy.continuation` are removed, with the lemmas `readPreambleAux_encodeAux` and `readPreambleAux_take`.
  A caller reads the preamble with `Snappy.readPreamble`, and the constant `128` with `Encoding.Varint.continuation`.
  The statements of `readPreamble_encode`, `readPreamble_le` and `readPreamble_take` are unchanged.

- In Lean, the abbreviated helpers of the pin reserve bound in `EthLib.Consensus.Models.Network.PinDrift.Internal` take descriptive names ([#2770](https://github.com/ethereum/EthLib/pull/2770) added them).
  Migration for the definitions: `AC` → `countedActiveVoters`, `AR` → `pulledActiveVoters`, `Q` → `countedQuorum`, `U` → `costKeys`, `eC` → `countedBalance`, `eR` → `pulledBalance`, `cV1` → `voterFallCost`, `cV2` → `inactiveVoterCost`, `cN` → `stayingRiseCost`, `cP` → `previousOnlyCost`, `cJ` → `joinedCost`, `cK7` → `outsideQuorumCost`, `cS` → `departedCost`, `VN` → `countedInactiveVoters`, `K4` → `stayingKeys`, `K5` → `previousOnlyKeys`, `K6` → `joinedKeys`, `SC` → `newlySlashed`, `CS` → `createdSlashed`, `sc3a` → `activeNewlySlashed`, `scCharged` → `chargedNewlySlashed`, `scSlashedReward` → `newlySlashedWhistleReward`.
  Migration for the lemmas named after them: `K5_charged` → `previousOnlyKeys_charged`, `K5_exiting_of_not_charged` → `previousOnlyKeys_exiting_of_not_charged`, `K5_previous_only` → `previousOnlyKeys_previous_only`, `K5_unslashed` → `previousOnlyKeys_unslashed`, `K6_class` → `joinedKeys_class`, `cJ_le` → `joinedCost_le`, `cN_le` → `stayingRiseCost_le`, `cP_le` → `previousOnlyCost_le`, `card_K5_le` → `card_previousOnlyKeys_le`, `charge_epoch_le_of_K5` → `charge_epoch_le_of_previousOnlyKeys`, `classes_mem_Q` → `classes_mem_countedQuorum`, `cs_disjoint` → `createdSlashed_disjoint`, `sc3a_unwithdrawn` → `activeNewlySlashed_unwithdrawn`, `sc_3a_split` → `newlySlashed_active_split`, `sc_disjoint` → `newlySlashed_disjoint`, `sum_eq_U` → `sum_eq_costKeys`.
  Migration for the budget lemmas: `bud_branchR` → `budget_branchR`, `bud_capSlots` → `budget_capSlots`, `bud_consolidations` → `budget_consolidations`, `bud_consolidations_base` → `budget_consolidations_base`, `bud_credits` → `budget_credits`, `bud_csUnits` → `budget_csUnits`, `bud_deposits` → `budget_deposits`, `bud_exitedR` → `budget_exitedR`, `bud_exiting` → `budget_exiting`, `bud_exitingBands` → `budget_exitingBands`, `bud_exitingCredits` → `budget_exitingCredits`, `bud_exitingRise` → `budget_exitingRise`, `bud_fall` → `budget_fall`, `bud_joinRise` → `budget_joinRise`, `bud_joining` → `budget_joining`, `bud_late` → `budget_late`, `bud_pendingR` → `budget_pendingR`, `bud_queueRise` → `budget_queueRise`, `bud_queues` → `budget_queues`, `bud_rise` → `budget_rise`, `bud_sync` → `budget_sync`, `bud_syncLeak` → `budget_syncLeak`, `bud_units` → `budget_units`, `bud_whistle_of` → `budget_whistle_of`.
  No statement changes.

- In Lean, the point evaluation precompile reads `[tau]_2` and the blob size from the KZG module, and keeps no copy of either.
  `Evm.Precompiles.PointEvaluation.KZG_SETUP_G2_MONOMIAL_1`, the 96 bytes of `[tau]_2`, is removed.
  The precompile decodes `G2` point 1 of the embedded setup with the new `Kzg.TrustedSetup.g2MonomialOfHex`, and fails with `invalidTrustedSetup` as before.
  `Evm.Precompiles.PointEvaluation.FIELD_ELEMENTS_PER_BLOB` is removed, and `Kzg.Constants.FIELD_ELEMENTS_PER_BLOB` has the same value, 4096.
  `Evm.Precompiles.PointEvaluation.uncompress_KZG_SETUP_G2_MONOMIAL_1` is removed.
  The new `Kzg.TrustedSetup.g2MonomialOfHex_eq` states, for every position, that a point decoded alone is that point of the decoded setup, when the setup decodes.
  Migration: a proof that used the removed theorem uses `Kzg.TrustedSetup.g2MonomialOfHex_eq h 1 (by decide)`.

- In Lean, `DirectSafety.Apriori.Internal.ScoresBelow.step` no longer takes the hypothesis `inside : n ≤ m.state.validators.data.size`.
  Its proof does not read it.
  Migration: a caller drops that argument.
  The new statement implies the old one, so a caller that proved the hypothesis only for this call can drop its proof.

- In Lean, `pinReserve` has a new body: it bounds drifts that the reserve of #2713 missed or under-read ([#2770](https://github.com/ethereum/EthLib/pull/2770)).
  `JustifiedPinned`, `ReservedTargetVotes`, `CallCheckpointInputs` and `CallObligations` read it in a premise.
  Migration: a caller that proved `total + (margin + pinReserve config state anc fin) < 3 * stake` for the old reserve must prove it for the new one.
  `quorumReserve_le_pinReserve` keeps its statement.

- In Lean, the `withdrawal` field of `EthLib.Consensus.Internal.CapStep` is stronger.
  For a slashed validator with an assigned exit, it now says that `withdrawableEpoch` is equal after the step.
  It said that the epoch does not fall.
  Migration: constructors of `CapStep` must now prove `withdrawableEpoch` is unchanged after slashing.
  The new field implies the old one, so a reader of the old field reads the new one through `le_of_eq`.
  `CapStep.refl`, `CapStep.trans` and `CapStep.data` carry the new field, and the readers in this repository keep their statements (`Internal.CapStep.run` changes above).

- In Lean, the result of `Store.Reachable.finalizedState_of_blockState` is stronger.
  After the anchor epoch, it also says that the store reads the finalized block of the state from the state's own block.
  That read is `store.getCheckpointBlock root anc.finalizedCheckpoint.epoch = .ok anc.finalizedCheckpoint.root`.
  Migration: a caller that destructures the result as `⟨fin, finRead, finAnchor⟩` adds a component, as `⟨fin, finRead, finAnchor, -⟩`.
  The new statement implies the old one, so a reader of the old statement drops the last conjunct.
  The four callers in this repository, two in `CheckpointConsistency` and two in `RootViability`, do that.

- The snap AccountRange message reads and writes each account body as the slim account list nested in its entry, the encoding used on the network ([#3491](https://github.com/ethereum/EthLib/issues/3491)).
  `caps/snap.md` types the body `B`, and a byte string that holds the list is now no account body.
  In Lean, `RangeEntry` takes the type of its data: an account entry is `RangeEntry Item`, and a slot entry `RangeEntry ByteArray`.
  `fullAccount` takes the item of the body, and `fullAccount_slimAccount` replaces `fullAccount_encode_slimAccount`.
  `AccountRangeWitness` loses its `slim` and `encode_slim` fields, since the entry carries the slim form itself.
  In Python, `decode_message` reads the nested form, and still reads a message whose body is a byte string.
  `full_account` and `verify_account_range` still take the RLP encoding of each body, and refuse a byte string as before.

- In Lean, `DirectSafety.Apriori.creditBudget` counts each active key's balance only up to its cap (part of [#2707](https://github.com/ethereum/EthLib/issues/2707)).
  The new `initialCappedExcess` sums, over the keys active at the reference state, the balance capped at `withdrawalMaxEffectiveBalance` minus the effective balance.
  `creditBudget` reads it in place of `initialExcess`.
  `initialExcess` is unchanged.
  `creditBudget`, `gainBudget` and `drift` are each at most their former value, so `accountable_safety_apriori` keeps its statement and implies the former one.
  `Apriori.Internal.potential` moves from `Apriori/Ownership.lean` to `Apriori/Bound.lean`, where `initialCappedExcess` reads it; its name and value are unchanged.
  In `Apriori.Internal`, pot 0 of `initialPot` is `potential x i - effectiveAt x i` for a key active at `x`, and `OwnedInitial` bounds its tokens with `initialCappedExcess`.
  The `NewReference` clause of `ReserveCut` bounds `potential u i` in place of `max (effectiveAt u i) (actualBalanceAt u i)`.
  The former clause implies the new one; a caller that read the balance from it reads `potential` instead.

- In Lean, `processInactivityUpdates_frame` moves from `EthLib.Consensus.Proofs.Transition.EpochParticipation` to `EthLib.Consensus.Proofs.Transition.EpochUpdates`, next to the other frame facts of the epoch steps.
  Its name and statement are unchanged; a caller that imports only the former adds `import EthLib.Consensus.Proofs.Transition.EpochUpdates`.

- In Lean, the light client signature theorems assume soundness only on the one aggregate call of the update ([#3432](https://github.com/ethereum/EthLib/issues/3432)).
  `validateLightClientUpdate_signed` and `validateLightClientUpdate_signed_outside` take `SignatureChecks.AggregateSoundOn` on `updateSignatureCall` in place of `SignatureChecks.AggregateSound`.
  The new hypothesis is weaker, so the theorems are stronger; a caller with `sound : checks.AggregateSound signed` passes `sound.on _` (`SignatureChecks.AggregateSound.on`).

- In Lean, `payloadInputs_processOperations` holds at every fork and no longer takes `gloas : .glamsterdam ≤ fork`.
  Before Gloas the deposits and, from Electra, the requests of the execution layer keep the inputs of a payload too.
  A caller drops the first explicit argument.

- In Lean, signed direct safety catches collisions of signing roots ([#3430](https://github.com/ethereum/EthLib/issues/3430)).
  `SignedIn` takes the signed root, and `SignedConflict` asks that the two roots differ, so one signature never counts as two.
  `signedConflict_of_accountable`, `accountableKeys_subset_signedConflictKeys`, `accountable_safety_signed` and `accountable_safety_signed_third` add the alternative `SigningEvidence`: SHA-256 collides among the messages of the signing roots that the checks of the runs compute.
  `AttestationCheck.signedIn` and `HeaderCheck.signedIn` also give the domain and root of the check, and its place among the signings of the run.
  The signing-value lemmas `wellFormed_signingShape_iff`, `fits_signingValue_iff`, `commitmentSized_signingValue_iff` and `signingValue_inj` move to `Consensus/Proofs/Signing.lean`, where they are public, with `signingValues_of_computeSigningRoot_eq`, `signingMessages` and `computeSigningRoot_ne_or_collision`.
  `valueMessages` (`Serialization/Proofs/Ssz/Codec/ValueMessages.lean`) names the messages of the tree of a value, which the hash objects of direct safety read too.

- In Lean, a signature of signed direct safety names the version of a fork of the config ([#3430](https://github.com/ethereum/EthLib/issues/3430)).
  `SignedIn` takes the version of its domain, and `SignedConflict` asks for the version of a fork of the config, the same for both headers.
  `AttestationCheck.signedIn` and `HeaderCheck.signedIn` name the version that the state before the block reads.
  `Run.forkVersions_ofConfig` shows that every state of a run from a genesis of deposits holds versions of forks of the config.
  `chainStep_forkVersions` and `chainSteps_forkVersions` move from the Beacon API proofs to `Consensus/Proofs/Transition/ForkVersions.lean`, where they are public.
  `signedConflict_of_accountable`, `accountable_safety_signed` and their corollaries keep their hypotheses and conclude this stronger form.

- The light client checks of req/resp responses compare fork digests, not forks ([#2642](https://github.com/ethereum/EthLib/issues/2642)).
  From Fulu, a change of blob parameters changes the digest within one fork, and a fork no longer tells those epochs apart.
  In Python, `reqresp_is_valid_response` takes a new argument `genesis_validators_root`, which the light client protocols need.
  An item of `ResponseLightClientUpdate` or `ResponseLightClientBootstrap` now ends with the 4-byte digest of its chunk in place of the name of a fork.
  In Lean, the update and bootstrap checks take the root of the genesis validators, and their items carry a digest field in place of a fork field.
  `lightClientForkMatches` and `ResponseUpdate.forkMatches` become `lightClientDigestMatches` and `ResponseUpdate.digestMatches`.
  `ResponseUpdate.ofUpdate` and `ResponseBootstrap.ofBootstrap` take the digest.

- In Lean, requests by range share one range predicate, `InCountRange`, and the light client updates limit is `lightClientUpdatesLimit` ([#2642](https://github.com/ethereum/EthLib/issues/2642)).
  `slotInRange`, `slotInRange_iff`, `BeaconApi.InRange` and `BeaconApi.updatesLimit` are removed; a caller writes `decide (InCountRange start count value)`, `InCountRange` or `lightClientUpdatesLimit`.

- In Lean, eight more laws move from the step laws to the base laws, with the same conclusions and a weaker laws premise.
  Each takes `EpochBaseLaws R` in place of `EpochStepLaws R`, which provides it.
  `EpochStepLaws.processVoluntaryExit`, `EpochStepLaws.processBlsToExecutionChange`, `EpochStepLaws.applySyncReward`, `EpochStepLaws.processSyncAggregate`, `EpochStepLaws.processHistoricalRootsUpdate`, `EpochStepLaws.processParticipationRecordUpdates`, `EpochStepLaws.processSyncCommitteeUpdates` and `EpochStepLaws.processPtcWindow` are renamed `EpochBaseLaws.processVoluntaryExit`, `EpochBaseLaws.processBlsToExecutionChange`, `EpochBaseLaws.applySyncReward`, `EpochBaseLaws.processSyncAggregate`, `EpochBaseLaws.processHistoricalRootsUpdate`, `EpochBaseLaws.processParticipationRecordUpdates`, `EpochBaseLaws.processSyncCommitteeUpdates` and `EpochBaseLaws.processPtcWindow`.
  A call `laws.X` through dot notation is unchanged; a call by the full name takes the new name and `laws.toEpochBaseLaws`.
  `payloadInputs_processVoluntaryExit`, `payloadInputs_processBlsToExecutionChange` and `payloadInputs_processSyncAggregate` are removed; a caller writes `payloadInputsLaws.processVoluntaryExit`, `payloadInputsLaws.processBlsToExecutionChange` or `payloadInputsLaws.processSyncAggregate`.
  `randaoMixes_slot_processHistoricalRootsUpdate` is removed; a caller with `h` writes `⟨(payloadInputsLaws.processHistoricalRootsUpdate h).randaoMixes, (payloadInputsLaws.processHistoricalRootsUpdate h).slot⟩`.
  That replacement needs `import EthLib.Consensus.Proofs.Transition.PayloadInputs`, which `Committees` does not import.

- In Lean, an XMSS secret key holds the trees it signs with, and signing returns the updated key ([#3404](https://github.com/ethereum/EthLib/pull/3404)).
  `Xmss.SecretKey` keeps the scheme seed, the public parameter, the top tree and up to `Xmss.MAX_CACHED_BOTTOM_TREES = 4` bottom trees, each with the top signature of its root.
  `Xmss.keyGen seed` returns the public key first, then the secret key, and the secret key keeps the top tree that key generation builds.
  `Xmss.sign sk idx m` returns the signature with the updated key; in a kept bottom tree it makes one one-time signature and never rebuilds a tree.
  The stateless signer of the note moves to the proofs as `Xmss.statelessSignWith`, with `signDerived`, `signLayer` and `publicKeyOf`; nothing exports it.
  `Xmss.SecretKey.Reachable.sign_fst` proves that every key that key generation and any sequence of signatures reach signs as the stateless signer, byte for byte.
  `Xmss.verify_keyGen_sign`, `Xmss.verifyWith_keyGenWith_signWith` and `Xmss.sign_error` take `sk.Reachable` in place of the key pair of `keyGen`; `Xmss.signatureIndex_sign` reads `(sign sk idx m).1`.
  `Xmss.prEvent_signWith_error_le` and `..._empty` take `hkept`: a bottom tree of the index that the key keeps holds a top signature.
  `Xmss.Cost.isQueryBoundP_signWith` and `Xmss.Cost.signCalls_eq` bound signing by `8603369879` calls; `isQueryBoundP_signWith_of_mem` and `signKeptCalls_eq` give `4294967500` in a kept tree.
  The old statements hold for the stateless signer, under new names: `Xmss.signWith_run`, `sign_eq_ok`, `sign_error`, `prEvent_signWith_error_le` and `..._empty` become `statelessSignWith_run`, `statelessSign_eq_ok`, `statelessSign_error`, `prEvent_statelessSignWith_error_le` and `..._empty`.
  `Xmss.Cost.isQueryBoundP_signWith` of the old signer becomes `Xmss.Cost.isQueryBoundP_statelessSignWith`, and `Unforgeability.isQueryBoundP_keyGenWith` and `isQueryBoundP_signWith` become `isQueryBoundP_statelessKeyGenWith` and `isQueryBoundP_statelessSignWith`.
  `Xmss.Cost.isQueryBoundP_keyGenWith` keeps its name and its bound over the new key generation.
  `Xmss.bottomTree_lt` moves from `Proofs/Xmss/Correctness.lean` to `Proofs/Xmss/Sign.lean`.
  The unforgeability game's signer keeps its key across requests, and `Unforgeability.HasHashQueryBound` counts the calls of the same game with the stateless signer, `statelessExperiment`.
  `Unforgeability.unforgeable`, `forgeAdvantage_le_adversaryBudget`, `forgeAdvantage_le_lifetime`, `reasonForgeAdvantage_le`, `reasonForgeAdvantage_le_add`, `signingFailure_le` and `reasonForgeAdvantage_le_bounded` keep their text over the new game.
  Their old games are named `statelessGameCore`, `statelessExperiment`, `statelessForgeAdvantage`, `statelessReasonRun` and `statelessSigningFailure`, and `forgeAdvantage_eq_statelessForgeAdvantage` proves that both games win equally often.
  The Python API is unchanged: `xmss.key_gen`, `xmss.sign`, `xmss.verify` and `xmss.signature_index` take and return the same values.
  The extension keeps the secret keys of the last 2 seeds, so a signature in a kept bottom tree no longer rebuilds two trees.
  The export `eth_xmss_key_gen` also returns the secret key, and `eth_xmss_sign` takes the secret key and returns the updated key with the result.

- In Lean, `Execution.payloadVerified_of_partiallySynchronous` asks less of the receiver ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  Its premise `closed` now asks only that the receiver's store marks the block root of each envelope it accepts from its view as verified.
  It no longer asks that the envelope leaves the store unchanged.
  The old premise fails when a second valid envelope for a held root replaces the stored message, which the abstract execution engine allows.
  A caller with the old premise `old` passes `fun s a m h => old s a m h ▸ Store.onExecutionPayloadEnvelope_verified h`.

- In Lean, `SphincsSecurity.Security.flatMap_ofFn_injective` is removed.
  `EthLib.Base.flatMap_inj_of_length` states the same fact for any list, and `List.ofFn_injective` gives it for `List.ofFn`.
  The SPHINCS+ and XMSS proofs now use it.

- In Lean, 22 laws of the epoch steps move to the base laws, and three to the frame base laws.
  `EpochStepLaws.foldlM`, `EpochStepLaws.setValidator`, `EpochStepLaws.setValidator_of_sameBalance`, `EpochStepLaws.setValidatorAt_of_sameBalance`, `EpochStepLaws.applyDeltas`, `EpochStepLaws.applyAllDeltas`, `EpochStepLaws.processRewardsAndPenalties`, `EpochStepLaws.updateRegistryEntry`, `EpochStepLaws.activateValidator`, `EpochStepLaws.updateRegistryEntryElectra`, `EpochStepLaws.processRegistryUpdates`, `EpochStepLaws.applySlashingPenalty`, `EpochStepLaws.applySlashingPenaltyElectra`, `EpochStepLaws.processSlashings`, `EpochStepLaws.processEth1DataReset`, `EpochStepLaws.updateEffectiveBalance`, `EpochStepLaws.processEffectiveBalanceUpdates`, `EpochStepLaws.processSlashingsReset`, `EpochStepLaws.processInactivityUpdates`, `EpochStepLaws.passPendingConsolidations`, `EpochStepLaws.processPendingConsolidations` and `EpochStepLaws.processHistoricalSummariesUpdate` are renamed `EpochBaseLaws.foldlM`, `EpochBaseLaws.setValidator`, `EpochBaseLaws.setValidator_of_sameBalance`, `EpochBaseLaws.setValidatorAt_of_sameBalance`, `EpochBaseLaws.applyDeltas`, `EpochBaseLaws.applyAllDeltas`, `EpochBaseLaws.processRewardsAndPenalties`, `EpochBaseLaws.updateRegistryEntry`, `EpochBaseLaws.activateValidator`, `EpochBaseLaws.updateRegistryEntryElectra`, `EpochBaseLaws.processRegistryUpdates`, `EpochBaseLaws.applySlashingPenalty`, `EpochBaseLaws.applySlashingPenaltyElectra`, `EpochBaseLaws.processSlashings`, `EpochBaseLaws.processEth1DataReset`, `EpochBaseLaws.updateEffectiveBalance`, `EpochBaseLaws.processEffectiveBalanceUpdates`, `EpochBaseLaws.processSlashingsReset`, `EpochBaseLaws.processInactivityUpdates`, `EpochBaseLaws.passPendingConsolidations`, `EpochBaseLaws.processPendingConsolidations` and `EpochBaseLaws.processHistoricalSummariesUpdate`, and each takes `EpochBaseLaws`.
  `EpochFrameLaws.applyPendingDeposit`, `EpochFrameLaws.passPendingDeposits` and `EpochFrameLaws.processPendingDeposits` are renamed `EpochFrameBaseLaws.applyPendingDeposit`, `EpochFrameBaseLaws.passPendingDeposits` and `EpochFrameBaseLaws.processPendingDeposits`, and each takes `EpochFrameBaseLaws`.
  A call `laws.X` through dot notation is unchanged; a call by the full name takes the new name and `laws.toEpochBaseLaws` or `laws.toEpochFrameBaseLaws`.
  `EpochStepLaws.mk` now takes the base laws and its two own laws, not the former flat positional arguments.
  `EpochFrameLaws.mk` takes the step laws and the two laws of the frame.
  An instance written with named fields, as a `where` literal, is unchanged.
  One built with `⟨…⟩` or `.mk` and positional arguments switches to a `where` literal.

- In Lean, six lemmas about `PayloadInputs` are removed in favour of `payloadInputsLaws`.
  A caller of `payloadInputs_processInactivityUpdates`, `payloadInputs_processRegistryUpdates`, `payloadInputs_passPendingDeposits`, `payloadInputs_passPendingConsolidations`, `payloadInputs_processHistoricalSummariesUpdate` or `payloadInputs_applyPendingDeposit` calls `payloadInputsLaws.X`, where `X` is the name after `payloadInputs_`.

- In Lean, five lemmas in `Committees` that state that a step of an epoch keeps the RANDAO mixes and the slot are removed.
  A caller of `randaoMixes_slot_processRewardsAndPenalties`, `randaoMixes_slot_processSlashings`, `randaoMixes_slot_processEth1DataReset` or `randaoMixes_slot_processEffectiveBalanceUpdates` reads `(payloadInputsLaws.X h).randaoMixes` and `.slot`, where `X` is the name after `randaoMixes_slot_`.
  Those four replacements need `import EthLib.Consensus.Proofs.Transition.PayloadInputs`, which `Committees` does not import.
  A caller passing `(hegota := …)` to the reset of the deposit votes passes `(before := …)`.
  A caller of `randaoMixes_slot_processJustificationAndFinalization` reads `⟨by rw [processJustificationAndFinalization_eq h], processJustificationAndFinalization_slot h⟩`, whose lemmas `Committees` already imports.

- In Lean, `payloadInputs_processDeposit` holds at every fork before Heze and no longer takes `electra : .pectra ≤ fork`.
  A caller drops that argument.

- In Lean, `Bls.Fr.fromBytesBE` takes its 32 bytes as a `Vector UInt8 32` (part of [#2189](https://github.com/ethereum/EthLib/issues/2189)).
  It still rejects an integer of at least `r`, with `nonCanonicalFieldElement`.
  `Kzg.bytesToBlsField` and the point evaluation precompile pass their `Bytes32` directly.
  `Signatures.SecretKey.fromBytes` keeps its `ByteArray`, and reads 32 bytes of it with `exactBytes?`.
  `Bls.Fr.fromBytesBE_toBytesBE` decodes the vector `⟨a.toBytesBE.data, Fr.size_data_toBytesBE a⟩`, where the new `Bls.Fr.size_data_toBytesBE` states that `a.toBytesBE` has 32 bytes.
  `Bls.Fr.fromBytesBE_ok` takes the vector, and concludes only the value and its bound, since the length is in the type.
  `Signatures.SecretKey.fromBytes_eq_ok_iff` is replaced by `Signatures.SecretKey.fromBytes_packBytes_eq_ok_iff`, about the packed bytes of a vector.
  The new `Signatures.SecretKey.fromBytes_of_size_ne` states that the decoder rejects an input that is not 32 bytes long.

- In Lean, the module `EthLib.Cryptography.Proofs.IdLoops` is removed, with its seven lemmas in the namespace `Cryptography.IdLoops`.
  They are `id_pure`, `id_bind`, `forIn_list_yield`, `forIn_range_yield`, `forIn_range_yield_ite`, `forIn_range_yield_ite₂` and `foldl_range'_getElem!`.
  They turned `for` loops of `Id.run do` blocks into folds.
  No proof of EthLib uses them, since the last such loop, the tail scan of a compressed BLS point, became a fold ([#2045](https://github.com/ethereum/EthLib/pull/2045)).
  `Proofs/Bls/G1Msm.lean` and `Proofs/Bls/G2Compress.lean` no longer import the module.

- In Lean, `Execution.blockStates_eq` no longer takes `first : u ∈ J` and `second : w ∈ J` ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  Two stores that start at the anchor store agree on states wherever their blocks agree, honest or not.
  A caller drops those two arguments.

- In Lean, `VoteAt.accepted_at_next_slot` and `VoteAt.recorded_at_next_slot` no longer take the premise `epoch : attestation.data.target.epoch = computeEpochAtSlot preset slot` ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  The honest vote data already puts the target at the epoch of the duty slot.
  A caller drops that argument.

- In Lean, `pendingTailRun_processBlock` and `pendingTailRun_stateTransition` hold at every fork and no longer take `fork < .glamsterdam` ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  From Gloas the requests of the parent payload leave the entries past the boundary pending.
  A caller drops the explicit argument `early`.

- In Lean, `Store.onBlock_pulledUp` also states that the finalized checkpoint before the pull-up is the store's or that of the block's state ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  A caller that destructures its result adds one pattern after the one for the justified checkpoint.
  The callers in EthLib that do so are `Store.onBlock_unrealized_epoch_le` and two private callers in `Checkpoints.lean` and `CheckpointBlocks.lean`.

- In Lean, `Store.getCheckpointBlock_trans` and `Store.getCheckpointBlock_self` hold at every fork and no longer take `fork < .glamsterdam` ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  The root of an ancestor walk does not depend on the payload status of its start.
  So a read at an earlier epoch goes through the checkpoint of a later one.
  A caller drops the first explicit argument.

- In Lean, `Store.isAncestor_of_getCheckpointBlock` holds at every fork and no longer takes `fork < .glamsterdam` ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  From Gloas the walk reaches the checkpoint's block with some payload status.
  The ancestor test against a pending node accepts every status.
  A caller drops the first explicit argument.

- In Lean, `HonestHeadsExist` no longer takes the store's filtered tree: every up-to-date honest store in the interval has a head ([#3352](https://github.com/ethereum/EthLib/issues/3352)).
  `Execution.honestHeadsExist_or_evidence` derives the filtered tree from the held justified block and the epoch room that the tree needs.
  It no longer takes `positive`, which its `parameters.slots` gives.
  It takes `seeds : (2 ^ 64 - 1) / (config.SLOT_DURATION_MS.toNat * preset.SLOTS_PER_EPOCH.toNat) + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64` after `scoreFits`, which `Config.CommitteeWindowsFit.seeds` gives.
  `Execution.callRolloverRead_or_evidence` no longer takes `history`, which its `parameters.lookahead` gives, and it takes the same `seeds` in place of `fit`.
  A caller that applied `HonestHeadsExist` to `nodes` and `tree` drops both arguments.
  A caller of `Execution.honestHeadsExist_or_evidence` drops `positive` and passes `fit.seeds` after `scoreFits`.
  A caller of `Execution.callRolloverRead_or_evidence` drops `history` and passes `fit.seeds` in place of `fit`.

- In Lean, `DirectSafety.Apriori.whistleblowerAllowanceAt` can now be below the cap form, which charges each slashable key at `MAX_EFFECTIVE_BALANCE_ELECTRA` (part of [#2707](https://github.com/ethereum/EthLib/issues/2707)).
  From Electra, when `WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA` is at least 2, it is the smaller of `whistleblowerAllowance` and a new bound.
  The new bound is the new `slashableBase`, plus `windowIssuance`, the deposit carry and the exit flow of the window, over one less than that quotient.
  `slashableBase` sums the larger of the effective and the actual balance over the validators that are unslashed and not yet withdrawable at the reference state.
  `creditBudget`, `gainBudget` and `drift` read the allowance, so each is at most its former value.
  `accountable_safety_apriori` keeps its statement, with that smaller drift, so it implies the former statement.
  A caller that unfolded `whistleblowerAllowanceAt` to `whistleblowerAllowance` now gets the `if` form.
  The new `Apriori.Internal.otherCredit_le_allowanceAt_electra` bounds the other funding credits of a branch by the allowance.
  The new `DirectSafety.replayRewards_sources` (DirectSafety/IntervalFunding.lean) states that the rewards pass records only reward, penalty and inactivity events; `epochReplay_events` and the allowance proof read it.

- The post-quantum key registration of EIP-8450 is removed, because it is not planned for mainnet.
  Its containers, its gossip checks, its proof of possession and their proofs are gone from Lean.
  The exports `eth_pq_keys_ssz`, `eth_pq_keys_possession_signing_root` and `eth_pq_keys_is_valid_possession_proof` are gone, with the Python functions `pq_keys_ssz`, `pq_keys_possession_signing_root` and `pq_keys_is_valid_possession_proof`.
  The leanXMSS and VRF specifications are unchanged.

- In Lean, the exit and partial-withdrawal cases of `withdrawalRequest_cases` record the validator in `WithdrawalAccepted` ([#2334](https://github.com/ethereum/EthLib/issues/2334)).
  The index is the first with the key of the request.
  The validator there has execution credentials from the address of the request, and it may make a request.
  `isActiveValidator_of_canRequest` gives that a validator that may make a request is active.
  A caller that matched the cases as `⟨index, exited⟩` and `⟨index, v, owed, withdrawn⟩` writes `⟨index, v, accepted, exited⟩` and `⟨index, v, owed, accepted, withdrawn⟩`.

- In Lean, `queriesWith` and its lemmas move from `Sphincs.Unforgeability` to `HashSig`, so that XMSS can count its calls with them ([#3334](https://github.com/ethereum/EthLib/issues/3334)).
  A caller opens `EthLib.Cryptography.HashSig` or writes `HashSig.queriesWith`.

- In Lean, the switch case of `consolidationRequest_cases` records the switched validator in `SwitchAccepted` ([#2334](https://github.com/ethereum/EthLib/issues/2334)).
  The request names one key twice, the index is the first with that key, and the validator there passes `isValidSwitchToCompoundingRequest`.
  A caller that matched the case as `⟨index, switched⟩` writes `⟨index, validator, accepted, switched⟩`.

- EthLib builds with Lean v4.36.0, Mathlib `v4.36.0` and VCVio `v4.36.0`.
  A Lean package that depends on EthLib moves to the same toolchain and Mathlib.

- The JSON parser of Lean v4.36.0 rejects an object that names one member twice.
  A JSON-RPC request with such an object now answers with the parse error `-32700`, where it read the last member before.
  The same holds for a keystore read from JSON text.

- In Lean, `Execution.rootViable_of_checked_call` concludes `RootViable root (e.world n).time time` again, in place of `RootViableAt root T` at each time `T` of the interval ([#2060](https://github.com/ethereum/EthLib/issues/2060)).
  It and `Execution.honestHeadsCover_of_checked_call` no longer take `rollover : CallRolloverRead …`, which `Execution.callRolloverRead_or_evidence` derives from their other premises.
  A caller drops the argument; a caller that read `RootViableAt` at a time `T` applies `RootViable` to the store at `T`.

- In Lean, `HistoricalDirectSafetyEvidence` now records a conflict.
  It requires that the earlier finalized epoch is at most the later justified epoch.
  It also requires that the later justified root does not read the earlier finalized root at that epoch.
  Before, one held state paired with itself satisfied it whenever the stake inequality or hash evidence on its run held.
  With enough churn since the anchor, the inequality holds with no accountable key.
  Every result that offers the evidence as an alternative was then true without a conflict.
  `Execution.finalized_prefix_or_accountable`, `Execution.mem_supportersOf_of_duty_epoch_or_accountable` and `Execution.isAncestor_getHead_of_duty_epoch_or_accountable` conclude the two new facts.
  A caller that takes the evidence apart has two more components after the time bound; a caller that passes it on is unchanged.

- In Lean, `Store.held_of_isAncestor` now takes any ancestor node.
  A caller that names the implicit `root` passes the node `⟨root, .pending⟩` as `ancestor`.

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
  `G1.compress` and `G1.infinityBytes` are a `Vector UInt8 48`, and `G1.uncompress`, `G1.keyValidatePoint` and `G1.keyValidate` take one.
  A caller that holds bytes of another length reads them with `exactBytes? 48`, and rejects `none` as decompression did.
  `exactBytes?` moves from the BLS exports to `EthLib.Base`.
  `exactBytes?_packBytes`, `packBytes_of_exactBytes?`, `packBytes_mk_data`, `packBytes_set` and `getElem_eq_get!_packBytes` are new in `EthLib.Base`.
  `G1.size_compress` and `keyValidatePoint_size_ne` are removed, since the type states the length.
  `G1.uncompress_ok_cases` no longer states the size.
  It and `uncompress_eq_zero_or` take a vector and read the flags in its first byte.
  `uncompress_ok_cases_bytes` and `uncompress_eq_zero_or_bytes` are new, and state their facts on the bytes of the input.
  `G1.compress_uncompress`, `uncompress_injective`, `uncompress_valid`, `keyValidatePoint_eq_ok_iff`, `exists_keyValidatePoint_of_isOk`, `exists_mul_generator_of_keyValidatePoint` and `Security.exists_decodeKey_of_uncompress` take the encoding as a vector.
  `G1.compress_congr` and `Kzg.compress_eq_of_toPoint_eq` keep their meaning, and now equate vectors.
  `TrustedSetup.decodeG1` and `TrustedSetup.decodeG2` decode one point of a setup, and `TrustedSetup.decodeG1_eq_ok` relates the first to decompression.
  `TrustedSetup.ofBytes_g1Monomial_mem`, `SetupLagrange.coords_of_encodes`, `SetupLagrange.ofBytes_getElem` and `SetupTorsion.modulus_smul_eq_zero` state their facts through `decodeG1`.
  `Kzg.uncompress_G1_POINT_AT_INFINITY` and `validateKzgG1Point_eq_ok_iff` pass the 48 bytes to decompression with no conversion to bytes.
  `Signatures.keyMessagePair` is the pair of one key and one message in the core aggregate verification.
  `coreVerify_iff` takes the key as a vector, and `packBytes_pointToPubkey` and `packBytes_skToPk` become `pointToPubkey_eq` and `skToPk_eq`.
  `coreVerify_of_represents`, `pointToPubkey_bytes`, `pkBytes_eq`, `skToPk_bytes` and `Security.G1Sub.encode_eq_compress` state the key as the bytes of the compressed point, `packBytes (G1.compress P)`.
  `Security.G1Sub.encode_def` is new, and states the encoding in the same form.
  `Signatures.addPubkeyPoint_invalidPubkey` validates the key with no conversion to bytes, and `fastAggregateVerify_rogue` states the keys with `skToPk`.
  `EpochDraws.keys`, `EpochDrawsEnd.keys`, `SyncDrawable.keys`, `UpgradeDraws` and `UpgradeDrawsEnd` validate each key as a vector.
  So do the hypotheses of `getNextSyncCommittee_ok`, `processEpoch_total_of_altair_of_lt_electra`, `processEpoch_total_of_electra` and `runHypotheses_of_quiet_altair`, and the conclusion of `witnessKey_valid`.
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
  So do `eth_consensus_ssz_static`, `eth_consensus_reqresp_message` and `eth_consensus_merkle_proof`.
  A list comes back as a list, the subscribed subnets as a list of `int`, and a pair as a tuple, where each came back as JSON text.
  The two SSZ exports return the root and the bytes as a pair, where they returned the two joined.
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

- In Lean, `Base.Fork.le_hegota` is removed: use `Base.Fork.le_last`.
  `Base.Fork.last` is the last fork, and `Base.Fork.le_last` states that every fork is at or before it.
  The lookup of a fork by its name reads it, and so do the proofs that the consensus fork upgrades and their balance replay stop.
  So a fork added at the end changes none of them; only `Base.Fork.last` must move to it.

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
