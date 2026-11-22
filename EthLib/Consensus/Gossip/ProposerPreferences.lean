module

public import EthLib.Consensus.Gossip.Seen
public import EthLib.Networking.Gossip.Validation

/-!
# `Consensus.Gossip.ProposerPreferences`

From Gloas: gossip validation of the preferences of proposers.

A proposer signs its preferences under their own domain, at the fork version of the proposal epoch.

A node checks the preferences against the proposers that the state of their dependent block fixes.

That state is advanced to the first slot of the lookahead of the proposal epoch.

Its lookahead then names the proposer of each slot from there, for the lookahead of seeds.

Preferences for a slot that has started, or whose proposer is not fixed yet, are ignored.

So are the second preferences for one slot and one dependent block.

A dependent block that the node has not seen, or whose state it does not hold, is ignored.

The preferences of a validator other than the proposer of the slot are rejected.

Some steps of the rule can fail, such as a root, or an addition out of range.

Such a failure is an error rather than an outcome.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Networking.Gossip

variable {preset : Preset} {fork : Fork}

/-! ## Signatures -/

/-- The root that a proposer signs for its preferences, on the chain of a state. -/
def proposerPreferencesSigningRoot (config : Config) (state : BeaconState preset fork)
    (preferences : ProposerPreferences) : Except Serialization.Ssz.Err Root := do
  -- The fork version of the epoch of the proposal slot.
  let version := config.computeForkVersion (computeEpochAtSlot preset preferences.proposalSlot)
  -- The domain `DOMAIN_PROPOSER_PREFERENCES` at that version, for the genesis validators root.
  let domain ← computeDomain config DOMAIN_PROPOSER_PREFERENCES version
    state.genesisValidatorsRoot
  -- The signing root of the preferences under that domain.
  computeSigningRoot preferences domain

/-- Whether the validator of some preferences signed them, under its key in a state.

A validator index outside the registry is an error. -/
def isValidProposerPreferencesSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedProposerPreferences) :
    Except ForkChoiceError Bool := do
  -- The signature verifies under the key of the validator, on the signing root of the preferences.
  let validator ← (getValidator state signed.message.validatorIndex).mapError .accessor
  let root ← (proposerPreferencesSigningRoot config state signed.message).mapError .ssz
  return checks.verify validator.pubkey (packBytes root) signed.signature

/-! ## The lookahead -/

/-- From Fulu: the proposer of a slot in the lookahead of a state, which starts at a given slot.

A slot before the start is an error, and so is a slot after the end of the lookahead. -/
def lookaheadProposer (state : BeaconState preset fork) (fulu : .fusaka ≤ fork)
    (start slot : Slot) : Except ForkChoiceError ValidatorIndex := do
  -- Entry `s - t` of the lookahead, for the slot `s` and the start `t`.
  let offset ← (subChecked slot start).mapError .arith
  match (state.proposerLookahead fulu)[offset.toNat]? with
  | some proposer => return proposer
  | none => throw (.accessor (.slotOutOfRange slot start))

/-! ## The topic -/

/-- The preferences seen for a proposal slot and a dependent root, if any. -/
def Seen.proposerPreferencesFor (seen : Seen) (key : Slot × Root) : Option ProposerPreferences :=
  seen.proposerPreferences.lookup key

/-- From Gloas: the checks of the preferences of a proposer on their topic, at a time in ms. -/
def validateProposerPreferences (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (gloas : .glamsterdam ≤ fork) (signed : SignedProposerPreferences)
    (currentTimeMs : UInt64) : Except ForkChoiceError ValidationResult :=
  let preferences := signed.message
  -- Let `e` be the epoch of the proposal slot.
  let proposalEpoch := computeEpochAtSlot preset preferences.proposalSlot
  -- IGNORE unless these are the first valid preferences for the proposal slot and dependent root.
  (ignoreUnless
    (seen.proposerPreferencesFor (preferences.proposalSlot, preferences.dependentRoot)).isNone
    "already seen preferences for this dependent root and proposal slot").andThenM fun _ =>
  -- IGNORE unless `e` is at least `GLOAS_FORK_EPOCH`.
  (ignoreUnless (config.GLOAS_FORK_EPOCH ≤ proposalEpoch) "proposal epoch is pre-gloas").andThenM
    fun _ => do
  -- IGNORE when the proposal slot started more than `MAXIMUM_GOSSIP_CLOCK_DISPARITY` ago.
  let past ← store.isPastSlot config preferences.proposalSlot currentTimeMs
  (ignoreUnless (!past) "proposal slot has already started").andThenM fun _ => do
  -- Let `t` be the first slot of the lookahead of `e`.
  --
  -- IGNORE unless `t` starts at most `MAXIMUM_GOSSIP_CLOCK_DISPARITY` after the clock.
  --
  -- Before `t` the node may not yet know the proposer of the slot.
  let start ← (computeShufflingLookaheadStartSlot preset proposalEpoch).mapError .arith
  let future ← store.isFutureSlot config start currentTimeMs
  (ignoreUnless (!future) "proposer for the proposal slot is not yet known").andThenM fun _ => do
  -- IGNORE unless the dependent block is known.
  match store.blocks[preferences.dependentRoot]? with
  | none => return .ignore "dependent block has not been seen"
  | some block =>
  -- IGNORE unless the dependent block has a state, since a block without one failed validation.
  match store.blockStates[preferences.dependentRoot]? with
  | none => return .ignore "dependent block failed validation"
  | some dependentState => do
  -- Let `d` be the dependent slot of `e`.
  --
  -- REJECT unless the dependent block is at a slot at most `d`.
  let dependentSlot ← (computeShufflingDependentSlot preset proposalEpoch).mapError .arith
  (rejectUnless (block.slot ≤ dependentSlot)
    "dependent block is after the shuffling dependent slot").andThenM fun _ => do
  -- IGNORE unless the dependent block is the head, or the parent of a known block after `d`.
  let possible ← store.isValidDependentRoot config preferences.dependentRoot dependentSlot
  (ignoreUnless possible "dependent block is not a possible dependent block").andThenM
    fun _ => do
  -- The state of the dependent block, advanced to `t` when it is earlier.
  let state ← lookaheadState config checks dependentState start
  -- REJECT unless the validator is the proposer of the proposal slot in its lookahead.
  let proposer ←
    lookaheadProposer state (Nat.le_trans (by decide) gloas) start preferences.proposalSlot
  (rejectUnless (proposer == preferences.validatorIndex)
    "validator is not the proposer for the given slot").andThenM fun _ => do
  -- REJECT unless the validator signed the preferences with its key in that state.
  let valid ← isValidProposerPreferencesSignature config checks state signed
  return rejectUnless valid "invalid proposer preferences signature"

/-- The keys after valid preferences: their proposal slot and dependent root, with them. -/
def Seen.recordProposerPreferences (seen : Seen) (signed : SignedProposerPreferences) : Seen :=
  let preferences := signed.message
  { seen with
    proposerPreferences :=
      ((preferences.proposalSlot, preferences.dependentRoot), preferences) ::
        seen.proposerPreferences }

end EthLib.Consensus
