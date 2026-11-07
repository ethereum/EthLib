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

/-- The root that a proposer signs for its preferences, on the chain of a state.

The domain is that of preferences, at the fork version of the proposal epoch. -/
def proposerPreferencesSigningRoot (config : Config) (state : BeaconState preset fork)
    (preferences : ProposerPreferences) : Except Serialization.Ssz.Err Root := do
  let version := config.computeForkVersion (computeEpochAtSlot preset preferences.proposalSlot)
  let domain ← computeDomain config DOMAIN_PROPOSER_PREFERENCES version
    state.genesisValidatorsRoot
  computeSigningRoot preferences domain

/-- Whether the validator of some preferences signed them, under its key in a state.

A validator index outside the registry is an error. -/
def isValidProposerPreferencesSignature (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedProposerPreferences) :
    Except ForkChoiceError Bool := do
  let validator ← (getValidator state signed.message.validatorIndex).mapError .accessor
  let root ← (proposerPreferencesSigningRoot config state signed.message).mapError .ssz
  return checks.verify (packBytes validator.pubkey) (packBytes root) (packBytes signed.signature)

/-! ## The lookahead -/

/-- The state of a dependent block at the first slot of a lookahead.

A state at or after that slot is kept as it is. -/
def lookaheadState (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (start : Slot) : Except ForkChoiceError (BeaconState preset fork) :=
  if state.slot < start then (processSlots config checks state start).mapError .transition
  else pure state

/-- From Fulu: the proposer of a slot in the lookahead of a state, which starts at a given slot.

A slot before the start is an error, and so is a slot after the end of the lookahead. -/
def lookaheadProposer (state : BeaconState preset fork) (fulu : .fusaka ≤ fork)
    (start slot : Slot) : Except ForkChoiceError ValidatorIndex := do
  let offset ← (subChecked slot start).mapError .arith
  match (state.proposerLookahead fulu)[offset.toNat]? with
  | some proposer => return proposer
  | none => throw (.accessor (.slotOutOfRange slot start))

/-! ## The topic -/

/-- The preferences seen for a proposal slot and a dependent root, if any. -/
def Seen.proposerPreferencesFor (seen : Seen) (key : Slot × Root) : Option ProposerPreferences :=
  seen.proposerPreferences.lookup key

/-- From Gloas: the checks of the preferences of a proposer on their topic, at a time in ms.

The first valid preferences for a proposal slot and a dependent root pass.

Later preferences for the same slot and root are ignored.

The proposal epoch must not come before Gloas, and the proposal slot must not have started.

The first slot of the lookahead of the proposal epoch must have started.

The dependent block must be known with its state, and must not come after the dependent slot.

It must be the head, or have a known child after that slot.

The validator must be the proposer of the slot in the state of the dependent block.

That state is advanced to the first slot of the lookahead, when it is earlier.

The validator must have signed the preferences with its key in that state. -/
def validateProposerPreferences (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (gloas : .glamsterdam ≤ fork) (signed : SignedProposerPreferences)
    (currentTimeMs : UInt64) : Except ForkChoiceError ValidationResult :=
  let preferences := signed.message
  let proposalEpoch := computeEpochAtSlot preset preferences.proposalSlot
  (ignoreUnless
    (seen.proposerPreferencesFor (preferences.proposalSlot, preferences.dependentRoot)).isNone
    "already seen preferences for this dependent root and proposal slot").andThenM fun _ =>
  (ignoreUnless (config.GLOAS_FORK_EPOCH ≤ proposalEpoch) "proposal epoch is pre-gloas").andThenM
    fun _ => do
  let past ← store.isPastSlot config preferences.proposalSlot currentTimeMs
  (ignoreUnless (!past) "proposal slot has already started").andThenM fun _ => do
  let start ← (computeShufflingLookaheadStartSlot preset proposalEpoch).mapError .arith
  let future ← store.isFutureSlot config start currentTimeMs
  (ignoreUnless (!future) "proposer for the proposal slot is not yet known").andThenM fun _ => do
  match store.blocks[preferences.dependentRoot]? with
  | none => return .ignore "dependent block has not been seen"
  | some block =>
  match store.blockStates[preferences.dependentRoot]? with
  | none => return .ignore "dependent block failed validation"
  | some dependentState => do
  let dependentSlot ← (computeShufflingDependentSlot preset proposalEpoch).mapError .arith
  (rejectUnless (block.slot ≤ dependentSlot)
    "dependent block is after the shuffling dependent slot").andThenM fun _ => do
  let possible ← store.isValidDependentRoot config preferences.dependentRoot dependentSlot
  (ignoreUnless possible "dependent block is not a possible dependent block").andThenM
    fun _ => do
  let state ← lookaheadState config checks dependentState start
  let proposer ←
    lookaheadProposer state (Nat.le_trans (by decide) gloas) start preferences.proposalSlot
  (rejectUnless (proposer == preferences.validatorIndex)
    "validator is not the proposer for the given slot").andThenM fun _ => do
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
