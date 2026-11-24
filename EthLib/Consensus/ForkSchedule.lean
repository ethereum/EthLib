module

public import EthLib.Base.Fork
public import EthLib.Consensus.Config
public import EthLib.Consensus.Preset

/-!
# `Consensus.ForkSchedule`

A configuration gives the first epoch and the version of each fork of the consensus layer.

The fork at an epoch is the latest of these forks whose first epoch is at or before it.

From Fulu on, the blob schedule raises the most blobs in a block at given epochs.

Such a change is not a fork of the consensus layer.

So the fork at an epoch is never one of BPO1 to BPO5.

From Gloas, the largest blob limit bounds the size of a data column sidecar.

From Gloas on, a gas limit schedule recommends a gas limit at given epochs, without a validity rule.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

namespace Config

/-- The fork of the consensus layer at an epoch.

It is the latest consensus fork whose first epoch is at or before the epoch. -/
def forkAtEpoch (config : Config) (epoch : Epoch) : Fork :=
  -- From the latest fork down, the first whose fork epoch is at most the epoch.
  if config.HEZE_FORK_EPOCH ≤ epoch then .hegota
  else if config.GLOAS_FORK_EPOCH ≤ epoch then .glamsterdam
  else if config.FULU_FORK_EPOCH ≤ epoch then .fusaka
  else if config.ELECTRA_FORK_EPOCH ≤ epoch then .pectra
  else if config.DENEB_FORK_EPOCH ≤ epoch then .dencun
  else if config.CAPELLA_FORK_EPOCH ≤ epoch then .shapella
  else if config.BELLATRIX_FORK_EPOCH ≤ epoch then .bellatrix
  else if config.ALTAIR_FORK_EPOCH ≤ epoch then .altair
  else .phase0

/-- The version of a fork: that of the latest consensus fork at or before it.

A fork that changes only the execution layer, or only the blob schedule, keeps that version.

The configuration lists the forks up to Heze, the last fork on the timeline. -/
def forkVersion (config : Config) (fork : Fork) : Version :=
  -- From the latest consensus fork down, the version of the first at or before the fork.
  if .hegota ≤ fork then config.HEZE_FORK_VERSION
  else if .glamsterdam ≤ fork then config.GLOAS_FORK_VERSION
  else if .fusaka ≤ fork then config.FULU_FORK_VERSION
  else if .pectra ≤ fork then config.ELECTRA_FORK_VERSION
  else if .dencun ≤ fork then config.DENEB_FORK_VERSION
  else if .shapella ≤ fork then config.CAPELLA_FORK_VERSION
  else if .bellatrix ≤ fork then config.BELLATRIX_FORK_VERSION
  else if .altair ≤ fork then config.ALTAIR_FORK_VERSION
  else config.GENESIS_FORK_VERSION

/-- The version of the fork at an epoch. -/
def computeForkVersion (config : Config) (epoch : Epoch) : Version :=
  -- The version of the fork at the epoch.
  config.forkVersion (config.forkAtEpoch epoch)

/-- The consensus fork after a consensus fork, with its first epoch.

Heze has no next fork yet, and a fork of the execution layer or of the blob schedule has none. -/
def nextFork (config : Config) : Fork → Option (Fork × Epoch)
  -- Each consensus fork to the next, with the fork epoch of the configuration.
  | .phase0 => some (.altair, config.ALTAIR_FORK_EPOCH)
  | .altair => some (.bellatrix, config.BELLATRIX_FORK_EPOCH)
  | .bellatrix => some (.shapella, config.CAPELLA_FORK_EPOCH)
  | .shapella => some (.dencun, config.DENEB_FORK_EPOCH)
  | .dencun => some (.pectra, config.ELECTRA_FORK_EPOCH)
  | .pectra => some (.fusaka, config.FULU_FORK_EPOCH)
  | .fusaka => some (.glamsterdam, config.GLOAS_FORK_EPOCH)
  | .glamsterdam => some (.hegota, config.HEZE_FORK_EPOCH)
  -- Heze and the other forks have none.
  | _ => none

end Config

/-- From Fulu: the blob limit in force at an epoch, with the epoch from which it holds. -/
structure BlobParameters where
  /-- The first epoch of the limit. -/
  epoch : Epoch
  /-- The most blobs in one block. -/
  maxBlobsPerBlock : UInt64
  deriving DecidableEq, Repr

/-- The entry of a schedule with the latest first epoch at or before an epoch.

Among entries with that same first epoch, the first in the schedule wins. -/
def latestStarted {α : Type} (first : α → Epoch) (entries : List α) (epoch : Epoch) :
    Option α :=
  -- The merge sort is stable, so entries with equal epochs keep their order.
  (entries.mergeSort fun a b => first b ≤ first a).find? (first · ≤ epoch)

namespace Config

/-- From Fulu: the blob limit at an epoch.

It is the limit of the schedule entry with the latest first epoch at or before the epoch.

Among entries with that same first epoch, the first in the schedule wins.

With no such entry, the limit of Electra holds, from the first epoch of Electra.

[EIP-7892] adds the schedule.

[EIP-7892]: https://eips.ethereum.org/EIPS/eip-7892#consensus-layer-configuration
-/
def getBlobParameters (config : Config) (epoch : Epoch) : BlobParameters :=
  -- The entry with the latest first epoch at or before the epoch, as EIP-7892 specifies.
  match latestStarted (·.EPOCH) config.BLOB_SCHEDULE epoch with
  | some entry => ⟨entry.EPOCH, entry.MAX_BLOBS_PER_BLOCK⟩
  -- Else the limit of Electra, from the first epoch of Electra.
  | none => ⟨config.ELECTRA_FORK_EPOCH, config.MAX_BLOBS_PER_BLOCK_ELECTRA⟩

/-- The largest blob limit, among the limit of Electra and the limits of the schedule.

It need not be the limit at the current epoch. -/
def largestBlobLimit (config : Config) : UInt64 :=
  -- The maximum of `MAX_BLOBS_PER_BLOCK_ELECTRA` and every limit of the schedule.
  config.BLOB_SCHEDULE.foldl (fun largest entry => max largest entry.MAX_BLOBS_PER_BLOCK)
    config.MAX_BLOBS_PER_BLOCK_ELECTRA

/-- From Fulu: whether the blob schedule of a configuration meets the rules of Fulu.

[EIP-7892] adds the schedule.

[EIP-7892]: https://eips.ethereum.org/EIPS/eip-7892#consensus-layer-configuration -/
def blobScheduleValid (preset : Preset) (config : Config) : Bool :=
  -- A schedule that breaks one of these rules is not a valid configuration; it may be empty.
  --
  -- The specification only recommends entries in increasing order of epoch, so any order passes.
  --
  -- Fulu: "There MUST NOT exist multiple blob schedule entries with the same epoch value."
  decide (config.BLOB_SCHEDULE.map (·.EPOCH)).Nodup &&
    config.BLOB_SCHEDULE.all fun entry =>
      -- "The epoch value in each entry MUST be greater than or equal to `FULU_FORK_EPOCH`."
      config.FULU_FORK_EPOCH ≤ entry.EPOCH &&
        -- Fulu: the limit in each entry "MUST be less than or equal to" the commitment bound.
        entry.MAX_BLOBS_PER_BLOCK ≤ preset.MAX_BLOB_COMMITMENTS_PER_BLOCK

/-- From Gloas: the gas limit that the schedule recommends at an epoch, if any.

It is the limit of the entry with the latest first epoch at or before the epoch.

With no such entry, the schedule recommends nothing.

[EIP-8261] adds the schedule, which changes no validity rule.

The EIP also has clients ignore the schedule for duties before the first epoch of Gloas.

Every entry starts at or after that epoch, so the schedule recommends nothing before it anyway.

[EIP-8261]: https://eips.ethereum.org/EIPS/eip-8261#gas-limit-schedule
-/
def getScheduledGasLimit (config : Config) (epoch : Epoch) : Option UInt64 :=
  -- The limit of the entry with the latest start at or before the epoch, as EIP-8261 says.
  (latestStarted (·.EPOCH) config.GAS_LIMIT_SCHEDULE epoch).map (·.GAS_LIMIT)

/-- From Gloas: whether the gas limit schedule of a configuration meets the rules of Gloas.

[EIP-8261] adds the schedule.

[EIP-8261]: https://eips.ethereum.org/EIPS/eip-8261#gas-limit-schedule -/
def gasLimitScheduleValid (config : Config) : Bool :=
  -- A schedule that breaks one of these rules is not a valid configuration; it may be empty.
  --
  -- The specification only recommends entries in increasing order of epoch, so any order passes.
  --
  -- Gloas: "There MUST NOT exist multiple gas limit schedule entries with the same epoch value."
  decide (config.GAS_LIMIT_SCHEDULE.map (·.EPOCH)).Nodup &&
    -- "The epoch value in each entry MUST be greater than or equal to `GLOAS_FORK_EPOCH`."
    config.GAS_LIMIT_SCHEDULE.all fun entry => config.GLOAS_FORK_EPOCH ≤ entry.EPOCH

end Config

end EthLib.Consensus
