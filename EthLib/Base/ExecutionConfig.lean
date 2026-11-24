module

public import EthLib.Base.ChainConfig
public import Lean.Data.Json

/-!
# `Base.ExecutionConfig`

The fork times and blob schedules of a chain, as the configuration file of a client gives them.

[EIP-7840][eip-7840] adds an object of blob schedules, with one entry per fork name.

[EIP-7892][eip-7892] gives the time of each fork in a key made of its name and `Time`.

[eip-7840]: https://eips.ethereum.org/EIPS/eip-7840#specification
[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration
-/

@[expose] public section

namespace EthLib.Base.ExecutionConfig

open Lean (Json ToJson toJson)

/-- Each fork that activates by time, with the name that a configuration file gives it.

Names from [EIP-6953][eip-6953], [EIP-7569][eip-7569], [EIP-7600][eip-7600], [EIP-7607][eip-7607].

BPO and Glamsterdam names: [EIP-7892][eip-7892] and the [Hoodi genesis file][hoodi].

Hegotá is missing, since no source gives the key of its time yet.

[eip-6953]: https://eips.ethereum.org/EIPS/eip-6953#post-merge-upgrades
[eip-7569]: https://eips.ethereum.org/EIPS/eip-7569
[eip-7600]: https://eips.ethereum.org/EIPS/eip-7600
[eip-7607]: https://eips.ethereum.org/EIPS/eip-7607
[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration
[hoodi]: https://github.com/eth-clients/hoodi/blob/ef8998901c1350f41a0bcc0a2a8d4baad973abcf/metadata/genesis.json#L23
-/
def forkNames : List (Fork × String) :=
  -- EIP-6953 names Shanghai, and EIP-7569 calls Dencun Deneb/Cancun, so its key is `cancun`.
  --
  -- EIP-7600 names Prague, and EIP-7607 names Osaka.
  [(.shapella, "shanghai"), (.dencun, "cancun"), (.pectra, "prague"), (.fusaka, "osaka"),
    -- The BPO forks follow the convention of EIP-7892: `bpo1`, `bpo2` and so on.
    (.bpo1, "bpo1"), (.bpo2, "bpo2"), (.bpo3, "bpo3"), (.bpo4, "bpo4"), (.bpo5, "bpo5"),
    -- No EIP names the execution side of Glamsterdam.
    --
    -- The Hoodi genesis file keyed its time as `amsterdamTime` before it unscheduled it.
    (.glamsterdam, "amsterdam")]

/-- Why a configuration file cannot be read. -/
inductive ConfigError where
  /-- The file is not a JSON object. -/
  | notObject
  /-- The blob schedules are present, not null, and not a JSON object. -/
  | schedulesNotObject
  /-- The time of a fork is not a natural number below `2^64`.

  The fork identifier holds each fork time as a `uint64`. -/
  | timeNotNumber (fork : Fork)
  /-- The entry of a fork is not an object with three natural numbers. -/
  | scheduleMalformed (fork : Fork)
  /-- The entry of a fork has a target above its maximum, or a maximum or fraction of 0.

  Or the blob gas of the maximum reaches `2^64`, so a target or maximum of `2^64` or more fails. -/
  | scheduleOutOfBounds (fork : Fork)
  /-- A fork has an entry, but the file gives it no time. -/
  | scheduleWithoutTime (fork : Fork)
  /-- The forks of the result do not activate in the order of the timeline. -/
  | notOrdered
  deriving DecidableEq, Repr

/-- The code of an error at the C boundary, one for each constructor. -/
def ConfigError.code : ConfigError → UInt32
  | .notObject => 1
  | .schedulesNotObject => 2
  | .timeNotNumber _ => 3
  | .scheduleMalformed _ => 4
  | .scheduleOutOfBounds _ => 5
  | .scheduleWithoutTime _ => 6
  | .notOrdered => 7

/-- The time that the file gives a fork, if it gives one.

A JSON number reads as a natural number when it has no fraction part.

So `1e3` reads as 1000, and `1000.0` is refused. -/
def readTime (j : Json) (fork : Fork) (name : String) : Except ConfigError (Option Nat) :=
  -- The key of a fork's time is its name followed by `Time`, such as `cancunTime`.
  match j.getObjVal? (name ++ "Time") with
  | .error _ => pure none
  | .ok v => match v.getNat? with
    -- The fork identifier hashes a fork time in 64 bits, so a larger time is refused.
    | .ok t => if t < ACTIVATION_BOUND then pure (some t) else throw (.timeNotNumber fork)
    | .error _ => throw (.timeNotNumber fork)

/-- The blob schedule of one entry: its target, maximum and update fraction. -/
def readSchedule (fork : Fork) (v : Json) : Except ConfigError BlobSchedule :=
  match v.getObjValAs? Nat "target", v.getObjValAs? Nat "max",
      v.getObjValAs? Nat "baseFeeUpdateFraction" with
  | .ok target, .ok max, .ok fraction =>
    -- The three numbers must meet the bounds of a schedule, which keep the first two in 64 bits.
    match BlobSchedule.ofNat? target max fraction with
    | some schedule => pure schedule
    | none => throw (.scheduleOutOfBounds fork)
  | _, _, _ => throw (.scheduleMalformed fork)

/-- The activation by time that a configuration gives a fork, if it gives one. -/
def timeOf (config : ChainConfig) (fork : Fork) : Option Nat :=
  config.activations.findSome? fun (f, a) =>
    match a with
    | .time t => if f = fork then some t else none
    | .block _ => none

/-- The blob schedule that a configuration keeps for a fork, if it keeps one. -/
def scheduleOf (config : ChainConfig) (fork : Fork) : Option BlobSchedule :=
  config.blobSchedules.findSome? fun (f, _, s) => if f = some fork then some s else none

/-- The time and the blob schedule of one fork, from the file and the base. -/
def readFork (base : ChainConfig) (j schedules : Json) (fork : Fork) (name : String) :
    Except ConfigError (Option Nat × Option BlobSchedule) := do
  -- The time of the file, else the time of the base.
  --
  -- The file may leave out a time that the base gives.
  --
  -- EIP-7892 requires a time only for a fork after Prague.
  let time := (← readTime j fork name) <|> timeOf base fork
  -- The entry of the fork, from Dencun on.
  --
  -- Blob schedules start at Dencun, as in the object of EIP-7840, so an earlier entry is ignored.
  let schedule ← if .dencun ≤ fork then
      match schedules.getObjVal? name with
      | .error _ => pure none
      | .ok v => some <$> readSchedule fork v
    else pure none
  -- An entry needs a time for its fork: without one, it would have no activation.
  if time.isNone ∧ schedule.isSome then throw (.scheduleWithoutTime fork)
  return (time, schedule)

/-- A chain configuration, with the fork times and blob schedules of a configuration file.

The file is the object that holds these keys, which a genesis file nests under `config`.

The base gives the chain ID, the deposit contract, the forks by block number and missing times. -/
def readExecutionConfig (base : ChainConfig) (j : Json) : Except ConfigError ChainConfig := do
  unless j matches .obj _ do throw .notObject
  -- An absent schedule object reads as null, which holds no entry.
  let schedules := j.getObjValD "blobSchedule"
  unless (schedules matches .obj _) || (schedules matches .null) do throw .schedulesNotObject
  -- The time and the entry of each named fork, in the order of the timeline.
  --
  -- A name in the file that no fork has is ignored.
  let read ← forkNames.mapM fun (fork, name) => do
    return (fork, ← readFork base j schedules fork name)
  let config : ChainConfig := { base with
    -- The forks by block number of the base, then the named forks by time.
    -- Last come the forks by time of the base that have no name in a file.
    activations := base.activations.filter (fun (_, a) => a matches .block _) ++
      read.filterMap (fun (fork, time, _) => time.map fun t => (fork, .time t)) ++
      base.activations.filter fun (f, a) => a matches .time _ ∧ f ∉ forkNames.map Prod.fst
    -- Each entry of the file, activated at the time of its fork.
    --
    -- The blob schedules come from the file, and replace those of the base.
    --
    -- A fork without an entry keeps the schedule before it.
    --
    -- For example, Fusaka keeps the schedule of Pectra on Hoodi.
    --
    -- EIP-7892 asks a fork that changes the schedule for an entry:
    -- https://eips.ethereum.org/EIPS/eip-7892#blob-schedule-configuration
    --
    -- A file without one gives that fork the schedule before it.
    blobSchedules := read.filterMap fun (fork, time, schedule) =>
      match time, schedule with
      | some t, some s => some (some fork, .time t, s)
      | _, _ => none }
  -- The forks of the result must activate in the order of the timeline.
  unless decide config.Ordered do throw .notOrdered
  return config

/-- The entry of a blob schedule: its target, maximum and update fraction, as JSON numbers. -/
def scheduleJson (s : BlobSchedule) : Json :=
  Json.mkObj [("target", toJson s.target.toNat), ("max", toJson s.max.toNat),
    ("baseFeeUpdateFraction", toJson s.baseFeeUpdateFraction)]

/-- The fork times and blob schedules of a configuration, as a configuration file holds them.

Reading what it writes gives back a writable configuration.

The base of that read keeps only the forks by block number.

A schedule takes the activation of its fork, which the file gives by time only. -/
def writeExecutionConfig (config : ChainConfig) : Json :=
  Json.mkObj <|
    -- One entry for each named fork that keeps a schedule: the first one kept with that fork.
    --
    -- A schedule without a fork, or of a fork with no name, is left out.
    --
    -- So is a later schedule of the same fork.
    --
    -- The reader ignores an entry before Dencun, so a schedule of Shanghai does not read back.
    ("blobSchedule", Json.mkObj (forkNames.filterMap fun (fork, name) =>
      (scheduleOf config fork).map fun s => (name, scheduleJson s))) ::
    -- One time key for each named fork that activates by time.
    --
    -- The time of a fork with no name in a file is left out.
    forkNames.filterMap fun (fork, name) =>
      (timeOf config fork).map fun t => (name ++ "Time", toJson t)

/-- A configuration that a configuration file holds whole, so that the writer loses nothing. -/
def Writable (config : ChainConfig) : Prop :=
  -- Its forks and schedules are in the order of the timeline.
  config.Ordered ∧
  -- Each fork that activates by time has a name in a file, and a time below `2^64`.
  (∀ f t, (f, Activation.time t) ∈ config.activations →
    f ∈ forkNames.map Prod.fst ∧ t < ACTIVATION_BOUND) ∧
  -- Each schedule belongs to a fork, in the order of the forks.
  config.blobSchedules.Pairwise (fun x y => ∀ f g, x.1 = some f → y.1 = some g → f < g) ∧
  -- Each belongs to a fork from Dencun on, and activates with it, by time.
  (∀ g a s, (g, a, s) ∈ config.blobSchedules →
    ∃ f t, g = some f ∧ .dencun ≤ f ∧ a = .time t ∧ (f, Activation.time t) ∈ config.activations)

end EthLib.Base.ExecutionConfig
