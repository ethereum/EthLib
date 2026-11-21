module

public import EthLib.Base.ChainConfig
public import Lean.Data.Json

/-!
# `Base.ExecutionConfig`

The fork times and blob schedules of a chain, as the configuration file of a client gives them.

[EIP-7840][eip-7840] adds an object of blob schedules, with one entry per fork name.

[EIP-7892][eip-7892] gives the time of each fork in a key made of its name and `Time`.

The reader merges these keys into a configuration that holds the rest of the chain.

It reads the keys of the forks from Shanghai to Glamsterdam, whose names a source gives.

The writer writes them back, and reading what it wrote gives the configuration back.

[eip-7840]: https://eips.ethereum.org/EIPS/eip-7840#specification
[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration
-/

@[expose] public section

namespace EthLib.Base.ExecutionConfig

open Lean (Json ToJson toJson)

/-- Each fork that activates by time, with the name that the execution layer gives it.

A configuration file names a fork this way, such as `cancun` for Dencun.

[EIP-6953][eip-6953] names Shanghai.

[EIP-7569][eip-7569] calls Dencun Deneb/Cancun, and [EIP-7600][eip-7600] names Prague.

[EIP-7607][eip-7607] names Osaka.

The BPO forks follow the convention of [EIP-7892][eip-7892]: `bpo1`, `bpo2` and so on.

No EIP names the execution side of Glamsterdam.

The [Hoodi genesis file][hoodi] keyed its time as `amsterdamTime` before it unscheduled it.

Hegotá is missing, since no source gives the key of its time yet.

[eip-6953]: https://eips.ethereum.org/EIPS/eip-6953#post-merge-upgrades
[eip-7569]: https://eips.ethereum.org/EIPS/eip-7569
[eip-7600]: https://eips.ethereum.org/EIPS/eip-7600
[eip-7607]: https://eips.ethereum.org/EIPS/eip-7607
[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration
[hoodi]: https://github.com/eth-clients/hoodi/blob/ef8998901c1350f41a0bcc0a2a8d4baad973abcf/metadata/genesis.json#L23
-/
def forkNames : List (Fork × String) :=
  [(.shapella, "shanghai"), (.dencun, "cancun"), (.pectra, "prague"), (.fusaka, "osaka"),
    (.bpo1, "bpo1"), (.bpo2, "bpo2"), (.bpo3, "bpo3"), (.bpo4, "bpo4"), (.bpo5, "bpo5"),
    (.glamsterdam, "amsterdam")]

/-- Why a configuration file cannot be read. -/
inductive ConfigError where
  /-- The file is not a JSON object. -/
  | notObject
  /-- The blob schedules are present, not null, and not a JSON object. -/
  | schedulesNotObject
  /-- The time of a fork is not a natural number below `2^64`, the bound of a block's time. -/
  | timeNotNumber (fork : Fork)
  /-- The entry of a fork is not an object with three natural numbers. -/
  | scheduleMalformed (fork : Fork)
  /-- The entry of a fork has a target above its maximum, or a maximum or fraction of 0. -/
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
  match j.getObjVal? (name ++ "Time") with
  | .error _ => pure none
  | .ok v => match v.getNat? with
    | .ok t => if t < 2 ^ 64 then pure (some t) else throw (.timeNotNumber fork)
    | .error _ => throw (.timeNotNumber fork)

/-- The blob schedule of one entry: its target, maximum and update fraction. -/
def readSchedule (fork : Fork) (v : Json) : Except ConfigError BlobSchedule :=
  match v.getObjValAs? Nat "target", v.getObjValAs? Nat "max",
      v.getObjValAs? Nat "baseFeeUpdateFraction" with
  | .ok target, .ok max, .ok fraction =>
    if h : target ≤ max ∧ 0 < max ∧ 0 < fraction then
      pure ⟨target, max, fraction, h.1, h.2.1, h.2.2⟩
    else throw (.scheduleOutOfBounds fork)
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

/-- The time and the blob schedule of one fork, from the file and the base.

A time in the file wins over the time of the base.

The file may leave out a time that the base gives, since EIP-7892 requires times only after Prague.

Blob schedules start at Dencun, as in the object of EIP-7840, so an earlier entry is ignored.

An entry needs a time for its fork, so that it has an activation. -/
def readFork (base : ChainConfig) (j schedules : Json) (fork : Fork) (name : String) :
    Except ConfigError (Option Nat × Option BlobSchedule) := do
  let time := (← readTime j fork name) <|> timeOf base fork
  let schedule ← if .dencun ≤ fork then
      match schedules.getObjVal? name with
      | .error _ => pure none
      | .ok v => some <$> readSchedule fork v
    else pure none
  if time.isNone ∧ schedule.isSome then throw (.scheduleWithoutTime fork)
  return (time, schedule)

/-- A chain configuration, with the fork times and blob schedules of a configuration file.

The file is the object that holds these keys, which a genesis file nests under `config`.

An absent `blobSchedule`, or a null one, holds no entry.

The base gives the chain ID, the deposit contract and the forks by block number.

It also gives the time of a fork that the file does not time.

The blob schedules come from the file, and replace those of the base.

A fork without an entry keeps the schedule before it, as Fusaka keeps that of Pectra on Hoodi.

[EIP-7892][eip-7892] asks a fork that changes the schedule for an entry.

A file without one gives that fork the schedule before it.

A name in the file that no fork has is ignored.

The forks of the result must activate in the order of the timeline.

[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#blob-schedule-configuration -/
def readExecutionConfig (base : ChainConfig) (j : Json) : Except ConfigError ChainConfig := do
  unless j matches .obj _ do throw .notObject
  let schedules := j.getObjValD "blobSchedule"
  unless (schedules matches .obj _) || (schedules matches .null) do throw .schedulesNotObject
  let read ← forkNames.mapM fun (fork, name) => do
    return (fork, ← readFork base j schedules fork name)
  let config : ChainConfig := { base with
    activations := base.activations.filter (fun (_, a) => a matches .block _) ++
      read.filterMap (fun (fork, time, _) => time.map fun t => (fork, .time t)) ++
      base.activations.filter fun (f, a) => a matches .time _ ∧ f ∉ forkNames.map Prod.fst
    blobSchedules := read.filterMap fun (fork, time, schedule) =>
      match time, schedule with
      | some t, some s => some (some fork, .time t, s)
      | _, _ => none }
  unless decide config.Ordered do throw .notOrdered
  return config

/-- The entry of a blob schedule: its target, maximum and update fraction, as JSON numbers. -/
def scheduleJson (s : BlobSchedule) : Json :=
  Json.mkObj [("target", toJson s.target), ("max", toJson s.max),
    ("baseFeeUpdateFraction", toJson s.baseFeeUpdateFraction)]

/-- The fork times and blob schedules of a configuration, as a configuration file holds them.

Each fork that activates by time gets its time key.

The first schedule kept with each fork that has a name gets the entry of that fork.

It leaves out a schedule without a fork, or of a fork with no name, and a later one of one fork.

It also leaves out the time of a fork with no name in a file.

A schedule takes the activation of its fork, which the file gives by time only.

The reader ignores an entry before Dencun, so a schedule of Shanghai does not read back. -/
def writeExecutionConfig (config : ChainConfig) : Json :=
  Json.mkObj <|
    ("blobSchedule", Json.mkObj (forkNames.filterMap fun (fork, name) =>
      (scheduleOf config fork).map fun s => (name, scheduleJson s))) ::
    forkNames.filterMap fun (fork, name) =>
      (timeOf config fork).map fun t => (name ++ "Time", toJson t)

/-- A configuration that a configuration file holds whole, so that the writer loses nothing.

Its forks and schedules are in the order of the timeline.

Each fork that activates by time has a name in a file, and a time below `2^64`.

Each schedule belongs to a fork from Dencun on, in the order of the forks.

It activates with its fork, by time. -/
def Writable (config : ChainConfig) : Prop :=
  config.Ordered ∧
  (∀ f t, (f, Activation.time t) ∈ config.activations →
    f ∈ forkNames.map Prod.fst ∧ t < 2 ^ 64) ∧
  config.blobSchedules.Pairwise (fun x y => ∀ f g, x.1 = some f → y.1 = some g → f < g) ∧
  (∀ g a s, (g, a, s) ∈ config.blobSchedules →
    ∃ f t, g = some f ∧ .dencun ≤ f ∧ a = .time t ∧ (f, Activation.time t) ∈ config.activations)

end EthLib.Base.ExecutionConfig
