module

public import EthLib.Consensus.ConsensusVersion
public import EthLib.Consensus.ForkSchedule

/-!
# Proofs: the consensus version of a fork

Each version reads back from its name, and a name that reads back is the name of the version.

A fork has a version exactly from Phase 0 up to, but not including, Hegotá.

The version that a response names gives the fork version of the fork, under every configuration.

Versions never move back along the timeline.

Each version starts at its first fork, which has it.
-/

@[expose] public section

namespace EthLib.Consensus.ConsensusVersion

open Base

/-- Each version reads back from its name. -/
theorem ofName?_name (v : ConsensusVersion) : ofName? v.name = some v := by
  cases v <;> rfl

/-- A version read from a name has that name. -/
theorem name_of_ofName? {s : String} {v : ConsensusVersion} (h : ofName? s = some v) :
    s = v.name := by
  unfold ofName? at h
  have named : (v.name == s) = true :=
    List.find?_some (p := fun x : ConsensusVersion => x.name == s) h
  exact (beq_iff_eq.mp named).symm

/-- The first fork of a version has that version. -/
theorem consensusVersion?_fork (v : ConsensusVersion) : v.fork.consensusVersion? = some v := by
  cases v <;> decide

end EthLib.Consensus.ConsensusVersion

namespace EthLib.Base.Fork

open EthLib.Consensus

/-- A fork has a version exactly from Phase 0 up to, but not including, Hegotá. -/
theorem consensusVersion?_isSome_iff (fork : Fork) :
    fork.consensusVersion?.isSome ↔ .phase0 ≤ fork ∧ fork < .hegota := by
  cases fork <;> decide

/-- The version of a fork names its fork version, under every configuration. -/
theorem consensusVersion?_forkVersion (config : Config) {fork : Fork} {v : ConsensusVersion}
    (h : fork.consensusVersion? = some v) : config.forkVersion fork = v.forkVersion config := by
  cases fork <;> cases v <;> first | rfl | exact absurd h (by decide)

/-- A fork with a version comes at or after the first fork of that version. -/
theorem fork_le_of_consensusVersion? {fork : Fork} {v : ConsensusVersion}
    (h : fork.consensusVersion? = some v) : v.fork ≤ fork := by
  cases fork <;> cases v <;> first | decide | exact absurd h (by decide)

/-- No version whose first fork has come by a fork is later than the version of that fork. -/
theorem le_consensusVersion?_of_fork_le {fork : Fork} {v w : ConsensusVersion}
    (h : fork.consensusVersion? = some v) (started : w.fork ≤ fork) : w ≤ v := by
  revert started
  cases fork <;> cases v <;> first | exact absurd h (by decide) | cases w <;> decide

/-- Versions never move back along the timeline. -/
theorem consensusVersion?_mono {fork fork' : Fork} {v v' : ConsensusVersion} (le : fork ≤ fork')
    (h : fork.consensusVersion? = some v) (h' : fork'.consensusVersion? = some v') : v ≤ v' :=
  le_consensusVersion?_of_fork_le h' (Nat.le_trans (fork_le_of_consensusVersion? h) le)

end EthLib.Base.Fork
