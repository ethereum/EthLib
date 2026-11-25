module

public import EthLib.Cryptography.Proofs.Hash.Keccak.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: the Keccak sponge over a permutation oracle

Answering the permutation's queries is running the sponge over the answers.

The sponge calls the permutation once per block of the padded message, FIPS 202 §4, Algorithm 8.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

open OracleComp OracleSpec

/-! ## Answering the oracle -/

section Simulate

variable {ι : Type} {spec : OracleSpec ι} {r : Type → Type} [Monad r] [LawfulMonad r]

/-- Answering the queries of Keccak-256 of lanes runs it over the answered calls. -/
theorem simulateQ_keccak256LanesWith (impl : QueryImpl spec r) (f : State → OracleComp spec State)
    (lanes : Array UInt64) :
    simulateQ impl (keccak256LanesWith f lanes) =
      keccak256LanesWith (fun T => simulateQ impl (f T)) lanes :=
  mmap_keccak256LanesWith (simulateQ' impl) f lanes

/-- Answering the queries of Keccak-256 of bytes runs it over the answered calls. -/
theorem simulateQ_keccak256With (impl : QueryImpl spec r) (f : State → OracleComp spec State)
    (msg : ByteArray) :
    simulateQ impl (keccak256With f msg) = keccak256With (fun T => simulateQ impl (f T)) msg :=
  mmap_keccak256With (simulateQ' impl) f msg

/-- If a function `g` answers each call, Keccak-256 of lanes is `pure` of its value over `g`.

Under the oracles of a permutation `π`, `g` is `π`, so this is the real-world hash of the model. -/
theorem simulateQ_keccak256LanesWith_of_pure (impl : QueryImpl spec r)
    (f : State → OracleComp spec State) (g : State → State)
    (hg : ∀ S, simulateQ impl (f S) = pure (g S)) (lanes : Array UInt64) :
    simulateQ impl (keccak256LanesWith f lanes) =
      pure (Id.run (keccak256LanesWith (fun T => pure (g T)) lanes)) := by
  rw [simulateQ_keccak256LanesWith, funext hg]
  exact keccak256LanesWith_pure g lanes

/-- If a function `g` answers each call, Keccak-256 of bytes is `pure` of its value over `g`. -/
theorem simulateQ_keccak256With_of_pure (impl : QueryImpl spec r)
    (f : State → OracleComp spec State) (g : State → State)
    (hg : ∀ S, simulateQ impl (f S) = pure (g S)) (msg : ByteArray) :
    simulateQ impl (keccak256With f msg) =
      pure (Id.run (keccak256With (fun T => pure (g T)) msg)) := by
  rw [simulateQ_keccak256With, funext hg]
  exact keccak256With_pure g msg

end Simulate

/-! ## Permutation calls

Each block of the padded message costs one call of the permutation, and squeezing costs none.

So a call that makes at most `c` selected queries gives at most `c` per block. -/

section Calls

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
  {f : State → OracleComp spec State} {c : ℕ}

open Internal in
/-- Absorbing `k` blocks makes at most `c * k` selected queries. -/
theorem isQueryBoundP_absorbBlocks (hf : ∀ S, IsQueryBoundP (f S) p c) (rate : Nat)
    (read : Nat → UInt64) (k start : Nat) (S : State) :
    IsQueryBoundP (absorbBlocks f rate read k start S) p (c * k) := by
  induction k generalizing start S with
  | zero => exact isQueryBoundP_pure p S _
  | succ k ih =>
    rw [absorbBlocks, Nat.mul_succ, Nat.add_comm (c * k) c]
    exact isQueryBoundP_bind (hf _) fun T _ => ih _ T

open Internal in
/-- Before the last permutation, the sponge makes at most `c` selected queries per full block. -/
theorem isQueryBoundP_stateBeforeLastPermutation (hf : ∀ S, IsQueryBoundP (f S) p c)
    (rate len : Nat) (read : Nat → UInt64) :
    IsQueryBoundP (stateBeforeLastPermutation f rate len read) p (c * (len / rate)) := by
  rw [stateBeforeLastPermutation, ← Nat.add_zero (c * (len / rate))]
  exact isQueryBoundP_bind (isQueryBoundP_absorbBlocks hf rate read _ 0 State.zero)
    fun T _ => isQueryBoundP_pure p _ 0

open Internal in
/-- The absorbing phase costs at most `c` selected queries per block of the padded message. -/
theorem isQueryBoundP_spongeAbsorb (hf : ∀ S, IsQueryBoundP (f S) p c) (rate len : Nat)
    (read : Nat → UInt64) :
    IsQueryBoundP (spongeAbsorb f rate len read) p (c * blockCount rate len) := by
  rw [spongeAbsorb, blockCount, Nat.mul_succ]
  exact isQueryBoundP_bind (isQueryBoundP_stateBeforeLastPermutation hf rate len read)
    fun T _ => hf T

/-- Keccak-256 of lanes costs at most `c` selected queries per block of its padded bytes. -/
theorem isQueryBoundP_keccak256LanesWith (hf : ∀ S, IsQueryBoundP (f S) p c)
    (lanes : Array UInt64) :
    IsQueryBoundP (keccak256LanesWith f lanes) p (c * blockCount RATE_256 (8 * lanes.size)) := by
  rw [keccak256LanesWith, Internal.keccak256Read, isQueryBoundP_map_iff]
  exact isQueryBoundP_spongeAbsorb hf _ _ _

/-- Keccak-256 of a byte string costs at most `c` selected queries per block of its padding. -/
theorem isQueryBoundP_keccak256With (hf : ∀ S, IsQueryBoundP (f S) p c) (msg : ByteArray) :
    IsQueryBoundP (keccak256With f msg) p (c * blockCount RATE_256 msg.size) := by
  rw [keccak256With_eq_squeeze256, isQueryBoundP_map_iff]
  exact isQueryBoundP_spongeAbsorb hf _ _ _

end Calls

end EthLib.Cryptography.Hash.Keccak
