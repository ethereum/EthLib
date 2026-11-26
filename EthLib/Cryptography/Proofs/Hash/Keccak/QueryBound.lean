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

/-! ## Charged permutation calls

Each block of the padded message costs one call of the permutation, and squeezing costs none.

So a call charged at most `B` gives at most `B` per block. -/

section Charge

variable {ι : Type} {spec : OracleSpec ι} {c : ι → ℕ} {f : State → OracleComp spec State} {B : ℕ}

open PFunctor.FreeM (IsChargeBound isChargeBound_pure isChargeBound_map_iff')

/-- The blocks Keccak-256 absorbs from `n` lanes, `8 n` bytes, one permutation call each. -/
def hashBlocks (n : Nat) : Nat :=
  blockCount RATE_256 (8 * n)

open Internal in
/-- Absorbing `k` blocks is charged at most `B * k`. -/
theorem isChargeBound_absorbBlocks (hf : ∀ S, IsChargeBound (f S) c B) (rate : Nat)
    (read : Nat → UInt64) (k start : Nat) (S : State) :
    IsChargeBound (absorbBlocks f rate read k start S) c (B * k) := by
  induction k generalizing start S with
  | zero => exact isChargeBound_pure _
  | succ k ih =>
    rw [absorbBlocks, Nat.mul_succ, Nat.add_comm (B * k) B]
    exact (hf _).bind fun T => ih _ T

open Internal in
/-- Before the last permutation, the sponge is charged at most `B` per full block. -/
theorem isChargeBound_stateBeforeLastPermutation (hf : ∀ S, IsChargeBound (f S) c B)
    (rate len : Nat) (read : Nat → UInt64) :
    IsChargeBound (stateBeforeLastPermutation f rate len read) c (B * (len / rate)) := by
  rw [stateBeforeLastPermutation, ← Nat.add_zero (B * (len / rate))]
  exact (isChargeBound_absorbBlocks hf rate read _ 0 State.zero).bind
    fun T => isChargeBound_pure (B := 0) _

open Internal in
/-- The absorbing phase is charged at most `B` per block of the padded message. -/
theorem isChargeBound_spongeAbsorb (hf : ∀ S, IsChargeBound (f S) c B) (rate len : Nat)
    (read : Nat → UInt64) :
    IsChargeBound (spongeAbsorb f rate len read) c (B * blockCount rate len) := by
  rw [spongeAbsorb, blockCount, Nat.mul_succ]
  exact (isChargeBound_stateBeforeLastPermutation hf rate len read).bind fun T => hf T

/-- Keccak-256 of lanes is charged at most `B` per block of its padded bytes. -/
theorem isChargeBound_keccak256LanesWith (hf : ∀ S, IsChargeBound (f S) c B)
    (lanes : Array UInt64) :
    IsChargeBound (keccak256LanesWith f lanes) c (B * hashBlocks lanes.size) := by
  rw [keccak256LanesWith, Internal.keccak256Read]
  exact (isChargeBound_map_iff' _ _).2 (isChargeBound_spongeAbsorb hf _ _ _)

/-- Keccak-256 of a byte string is charged at most `B` per block of its padding. -/
theorem isChargeBound_keccak256With (hf : ∀ S, IsChargeBound (f S) c B) (msg : ByteArray) :
    IsChargeBound (keccak256With f msg) c (B * blockCount RATE_256 msg.size) := by
  rw [keccak256With_eq_squeeze256]
  exact (isChargeBound_map_iff' _ _).2 (isChargeBound_spongeAbsorb hf _ _ _)

end Charge

/-! ## Permutation calls

A count of the queries that `p` accepts charges one per such query. -/

section Calls

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
  {f : State → OracleComp spec State} {c : ℕ}

/-- A per-call bound on the counted queries is a per-call bound on their charge. -/
private theorem isChargeBound_of_isQueryBoundP (hf : ∀ S, IsQueryBoundP (f S) p c) (S : State) :
    PFunctor.FreeM.IsChargeBound (f S) (fun t => if p t then 1 else 0) c :=
  (isQueryBoundP_iff_isChargeBound p _ _).1 (hf S)

open Internal in
/-- Absorbing `k` blocks makes at most `c * k` selected queries. -/
theorem isQueryBoundP_absorbBlocks (hf : ∀ S, IsQueryBoundP (f S) p c) (rate : Nat)
    (read : Nat → UInt64) (k start : Nat) (S : State) :
    IsQueryBoundP (absorbBlocks f rate read k start S) p (c * k) :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <|
    isChargeBound_absorbBlocks (isChargeBound_of_isQueryBoundP hf) rate read k start S

open Internal in
/-- Before the last permutation, the sponge makes at most `c` selected queries per full block. -/
theorem isQueryBoundP_stateBeforeLastPermutation (hf : ∀ S, IsQueryBoundP (f S) p c)
    (rate len : Nat) (read : Nat → UInt64) :
    IsQueryBoundP (stateBeforeLastPermutation f rate len read) p (c * (len / rate)) :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <|
    isChargeBound_stateBeforeLastPermutation (isChargeBound_of_isQueryBoundP hf) rate len read

open Internal in
/-- The absorbing phase costs at most `c` selected queries per block of the padded message. -/
theorem isQueryBoundP_spongeAbsorb (hf : ∀ S, IsQueryBoundP (f S) p c) (rate len : Nat)
    (read : Nat → UInt64) :
    IsQueryBoundP (spongeAbsorb f rate len read) p (c * blockCount rate len) :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <|
    isChargeBound_spongeAbsorb (isChargeBound_of_isQueryBoundP hf) rate len read

/-- Keccak-256 of lanes costs at most `c` selected queries per block of its padded bytes. -/
theorem isQueryBoundP_keccak256LanesWith (hf : ∀ S, IsQueryBoundP (f S) p c)
    (lanes : Array UInt64) :
    IsQueryBoundP (keccak256LanesWith f lanes) p (c * blockCount RATE_256 (8 * lanes.size)) :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <|
    isChargeBound_keccak256LanesWith (isChargeBound_of_isQueryBoundP hf) lanes

/-- Keccak-256 of a byte string costs at most `c` selected queries per block of its padding. -/
theorem isQueryBoundP_keccak256With (hf : ∀ S, IsQueryBoundP (f S) p c) (msg : ByteArray) :
    IsQueryBoundP (keccak256With f msg) p (c * blockCount RATE_256 msg.size) :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <|
    isChargeBound_keccak256With (isChargeBound_of_isQueryBoundP hf) msg

end Calls

end EthLib.Cryptography.Hash.Keccak
