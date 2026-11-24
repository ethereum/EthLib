module

public import EthLib.Base.Address
public import EthLib.Base.Fork

/-!
# `Base.ChainConfig`

A chain configuration says when each fork activates on an execution chain.

It also gives the blob parameters that a fork or an activation of the chain sets.
-/

@[expose] public section

namespace EthLib.Base

/-- The blob gas of one blob.

Source: [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters). -/
def GAS_PER_BLOB : Nat := 2 ^ 17

/-- The blob parameters of one fork, or of one change that a chain configures.

Source: [EIP-7892](https://eips.ethereum.org/EIPS/eip-7892#blob-base-fee-computations).

[EIP-7892][eip-7892] makes them chain configuration, which a chain can change at its own activation.

[EIP-7840][eip-7840] names them in the configuration file of a client.

[eip-7840]: https://eips.ethereum.org/EIPS/eip-7840#specification
[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#blob-schedule-configuration -/
structure BlobSchedule where
  /-- The blobs per block that the fee aims for, a 64-bit integer as EIP-7892 types it. -/
  target : UInt64
  /-- The most blobs a block may carry, a 64-bit integer as EIP-7892 types it. -/
  max : UInt64
  /-- The excess that multiplies the fee by about e, unbounded as EIP-7892 types it. -/
  baseFeeUpdateFraction : Nat
  -- The bounds below exclude the schedules that would divide by 0 or subtract below 0.
  --
  -- They also keep the blob gas of a full block below `2^64`.
  --
  -- For a schedule written in numbers, `decide` proves them.
  /-- The target is at most the maximum, so the subtraction `max - target` never truncates. -/
  target_le_max : target ≤ max := by decide
  /-- The maximum is positive, so the reserve price rule never divides by 0. -/
  max_pos : 0 < max := by decide
  /-- The blob gas of `max` blobs is below `2^64`.

  A header holds the blob gas of its block in 64 bits, as [EIP-4844][eip-4844] sets.

  So the blob gas of the target and of the maximum never overflows 64 bits.

  EIP-7892 does not state this bound: EthLib adds it, and SOUNDNESS.md records it.

  [eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#header-extension -/
  maxBlobGas_lt : GAS_PER_BLOB * max.toNat < 2 ^ 64 := by decide
  /-- The update fraction is positive, so the exponential never divides by 0. -/
  baseFeeUpdateFraction_pos : 0 < baseFeeUpdateFraction := by decide
  deriving Repr, DecidableEq

/-- The blob schedule with a target, a maximum and an update fraction, if they meet its bounds.

Every reader of a blob schedule builds it with this function. -/
def BlobSchedule.ofNat? (target max baseFeeUpdateFraction : Nat) : Option BlobSchedule :=
  -- The target must be at most the maximum, and the maximum and the fraction must be positive.
  --
  -- The blob gas of the maximum must be below `2^64`, so neither number reaches `2^64`.
  if h : target ≤ max ∧ 0 < max ∧ GAS_PER_BLOB * max < 2 ^ 64 ∧ 0 < baseFeeUpdateFraction then
    -- The blob gas bound keeps the maximum, and so the target, below `2^64`.
    have hmax : max < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left max (by decide)) h.2.2.1
    have toNat_max : (UInt64.ofNat max).toNat = max := UInt64.toNat_ofNat_of_lt' hmax
    have toNat_target : (UInt64.ofNat target).toNat = target :=
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt h.1 hmax)
    some { target := .ofNat target, max := .ofNat max, baseFeeUpdateFraction
           target_le_max := by rw [UInt64.le_iff_toNat_le, toNat_target, toNat_max]; exact h.1
           max_pos := by rw [UInt64.lt_iff_toNat_lt, toNat_max]; exact h.2.1
           maxBlobGas_lt := by rw [toNat_max]; exact h.2.2.1
           baseFeeUpdateFraction_pos := h.2.2.2 }
  else none

/-- The bound of the block number or timestamp of an activation that a configuration gives.

The fork identifier of [EIP-2124][eip-2124] and [EIP-6122][eip-6122] holds each as a `uint64`.

So no fork identifier can encode an activation of `2^64` or more, as a passed fork or as the next.

No EIP bounds a fork block or time itself, so the bound is a choice that SOUNDNESS.md records.

[eip-2124]: https://eips.ethereum.org/EIPS/eip-2124#specification
[eip-6122]: https://eips.ethereum.org/EIPS/eip-6122#specification -/
abbrev ACTIVATION_BOUND : Nat := 2 ^ 64

/-- The point of an execution chain from which a fork is active.

[EIP-6953](https://eips.ethereum.org/EIPS/eip-6953#specification) describes both triggers. -/
inductive Activation where
  /-- The fork is active from the block with this number on. -/
  | block (number : Nat)
  /-- The fork is active in each block whose timestamp is at least this many seconds.

  Forks activate this way from Shapella on. -/
  | time (timestamp : Nat)
  deriving DecidableEq, Repr

namespace Activation

/-- Whether a block, with its number and its timestamp, has reached an activation. -/
def reached : Activation → (number timestamp : Nat) → Bool
  -- A block number is reached by that block and every later one.
  | block n, number, _ => n ≤ number
  -- A timestamp is reached by every block at or after it.
  | time t, _, timestamp => t ≤ timestamp

/-- One activation comes no later than another along a chain.

A block number and a timestamp are different units, so a rule orders the two kinds.

Forks by timestamp come at or after forks by block, by the additional rules of [EIP-6122][eip-6122].

[eip-6122]: https://eips.ethereum.org/EIPS/eip-6122#additional-rules -/
def le : Activation → Activation → Prop
  -- Two forks by block: block numbers grow along a chain, so the lower number comes first.
  | block m, block n => m ≤ n
  -- A fork by block comes before every fork by timestamp, as EIP-6122 requires.
  | block _, time _ => True
  -- So a fork by timestamp never comes before a fork by block.
  | time _, block _ => False
  -- Two forks by timestamp: timestamps grow along a chain, so the earlier one comes first.
  | time s, time t => s ≤ t

instance : LE Activation := ⟨le⟩

/-- Whether one activation comes no later than another, decided case by case as the order is. -/
instance : (a b : Activation) → Decidable (a ≤ b)
  -- Two forks by block compare their numbers.
  | block m, block n => Nat.decLe m n
  -- A fork by block always comes first, by EIP-6122.
  | block _, time _ => isTrue trivial
  -- A fork by timestamp never comes before a fork by block.
  | time _, block _ => isFalse id
  -- Two forks by timestamp compare their timestamps.
  | time s, time t => Nat.decLe s t

end Activation

/-- The chain ID, deposit contract, fork activations and blob schedules of an execution chain. -/
structure ChainConfig where
  /-- The chain ID that a transaction signs, as EIP-155 introduces.

  It is a 64-bit number. -/
  chainId : UInt64
  /-- The address of the deposit contract of the chain.

  From Pectra, its deposit logs give the deposit requests of a block, as EIP-6110 configures. -/
  depositContractAddress : Address
  /-- Each fork of the chain with its activation, in the order of the timeline.

  The forks of the consensus layer alone activate by epoch, so the list never holds them. -/
  activations : List (Fork × Activation)
  /-- The blob schedules that the chain sets itself, each with its fork and activation, in order.

  [EIP-7892][eip-7892] lets a chain set its own blob parameters from an activation.

  A schedule holds from its activation until the activation of the next one.

  Before the first one, each fork keeps the schedule that its EIPs give.

  A configuration file keys each schedule by the name of its fork, as [EIP-7840][eip-7840] does.

  So two forks that activate at one time keep their schedules apart.

  A schedule that a chain sets at an activation of no fork of the timeline has no fork.

  [eip-7840]: https://eips.ethereum.org/EIPS/eip-7840#specification
  [eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration -/
  blobSchedules : List (Option Fork × Activation × BlobSchedule) := []
  deriving DecidableEq, Repr

namespace ChainConfig

/-- The configuration lists its forks in the order of the timeline.

[EIP-6122][eip-6122] puts forks by timestamp after forks by block.

[eip-6122]: https://eips.ethereum.org/EIPS/eip-6122#additional-rules
-/
def Ordered (config : ChainConfig) : Prop :=
  -- Each fork activates no earlier than the forks before it.
  --
  -- So Petersburg never activates before Constantinople, a case that EIP-1716 sets apart.
  config.activations.Pairwise (fun x y => x.1 < y.1 ∧ x.2 ≤ y.2) ∧
    -- Each blob schedule also activates no earlier than the schedules before it.
    config.blobSchedules.Pairwise fun x y => x.2.1 ≤ y.2.1

instance (config : ChainConfig) : Decidable config.Ordered :=
  inferInstanceAs (Decidable (List.Pairwise _ _ ∧ List.Pairwise _ _))

/-- Whether no fork by block number comes after a fork by timestamp in the order of the forks.

[EIP-6122](https://eips.ethereum.org/EIPS/eip-6122#additional-rules) requires this order. -/
def activationsOrdered (activations : List (Fork × Activation)) : Bool :=
  -- For each fork by block number, every fork before it in the order is by block number too.
  activations.all fun (g, b) => !(b matches .block _) ||
    activations.all fun (f, a) => a matches .block _ || !decide (f < g)

/-- The active fork at a block: the latest fork whose activation the block has reached.

Two forks can activate at one block, and then the later fork is active.

[EIP-1716](https://eips.ethereum.org/EIPS/eip-1716) requires this for Petersburg.

No fork is active at a block that has reached no activation. -/
def activeFork (config : ChainConfig) (number timestamp : Nat) : Option Fork :=
  -- Fold from the last fork, keeping the latest reached fork in the order of the forks.
  config.activations.foldr (init := none) fun (fork, activation) later =>
    if activation.reached number timestamp then
      match later with
      -- A later fork already reached wins, as Petersburg wins over Constantinople.
      | some other => if fork ≤ other then some other else some fork
      | none => some fork
    else later

/-- The blob schedule that a chain sets itself at a block.

It is the last one in the list whose activation the block has reached.

None holds at a block that has reached no activation of a blob schedule. -/
def blobScheduleAt (config : ChainConfig) (number timestamp : Nat) : Option BlobSchedule :=
  -- Search from the end, so the last reached schedule in the list wins.
  --
  -- Two schedules can activate at one block, and then the later one in the list holds.
  (config.blobSchedules.reverse.find? fun entry => entry.2.1.reached number timestamp).map
    (·.2.2)

/-- The configuration of Ethereum mainnet, from Frontier to BPO2.

Mainnet sets no blob schedule of its own: each fork keeps the schedule of its EIPs.

Sources:

- [EIP-155][eip-155]: the chain ID.
- [EIP-6110][eip-6110]: the deposit contract.
- [EIP-6953][eip-6953-pow]: the blocks from Homestead to Gray Glacier.
- [EIP-3675][eip-3675] and [EIP-7643][eip-7643]: the block of Paris.
- [EIP-6953][eip-6953-pos]: the time of Shapella.
- The meta EIP of each later fork: EIP-7569, EIP-7600, EIP-7607, EIP-8134 and EIP-8135.

[eip-155]: https://eips.ethereum.org/EIPS/eip-155#list-of-chain-ids
[eip-6110]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-6110.md#configuration
[eip-6953-pow]: https://eips.ethereum.org/EIPS/eip-6953#proof-of-work-network-upgrades
[eip-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#transition-block-validity
[eip-7643]: https://eips.ethereum.org/EIPS/eip-7643#pre-pos-root
[eip-6953-pos]: https://eips.ethereum.org/EIPS/eip-6953#post-merge-upgrades
-/
def mainnet : ChainConfig where
  -- EIP-155 lists chain ID 1 for mainnet.
  chainId := 1
  -- The deposit contract that EIP-6110 configures.
  depositContractAddress := #v[0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40, 0x35, 0x6c, 0xbb,
    0x83, 0x9c, 0xbe, 0x05, 0x30, 0x3d, 0x77, 0x05, 0xfa]
  activations := [
    -- Frontier holds from the genesis block on.
    (.frontier, .block 0),
    -- Homestead to Gray Glacier activate at the blocks of EIP-6953.
    (.homestead, .block 1150000),
    (.daoFork, .block 1920000),
    (.tangerineWhistle, .block 2463000),
    (.spuriousDragon, .block 2675000),
    (.byzantium, .block 4370000),
    -- Petersburg activates at the block of Constantinople, and takes precedence.
    (.constantinople, .block 7280000),
    (.petersburg, .block 7280000),
    (.istanbul, .block 9069000),
    (.muirGlacier, .block 9200000),
    (.berlin, .block 12244000),
    (.london, .block 12965000),
    (.arrowGlacier, .block 13773000),
    (.grayGlacier, .block 15050000),
    -- The first block whose parent reaches the terminal total difficulty of EIP-3675.
    (.paris, .block 15537394),
    -- Shapella activates at the time of EIP-6953.
    (.shapella, .time 1681338455),
    -- Each later fork activates at the time of its meta EIP.
    (.dencun, .time 1710338135),
    (.pectra, .time 1746612311),
    (.fusaka, .time 1764798551),
    (.bpo1, .time 1765290071),
    (.bpo2, .time 1767747671)]

/-- The configuration of the Hoodi test network, from Frontier to BPO2.

The [genesis file][hoodi] gives every value.

No fork follows BPO2: neither it nor the Hoodi row of [EIP-7773][eip-7773] gives one.

Hoodi sets no blob schedule: Fusaka keeps the schedule of Pectra, each other fork that of its EIPs.

[hoodi]: https://github.com/eth-clients/hoodi/blob/2a7efb3c530cce7c71702cc98d0f965df2411c11/metadata/genesis.json
[eip-7773]: https://github.com/ethereum/EIPs/blob/b055feec322fbc37e9d77a393a50b3ff56b31c92/EIPS/eip-7773.md#activation
-/
def hoodi : ChainConfig where
  chainId := 560048
  -- The same deposit contract as on mainnet.
  depositContractAddress := #v[0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40, 0x35, 0x6c, 0xbb,
    0x83, 0x9c, 0xbe, 0x05, 0x30, 0x3d, 0x77, 0x05, 0xfa]
  activations := [
    -- Every fork up to London activates at block 0.
    -- The DAO fork and the forks that only delay the difficulty bomb are absent.
    (.frontier, .block 0),
    (.homestead, .block 0),
    (.tangerineWhistle, .block 0),
    (.spuriousDragon, .block 0),
    (.byzantium, .block 0),
    (.constantinople, .block 0),
    (.petersburg, .block 0),
    (.istanbul, .block 0),
    (.berlin, .block 0),
    (.london, .block 0),
    -- The terminal total difficulty is 0, so Paris activates at block 0 too.
    (.paris, .block 0),
    -- Shapella and Dencun activate at time 0, so Hoodi starts with the rules of Dencun.
    (.shapella, .time 0),
    (.dencun, .time 0),
    -- The meta EIPs EIP-7600 and EIP-7607 give the same times to the later forks.
    --
    -- They give those of BPO1 and BPO2 too.
    (.pectra, .time 1742999832),
    (.fusaka, .time 1761677592),
    (.bpo1, .time 1762365720),
    (.bpo2, .time 1762955544)]

end ChainConfig

end EthLib.Base
