module

public import EthLib.Base.BlobSchedule
public import EthLib.Base.Fork

/-!
# `Base.ChainConfig`

A chain configuration says when each fork activates on an execution chain.

A fork activates at a block number, or from Shapella on at a timestamp.

At a block, the active fork is the latest fork whose activation the block has reached.

[EIP-6953](https://eips.ethereum.org/EIPS/eip-6953#specification) describes both triggers.

The forks of the consensus layer alone activate by epoch, so an execution chain never lists them.

A chain can also set its own blob parameters from an activation, as [EIP-7892][eip-7892] allows.

[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration
-/

@[expose] public section

namespace EthLib.Base

/-- The point of an execution chain from which a fork is active. -/
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
  | block n, number, _ => n ≤ number
  | time t, _, timestamp => t ≤ timestamp

/-- One activation comes no later than another along a chain.

Blocks of a chain grow in number and in timestamp, and activations by number come first. -/
def le : Activation → Activation → Prop
  | block m, block n => m ≤ n
  | block _, time _ => True
  | time _, block _ => False
  | time s, time t => s ≤ t

instance : LE Activation := ⟨le⟩

instance : (a b : Activation) → Decidable (a ≤ b)
  | block m, block n => Nat.decLe m n
  | block _, time _ => isTrue trivial
  | time _, block _ => isFalse id
  | time s, time t => Nat.decLe s t

end Activation

/-- The chain ID of an execution chain, the activations of its forks, and its blob schedules. -/
structure ChainConfig where
  /-- The chain ID that a transaction signs, as EIP-155 introduces.

  It is a 64-bit number. -/
  chainId : UInt64
  /-- Each fork of the chain with its activation, in the order of the timeline. -/
  activations : List (Fork × Activation)
  /-- The blob schedules that the chain sets itself, each with its activation, in order.

  A schedule holds from its activation until the activation of the next one.

  Before the first one, each fork keeps the schedule that its EIPs give. -/
  blobSchedules : List (Activation × BlobSchedule) := []
  deriving DecidableEq, Repr

namespace ChainConfig

/-- The configuration lists its forks in the order of the timeline.

Each fork activates no earlier than the forks before it.

[EIP-6122](https://eips.ethereum.org/EIPS/eip-6122#additional-rules) puts forks by timestamp after
forks by block.

So Petersburg never activates before Constantinople, a case that EIP-1716 sets apart.

Each blob schedule also activates no earlier than the schedules before it. -/
def Ordered (config : ChainConfig) : Prop :=
  config.activations.Pairwise (fun x y => x.1 < y.1 ∧ x.2 ≤ y.2) ∧
    config.blobSchedules.Pairwise fun x y => x.1 ≤ y.1

instance (config : ChainConfig) : Decidable config.Ordered :=
  inferInstanceAs (Decidable (List.Pairwise _ _ ∧ List.Pairwise _ _))

/-- Whether no fork by block number comes after a fork by timestamp in the order of the forks.

[EIP-6122](https://eips.ethereum.org/EIPS/eip-6122#additional-rules) requires this order. -/
def activationsOrdered (activations : List (Fork × Activation)) : Bool :=
  activations.all fun (g, b) => !(b matches .block _) ||
    activations.all fun (f, a) => a matches .block _ || !decide (f < g)

/-- The active fork at a block: the latest fork whose activation the block has reached.

Two forks can activate at one block, and then the later fork is active.

[EIP-1716](https://eips.ethereum.org/EIPS/eip-1716) requires this for Petersburg.

No fork is active at a block that has reached no activation. -/
def activeFork (config : ChainConfig) (number timestamp : Nat) : Option Fork :=
  config.activations.foldr (init := none) fun (fork, activation) later =>
    if activation.reached number timestamp then
      match later with
      | some other => if fork ≤ other then some other else some fork
      | none => some fork
    else later

/-- The blob schedule that a chain sets itself at a block.

It is the last one in the list whose activation the block has reached.

Two schedules can activate at one block, and then the later one in the list holds.

None holds at a block that has reached no activation of a blob schedule. -/
def blobScheduleAt (config : ChainConfig) (number timestamp : Nat) : Option BlobSchedule :=
  (config.blobSchedules.reverse.find? fun entry => entry.1.reached number timestamp).map Prod.snd

/-- The configuration of Ethereum mainnet, from Frontier to BPO2.

Its chain ID is 1, as [EIP-155](https://eips.ethereum.org/EIPS/eip-155#list-of-chain-ids) lists.

Frontier holds from the genesis block on.

[EIP-6953](https://eips.ethereum.org/EIPS/eip-6953#proof-of-work-network-upgrades) gives the blocks
from Homestead to Gray Glacier.

[EIP-3675](https://eips.ethereum.org/EIPS/eip-3675#transition-block-validity) starts Paris at the
first block whose parent reaches the terminal total difficulty.

On mainnet that block is 15,537,394, the first block after the history of
[EIP-7643](https://eips.ethereum.org/EIPS/eip-7643#pre-pos-root).

[EIP-6953](https://eips.ethereum.org/EIPS/eip-6953#post-merge-upgrades) gives the time of Shapella.

The meta EIP of each later fork gives its time: EIP-7569, EIP-7600, EIP-7607, EIP-8134, EIP-8135.

Mainnet sets no blob schedule of its own: each fork keeps the schedule of its EIPs. -/
def mainnet : ChainConfig where
  chainId := 1
  activations := [
    (.frontier, .block 0),
    (.homestead, .block 1150000),
    (.daoFork, .block 1920000),
    (.tangerineWhistle, .block 2463000),
    (.spuriousDragon, .block 2675000),
    (.byzantium, .block 4370000),
    (.constantinople, .block 7280000),
    (.petersburg, .block 7280000),
    (.istanbul, .block 9069000),
    (.muirGlacier, .block 9200000),
    (.berlin, .block 12244000),
    (.london, .block 12965000),
    (.arrowGlacier, .block 13773000),
    (.grayGlacier, .block 15050000),
    (.paris, .block 15537394),
    (.shapella, .time 1681338455),
    (.dencun, .time 1710338135),
    (.pectra, .time 1746612311),
    (.fusaka, .time 1764798551),
    (.bpo1, .time 1765290071),
    (.bpo2, .time 1767747671)]

/-- The configuration of the Hoodi test network, from Frontier to Glamsterdam.

Its chain ID is 560048, as its [genesis file][hoodi] gives.

The genesis file activates every fork up to London at block 0.

Its terminal total difficulty is 0, so Paris activates at block 0 too.

Shapella and Dencun activate at time 0, so Hoodi starts with the rules of Dencun.

The genesis file lists no DAO fork and no fork that only delays the difficulty bomb.

The meta EIP of each later fork gives its time: EIP-7600, EIP-7607 (BPO1, BPO2) and EIP-7773.

The genesis file gives each fork from Dencun to BPO2 the blob schedule of its EIPs.

So Hoodi sets no blob schedule of its own.

[hoodi]: https://github.com/eth-clients/hoodi/blob/2a7efb3c530cce7c71702cc98d0f965df2411c11/metadata/genesis.json -/
def hoodi : ChainConfig where
  chainId := 560048
  activations := [
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
    (.paris, .block 0),
    (.shapella, .time 0),
    (.dencun, .time 0),
    (.pectra, .time 1742999832),
    (.fusaka, .time 1761677592),
    (.bpo1, .time 1762365720),
    (.bpo2, .time 1762955544),
    (.glamsterdam, .time 1793036568)]

end ChainConfig

end EthLib.Base
