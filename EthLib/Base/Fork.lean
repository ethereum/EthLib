module

/-!
# `Base.Fork`

The network upgrades of both layers of Ethereum, in the order in which they activate on mainnet.

Before the Merge the two layers forked apart, so their forks interleave by date.

[EIP-7568](https://eips.ethereum.org/EIPS/eip-7568#specification) orders them up to Shapella.

From Shapella on, one upgrade changes both layers, and it is one fork.

When a fork activates is chain configuration, so the type holds only the order.

A field that a fork adds to a type holds a value only from that fork on.
-/

@[expose] public section

namespace EthLib.Base

/-- A network upgrade of the execution layer, the consensus layer or both. -/
inductive Fork where
  /-- Frontier: the execution layer at its launch. -/
  | frontier
  /-- Homestead changes the execution layer.

  [EIP-606](https://eips.ethereum.org/EIPS/eip-606) lists its EIPs: EIP-2, EIP-7 and EIP-8. -/
  | homestead
  /-- The DAO Fork changes no rule of the execution layer.

  At its first block, the ether of a list of accounts moves to one contract.

  Its first ten blocks carry fixed extra data.

  [EIP-779](https://eips.ethereum.org/EIPS/eip-779) specifies both. -/
  | daoFork
  /-- Tangerine Whistle changes the execution layer.

  [EIP-608](https://eips.ethereum.org/EIPS/eip-608) lists its one EIP: EIP-150. -/
  | tangerineWhistle
  /-- Spurious Dragon changes the execution layer.

  [EIP-607](https://eips.ethereum.org/EIPS/eip-607) lists its EIPs.

  They are EIP-155, EIP-160, EIP-161 and EIP-170. -/
  | spuriousDragon
  /-- Byzantium changes the execution layer.

  [EIP-609](https://eips.ethereum.org/EIPS/eip-609) lists its EIPs.

  They are EIP-100, EIP-140, EIP-196 to EIP-198, EIP-211, EIP-214, EIP-649 and EIP-658. -/
  | byzantium
  /-- Constantinople changes the execution layer.

  [EIP-1013](https://eips.ethereum.org/EIPS/eip-1013) lists its EIPs.

  They are EIP-145, EIP-1014, EIP-1052, EIP-1234 and EIP-1283. -/
  | constantinople
  /-- Petersburg removes EIP-1283 from the execution layer.

  When it activates at the block of Constantinople, as on mainnet, Petersburg takes precedence.

  [EIP-1716](https://eips.ethereum.org/EIPS/eip-1716) specifies both. -/
  | petersburg
  /-- Istanbul changes the execution layer.

  [EIP-1679](https://eips.ethereum.org/EIPS/eip-1679) lists its EIPs.

  They are EIP-152, EIP-1108, EIP-1344, EIP-1884, EIP-2028 and EIP-2200. -/
  | istanbul
  /-- Muir Glacier only delays the difficulty bomb of the execution layer.

  [EIP-2387](https://eips.ethereum.org/EIPS/eip-2387) lists its one EIP: EIP-2384. -/
  | muirGlacier
  /-- Phase 0 launches the beacon chain, the first fork of the consensus layer.

  [EIP-2982](https://eips.ethereum.org/EIPS/eip-2982) describes it. -/
  | phase0
  /-- Berlin changes the execution layer.

  It includes EIP-2565, EIP-2718, EIP-2929 and EIP-2930. -/
  | berlin
  /-- London changes the execution layer.

  It includes EIP-1559, EIP-3198, EIP-3529, EIP-3541 and EIP-3554. -/
  | london
  /-- Altair changes the consensus layer.

  It adds sync committees, and it pays rewards by participation flags. -/
  | altair
  /-- Arrow Glacier only delays the difficulty bomb of the execution layer, by EIP-4345. -/
  | arrowGlacier
  /-- Gray Glacier only delays the difficulty bomb of the execution layer, by EIP-5133. -/
  | grayGlacier
  /-- Bellatrix changes the consensus layer: a beacon block carries an execution payload.

  It is the first half of the Merge. -/
  | bellatrix
  /-- Paris changes the execution layer, and it is the second half of the Merge.

  EIP-3675 ends proof of work, and EIP-4399 replaces DIFFICULTY with PREVRANDAO. -/
  | paris
  /-- Shapella, Shanghai with Capella, changes both layers.

  It adds the withdrawals of EIP-4895, with EIP-3651, EIP-3855, EIP-3860 and EIP-6049. -/
  | shapella
  /-- Dencun, Deneb with Cancun, changes both layers.

  [EIP-7569](https://eips.ethereum.org/EIPS/eip-7569) lists its EIPs.

  They include the blobs of EIP-4844, and EIP-1153, EIP-4788, EIP-5656 and EIP-6780. -/
  | dencun
  /-- Pectra, Prague with Electra, changes both layers.

  [EIP-7600](https://eips.ethereum.org/EIPS/eip-7600) lists its EIPs.

  They include EIP-2537, EIP-6110, EIP-7002, EIP-7251, EIP-7685 and EIP-7702. -/
  | pectra
  /-- Fusaka, Fulu with Osaka, changes both layers.

  [EIP-7607](https://eips.ethereum.org/EIPS/eip-7607) lists its EIPs.

  They include the data column sampling of EIP-7594, and EIP-7825, EIP-7918 and EIP-7951. -/
  | fusaka
  /-- BPO1 changes only the blob parameters, as EIP-7892 allows.

  [EIP-8134](https://eips.ethereum.org/EIPS/eip-8134) specifies it. -/
  | bpo1
  /-- BPO2 changes only the blob parameters, as EIP-7892 allows.

  [EIP-8135](https://eips.ethereum.org/EIPS/eip-8135) specifies it. -/
  | bpo2
  /-- Glamsterdam, Gloas with Amsterdam, changes both layers.

  [EIP-7773](https://eips.ethereum.org/EIPS/eip-7773) lists its EIPs.

  They include EIP-7732 and EIP-7928. -/
  | glamsterdam
  /-- Hegotá, Heze with Bogotá, changes both layers.

  [EIP-8081](https://eips.ethereum.org/EIPS/eip-8081) lists its EIPs.

  They include EIP-7805 and EIP-8141. -/
  | hegota
  deriving DecidableEq, Ord, Repr

namespace Fork

/-- A fork is before another when it comes earlier in the list. -/
instance : LT Fork := ⟨fun a b => a.ctorIdx < b.ctorIdx⟩

/-- A fork is at or before another when it comes no later in the list. -/
instance : LE Fork := ⟨fun a b => a.ctorIdx ≤ b.ctorIdx⟩

instance (a b : Fork) : Decidable (a < b) := Nat.decLt _ _

instance (a b : Fork) : Decidable (a ≤ b) := Nat.decLe _ _

end Fork

/-- A field that appears at fork `f`, in a type at fork `fork`.

It maps a proof of `f ≤ fork` to a value.

Before `f` no such proof exists, so the field has one value and holds nothing.

From `f` on, the field holds one value of `α`. -/
def Since (f fork : Fork) (α : Type) : Type := f ≤ fork → α

end EthLib.Base
