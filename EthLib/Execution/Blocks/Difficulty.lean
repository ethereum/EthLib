module

public import EthLib.Base.Fork

/-!
# `Blocks.Difficulty`

The difficulty of a block before Paris, from its parent's difficulty and the time between them.

A block that comes soon after its parent raises the difficulty, and a late one lowers it.

The difficulty bomb adds a term that doubles every 100,000 blocks.

From Byzantium, the bomb reads a block number lowered by a delay, and later forks raise the delay.

From Paris on, the difficulty is 0.

Section 4.3.4 of the Yellow Paper, Berlin version, gives the rule from Byzantium: [`Paper.tex`][yp].

[EIP-2][eip-2] gives the Frontier rule and replaces it at Homestead.

[EIP-100][eip-100] counts the parent's ommers from Byzantium.

Section 4.3.4 also requires a block to be later than its parent, and the rule is for such blocks.

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[eip-2]: https://eips.ethereum.org/EIPS/eip-2#specification
[eip-100]: https://eips.ethereum.org/EIPS/eip-100#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base

/-- The least difficulty of a block before Paris: `D_min = 2^17` of the Yellow Paper, 4.3.4. -/
def MINIMUM_DIFFICULTY : Nat := 131072

/-- The parent's difficulty over this is the step by which the difficulty moves. -/
def DIFFICULTY_BOUND_DIVISOR : Nat := 2048

/-- The blocks in one period of the bomb, whose term doubles each period. -/
def BOMB_PERIOD : Nat := 100000

/-- The blocks by which a fork delays the bomb: `κ` of the Yellow Paper, 4.3.4.

- Frontier to Spurious Dragon: no delay.
- [EIP-649](https://eips.ethereum.org/EIPS/eip-649#specification), Byzantium: 3,000,000.
- [EIP-1234](https://eips.ethereum.org/EIPS/eip-1234#specification), Constantinople: 5,000,000.
- [EIP-2384](https://eips.ethereum.org/EIPS/eip-2384#specification), Muir Glacier: 9,000,000.
- [EIP-3554](https://eips.ethereum.org/EIPS/eip-3554#specification), London: 9,700,000.
- [EIP-4345](https://eips.ethereum.org/EIPS/eip-4345#specification), Arrow Glacier: 10,700,000.
- [EIP-5133](https://eips.ethereum.org/EIPS/eip-5133#specification), Gray Glacier: 11,400,000.

A fork keeps the delay of the last fork before it that set one.

From Paris on there is no bomb, and the delay is not read. -/
def bombDelay (fork : Fork) : Nat :=
  if fork < .byzantium then 0
  else if fork < .constantinople then 3000000
  else if fork < .muirGlacier then 5000000
  else if fork < .london then 9000000
  else if fork < .arrowGlacier then 9700000
  else if fork < .grayGlacier then 10700000
  else 11400000

/-- The bomb of a block: `ε = ⌊2^(⌊H'_i / 100000⌋ - 2)⌋` of the Yellow Paper, 4.3.4.

`H'_i` is the block number less the delay, or 0 below the delay.

The floor makes the term 0 while the exponent is negative, in the first two periods. -/
def bomb (fork : Fork) (number : Nat) : Nat :=
  -- Natural subtraction stops at 0, as `max(H_i - κ, 0)` does.
  let periods := (number - bombDelay fork) / BOMB_PERIOD
  if 2 ≤ periods then 2 ^ (periods - 2) else 0

/-- The factor of the step that the time since the parent gives, before the bomb.

- Frontier: 1 below 13 seconds, else -1 ([EIP-2][eip-2], Specification, item 4).
- Homestead: `max(1 - ⌊Δ / 10⌋, -99)` ([EIP-2][eip-2]).
- Byzantium on: `max(y - ⌊Δ / 9⌋, -99)`, with `y = 2` if the parent has ommers, else 1.

`Δ` is the time from the parent to the block, in seconds.

The last form is `ς_2` of the Yellow Paper, 4.3.4, and [EIP-100][eip-100] gives it.

[eip-2]: https://eips.ethereum.org/EIPS/eip-2#specification
[eip-100]: https://eips.ethereum.org/EIPS/eip-100#specification -/
def timeFactor (fork : Fork) (timestamp parentTimestamp : Nat) (parentHasOmmers : Bool) : Int :=
  -- A valid block is later than its parent, so `Δ` is positive.
  let elapsed : Int := timestamp - parentTimestamp
  if fork < .homestead then
    if timestamp < parentTimestamp + 13 then 1 else -1
  else if fork < .byzantium then
    max (1 - elapsed / 10) (-99)
  else
    max ((if parentHasOmmers then 2 else 1) - elapsed / 9) (-99)

/-- The difficulty of a block at a fork: `D(H)` of the Yellow Paper, 4.3.4, before Paris.

```text
    D(H) = max(D_min, P_d + ⌊P_d / 2048⌋ · factor + ε)
```

`P_d` is the parent's difficulty, and `ε` is the bomb.

The factor is the one of the time since the parent.

From Paris on, [EIP-3675](https://eips.ethereum.org/EIPS/eip-3675#block-structure) sets it to 0.

The genesis block has no parent, and its difficulty is part of the chain's configuration. -/
def blockDifficulty (fork : Fork) (number timestamp parentTimestamp parentDifficulty : Nat)
    (parentHasOmmers : Bool) : Nat :=
  if .paris ≤ fork then 0
  else
    let step : Int := parentDifficulty / DIFFICULTY_BOUND_DIVISOR
    let factor := timeFactor fork timestamp parentTimestamp parentHasOmmers
    -- The minimum applies after the bomb is added, as in the formula above.
    max MINIMUM_DIFFICULTY (parentDifficulty + step * factor + bomb fork number).toNat

end EthLib.Execution.Blocks
