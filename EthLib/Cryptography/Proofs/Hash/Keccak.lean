import EthLib.Cryptography.Hash.Keccak

/-!
# Proofs: `Hash.Keccak`

The constants of Keccak-f[1600] agree with the algorithms that define them, and the permutation agrees with the Keccak team's reference values.
-/

namespace EthLib.Cryptography.Hash.Keccak

/-! ## The constants -/

/-- The table of round constants is what FIPS 202 §3.2.5, Algorithm 6 derives.

So no round constant is taken on trust. -/
theorem roundConstants_eq : RC = Vector.ofFn fun ir => Internal.roundConstant ir := by
  -- 24 constants of 7 bits each, with at most 167 register steps per bit.
  decide +kernel

/-- The table of rotation offsets is what FIPS 202 §3.2.2, Algorithm 2 derives.

So no rotation offset is taken on trust. -/
theorem rhoOffsets_eq : RHO.map UInt64.toNat = Internal.rhoOffsets := by
  -- The walk of 24 steps, run by the kernel.
  decide +kernel

/-! ## Known answers

Both come from `KeccakF-1600-IntermediateValues.txt`, in the `tests/TestVectors/` directory of the Keccak team's XKCP repository.

That file applies Keccak-f[1600] twice:

```text
    all-zero state  --f-->  output 1  --f-->  output 2
```

Each theorem pins all 25 lanes, so every round, step mapping and constant is exercised. -/

/-- Output 1 of the reference file, lane `(x, y)` at index `x + 5 * y`. -/
def zeroOnce : State := #v[
  0xF1258F7940E1DDE7, 0x84D5CCF933C0478A, 0xD598261EA65AA9EE, 0xBD1547306F80494D, 0x8B284E056253D057,
  0xFF97A42D7F8E6FD4, 0x90FEE5A0A44647C4, 0x8C5BDA0CD6192E76, 0xAD30A6F71B19059C, 0x30935AB7D08FFC64,
  0xEB5AA93F2317D635, 0xA9A6E6260D712103, 0x81A57C16DBCF555F, 0x43B831CD0347C826, 0x01F22F1A11A5569F,
  0x05E5635A21D9AE61, 0x64BEFEF28CC970F2, 0x613670957BC46611, 0xB87C5A554FD00ECB, 0x8C3EE88A1CCF32C8,
  0x940C7922AE3A2614, 0x1841F924A2C509E4, 0x16F53526E70465C2, 0x75F644E97F30A13B, 0xEAF1FF7B5CECA249]

/-- Output 2 of the reference file, lane `(x, y)` at index `x + 5 * y`. -/
def zeroTwice : State := #v[
  0x2D5C954DF96ECB3C, 0x6A332CD07057B56D, 0x093D8D1270D76B6C, 0x8A20D9B25569D094, 0x4F9C4F99E5E7F156,
  0xF957B9A2DA65FB38, 0x85773DAE1275AF0D, 0xFAF4F247C3D810F7, 0x1F1B9EE6F79A8759, 0xE4FECC0FEE98B425,
  0x68CE61B6B9CE68A1, 0xDEEA66C4BA8F974F, 0x33C43D836EAFB1F5, 0xE00654042719DBD9, 0x7CF8A9F009831265,
  0xFD5449A6BF174743, 0x97DDAD33D8994B40, 0x48EAD5FC5D0BE774, 0xE3B8C8EE55B7B03C, 0x91A0226E649E42E9,
  0x900E3129E7BADD7B, 0x202A9EC5FAA3CCE8, 0x5B3402464E1C3DB6, 0x609F4E62A44C1059, 0x20D06CD26A8FBF5C]

/-- Keccak-f[1600] of the all-zero state. -/
theorem keccakF_zero : keccakF State.zero = zeroOnce := by
  -- 24 rounds on 25 lanes, evaluated by the kernel.
  decide +kernel

/-- Keccak-f[1600] of the previous output. -/
theorem keccakF_zeroOnce : keccakF zeroOnce = zeroTwice := by
  -- 24 rounds on 25 lanes, evaluated by the kernel.
  decide +kernel

end EthLib.Cryptography.Hash.Keccak
