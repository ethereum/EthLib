module

public import EthLib.Cryptography.Hash.Keccak

/-!
# Keccak-256 on bits

FIPS 202 sections 3.1 to 3.4 define the state and permutation.
Section 4, Algorithm 8, defines the sponge.
Section 5.1, Algorithm 9, defines pad10*1.
Section 5.2 defines Keccak[512].
Appendix B.1 orders bits within each byte from least significant to most significant.
The Keccak reference, version 3.0, section 1.1.2 defines the original multi-rate padding.
This is the original Keccak-256 input, without the SHA3-256 suffix from FIPS 202 section 6.1.

This independent bit model does not use the lane permutation or sponge implementation.
Its refinement to the executable hash is proved in the separate proof library.
-/

@[expose] public section
namespace EthLib.Cryptography.Hash.KeccakBits

/-- One bit at each bounded Keccak state coordinate. -/
abbrev State := Fin 5 → Fin 5 → Fin 64 → Bool

/-- Wrap an x or y coordinate. -/
def xy (n : Nat) : Fin 5 := ⟨n % 5, Nat.mod_lt _ (by decide)⟩

/-- Wrap a bit coordinate within a lane. -/
def zcoord (n : Nat) : Fin 64 := ⟨n % 64, Nat.mod_lt _ (by decide)⟩

/-- Theta column parity, FIPS 202 Algorithm 1, step 1. -/
def column (a : State) (x : Fin 5) (z : Fin 64) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (Bool.xor (a x 0 z) (a x 1 z)) (a x 2 z)) (a x 3 z)) (a x 4 z)

/-- Theta, FIPS 202 Algorithm 1. -/
def theta (a : State) : State := fun x y z =>
  Bool.xor (a x y z)
    (Bool.xor (column a (xy (x.val + 4)) z)
      (column a (xy (x.val + 1)) (zcoord (z.val + 63))))

/-- Position visited by the rho walk after `steps` applications.

The function accepts any natural number of steps.
FIPS 202 Algorithm 2 uses the first 24 positions.
-/
def rhoPosition (steps : Nat) : Nat × Nat :=
  (List.range steps).foldl (fun p _ => (p.2, (2 * p.1 + 3 * p.2) % 5)) (1, 0)

/-- The offset assigned by the 24-step rho walk, FIPS 202 Algorithm 2. -/
def rhoOffset (x y : Fin 5) : Nat :=
  (List.range 24).foldl (fun offset t =>
    if rhoPosition t = (x.val, y.val) then ((t + 1) * (t + 2) / 2) % 64 else offset) 0

/-- Rho reads the bit displaced by the lane's source-defined offset. -/
def rho (a : State) : State := fun x y z =>
  a x y (zcoord (z.val + 64 - rhoOffset x y))

/-- Pi, FIPS 202 Algorithm 3. -/
def pi (a : State) : State := fun x y z => a (xy (x.val + 3 * y.val)) x z

/-- Chi, FIPS 202 Algorithm 4. -/
def chi (a : State) : State := fun x y z =>
  Bool.xor (a x y z) ((!a (xy (x.val + 1)) y z) && a (xy (x.val + 2)) y z)

/-- The eight register bits used by FIPS 202 Algorithm 5. -/
abbrev Register := Fin 8 → Bool

/-- One register update, with the outgoing bit fed into positions 0, 4, 5 and 6. -/
def registerStep (r : Register) : Register := fun i =>
  let shifted := if i.val = 0 then false else r ⟨i.val - 1, by omega⟩
  if i.val = 0 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 then Bool.xor shifted (r 7)
  else shifted

/-- The FIPS 202 Algorithm 5 round-constant bit, with the index reduced modulo 255. -/
def rc (t : Nat) : Bool :=
  ((List.range (t % 255)).foldl (fun r _ => registerStep r)
    (fun i => i.val == 0)) 0

/-- A bit of the round constant, FIPS 202 Algorithm 6, steps 2 and 3. -/
def roundConstantBit (round : Nat) (z : Fin 64) : Bool :=
  (List.range 7).foldl (fun bit j =>
    if z.val = 2 ^ j - 1 then rc (j + 7 * round) else bit) false

/-- Iota, FIPS 202 Algorithm 6.

The function accepts any natural round index.
Keccak-f[1600] uses indices 0 through 23.
-/
def iota (round : Nat) (a : State) : State := fun x y z =>
  if x.val = 0 ∧ y.val = 0 then Bool.xor (a x y z) (roundConstantBit round z)
  else a x y z

/-- One round, FIPS 202 section 3.3. -/
def round (ir : Nat) (a : State) : State := iota ir (chi (pi (rho (theta a))))

/-- Keccak-f[1600], FIPS 202 section 3.4. -/
def permutation (a : State) : State :=
  (List.range 24).foldl (fun state ir => round ir state) a

/-- Bits of a byte in FIPS 202 Appendix B.1 order. -/
def byteBits (byte : UInt8) : List Bool :=
  (List.range 8).map (fun i => byte.toNat.testBit i)

/-- The bits of a byte string, in increasing byte and bit order. -/
def messageBits (msg : ByteArray) : List Bool := msg.data.toList.flatMap byteBits

/-- FIPS 202 Algorithm 9 at the 1088-bit rate. -/
def padding (length : Nat) : List Bool :=
  true :: List.replicate ((1088 - ((length + 2) % 1088)) % 1088) false ++ [true]

/-- The original Keccak message and its multi-rate padding. -/
def padded (msg : ByteArray) : List Bool :=
  let bits := messageBits msg
  bits ++ padding bits.length

/-- FIPS 202 section 3.1.2 linear state index. -/
def index (x y : Fin 5) (z : Fin 64) : Nat := 64 * (x.val + 5 * y.val) + z.val

/-- Each padded message has a whole number of rate-sized blocks. -/
theorem padded_size_multiple (msg : ByteArray) : (padded msg).length % 1088 = 0 := by
  simp only [padded, List.length_append, padding, List.length_cons,
    List.length_replicate, List.length_nil]
  have h : ((messageBits msg).length + 2) % 1088 < 1088 := Nat.mod_lt _ (by decide)
  omega

/-- A rate-sized source block. -/
abbrev Block := Vector Bool 1088

/-- Extract a complete block from a padded message. -/
def paddedBlock (msg : ByteArray) (i : Fin ((padded msg).length / 1088)) : Block :=
  Vector.ofFn fun j => (padded msg)[1088 * i.val + j.val]'(by
    have hm := padded_size_multiple msg
    have hi := i.isLt
    have hj := j.isLt
    omega)

/-- XOR one rate-sized block into the state, leaving the capacity unchanged. -/
def absorb (a : State) (block : Block) : State := fun x y z =>
  let i := index x y z
  Bool.xor (a x y z) (if h : i < 1088 then block[i]'h else false)

/-- Absorb every complete rate-sized block of a padded message. -/
def absorbAll (msg : ByteArray) : State :=
  (List.finRange ((padded msg).length / 1088)).foldl
    (fun a i => permutation (absorb a (paddedBlock msg i)))
    (fun _ _ _ => false)

/-- The state bit at a linear index, modulo the state dimensions. -/
def stateBit (a : State) (i : Nat) : Bool :=
  a (xy ((i / 64) % 5)) (xy ((i / 64) / 5)) (zcoord i)

/-- Pack eight output bits into a byte, least significant bit first. -/
def outputByte (a : State) (i : Nat) : UInt8 :=
  UInt8.ofNat ((List.range 8).foldl (fun n j =>
    if stateBit a (8 * i + j) then n + 2 ^ j else n) 0)

/-- Original Keccak-256, FIPS 202 sections 4 and 5.2. -/
def keccak256 (msg : ByteArray) : Vector UInt8 32 :=
  let a := absorbAll msg
  Vector.ofFn fun i => outputByte a i.val

end EthLib.Cryptography.Hash.KeccakBits
