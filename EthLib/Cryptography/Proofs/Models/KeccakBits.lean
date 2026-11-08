module

/-!
# Keccak on bits

The source is [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf).

FIPS 202 sections 3.1 to 3.4 define the state and permutation.

Section 4, Algorithm 8, defines the sponge.

Section 5.1, Algorithm 9, defines pad10*1.

Section 5.2 defines KECCAK[c].

Keccak-256 is KECCAK[512] with a 256-bit output.

Keccak-512 is KECCAK[1024] with a 512-bit output.

Appendix B.1 orders bits within each byte from least significant to most significant.

Keccak-256 and Keccak-512 pad the message bits with pad10*1 directly.

Neither hash appends the SHA-3 domain suffix of section 6.1.

The model imports nothing from the lane implementation, and it does not reuse its tables.

It is a model, so it lives in the proof library and no specification imports it.

The sponge proofs show that the lane implementation equals this model on every message.
-/

@[expose] public section
namespace EthLib.Cryptography.Models.KeccakBits

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

/-- Rho, FIPS 202 Algorithm 2: it rotates each lane by its offset. -/
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

/-- FIPS 202 Algorithm 9 at a positive rate of `rateBits` bits. -/
def padding (rateBits length : Nat) : List Bool :=
  true :: List.replicate ((rateBits - ((length + 2) % rateBits)) % rateBits) false ++ [true]

/-- The bits of a message followed by pad10*1 at a rate of `rateBits` bits. -/
def padded (rateBits : Nat) (msg : ByteArray) : List Bool :=
  let bits := messageBits msg
  bits ++ padding rateBits bits.length

/-- FIPS 202 section 3.1.2 linear state index. -/
def index (x y : Fin 5) (z : Fin 64) : Nat := 64 * (x.val + 5 * y.val) + z.val

/-- Each padded message has a whole number of rate-sized blocks, at any positive bit rate. -/
theorem padded_size_multiple {rateBits : Nat} (hr : 0 < rateBits) (msg : ByteArray) :
    (padded rateBits msg).length % rateBits = 0 := by
  simp only [padded, List.length_append, padding, List.length_cons,
    List.length_replicate, List.length_nil]
  let n := (messageBits msg).length + 2
  have hmod : n % rateBits < rateBits := Nat.mod_lt _ hr
  have hdiv := Nat.div_add_mod n rateBits
  by_cases h0 : n % rateBits = 0
  · have hlen : (messageBits msg).length +
        ((rateBits - n % rateBits) % rateBits + 1 + (0 + 1)) = rateBits * (n / rateBits) := by
      rw [h0, Nat.sub_zero, Nat.mod_self]
      omega
    rw [hlen, Nat.mul_mod_right]
  · have hsub : (rateBits - n % rateBits) % rateBits = rateBits - n % rateBits :=
      Nat.mod_eq_of_lt (by omega)
    have hlen : (messageBits msg).length +
        ((rateBits - n % rateBits) % rateBits + 1 + (0 + 1)) = rateBits * (n / rateBits + 1) := by
      rw [hsub, Nat.mul_add, Nat.mul_one]
      omega
    rw [hlen, Nat.mul_mod_right]

/-- A source block of `rateBits` bits. -/
abbrev Block (rateBits : Nat) := Vector Bool rateBits

/-- Extract complete block `i` from a message padded at `rateBits` bits. -/
def paddedBlock {rateBits : Nat} (hr : 0 < rateBits) (msg : ByteArray)
    (i : Fin ((padded rateBits msg).length / rateBits)) : Block rateBits :=
  Vector.ofFn fun j => (padded rateBits msg)[rateBits * i.val + j.val]'(by
    have hm := padded_size_multiple hr msg
    have hi := i.isLt
    have hj := j.isLt
    have hd := Nat.div_add_mod (padded rateBits msg).length rateBits
    have hmul : rateBits * (i.val + 1) ≤ rateBits * ((padded rateBits msg).length / rateBits) :=
      Nat.mul_le_mul_left rateBits hi
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega)

/-- XOR one `rateBits`-bit block into the state, leaving the capacity unchanged.

Bits at index 1600 and above are dropped, so the sponge requires a rate below 1600. -/
def absorb {rateBits : Nat} (a : State) (block : Block rateBits) : State := fun x y z =>
  let i := index x y z
  Bool.xor (a x y z) (if h : i < rateBits then block[i]'h else false)

/-- Absorb every complete block of a message padded at `rateBits` bits. -/
def absorbAll {rateBits : Nat} (hr : 0 < rateBits) (msg : ByteArray) : State :=
  (List.finRange ((padded rateBits msg).length / rateBits)).foldl
    (fun a i => permutation (absorb a (paddedBlock hr msg i)))
    (fun _ _ _ => false)

/-- The state bit at a linear index, modulo the state dimensions. -/
def stateBit (a : State) (i : Nat) : Bool :=
  a (xy ((i / 64) % 5)) (xy ((i / 64) / 5)) (zcoord i)

/-- Pack eight output bits into a byte, least significant bit first. -/
def outputByte (a : State) (i : Nat) : UInt8 :=
  UInt8.ofNat ((List.range 8).foldl (fun n j =>
    if stateBit a (8 * i + j) then n + 2 ^ j else n) 0)

/-- The first `outBytes` output bytes of a state, least significant bit first in each byte. -/
def squeezeBytes (outBytes : Nat) (a : State) : Vector UInt8 outBytes :=
  Vector.ofFn fun i => outputByte a i.val

/-- The sponge of FIPS 202 section 4, Algorithm 8, when `outBytes` fits in one rate block.

The rate is below the 1600-bit width, so the capacity is positive as section 5.2 requires. -/
def sponge {rateBits outBytes : Nat} (hr : 0 < rateBits) (_hb : rateBits < 1600)
    (_hout : 8 * outBytes ≤ rateBits) (msg : ByteArray) : Vector UInt8 outBytes :=
  squeezeBytes outBytes (absorbAll hr msg)

/-- Original Keccak-256, FIPS 202 sections 4 and 5.2, at the 1088-bit rate. -/
def keccak256 (msg : ByteArray) : Vector UInt8 32 :=
  sponge (rateBits := 1088) (by decide) (by decide) (by decide) msg

/-- Original Keccak-512, FIPS 202 sections 4 and 5.2, at the 576-bit rate. -/
def keccak512 (msg : ByteArray) : Vector UInt8 64 :=
  sponge (rateBits := 576) (by decide) (by decide) (by decide) msg

end EthLib.Cryptography.Models.KeccakBits
