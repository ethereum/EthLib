module

public import EthLib.Cryptography.Bls.Fp
public import EthLib.Cryptography.Bls.Fr

/-!
# `G1`

The curve `E : y^2 = x^3 + 4` over `Fp`.

A point is a Jacobian triple `(X, Y, Z)`, for the affine point `(X / Z^2, Y / Z^3)`.

A triple `(X, Y, 0)` is the point at infinity.

Affine addition needs one inversion, which costs about `log p` multiplications.

Jacobian doubling and addition need none, and one inversion at the end gives the affine form.

The formulas are those of the explicit-formulas database, for short Weierstrass curves with `a = 0`:
<https://hyperelliptic.org/EFD/>

The code is generic in the base field, as for `Fp2`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- A G1 point in Jacobian projective coordinates.

`z = 0` is the point at infinity.

The base field is `Fp` unless stated. -/
structure G1 (F : Type := Fp) where
  x : F
  y : F
  z : F
deriving Inhabited, BEq, Repr

namespace G1

variable {F : Type} [BaseField F]

/-- The x-coordinate of the generator of G1, as an integer. -/
def generatorX : Nat :=
  0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb

/-- The y-coordinate of the generator of G1, as an integer. -/
def generatorY : Nat :=
  0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

/-- Affine generator of G1, embedded with `z = 1`. -/
def generator : G1 F := ⟨BaseField.ofNat generatorX, BaseField.ofNat generatorY, BaseField.one⟩

/-- The point at infinity. -/
def zero : G1 F := ⟨BaseField.one, BaseField.one, BaseField.zero⟩

@[inline] def isInfinity (p : G1 F) : Bool := BaseField.isZero p.z

/-- Jacobian point doubling for `a = 0` curves.

These are the `dbl-2009-l` formulas of the explicit-formulas database.

Each product by 2, 3 or 8 is written as additions, which are cheaper than a multiplication. -/
def double (p : G1 F) : G1 F :=
  if BaseField.isZero p.z then p else
    let A := p.x * p.x
    let B := p.y * p.y
    let C := B * B
    let t := (p.x + B) * (p.x + B) - A - C
    let D := t + t
    let E := A + A + A
    let F := E * E
    let x' := F - (D + D)
    -- 8 C as three doublings.
    let C2 := C + C
    let C4 := C2 + C2
    let y' := E * (D - x') - (C4 + C4)
    let z' := (p.y + p.y) * p.z
    ⟨x', y', z'⟩

/-- Negation: `(x, y, z) ↦ (x, −y, z)`. -/
@[inline] def neg (p : G1 F) : G1 F := ⟨p.x, -p.y, p.z⟩

/-- `p + q` for two finite points, by the `add-2007-bl` formulas of the explicit-formulas database.

Each product by 2 is written as an addition.

Equal points double, and opposite points sum to the point at infinity. -/
def addGeneral (p q : G1 F) : G1 F :=
  let z1z1 := p.z * p.z
  let z2z2 := q.z * q.z
  let u1 := p.x * z2z2
  let u2 := q.x * z1z1
  let s1 := p.y * q.z * z2z2
  let s2 := q.y * p.z * z1z1
  if BaseField.beq u1 u2 then
    if BaseField.beq s1 s2 then double p else zero
  else
    let h := u2 - u1
    let h2 := h + h
    let i := h2 * h2
    let j := h * i
    let r := (s2 - s1) + (s2 - s1)
    let v := u1 * i
    let x' := r * r - j - (v + v)
    let y' := r * (v - x') - (s1 + s1) * j
    let z' := ((p.z + q.z) * (p.z + q.z) - z1z1 - z2z2) * h
    ⟨x', y', z'⟩

/-- `p + q` for finite points where `q` has `z = 1`, by the `madd-2007-bl` formulas.

These are the general formulas with `z2 = 1`, so `u1 = x1` and `s1 = y1`.

The last coordinate `((z1 + 1)^2 - z1^2 - 1) * h` simplifies to `2 * z1 * h`.

They take 11 multiplications instead of 20, and give the same coordinates. -/
def addMixed (p q : G1 F) : G1 F :=
  let z1z1 := p.z * p.z
  let u2 := q.x * z1z1
  let s2 := q.y * p.z * z1z1
  if BaseField.beq p.x u2 then
    if BaseField.beq p.y s2 then double p else zero
  else
    let h := u2 - p.x
    let h2 := h + h
    let i := h2 * h2
    let j := h * i
    let r := (s2 - p.y) + (s2 - p.y)
    let v := p.x * i
    let x' := r * r - j - (v + v)
    let y' := r * (v - x') - (p.y + p.y) * j
    let z' := (p.z + p.z) * h
    ⟨x', y', z'⟩

/-- Jacobian addition. Handles all special cases (infinity, doubling, opposite-sign points).

Every point decompressed from bytes has `z = 1`, and then the mixed formulas apply.

So most additions in a multi-scalar multiplication take that shorter path. -/
def add (p q : G1 F) : G1 F :=
  if BaseField.isZero p.z then q else
  if BaseField.isZero q.z then p else
  if BaseField.beq q.z BaseField.one then addMixed p q else addGeneral p q

instance : Add (G1 F) := ⟨add⟩
instance : Neg (G1 F) := ⟨neg⟩

/-- Project a Jacobian point to affine `(x, y)`. Undefined at infinity. -/
def toAffine (p : G1 F) : F × F :=
  if BaseField.isZero p.z then (BaseField.zero, BaseField.zero)
  else
    let zinv  := BaseField.inverse p.z
    let zinv2 := zinv * zinv
    let zinv3 := zinv2 * zinv
    (p.x * zinv2, p.y * zinv3)

/-- Scalar multiplication via double-and-add. -/
def mulNat (p : G1 F) (k : Nat) : G1 F :=
  if k = 0 then zero
  else
    let half := mulNat (double p) (k / 2)
    if k % 2 = 1 then add p half else half
termination_by k
decreasing_by omega

@[inline] def mul (p : G1 F) (s : Fr) : G1 F := mulNat p s.val

/-! ## Multi-scalar multiplication

Pippenger's algorithm splits each scalar into 8-bit windows.

- Window `k` sums `v * B_v`, where `B_v` is the sum of the points whose digit `k` is `v`.
- The windows combine as `acc = 2^8 * acc + S_k`, from the top window down.

Each window's sum needs only the points and the scalars, so each one runs as its own task.
-/

/-- Window `k` of the value of a scalar: its bits `[8k, 8k + 8)`. -/
def windowVal (s : Nat) (k : Nat) : Nat := (s >>> (k * 8)) &&& (1 <<< 8 - 1)

/-- The largest bit length among the values of the first `n` scalars.

Windows above it are all zero, so they are skipped. -/
def msmMaxBits (vals : Array Nat) (n : Nat) : Nat :=
  (List.range' 0 n).foldl (fun m j =>
    if vals[j]! ≠ 0 then
      if vals[j]!.log2 + 1 > m then vals[j]!.log2 + 1 else m
    else m) 0

section Buckets

-- The buckets are arrays, and reading one needs a default point.
variable [Inhabited F]

/-- The buckets of window `k`: bucket `v` sums the points whose digit `k` is `v`.

Bucket 0 stays empty, since those points contribute nothing. -/
def msmBuckets (points : Array (G1 F)) (vals : Array Nat) (n k : Nat) : Array (G1 F) :=
  (List.range' 0 n).foldl (fun bs j =>
    if windowVal vals[j]! k ≠ 0 then
      bs.set! (windowVal vals[j]! k)
        (add bs[windowVal vals[j]! k]! points[j]!)
    else bs) (Array.replicate (1 <<< 8) zero)

/-- `sum_v v * B_v`, by the running-sum trick, walking `v` from 255 down to 1.

The state is `(partialSum, running)`.

The running sum holds `sum_{u >= v} B_u`.

Adding it at each step counts bucket `u` exactly `u` times. -/
def msmRunning (bs : Array (G1 F)) : MProd (G1 F) (G1 F) :=
  (List.range' 0 (1 <<< 8 - 1)).foldl (fun rp vv =>
    ⟨add rp.1 (add rp.2 bs[1 <<< 8 - 1 - vv]!),
     add rp.2 bs[1 <<< 8 - 1 - vv]!⟩) ⟨zero, zero⟩

/-- One step of the window fold: shift `acc` up by 8 bits, then add the window sum `S`.

The first step starts from zero and skips the doublings. -/
def msmCombine (nW : Nat) (acc : G1 F) (kk : Nat) (S : G1 F) : G1 F :=
  if nW - 1 - kk + 1 < nW then
    add ((List.range' 0 8).foldl (fun a _ => double a) acc) S
  else
    add acc S

/-- Multi-scalar multiplication `sum_j [scalars[j]] points[j]`, by Pippenger's algorithm.

The window sums are independent, so each runs as its own task.

The fold then combines them in order, from the top window down. -/
def msm (points : Array (G1 F)) (scalars : Array Fr) : G1 F :=
  let n := if points.size ≤ scalars.size then points.size else scalars.size
  -- Leaving Montgomery form costs a product, so each scalar is converted once, before the windows.
  let vals := scalars.map Fr.val
  if n = 0 then zero
  else if msmMaxBits vals n = 0 then zero
  else
    let nW := (msmMaxBits vals n + 8 - 1) / 8
    let windows := List.range' 0 nW
    -- The windows are spawned from a task of their own.
    -- Lean's pool starts a new worker only when no worker is idle.
    -- From outside the pool, a burst of windows can all land on one idle worker.
    -- From a busy worker, each window finds no idle worker, and the pool grows.
    (Task.spawn fun _ =>
      -- Spawn every window first, then wait for them in fold order.
      let sums := windows.map fun kk => Task.spawn fun _ =>
        (msmRunning (msmBuckets points vals n (nW - 1 - kk))).1
      (windows.zip sums).foldl (fun acc w => msmCombine nW acc w.1 w.2.get) zero).get

end Buckets

end G1

end EthLib.Cryptography.Bls
