import EthLib.Cryptography.Bls.Fp
import EthLib.Cryptography.Bls.Fr

/-!
# `G1`

The curve `E : y² = x³ + 4` over `Fp`. We represent points in **Jacobian
projective** coordinates `(X, Y, Z)` with the affine map `(x, y) =
(X/Z², Y/Z³)`. The point at infinity is encoded as any `(X, Y, 0)`.

Why projective? Affine arithmetic needs an inversion per addition,
which costs `O(log p)` muls. Jacobian doubling/adding is inversion-free,
just polynomial in the coordinates. We pay one inversion at the end
when we serialize.

Arithmetic formulas are the textbook ones from Bernstein–Lange's
[explicit-formulas database](https://hyperelliptic.org/EFD/) for short
Weierstrass curves with `a = 0`.
-/

namespace EthLib.Cryptography.Bls

/-- A G1 point in Jacobian projective coordinates. `z = 0` is the
point at infinity. -/
structure G1 where
  x : Fp
  y : Fp
  z : Fp
deriving Inhabited, BEq, Repr

namespace G1

/-- Affine generator of G1, embedded with `z = 1`. -/
def generator : G1 :=
  { x := Fp.ofNat 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
  , y := Fp.ofNat 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1
  , z := Fp.one }

/-- The point at infinity. -/
def zero : G1 := ⟨Fp.one, Fp.one, Fp.zero⟩

@[inline] def isInfinity (p : G1) : Bool := p.z.isZero

/-- Jacobian point doubling for `a = 0` curves.

These are the `dbl-2009-l` formulas of the explicit-formulas database.

Each product by 2, 3 or 8 is written as additions, which are cheaper than a multiplication. -/
def double (p : G1) : G1 :=
  if p.z.isZero then p else
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
@[inline] def neg (p : G1) : G1 := ⟨p.x, -p.y, p.z⟩

/-- `p + q` for two finite points, by the `add-2007-bl` formulas of the explicit-formulas database.

Each product by 2 is written as an addition.

Equal points double, and opposite points sum to the point at infinity. -/
def addGeneral (p q : G1) : G1 :=
  let z1z1 := p.z * p.z
  let z2z2 := q.z * q.z
  let u1 := p.x * z2z2
  let u2 := q.x * z1z1
  let s1 := p.y * q.z * z2z2
  let s2 := q.y * p.z * z1z1
  if u1.beq u2 then
    if s1.beq s2 then double p else zero
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
def addMixed (p q : G1) : G1 :=
  let z1z1 := p.z * p.z
  let u2 := q.x * z1z1
  let s2 := q.y * p.z * z1z1
  if p.x.beq u2 then
    if p.y.beq s2 then double p else zero
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
def add (p q : G1) : G1 :=
  if p.z.isZero then q else
  if q.z.isZero then p else
  if q.z.beq Fp.one then addMixed p q else addGeneral p q

instance : Add G1 := ⟨add⟩
instance : Neg G1 := ⟨neg⟩

/-- Project a Jacobian point to affine `(x, y)`. Undefined at infinity. -/
def toAffine (p : G1) : Fp × Fp :=
  if p.z.isZero then (Fp.zero, Fp.zero)
  else
    let zinv  := p.z.inverse
    let zinv2 := zinv * zinv
    let zinv3 := zinv2 * zinv
    (p.x * zinv2, p.y * zinv3)

/-- Scalar multiplication via double-and-add. -/
def mulNat (p : G1) (k : Nat) : G1 :=
  if k = 0 then zero
  else
    let half := mulNat (double p) (k / 2)
    if k % 2 = 1 then add p half else half
termination_by k
decreasing_by omega

@[inline] def mul (p : G1) (s : Fr) : G1 := mulNat p s.val

/-! ## Multi-scalar multiplication

Pippenger's algorithm splits each scalar into 8-bit windows.

```text
    window k   : sum_v v * B_v,  B_v = the sum of the points whose digit k is v     independent of other windows
    combine    : acc = 2^8 * acc + S_k, from the top window down
```

Each window's sum needs only the points and the scalars, so each one runs as its own task.
-/

/-- Window `k` of a scalar: bits `[8k, 8k + 8)` of its value. -/
def windowVal (s : Fr) (k : Nat) : Nat := (s.val >>> (k * 8)) &&& (1 <<< 8 - 1)

/-- The largest bit length among the first `n` scalars.

Windows above it are all zero, so they are skipped. -/
def msmMaxBits (scalars : Array Fr) (n : Nat) : Nat :=
  (List.range' 0 n).foldl (fun m j =>
    if scalars[j]!.val ≠ 0 then
      if scalars[j]!.val.log2 + 1 > m then scalars[j]!.val.log2 + 1 else m
    else m) 0

/-- The buckets of window `k`: bucket `v` sums the points whose digit `k` is `v`.

Bucket 0 stays empty, since those points contribute nothing. -/
def msmBuckets (points : Array G1) (scalars : Array Fr) (n k : Nat) : Array G1 :=
  (List.range' 0 n).foldl (fun bs j =>
    if windowVal scalars[j]! k ≠ 0 then
      bs.set! (windowVal scalars[j]! k)
        (add bs[windowVal scalars[j]! k]! points[j]!)
    else bs) (Array.replicate (1 <<< 8) zero)

/-- `sum_v v * B_v`, by the running-sum trick, walking `v` from 255 down to 1.

The state is `(partialSum, running)`.

`running` holds `sum_{u >= v} B_u`, and adding it at each step counts bucket `u` exactly `u` times. -/
def msmRunning (bs : Array G1) : MProd G1 G1 :=
  (List.range' 0 (1 <<< 8 - 1)).foldl (fun rp vv =>
    ⟨add rp.1 (add rp.2 bs[1 <<< 8 - 1 - vv]!),
     add rp.2 bs[1 <<< 8 - 1 - vv]!⟩) ⟨zero, zero⟩

/-- One step of the window fold: shift `acc` up by 8 bits, then add the window sum `S`.

The first step starts from zero and skips the doublings. -/
def msmCombine (nW : Nat) (acc : G1) (kk : Nat) (S : G1) : G1 :=
  if nW - 1 - kk + 1 < nW then
    add ((List.range' 0 8).foldl (fun a _ => double a) acc) S
  else
    add acc S

/-- Multi-scalar multiplication `sum_j [scalars[j]] points[j]`, by Pippenger's algorithm.

The window sums are independent, so each runs as its own task.

The fold then combines them in order, from the top window down. -/
def msm (points : Array G1) (scalars : Array Fr) : G1 :=
  let n := if points.size ≤ scalars.size then points.size else scalars.size
  if n = 0 then zero
  else if msmMaxBits scalars n = 0 then zero
  else
    let nW := (msmMaxBits scalars n + 8 - 1) / 8
    let windows := List.range' 0 nW
    -- The windows are spawned from a task of their own.
    -- Lean's pool starts a new worker only when no worker is idle.
    -- From outside the pool, a burst of windows can all land on one idle worker.
    -- From a busy worker, each window finds no idle worker, and the pool grows.
    (Task.spawn fun _ =>
      -- Spawn every window first, then wait for them in fold order.
      let sums := windows.map fun kk => Task.spawn fun _ =>
        (msmRunning (msmBuckets points scalars n (nW - 1 - kk))).1
      (windows.zip sums).foldl (fun acc w => msmCombine nW acc w.1 w.2.get) zero).get

end G1

end EthLib.Cryptography.Bls
