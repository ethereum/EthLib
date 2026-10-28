import EthLib.Cryptography.Hash.Keccak

/-!
# Proofs: a fast form of Keccak-f for the kernel

A known answer over Keccak is checked by the kernel, which evaluates the hash term by term.

The specification keeps the 25 lanes in a vector, as FIPS 202 writes them.

The kernel reads a vector by walking a list, so one permutation costs it seconds and close to a gigabyte.

This file states the same permutation with one record field per lane.

```text
    vector of 25 lanes   -->   record with fields a0 .. a24
    each step mapping     =    the same step mapping, lane by lane
    Keccak-f[1600]        =    the record permutation, for every state
```

The equalities are proved once, for every state.

A known answer rewrites its permutation to the fast form, then lets the kernel evaluate it.
-/

namespace EthLib.Cryptography.Hash.Keccak

namespace Kernel

/-- The 25 lanes of the state, lane `(x, y)` in field `a_(x + 5y)`. -/
structure Lanes where
  (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : UInt64)

/-- The record of a state's lanes. -/
def Lanes.ofVector (A : State) : Lanes :=
  ⟨A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9], A[10], A[11], A[12], A[13], A[14], A[15], A[16], A[17], A[18], A[19], A[20], A[21], A[22], A[23], A[24]⟩

/-- The state of a record's lanes. -/
def Lanes.toVector (s : Lanes) : State :=
  #v[s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13, s.a14, s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

/-- A state is the vector of its record. -/
theorem toVector_ofVector (A : State) : (Lanes.ofVector A).toVector = A := by
  apply Vector.ext
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | _ + 25, hi => exact absurd hi (by simp [LANES])

/-- A record is the record of its vector. -/
theorem ofVector_toVector (s : Lanes) : Lanes.ofVector s.toVector = s := rfl

/-! ## The step mappings, lane by lane

Each is the FIPS 202 §3.2 step mapping of the same name, written out for the 25 lanes. -/

/-- Theta: each lane XORs the column effect `D[x] = C[x - 1] ^ rot(C[x + 1], 1)`. -/
def theta (s : Lanes) : Lanes :=
  -- The parity `C[x]` of each column, then the column effect `D[x]`.
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  ⟨s.a0 ^^^ d0,
   s.a1 ^^^ d1,
   s.a2 ^^^ d2,
   s.a3 ^^^ d3,
   s.a4 ^^^ d4,
   s.a5 ^^^ d0,
   s.a6 ^^^ d1,
   s.a7 ^^^ d2,
   s.a8 ^^^ d3,
   s.a9 ^^^ d4,
   s.a10 ^^^ d0,
   s.a11 ^^^ d1,
   s.a12 ^^^ d2,
   s.a13 ^^^ d3,
   s.a14 ^^^ d4,
   s.a15 ^^^ d0,
   s.a16 ^^^ d1,
   s.a17 ^^^ d2,
   s.a18 ^^^ d3,
   s.a19 ^^^ d4,
   s.a20 ^^^ d0,
   s.a21 ^^^ d1,
   s.a22 ^^^ d2,
   s.a23 ^^^ d3,
   s.a24 ^^^ d4⟩

/-- Rho: each lane rotates by its own offset. -/
def rho (s : Lanes) : Lanes :=
  ⟨rotl s.a0 0,
   rotl s.a1 1,
   rotl s.a2 62,
   rotl s.a3 28,
   rotl s.a4 27,
   rotl s.a5 36,
   rotl s.a6 44,
   rotl s.a7 6,
   rotl s.a8 55,
   rotl s.a9 20,
   rotl s.a10 3,
   rotl s.a11 10,
   rotl s.a12 43,
   rotl s.a13 25,
   rotl s.a14 39,
   rotl s.a15 41,
   rotl s.a16 45,
   rotl s.a17 15,
   rotl s.a18 21,
   rotl s.a19 8,
   rotl s.a20 18,
   rotl s.a21 2,
   rotl s.a22 61,
   rotl s.a23 56,
   rotl s.a24 14⟩

/-- Pi: lane `(x + 3y mod 5, x)` moves to `(x, y)`. -/
def pi (s : Lanes) : Lanes :=
  ⟨s.a0,
   s.a6,
   s.a12,
   s.a18,
   s.a24,
   s.a3,
   s.a9,
   s.a10,
   s.a16,
   s.a22,
   s.a1,
   s.a7,
   s.a13,
   s.a19,
   s.a20,
   s.a4,
   s.a5,
   s.a11,
   s.a17,
   s.a23,
   s.a2,
   s.a8,
   s.a14,
   s.a15,
   s.a21⟩

/-- Chi: each lane XORs the next lane of its row, complemented, ANDed with the one after. -/
def chi (s : Lanes) : Lanes :=
  ⟨s.a0 ^^^ (~~~s.a1 &&& s.a2),
   s.a1 ^^^ (~~~s.a2 &&& s.a3),
   s.a2 ^^^ (~~~s.a3 &&& s.a4),
   s.a3 ^^^ (~~~s.a4 &&& s.a0),
   s.a4 ^^^ (~~~s.a0 &&& s.a1),
   s.a5 ^^^ (~~~s.a6 &&& s.a7),
   s.a6 ^^^ (~~~s.a7 &&& s.a8),
   s.a7 ^^^ (~~~s.a8 &&& s.a9),
   s.a8 ^^^ (~~~s.a9 &&& s.a5),
   s.a9 ^^^ (~~~s.a5 &&& s.a6),
   s.a10 ^^^ (~~~s.a11 &&& s.a12),
   s.a11 ^^^ (~~~s.a12 &&& s.a13),
   s.a12 ^^^ (~~~s.a13 &&& s.a14),
   s.a13 ^^^ (~~~s.a14 &&& s.a10),
   s.a14 ^^^ (~~~s.a10 &&& s.a11),
   s.a15 ^^^ (~~~s.a16 &&& s.a17),
   s.a16 ^^^ (~~~s.a17 &&& s.a18),
   s.a17 ^^^ (~~~s.a18 &&& s.a19),
   s.a18 ^^^ (~~~s.a19 &&& s.a15),
   s.a19 ^^^ (~~~s.a15 &&& s.a16),
   s.a20 ^^^ (~~~s.a21 &&& s.a22),
   s.a21 ^^^ (~~~s.a22 &&& s.a23),
   s.a22 ^^^ (~~~s.a23 &&& s.a24),
   s.a23 ^^^ (~~~s.a24 &&& s.a20),
   s.a24 ^^^ (~~~s.a20 &&& s.a21)⟩

/-- Iota: the round constant enters lane `(0, 0)`. -/
def iota (rc : UInt64) (s : Lanes) : Lanes :=
  { s with a0 := s.a0 ^^^ rc }

/-- One round of FIPS 202 §3.3 on the record, with the round constant given. -/
def round (rc : UInt64) (s : Lanes) : Lanes :=
  iota rc (chi (pi (rho (theta s))))

/-- Keccak-f[1600] on the record: the 24 rounds in order. -/
def keccakF (s : Lanes) : Lanes :=
  (List.finRange ROUNDS).foldl (fun s ir => round RC[ir] s) s

/-! ## The record form is the specification

These name each lane and each offset by its index, for the lane-by-lane proofs. -/

private theorem toVector_0 (s : Lanes) : s.toVector[0] = s.a0 := rfl
private theorem toVector_1 (s : Lanes) : s.toVector[1] = s.a1 := rfl
private theorem toVector_2 (s : Lanes) : s.toVector[2] = s.a2 := rfl
private theorem toVector_3 (s : Lanes) : s.toVector[3] = s.a3 := rfl
private theorem toVector_4 (s : Lanes) : s.toVector[4] = s.a4 := rfl
private theorem toVector_5 (s : Lanes) : s.toVector[5] = s.a5 := rfl
private theorem toVector_6 (s : Lanes) : s.toVector[6] = s.a6 := rfl
private theorem toVector_7 (s : Lanes) : s.toVector[7] = s.a7 := rfl
private theorem toVector_8 (s : Lanes) : s.toVector[8] = s.a8 := rfl
private theorem toVector_9 (s : Lanes) : s.toVector[9] = s.a9 := rfl
private theorem toVector_10 (s : Lanes) : s.toVector[10] = s.a10 := rfl
private theorem toVector_11 (s : Lanes) : s.toVector[11] = s.a11 := rfl
private theorem toVector_12 (s : Lanes) : s.toVector[12] = s.a12 := rfl
private theorem toVector_13 (s : Lanes) : s.toVector[13] = s.a13 := rfl
private theorem toVector_14 (s : Lanes) : s.toVector[14] = s.a14 := rfl
private theorem toVector_15 (s : Lanes) : s.toVector[15] = s.a15 := rfl
private theorem toVector_16 (s : Lanes) : s.toVector[16] = s.a16 := rfl
private theorem toVector_17 (s : Lanes) : s.toVector[17] = s.a17 := rfl
private theorem toVector_18 (s : Lanes) : s.toVector[18] = s.a18 := rfl
private theorem toVector_19 (s : Lanes) : s.toVector[19] = s.a19 := rfl
private theorem toVector_20 (s : Lanes) : s.toVector[20] = s.a20 := rfl
private theorem toVector_21 (s : Lanes) : s.toVector[21] = s.a21 := rfl
private theorem toVector_22 (s : Lanes) : s.toVector[22] = s.a22 := rfl
private theorem toVector_23 (s : Lanes) : s.toVector[23] = s.a23 := rfl
private theorem toVector_24 (s : Lanes) : s.toVector[24] = s.a24 := rfl

private theorem ofVector_0 (A : State) : (Lanes.ofVector A).a0 = A[0] := rfl
private theorem ofVector_1 (A : State) : (Lanes.ofVector A).a1 = A[1] := rfl
private theorem ofVector_2 (A : State) : (Lanes.ofVector A).a2 = A[2] := rfl
private theorem ofVector_3 (A : State) : (Lanes.ofVector A).a3 = A[3] := rfl
private theorem ofVector_4 (A : State) : (Lanes.ofVector A).a4 = A[4] := rfl
private theorem ofVector_5 (A : State) : (Lanes.ofVector A).a5 = A[5] := rfl
private theorem ofVector_6 (A : State) : (Lanes.ofVector A).a6 = A[6] := rfl
private theorem ofVector_7 (A : State) : (Lanes.ofVector A).a7 = A[7] := rfl
private theorem ofVector_8 (A : State) : (Lanes.ofVector A).a8 = A[8] := rfl
private theorem ofVector_9 (A : State) : (Lanes.ofVector A).a9 = A[9] := rfl
private theorem ofVector_10 (A : State) : (Lanes.ofVector A).a10 = A[10] := rfl
private theorem ofVector_11 (A : State) : (Lanes.ofVector A).a11 = A[11] := rfl
private theorem ofVector_12 (A : State) : (Lanes.ofVector A).a12 = A[12] := rfl
private theorem ofVector_13 (A : State) : (Lanes.ofVector A).a13 = A[13] := rfl
private theorem ofVector_14 (A : State) : (Lanes.ofVector A).a14 = A[14] := rfl
private theorem ofVector_15 (A : State) : (Lanes.ofVector A).a15 = A[15] := rfl
private theorem ofVector_16 (A : State) : (Lanes.ofVector A).a16 = A[16] := rfl
private theorem ofVector_17 (A : State) : (Lanes.ofVector A).a17 = A[17] := rfl
private theorem ofVector_18 (A : State) : (Lanes.ofVector A).a18 = A[18] := rfl
private theorem ofVector_19 (A : State) : (Lanes.ofVector A).a19 = A[19] := rfl
private theorem ofVector_20 (A : State) : (Lanes.ofVector A).a20 = A[20] := rfl
private theorem ofVector_21 (A : State) : (Lanes.ofVector A).a21 = A[21] := rfl
private theorem ofVector_22 (A : State) : (Lanes.ofVector A).a22 = A[22] := rfl
private theorem ofVector_23 (A : State) : (Lanes.ofVector A).a23 = A[23] := rfl
private theorem ofVector_24 (A : State) : (Lanes.ofVector A).a24 = A[24] := rfl

private theorem rho_0 : RHO[0] = 0 := rfl
private theorem rho_1 : RHO[1] = 1 := rfl
private theorem rho_2 : RHO[2] = 62 := rfl
private theorem rho_3 : RHO[3] = 28 := rfl
private theorem rho_4 : RHO[4] = 27 := rfl
private theorem rho_5 : RHO[5] = 36 := rfl
private theorem rho_6 : RHO[6] = 44 := rfl
private theorem rho_7 : RHO[7] = 6 := rfl
private theorem rho_8 : RHO[8] = 55 := rfl
private theorem rho_9 : RHO[9] = 20 := rfl
private theorem rho_10 : RHO[10] = 3 := rfl
private theorem rho_11 : RHO[11] = 10 := rfl
private theorem rho_12 : RHO[12] = 43 := rfl
private theorem rho_13 : RHO[13] = 25 := rfl
private theorem rho_14 : RHO[14] = 39 := rfl
private theorem rho_15 : RHO[15] = 41 := rfl
private theorem rho_16 : RHO[16] = 45 := rfl
private theorem rho_17 : RHO[17] = 15 := rfl
private theorem rho_18 : RHO[18] = 21 := rfl
private theorem rho_19 : RHO[19] = 8 := rfl
private theorem rho_20 : RHO[20] = 18 := rfl
private theorem rho_21 : RHO[21] = 2 := rfl
private theorem rho_22 : RHO[22] = 61 := rfl
private theorem rho_23 : RHO[23] = 56 := rfl
private theorem rho_24 : RHO[24] = 14 := rfl

attribute [local simp] toVector_0 toVector_1 toVector_2 toVector_3 toVector_4 toVector_5 toVector_6 toVector_7 toVector_8 toVector_9 toVector_10 toVector_11 toVector_12 toVector_13 toVector_14 toVector_15 toVector_16 toVector_17 toVector_18 toVector_19 toVector_20 toVector_21 toVector_22 toVector_23 toVector_24 ofVector_0 ofVector_1 ofVector_2 ofVector_3 ofVector_4 ofVector_5 ofVector_6 ofVector_7 ofVector_8 ofVector_9 ofVector_10 ofVector_11 ofVector_12 ofVector_13 ofVector_14 ofVector_15 ofVector_16 ofVector_17 ofVector_18 ofVector_19 ofVector_20 ofVector_21 ofVector_22 ofVector_23 ofVector_24 rho_0 rho_1 rho_2 rho_3 rho_4 rho_5 rho_6 rho_7 rho_8 rho_9 rho_10 rho_11 rho_12 rho_13 rho_14 rho_15 rho_16 rho_17 rho_18 rho_19 rho_20 rho_21 rho_22 rho_23 rho_24

/-- Theta on the record is Theta on the vector. -/
theorem theta_eq (A : State) : Keccak.theta A = (theta (Lanes.ofVector A)).toVector := by
  apply Vector.ext
  intro i hi
  -- One lane at a time: both sides unfold to the same expression in the input lanes.
  match i, hi with
  | 0, _ => simp [Keccak.theta, theta, lane]
  | 1, _ => simp [Keccak.theta, theta, lane]
  | 2, _ => simp [Keccak.theta, theta, lane]
  | 3, _ => simp [Keccak.theta, theta, lane]
  | 4, _ => simp [Keccak.theta, theta, lane]
  | 5, _ => simp [Keccak.theta, theta, lane]
  | 6, _ => simp [Keccak.theta, theta, lane]
  | 7, _ => simp [Keccak.theta, theta, lane]
  | 8, _ => simp [Keccak.theta, theta, lane]
  | 9, _ => simp [Keccak.theta, theta, lane]
  | 10, _ => simp [Keccak.theta, theta, lane]
  | 11, _ => simp [Keccak.theta, theta, lane]
  | 12, _ => simp [Keccak.theta, theta, lane]
  | 13, _ => simp [Keccak.theta, theta, lane]
  | 14, _ => simp [Keccak.theta, theta, lane]
  | 15, _ => simp [Keccak.theta, theta, lane]
  | 16, _ => simp [Keccak.theta, theta, lane]
  | 17, _ => simp [Keccak.theta, theta, lane]
  | 18, _ => simp [Keccak.theta, theta, lane]
  | 19, _ => simp [Keccak.theta, theta, lane]
  | 20, _ => simp [Keccak.theta, theta, lane]
  | 21, _ => simp [Keccak.theta, theta, lane]
  | 22, _ => simp [Keccak.theta, theta, lane]
  | 23, _ => simp [Keccak.theta, theta, lane]
  | 24, _ => simp [Keccak.theta, theta, lane]
  | _ + 25, hi => exact absurd hi (by simp [LANES])

/-- Rho on the record is Rho on the vector. -/
theorem rho_eq (A : State) : Keccak.rho A = (rho (Lanes.ofVector A)).toVector := by
  apply Vector.ext
  intro i hi
  -- One lane at a time: both sides unfold to the same expression in the input lanes.
  match i, hi with
  | 0, _ => simp [Keccak.rho, rho]
  | 1, _ => simp [Keccak.rho, rho]
  | 2, _ => simp [Keccak.rho, rho]
  | 3, _ => simp [Keccak.rho, rho]
  | 4, _ => simp [Keccak.rho, rho]
  | 5, _ => simp [Keccak.rho, rho]
  | 6, _ => simp [Keccak.rho, rho]
  | 7, _ => simp [Keccak.rho, rho]
  | 8, _ => simp [Keccak.rho, rho]
  | 9, _ => simp [Keccak.rho, rho]
  | 10, _ => simp [Keccak.rho, rho]
  | 11, _ => simp [Keccak.rho, rho]
  | 12, _ => simp [Keccak.rho, rho]
  | 13, _ => simp [Keccak.rho, rho]
  | 14, _ => simp [Keccak.rho, rho]
  | 15, _ => simp [Keccak.rho, rho]
  | 16, _ => simp [Keccak.rho, rho]
  | 17, _ => simp [Keccak.rho, rho]
  | 18, _ => simp [Keccak.rho, rho]
  | 19, _ => simp [Keccak.rho, rho]
  | 20, _ => simp [Keccak.rho, rho]
  | 21, _ => simp [Keccak.rho, rho]
  | 22, _ => simp [Keccak.rho, rho]
  | 23, _ => simp [Keccak.rho, rho]
  | 24, _ => simp [Keccak.rho, rho]
  | _ + 25, hi => exact absurd hi (by simp [LANES])

/-- Pi on the record is Pi on the vector. -/
theorem pi_eq (A : State) : Keccak.pi A = (pi (Lanes.ofVector A)).toVector := by
  apply Vector.ext
  intro i hi
  -- One lane at a time: both sides unfold to the same expression in the input lanes.
  match i, hi with
  | 0, _ => simp [Keccak.pi, pi, lane]
  | 1, _ => simp [Keccak.pi, pi, lane]
  | 2, _ => simp [Keccak.pi, pi, lane]
  | 3, _ => simp [Keccak.pi, pi, lane]
  | 4, _ => simp [Keccak.pi, pi, lane]
  | 5, _ => simp [Keccak.pi, pi, lane]
  | 6, _ => simp [Keccak.pi, pi, lane]
  | 7, _ => simp [Keccak.pi, pi, lane]
  | 8, _ => simp [Keccak.pi, pi, lane]
  | 9, _ => simp [Keccak.pi, pi, lane]
  | 10, _ => simp [Keccak.pi, pi, lane]
  | 11, _ => simp [Keccak.pi, pi, lane]
  | 12, _ => simp [Keccak.pi, pi, lane]
  | 13, _ => simp [Keccak.pi, pi, lane]
  | 14, _ => simp [Keccak.pi, pi, lane]
  | 15, _ => simp [Keccak.pi, pi, lane]
  | 16, _ => simp [Keccak.pi, pi, lane]
  | 17, _ => simp [Keccak.pi, pi, lane]
  | 18, _ => simp [Keccak.pi, pi, lane]
  | 19, _ => simp [Keccak.pi, pi, lane]
  | 20, _ => simp [Keccak.pi, pi, lane]
  | 21, _ => simp [Keccak.pi, pi, lane]
  | 22, _ => simp [Keccak.pi, pi, lane]
  | 23, _ => simp [Keccak.pi, pi, lane]
  | 24, _ => simp [Keccak.pi, pi, lane]
  | _ + 25, hi => exact absurd hi (by simp [LANES])

/-- Chi on the record is Chi on the vector. -/
theorem chi_eq (A : State) : Keccak.chi A = (chi (Lanes.ofVector A)).toVector := by
  apply Vector.ext
  intro i hi
  -- One lane at a time: both sides unfold to the same expression in the input lanes.
  match i, hi with
  | 0, _ => simp [Keccak.chi, chi, lane]
  | 1, _ => simp [Keccak.chi, chi, lane]
  | 2, _ => simp [Keccak.chi, chi, lane]
  | 3, _ => simp [Keccak.chi, chi, lane]
  | 4, _ => simp [Keccak.chi, chi, lane]
  | 5, _ => simp [Keccak.chi, chi, lane]
  | 6, _ => simp [Keccak.chi, chi, lane]
  | 7, _ => simp [Keccak.chi, chi, lane]
  | 8, _ => simp [Keccak.chi, chi, lane]
  | 9, _ => simp [Keccak.chi, chi, lane]
  | 10, _ => simp [Keccak.chi, chi, lane]
  | 11, _ => simp [Keccak.chi, chi, lane]
  | 12, _ => simp [Keccak.chi, chi, lane]
  | 13, _ => simp [Keccak.chi, chi, lane]
  | 14, _ => simp [Keccak.chi, chi, lane]
  | 15, _ => simp [Keccak.chi, chi, lane]
  | 16, _ => simp [Keccak.chi, chi, lane]
  | 17, _ => simp [Keccak.chi, chi, lane]
  | 18, _ => simp [Keccak.chi, chi, lane]
  | 19, _ => simp [Keccak.chi, chi, lane]
  | 20, _ => simp [Keccak.chi, chi, lane]
  | 21, _ => simp [Keccak.chi, chi, lane]
  | 22, _ => simp [Keccak.chi, chi, lane]
  | 23, _ => simp [Keccak.chi, chi, lane]
  | 24, _ => simp [Keccak.chi, chi, lane]
  | _ + 25, hi => exact absurd hi (by simp [LANES])

/-- Iota on the record is iota on the vector. -/
theorem iota_eq (ir : Fin ROUNDS) (A : State) :
    Keccak.iota ir A = (iota RC[ir] (Lanes.ofVector A)).toVector := by
  apply Vector.ext
  intro i hi
  -- Lane 0 takes the constant, and the others pass through.
  match i, hi with
  | 0, _ => simp [Keccak.iota, iota]
  | 1, _ => simp [Keccak.iota, iota]
  | 2, _ => simp [Keccak.iota, iota]
  | 3, _ => simp [Keccak.iota, iota]
  | 4, _ => simp [Keccak.iota, iota]
  | 5, _ => simp [Keccak.iota, iota]
  | 6, _ => simp [Keccak.iota, iota]
  | 7, _ => simp [Keccak.iota, iota]
  | 8, _ => simp [Keccak.iota, iota]
  | 9, _ => simp [Keccak.iota, iota]
  | 10, _ => simp [Keccak.iota, iota]
  | 11, _ => simp [Keccak.iota, iota]
  | 12, _ => simp [Keccak.iota, iota]
  | 13, _ => simp [Keccak.iota, iota]
  | 14, _ => simp [Keccak.iota, iota]
  | 15, _ => simp [Keccak.iota, iota]
  | 16, _ => simp [Keccak.iota, iota]
  | 17, _ => simp [Keccak.iota, iota]
  | 18, _ => simp [Keccak.iota, iota]
  | 19, _ => simp [Keccak.iota, iota]
  | 20, _ => simp [Keccak.iota, iota]
  | 21, _ => simp [Keccak.iota, iota]
  | 22, _ => simp [Keccak.iota, iota]
  | 23, _ => simp [Keccak.iota, iota]
  | 24, _ => simp [Keccak.iota, iota]
  | _ + 25, hi => exact absurd hi (by simp [LANES])

/-- The record round is the specification's round. -/
theorem round_eq (ir : Fin ROUNDS) (A : State) :
    Keccak.round ir A = (round RC[ir] (Lanes.ofVector A)).toVector := by
  -- Each step's output is the vector of the record step's output, so the records chain.
  simp only [Keccak.round, round, theta_eq, rho_eq, pi_eq, chi_eq, iota_eq, ofVector_toVector]

/-- The record permutation is the specification's permutation. -/
theorem keccakF_eq (A : State) : Keccak.keccakF A = (keccakF (Lanes.ofVector A)).toVector := by
  -- Run both folds over the same rounds, the record carried alongside the state.
  suffices h : ∀ (rounds : List (Fin ROUNDS)) (A : State),
      rounds.foldl (fun A ir => Keccak.round ir A) A
        = (rounds.foldl (fun s ir => round RC[ir] s) (Lanes.ofVector A)).toVector from h _ A
  intro rounds
  induction rounds with
  | nil => intro A; exact (toVector_ofVector A).symm
  | cons ir rest ih =>
    intro A
    -- One round on each side, then the rest by induction.
    rw [List.foldl_cons, List.foldl_cons, round_eq, ih, ofVector_toVector]

end Kernel

end EthLib.Cryptography.Hash.Keccak
