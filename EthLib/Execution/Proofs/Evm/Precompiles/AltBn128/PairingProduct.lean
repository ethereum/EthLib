module

public import EthLib.Execution.Proofs.Evm.Precompiles.AltBn128.Encoding
public import EthLib.Execution.Proofs.Evm.Precompiles.AltBn128.Pairing
public import EthLib.Cryptography.Proofs.AltBn128.PairingLaws
import EthLib.Cryptography.Proofs.AltBn128.PairingAte

/-!
# Proofs: ECPAIRING checks a product of pairings

Let `P_i = a_i P1` and `Q_i = b_i P2`, for scalars `a_i` and `b_i` in `ZMod q`.

Then `prod_i e(P_i, Q_i) = e(P1, P2)^(sum_i a_i * b_i)`, and `e(P1, P2)` has prime order `q`.

So the product is 1, and ECPAIRING returns the word 1, exactly when `sum_i a_i * b_i = 0`.

Every pair that ECPAIRING decodes holds such multiples of `P1` and `P2`.

The pairing law is proved in `PairingAte.lean`, so no theorem here assumes it.

Source: [EIP-197][eip197], section Specification.

[eip197]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-197.md#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Base (Fork bytesToNat natToBytes natToBytes_length bytesToNat_natToBytes_of_lt
  natToBytes_zero_right mapM_eq_ok_map mapM_ok_getElem mapM_ok_length)
open EthLib.Cryptography.AltBn128
open EthLib.Execution.Evm (bufferRead)

/-! ## Discrete logarithms of decoded pairs -/

/-- Each pair that decodes holds `a P1` and `b P2`, for some `a` and `b` in `ZMod q`. -/
theorem exists_represents_of_decodePair {data : ByteArray} {index : Nat} {p : Point} {Q : Point2}
    (h : decodePair data index = .ok (p, Q)) :
    (∃ a, p.Represents a) ∧ ∃ b, Q.Represents b := by
  obtain ⟨⟨a, ha, hp⟩, b, hb, hQ⟩ := exists_mulBits_generator_of_decodePair h
  exact ⟨⟨a, by rw [Point.Represents, ZMod.val_cast_of_lt ha]; exact hp⟩,
    ⟨b, by rw [Point2.Represents, ZMod.val_cast_of_lt hb]; exact hQ⟩⟩

/-- When each point of a list of pairs has a discrete logarithm, lists of them exist. -/
private theorem exists_lists {pairs : List (Point × Point2)}
    (h : ∀ pair ∈ pairs, (∃ a, pair.1.Represents a) ∧ ∃ b, pair.2.Represents b) :
    ∃ a b : List (ZMod Fr.modulus), ∃ (ha : a.length = pairs.length)
      (hb : b.length = pairs.length),
      ∀ i (hi : i < pairs.length),
        (pairs[i]).1.Represents (a[i]'(ha ▸ hi)) ∧
          (pairs[i]).2.Represents (b[i]'(hb ▸ hi)) := by
  induction pairs with
  | nil => exact ⟨[], [], rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons pair pairs ih =>
    obtain ⟨⟨a0, ha0⟩, b0, hb0⟩ := h pair List.mem_cons_self
    obtain ⟨a, b, ha, hb, hrep⟩ := ih fun p hp => h p (List.mem_cons_of_mem pair hp)
    refine ⟨a0 :: a, b0 :: b, by simp [ha], by simp [hb], fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨ha0, hb0⟩
    | succ i => simpa using hrep i (by simpa using hi)

/-- Every pair that ECPAIRING decodes has a discrete logarithm for each point.

So lists `a` and `b` exist with `P_i = a_i P1` and `Q_i = b_i P2`. -/
theorem exists_represents_of_decodePairs {data : ByteArray} {n : Nat}
    {pairs : List (Point × Point2)}
    (hdec : (List.range n).mapM (decodePair data) = .ok pairs) :
    ∃ a b : List (ZMod Fr.modulus), ∃ (ha : a.length = pairs.length)
      (hb : b.length = pairs.length),
      ∀ i (hi : i < pairs.length),
        (pairs[i]).1.Represents (a[i]'(ha ▸ hi)) ∧
          (pairs[i]).2.Represents (b[i]'(hb ▸ hi)) := by
  refine exists_lists fun pair hpair => ?_
  obtain ⟨index, -, hraw⟩ := EthLib.Base.mapM_ok_mem hdec pair hpair
  exact exists_represents_of_decodePair hraw

/-- Every call of ECPAIRING that succeeds has decoded pairs and scalars for them. -/
theorem exists_represents_of_ecpairing {fork : Fork} {data : ByteArray} {gas : Nat}
    {out : ByteArray} (h : ecpairing fork data gas = .ok out) :
    ∃ pairs : List (Point × Point2),
      (List.range (data.size / 192)).mapM (decodePair data) = .ok pairs ∧
      ∃ a b : List (ZMod Fr.modulus), ∃ (ha : a.length = pairs.length)
        (hb : b.length = pairs.length),
        ∀ i (hi : i < pairs.length),
          (pairs[i]).1.Represents (a[i]'(ha ▸ hi)) ∧
            (pairs[i]).2.Represents (b[i]'(hb ▸ hi)) := by
  obtain ⟨-, -, pairs, hdec, -⟩ := (ecpairing_eq_ok_iff fork data gas out).mp h
  exact ⟨pairs, hdec, exists_represents_of_decodePairs hdec⟩

/-! ## The output of ECPAIRING -/

/-- The words of the two booleans differ. -/
theorem ecpairingWord_injective : Function.Injective ecpairingWord := by
  intro a b h
  cases a <;> cases b <;> simp_all [ecpairingWord]

/-- On a successful call, ECPAIRING returns the word 1 exactly when `sum_i a_i * b_i = 0`.

Here `(P_i, Q_i)` are the decoded pairs, with `P_i = a_i P1` and `Q_i = b_i P2`.

Such `a` and `b` exist for every successful call, with no hypothesis on the pairing. -/
theorem ecpairing_eq_one_iff {fork : Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : ecpairing fork data gas = .ok out) {pairs : List (Point × Point2)}
    (hdec : (List.range (data.size / 192)).mapM (decodePair data) = .ok pairs)
    {a b : List (ZMod Fr.modulus)} (ha : a.length = pairs.length) (hb : b.length = pairs.length)
    (hrep : ∀ i (hi : i < pairs.length),
      (pairs[i]).1.Represents (a[i]'(ha ▸ hi)) ∧
        (pairs[i]).2.Represents (b[i]'(hb ▸ hi))) :
    out = ⟨(ecpairingWord true).toArray⟩ ↔ (List.zipWith (· * ·) a b).sum = 0 := by
  obtain ⟨-, -, pairs', hdec', rfl⟩ := (ecpairing_eq_ok_iff fork data gas out).mp h
  rw [hdec] at hdec'
  cases hdec'
  rw [← pairingLaws.pairingCheck_iff pairs a b ha hb hrep]
  constructor
  · intro hout
    have hword : ecpairingWord (pairingCheck pairs) = ecpairingWord true := by
      have := congrArg (fun bytes : ByteArray => bytes.data.toList) hout
      simpa [ecpairingWord] using this
    exact ecpairingWord_injective hword
  · intro hcheck
    simp [ecpairingWord, hcheck]

/-- On a successful call, ECPAIRING returns the word 0 exactly when `sum_i a_i * b_i ≠ 0`.

Here `(P_i, Q_i)` are the decoded pairs, with `P_i = a_i P1` and `Q_i = b_i P2`. -/
theorem ecpairing_eq_zero_iff {fork : Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : ecpairing fork data gas = .ok out) {pairs : List (Point × Point2)}
    (hdec : (List.range (data.size / 192)).mapM (decodePair data) = .ok pairs)
    {a b : List (ZMod Fr.modulus)} (ha : a.length = pairs.length) (hb : b.length = pairs.length)
    (hrep : ∀ i (hi : i < pairs.length),
      (pairs[i]).1.Represents (a[i]'(ha ▸ hi)) ∧
        (pairs[i]).2.Represents (b[i]'(hb ▸ hi))) :
    out = ⟨(ecpairingWord false).toArray⟩ ↔ (List.zipWith (· * ·) a b).sum ≠ 0 := by
  obtain ⟨-, -, pairs', hdec', rfl⟩ := (ecpairing_eq_ok_iff fork data gas out).mp h
  rw [hdec] at hdec'
  cases hdec'
  rw [ne_eq, ← pairingLaws.pairingCheck_iff pairs a b ha hb hrep, Bool.not_eq_true]
  constructor
  · intro hout
    have hword : ecpairingWord (pairingCheck pairs) = ecpairingWord false := by
      have := congrArg (fun bytes : ByteArray => bytes.data.toList) hout
      simpa [ecpairingWord] using this
    exact ecpairingWord_injective hword
  · intro hcheck
    simp [ecpairingWord, hcheck]

/-! ## The encodings of represented pairs -/

/-- The 128 bytes of a point of the twist. -/
theorem length_g2ToBytes : (q : Point2) → (g2ToBytes q).length = 128
  | .infinity => by simp [g2ToBytes]
  | .affine _ _ => by simp [g2ToBytes, natToBytes_length]

/-- A coordinate fits in 32 bytes, since `p < 2^256`. -/
private theorem fp_lt_two_pow (x : Fp) : x.val < 256 ^ 32 :=
  Nat.lt_trans x.isLt (by decide)

/-- The 32 bytes of an element of `Fp` decode back to it. -/
theorem bytesToFp_natToBytes (x : Fp) : bytesToFp (natToBytes 32 x.val) = .ok x := by
  simp [bytesToFp, bytesToNat_natToBytes_of_lt (fp_lt_two_pow x), x.isLt]

/-- The point `(0, 0)` is not on the twist, since `b2 ≠ 0`. -/
theorem isOnCurve_point2_zero : (Point2.affine ⟨0, 0⟩ ⟨0, 0⟩).isOnCurve = false := by
  rw [Bool.eq_false_iff]
  intro hon
  rw [Point2.isOnCurve_affine] at hon
  have h0 : (⟨0, 0⟩ : Fp2) = 0 := rfl
  rw [h0, zero_mul, zero_mul, zero_add] at hon
  exact b2_ne_zero hon.symm

/-- Dropping 64 bytes from four blocks of 32 bytes leaves the last two blocks. -/
private theorem drop_64_of_four {a b c d : List UInt8}
    (ha : a.length = 32) (hb : b.length = 32) :
    (a ++ (b ++ (c ++ d))).drop 64 = c ++ d := by
  rw [show (64 : Nat) = 32 + 32 from rfl, ← List.drop_drop, List.drop_left' ha, List.drop_left' hb]

/-- Dropping 96 bytes from four blocks of 32 bytes leaves the last block. -/
private theorem drop_96_of_four {a b c d : List UInt8}
    (ha : a.length = 32) (hb : b.length = 32) (hc : c.length = 32) :
    (a ++ (b ++ (c ++ d))).drop 96 = d := by
  rw [show (96 : Nat) = 64 + 32 from rfl, ← List.drop_drop, drop_64_of_four ha hb,
    List.drop_left' hc]

/-- The decoder reads back each point on the twist from its 128 bytes. -/
theorem bytesToG2_g2ToBytes {q : Point2} (hq : q.isOnCurve = true) :
    bytesToG2 (g2ToBytes q) = .ok q := by
  cases q with
  | infinity =>
    have h0 : natToBytes 32 0 = List.replicate 32 0 := natToBytes_zero_right 32
    have hbytes : g2ToBytes .infinity =
        natToBytes 32 0 ++ (natToBytes 32 0 ++ (natToBytes 32 0 ++ natToBytes 32 0)) := by
      simp [g2ToBytes, h0]
    have hl0 : (natToBytes 32 0).length = 32 := natToBytes_length 32 0
    have hzero : bytesToFp (natToBytes 32 0) = .ok 0 := bytesToFp_natToBytes 0
    rw [bytesToG2, hbytes, List.take_left' hl0, List.drop_left' hl0, List.take_left' hl0,
      drop_64_of_four hl0 hl0, List.take_left' hl0, drop_96_of_four hl0 hl0 hl0]
    simp [hzero, bind, Except.bind, pure, Except.pure]
  | affine x y =>
    have hassoc : g2ToBytes (.affine x y) =
        natToBytes 32 x.c1.val ++
          (natToBytes 32 x.c0.val ++ (natToBytes 32 y.c1.val ++ natToBytes 32 y.c0.val)) := by
      simp [g2ToBytes, List.append_assoc]
    have hx1 : (natToBytes 32 x.c1.val).length = 32 := natToBytes_length 32 x.c1.val
    have hx0 : (natToBytes 32 x.c0.val).length = 32 := natToBytes_length 32 x.c0.val
    have hy1 : (natToBytes 32 y.c1.val).length = 32 := natToBytes_length 32 y.c1.val
    have hnz : ¬(x.c0 = 0 ∧ x.c1 = 0 ∧ y.c0 = 0 ∧ y.c1 = 0) := by
      rintro ⟨hc0, hc1, hd0, hd1⟩
      have hx : x = ⟨0, 0⟩ := Fp2.ext hc0 hc1
      have hy : y = ⟨0, 0⟩ := Fp2.ext hd0 hd1
      rw [hx, hy, isOnCurve_point2_zero] at hq
      cases hq
    rw [bytesToG2, hassoc, List.take_left' hx1, List.drop_left' hx1, List.take_left' hx0,
      drop_64_of_four hx1 hx0, List.take_left' hy1, drop_96_of_four hx1 hx0 hy1]
    simp only [bytesToFp_natToBytes, hq, bind, Except.bind, pure, Except.pure, ↓reduceIte]
    split
    · rename_i hzero
      exact absurd ⟨congrArg Fp2.c0 hzero.1, congrArg Fp2.c1 hzero.1,
        congrArg Fp2.c0 hzero.2, congrArg Fp2.c1 hzero.2⟩ hnz
    · rfl

/-- The 192 bytes of a pair: its point of the curve, then its point of the twist. -/
def encodePair (pair : Point × Point2) : List UInt8 :=
  g1ToBytes pair.1 ++ g2ToBytes pair.2

/-- Each encoded pair has 192 bytes. -/
private theorem length_encodePair (pair : Point × Point2) :
    (encodePair pair).length = 192 := by
  rw [encodePair, List.length_append, length_g1ToBytes, length_g2ToBytes]

/-- The encodings of `k` pairs have `192 * k` bytes. -/
private theorem length_encodePairs (pairs : List (Point × Point2)) :
    (pairs.map encodePair).flatten.length = 192 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    rw [List.map_cons, List.flatten_cons, List.length_append, ih, length_encodePair,
      List.length_cons, Nat.mul_succ, Nat.add_comm]

/-- Slicing `size` bytes at `start` takes `size` bytes after dropping `start`. -/
private theorem bufferRead_of_le {bytes : List UInt8} {start size : Nat}
    (h : start + size ≤ bytes.length) :
    bufferRead ⟨bytes.toArray⟩ start size = (bytes.drop start).take size := by
  apply List.ext_getElem
  · rw [bufferRead_length, List.length_take_of_le (by simp; omega)]
  · intro j hj _
    rw [bufferRead_length] at hj
    have hlt : start + j < bytes.length := by omega
    simp [bufferRead, EthLib.Base.byteAt_eq_getD, Array.getD_eq_getD_getElem?,
      List.getElem?_eq_getElem hlt]

/-- Dropping `size * i` bytes from blocks of `size` bytes leaves the blocks from `i` on. -/
private theorem drop_flatten_of_length {size : Nat} :
    ∀ (blocks : List (List UInt8)) (i : Nat),
      (∀ block ∈ blocks, block.length = size) → i ≤ blocks.length →
      blocks.flatten.drop (size * i) = (blocks.drop i).flatten
  | _, 0, _, _ => by simp
  | [], _ + 1, _, hi => absurd hi (by simp)
  | block :: blocks, i + 1, h, hi => by
    have hblock := h block List.mem_cons_self
    rw [List.flatten_cons, Nat.mul_succ, Nat.add_comm, ← List.drop_drop,
      List.drop_left' hblock,
      drop_flatten_of_length blocks i (fun b hb => h b (List.mem_cons_of_mem _ hb))
        (by simpa using hi)]
    rfl

/-- Block `i` of a list of blocks of one size is the slice of `size` bytes at `size * i`. -/
private theorem take_drop_flatten {size : Nat} {blocks : List (List UInt8)}
    (h : ∀ block ∈ blocks, block.length = size) {i : Nat} (hi : i < blocks.length) :
    ((blocks.flatten.drop (size * i)).take size) = blocks[i] := by
  rw [drop_flatten_of_length blocks i h (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi,
    List.flatten_cons, List.take_left' (h _ (List.getElem_mem hi))]

/-- Splitting a slice of `a + b` bytes into `a` bytes and `b` bytes. -/
private theorem bufferRead_split (data : ByteArray) (start a b : Nat) :
    bufferRead data start a = (bufferRead data start (a + b)).take a ∧
      bufferRead data (start + a) b = (bufferRead data start (a + b)).drop a := by
  constructor
  · apply List.ext_getElem
    · rw [bufferRead_length, List.length_take_of_le (by rw [bufferRead_length]; omega)]
    · intro j hj _
      rw [bufferRead_length] at hj
      simp [bufferRead]
  · apply List.ext_getElem
    · rw [bufferRead_length, List.length_drop, bufferRead_length, Nat.add_sub_cancel_left]
    · intro j hj _
      rw [bufferRead_length] at hj
      simp [bufferRead, Nat.add_assoc]

/-- The bytes of block `i` of the encoded pairs, read by ECPAIRING. -/
private theorem bufferRead_encodePairs {pairs : List (Point × Point2)} {i : Nat}
    (hi : i < pairs.length) :
    bufferRead ⟨(pairs.map encodePair).flatten.toArray⟩ (192 * i) 192 =
      encodePair pairs[i] := by
  have hlen : ∀ block ∈ pairs.map encodePair, block.length = 192 := by
    intro block hblock
    obtain ⟨pair, -, rfl⟩ := List.mem_map.mp hblock
    exact length_encodePair pair
  rw [bufferRead_of_le (by rw [length_encodePairs]; omega),
    take_drop_flatten hlen (by simpa using hi), List.getElem_map]

/-- The decoder reads back each pair of points on their curves from its 192 bytes. -/
private theorem decodePair_encodePair {pair : Point × Point2}
    (hp : pair.1.isOnCurve = true) (hq : pair.2.isOnCurve = true)
    (hord : Point2.mulBits 256 Fr.modulus pair.2 = .infinity) {data : ByteArray} {index : Nat}
    (hread : bufferRead data (192 * index) 192 = encodePair pair) :
    decodePair data index = .ok pair := by
  obtain ⟨p, q⟩ := pair
  obtain ⟨h1, h2⟩ := bufferRead_split data (192 * index) 64 128
  have hsplit : encodePair (p, q) = g1ToBytes p ++ g2ToBytes q := rfl
  have hlen1 : (g1ToBytes p).length = 64 := length_g1ToBytes p
  rw [decodePair, h1, h2, show 64 + 128 = 192 from rfl, hread, hsplit,
    List.take_left' hlen1, List.drop_left' hlen1, bytesToG1_g1ToBytes hp, bytesToG2_g2ToBytes hq]
  simp [hord, bind, Except.bind, pure, Except.pure]

/-- With enough gas, ECPAIRING on encoded pairs returns the word 1 when `sum_i a_i * b_i = 0`.

Otherwise it returns the word 0.

Here `P_i = a_i P1` and `Q_i = b_i P2`.

The list of pairs may be empty, as EIP-197 allows. -/
theorem ecpairing_encodePairs {pairs : List (Point × Point2)}
    {a b : List (ZMod Fr.modulus)} (ha : a.length = pairs.length) (hb : b.length = pairs.length)
    (hrep : ∀ i (hi : i < pairs.length),
      (pairs[i]).1.Represents (a[i]'(ha ▸ hi)) ∧ (pairs[i]).2.Represents (b[i]'(hb ▸ hi)))
    {fork : Fork} {gas : Nat}
    (hgas : ecpairingGas fork (192 * pairs.length) ≤ gas) :
    ecpairing fork ⟨(pairs.map encodePair).flatten.toArray⟩ gas =
      .ok ⟨(ecpairingWord (decide ((List.zipWith (· * ·) a b).sum = 0))).toArray⟩ := by
  set data : ByteArray := ⟨(pairs.map encodePair).flatten.toArray⟩ with hdata
  have hsize : data.size = 192 * pairs.length := by
    rw [hdata, ByteArray.size, List.size_toArray, length_encodePairs]
  have hwhole : data.size % 192 = 0 := by rw [hsize]; exact Nat.mul_mod_right 192 _
  have hk : data.size / 192 = pairs.length := by rw [hsize, Nat.mul_div_cancel_left _ (by decide)]
  -- Each encoded pair decodes to its points, which are on their curves by representation.
  have hdec : (List.range pairs.length).mapM (decodePair data) = .ok pairs := by
    refine EthLib.Base.mapM_eq_ok_iff.mpr ⟨(List.length_range).symm, fun i hi => ?_⟩
    have hi' : i < pairs.length := by simpa using hi
    rw [List.getElem_range]
    have hread := bufferRead_encodePairs (pairs := pairs) hi'
    rw [← hdata] at hread
    obtain ⟨hP, hQ⟩ := hrep i hi'
    have hon1 : (pairs[i]).1.isOnCurve = true := by
      rw [Point.Represents] at hP
      exact hP ▸ Point.isOnCurve_mulBits _ _ Point.isOnCurve_generator
    have hon2 : (pairs[i]).2.isOnCurve = true := by
      rw [Point2.Represents] at hQ
      exact hQ ▸ Point2.isOnCurve_mulBits _ _ Point2.isOnCurve_generator
    have hord : Point2.mulBits 256 Fr.modulus (pairs[i]).2 = .infinity :=
      (Point2.mulBits_order_eq_infinity_iff_exists hon2).mpr ⟨_, ZMod.val_lt _, hQ⟩
    exact decodePair_encodePair hon1 hon2 hord hread
  have hcheck : pairingCheck pairs = decide ((List.zipWith (· * ·) a b).sum = 0) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact pairingLaws.pairingCheck_iff pairs a b ha hb hrep
  refine (ecpairing_eq_ok_iff fork data gas _).mpr ⟨hsize ▸ hgas, hwhole, pairs, hk ▸ hdec, ?_⟩
  rw [hcheck, ecpairingWord]

/-! ## Both outputs are reached -/

/-- With enough gas, ECPAIRING on `(P1, P2)` returns the word 0.

The product is `e(P1, P2)`, which is not 1. -/
theorem ecpairing_generators {fork : Fork} {gas : Nat}
    (hgas : ecpairingGas fork 192 ≤ gas) :
    ecpairing fork ⟨(encodePair (Point.generator, Point2.generator)).toArray⟩ gas =
      .ok ⟨(ecpairingWord false).toArray⟩ := by
  have h := ecpairing_encodePairs (pairs := [(Point.generator, Point2.generator)])
    (a := [1]) (b := [1]) rfl rfl (fun i hi => by
      match i, hi with
      | 0, _ => exact ⟨Point.represents_generator, Point2.represents_generator⟩) hgas
  have hsum : (List.zipWith (· * ·) [(1 : ZMod Fr.modulus)] [1]).sum ≠ 0 := by simp
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    decide_eq_false hsum] at h
  exact h

/-- With enough gas, ECPAIRING on `(P1, P2)` and `(-P1, P2)` returns the word 1.

The product is `e(P1, P2) * e(P1, P2)^(-1) = 1`. -/
theorem ecpairing_generator_neg {fork : Fork} {gas : Nat}
    (hgas : ecpairingGas fork 384 ≤ gas) :
    ecpairing fork ⟨(encodePair (Point.generator, Point2.generator) ++
        encodePair (Point.generator.neg, Point2.generator)).toArray⟩ gas =
      .ok ⟨(ecpairingWord true).toArray⟩ := by
  have h := ecpairing_encodePairs
    (pairs := [(Point.generator, Point2.generator),
      (Point.generator.neg, Point2.generator)])
    (a := [1, -1]) (b := [1, 1]) rfl rfl (fun i hi => by
      match i, hi with
      | 0, _ => exact ⟨Point.represents_generator, Point2.represents_generator⟩
      | 1, _ => exact ⟨Point.represents_generator.neg, Point2.represents_generator⟩) hgas
  have hsum : (List.zipWith (· * ·) [(1 : ZMod Fr.modulus), -1] [1, 1]).sum = 0 := by simp
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    decide_eq_true hsum] at h
  exact h

/-- With enough gas, ECPAIRING on no pairs returns the word 1, as EIP-197 specifies. -/
theorem ecpairing_empty {fork : Fork} {gas : Nat}
    (hgas : ecpairingGas fork 0 ≤ gas) :
    ecpairing fork ⟨#[]⟩ gas = .ok ⟨(ecpairingWord true).toArray⟩ := by
  have h := ecpairing_encodePairs (pairs := []) (a := []) (b := []) rfl rfl
    (fun i hi => absurd hi (Nat.not_lt_zero i)) hgas
  simp only [List.map_nil, List.flatten_nil, List.zipWith_nil_right, List.sum_nil,
    decide_true] at h
  exact h

end EthLib.Execution.Evm.Precompiles.AltBn128

