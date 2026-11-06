module

public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Pairing
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Group
public import EthLib.Cryptography.Proofs.Bls.KeyValidate
import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.G1
import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.G2

/-!
# Proofs: the pairing check of EIP-2537 tests a product of pairings

Let `P_i` represent `a_i • g1` and `Q_i` represent `b_i • g2`.

Then `prod_i e(P_i, Q_i) = e(g1, g2)^(sum_i a_i * b_i)`, and `e(g1, g2)` has prime order `r`.

So the product is 1 exactly when that sum is 0 in `Fr`.

Every point that the check decodes lies in its subgroup, so it has such a discrete logarithm.

The theorems take the pairing law as a hypothesis.

EthLib does not prove that law for its Miller loop.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bind_ok_iff mapM_cons_ok mapM_ok_mem mapM_ok_getElem mapM_exists_ok)
open EthLib.Cryptography.Bls (Fr G1 G2 PairingLaws pairingCheck)
open scoped EthLib.Cryptography.Bls.Fr

/-! ## Discrete logarithms of decoded points -/

/-- A raw pair decodes exactly when its G1 point and then its G2 point decode.

Both use the subgroup check. -/
private theorem decodePair_eq_ok_iff {rawG1 rawG2 : List UInt8} {pair : G1 × G2} :
    (fun (rawG1, rawG2) => do return (← bytesToG1 rawG1 true, ← bytesToG2 rawG2 true) :
        List UInt8 × List UInt8 → Except Bls12381Error (G1 × G2)) (rawG1, rawG2) = .ok pair ↔
      bytesToG1 rawG1 true = .ok pair.1 ∧ bytesToG2 rawG2 true = .ok pair.2 := by
  constructor
  · intro h
    obtain ⟨p, hp, h⟩ := bind_ok_iff.mp h
    obtain ⟨q, hq, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact bind_ok_iff.mpr ⟨_, hp, bind_ok_iff.mpr ⟨_, hq, rfl⟩⟩

/-- A list of pairs with a discrete logarithm for each point has lists of them. -/
private theorem exists_lists {pairs : List (G1 × G2)}
    (h : ∀ pair ∈ pairs, (∃ a, G1.Represents pair.1 a) ∧ ∃ b, G2.Represents pair.2 b) :
    ∃ a b : List Fr, ∃ (ha : a.length = pairs.length) (hb : b.length = pairs.length),
      ∀ i (hi : i < pairs.length),
        G1.Represents (pairs[i]).1 (a[i]'(ha ▸ hi)) ∧
          G2.Represents (pairs[i]).2 (b[i]'(hb ▸ hi)) := by
  induction pairs with
  | nil => exact ⟨[], [], rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons pair pairs ih =>
    obtain ⟨⟨a0, ha0⟩, b0, hb0⟩ := h pair List.mem_cons_self
    obtain ⟨a, b, ha, hb, hrep⟩ := ih fun p hp => h p (List.mem_cons_of_mem pair hp)
    refine ⟨a0 :: a, b0 :: b, by simp [ha], by simp [hb], fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨ha0, hb0⟩
    | succ i =>
      simpa using hrep i (by simpa using hi)

/-- Every pair that the pairing check decodes has a discrete logarithm for each point.

So lists `a` and `b` exist with `P_i` representing `a_i • g1` and `Q_i` representing `b_i • g2`. -/
theorem exists_represents_of_decodePairs {rawPairs : List (List UInt8 × List UInt8)}
    {pairs : List (G1 × G2)}
    (hdec : rawPairs.mapM (fun (rawG1, rawG2) => do
        return (← bytesToG1 rawG1 true, ← bytesToG2 rawG2 true)) = .ok pairs) :
    ∃ a b : List Fr, ∃ (ha : a.length = pairs.length) (hb : b.length = pairs.length),
      ∀ i (hi : i < pairs.length),
        G1.Represents (pairs[i]).1 (a[i]'(ha ▸ hi)) ∧
          G2.Represents (pairs[i]).2 (b[i]'(hb ▸ hi)) := by
  refine exists_lists fun pair hpair => ?_
  obtain ⟨⟨rawG1, rawG2⟩, -, hraw⟩ := mapM_ok_mem hdec pair hpair
  obtain ⟨h1, h2⟩ := decodePair_eq_ok_iff.mp hraw
  exact ⟨(G1.inSubgroup_iff_exists_represents (valid_of_bytesToG1_eq_ok h1)).mp
      (inSubgroup_of_bytesToG1_eq_ok h1),
    (G2.inSubgroup_iff_exists_represents (valid_of_bytesToG2_eq_ok h2)).mp
      (inSubgroup_of_bytesToG2_eq_ok h2)⟩

/-! ## The output of the pairing check -/

/-- Under the pairing law, the pairing check returns the word 1 exactly when `sum_i a_i * b_i = 0`.

Here `(P_i, Q_i)` are the decoded pairs.

`P_i` represents `a_i • g1`, and `Q_i` represents `b_i • g2`.

Such `a` and `b` exist for every successful call. -/
theorem bls12Pairing_eq_one_iff (hlaws : PairingLaws) {data : ByteArray} {gas : Nat}
    {out : ByteArray} (h : bls12Pairing data gas = .ok out)
    {rawPairs : List (List UInt8 × List UInt8)} {pairs : List (G1 × G2)}
    (hraw : (chunks LENGTH_PER_PAIRING_PAIR (data.size / LENGTH_PER_PAIRING_PAIR)
        data.data.toList).mapM
        (fun pair => do return (← unpadG1 (pair.take 128), ← unpadG2 (pair.drop 128))) =
      .ok rawPairs)
    (hdec : rawPairs.mapM (fun (rawG1, rawG2) => do
        return (← bytesToG1 rawG1 true, ← bytesToG2 rawG2 true)) = .ok pairs)
    {a b : List Fr} (ha : a.length = pairs.length) (hb : b.length = pairs.length)
    (hrep : ∀ i (hi : i < pairs.length),
      G1.Represents (pairs[i]).1 (a[i]'(ha ▸ hi)) ∧ G2.Represents (pairs[i]).2 (b[i]'(hb ▸ hi))) :
    out = ⟨(boolWord true).toArray⟩ ↔ (List.zipWith (· * ·) a b).sum = 0 := by
  obtain ⟨-, -, rawPairs', pairs', hraw', hdec', rfl⟩ := (bls12Pairing_eq_ok_iff data gas out).mp h
  rw [hraw] at hraw'
  cases hraw'
  rw [hdec] at hdec'
  cases hdec'
  rw [← hlaws.pairingCheck_iff pairs a b ha hb hrep]
  constructor
  · intro hout
    have hword : boolWord (pairingCheck pairs.toArray) = boolWord true := by
      have := congrArg (fun bytes : ByteArray => bytes.data.toList) hout
      simpa using this
    exact boolWord_injective hword
  · intro hcheck
    rw [hcheck]

/-! ## The encodings of represented pairs -/

/-- The padded encoding of a pair: its G1 point, then its G2 point. -/
private theorem length_encodePair (pair : G1 × G2) :
    (padG1 (g1ToBytes pair.1) ++ padG2 (g2ToBytes pair.2)).length = LENGTH_PER_PAIRING_PAIR := by
  rw [List.length_append, length_padG1_g1ToBytes, length_padG2_g2ToBytes]
  rfl

/-- The encodings of `n` pairs have `384 * n` bytes. -/
private theorem length_encodePairs (pairs : List (G1 × G2)) :
    (pairs.map fun pair => padG1 (g1ToBytes pair.1) ++ padG2 (g2ToBytes pair.2)).flatten.length =
      LENGTH_PER_PAIRING_PAIR * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    rw [List.map_cons, List.flatten_cons, List.length_append, ih, length_encodePair,
      List.length_cons, Nat.mul_succ, Nat.add_comm]

/-- Cutting blocks of one size, put end to end, gives the blocks back. -/
private theorem chunks_flatten {size : Nat} :
    ∀ blocks : List (List UInt8), (∀ block ∈ blocks, block.length = size) →
      chunks size blocks.length blocks.flatten = blocks
  | [], _ => rfl
  | block :: blocks, h => by
    have hblock := h block List.mem_cons_self
    rw [List.length_cons, List.flatten_cons, chunks, List.take_left' hblock,
      List.drop_left' hblock, chunks_flatten blocks fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- The raw bytes of a G1 point have 96 bytes. -/
private theorem length_g1ToBytes (point : G1) : (g1ToBytes point).length = 96 := by
  simp [g1ToBytes, EthLib.Base.natToBytes_length]

/-- The raw bytes of a G2 point have 192 bytes. -/
private theorem length_g2ToBytes (point : G2) : (g2ToBytes point).length = 192 := by
  simp [g2ToBytes, EthLib.Base.natToBytes_length]

/-- The padding of every encoded pair is removed, leaving the raw bytes of its two points. -/
private theorem unpad_encodePairs :
    ∀ pairs : List (G1 × G2),
      (pairs.map fun pair => padG1 (g1ToBytes pair.1) ++ padG2 (g2ToBytes pair.2)).mapM
          (fun pair => do return (← unpadG1 (pair.take 128), ← unpadG2 (pair.drop 128))) =
        .ok (pairs.map fun pair => (g1ToBytes pair.1, g2ToBytes pair.2))
  | [] => rfl
  | pair :: pairs => by
    rw [List.map_cons, List.map_cons, mapM_cons_ok]
    refine ⟨_, _, ?_, unpad_encodePairs pairs, rfl⟩
    rw [List.take_left' (length_padG1_g1ToBytes pair.1),
      List.drop_left' (length_padG1_g1ToBytes pair.1),
      unpadG1_padG1 (length_g1ToBytes pair.1), unpadG2_padG2 (length_g2ToBytes pair.2)]
    rfl

/-- Under the pairing law, the check of encoded pairs returns the word of `sum_i a_i * b_i = 0`.

Here `P_i` represents `a_i • g1` and `Q_i` represents `b_i • g2`.

There must be at least one pair, and gas for all of them. -/
theorem bls12Pairing_encodePairs (hlaws : PairingLaws) {pairs : List (G1 × G2)}
    (hne : pairs ≠ []) {a b : List Fr} (ha : a.length = pairs.length)
    (hb : b.length = pairs.length)
    (hrep : ∀ i (hi : i < pairs.length),
      G1.Represents (pairs[i]).1 (a[i]'(ha ▸ hi)) ∧ G2.Represents (pairs[i]).2 (b[i]'(hb ▸ hi)))
    {gas : Nat} (hgas : bls12PairingGas pairs.length ≤ gas) :
    bls12Pairing
        ⟨(pairs.map fun pair =>
          padG1 (g1ToBytes pair.1) ++ padG2 (g2ToBytes pair.2)).flatten.toArray⟩
        gas =
      .ok ⟨(boolWord (decide ((List.zipWith (· * ·) a b).sum = 0))).toArray⟩ := by
  set data : ByteArray :=
    ⟨(pairs.map fun pair => padG1 (g1ToBytes pair.1) ++ padG2 (g2ToBytes pair.2)).flatten.toArray⟩
    with hdata
  have hsize : data.size = LENGTH_PER_PAIRING_PAIR * pairs.length := by
    rw [hdata, ByteArray.size, List.size_toArray, length_encodePairs]
  have hlen : 0 < pairs.length := List.length_pos_iff.mpr hne
  have hk : data.size / LENGTH_PER_PAIRING_PAIR = pairs.length := by
    rw [hsize, Nat.mul_div_cancel_left _ (by decide)]
  have hchunks : chunks LENGTH_PER_PAIRING_PAIR (data.size / LENGTH_PER_PAIRING_PAIR)
      data.data.toList =
        pairs.map fun pair => padG1 (g1ToBytes pair.1) ++ padG2 (g2ToBytes pair.2) := by
    rw [hk, hdata, List.toList_toArray]
    conv => lhs; arg 2; rw [← List.length_map (f := fun pair : G1 × G2 =>
      padG1 (g1ToBytes pair.1) ++ padG2 (g2ToBytes pair.2))]
    refine chunks_flatten _ fun block hblock => ?_
    obtain ⟨pair, -, rfl⟩ := List.mem_map.mp hblock
    exact length_encodePair pair
  -- Every raw point decodes, with the subgroup check, to the same group element.
  have hdecodes : ∀ raw ∈ pairs.map (fun pair => (g1ToBytes pair.1, g2ToBytes pair.2)),
      ∃ decoded, (fun (rawG1, rawG2) => do
        return (← bytesToG1 rawG1 true, ← bytesToG2 rawG2 true) :
          _ → Except Bls12381Error (G1 × G2))
          raw = .ok decoded := by
    intro raw hraw
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hraw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpair
    obtain ⟨hP, hQ⟩ := hrep i hi
    obtain ⟨p, hp, -⟩ := bytesToG1_g1ToBytes hP.1 fun _ =>
      (G1.inSubgroup_iff_exists_represents hP.1).mpr ⟨_, hP⟩
    obtain ⟨q, hq, -⟩ := bytesToG2_g2ToBytes hQ.1 fun _ =>
      (G2.inSubgroup_iff_exists_represents hQ.1).mpr ⟨_, hQ⟩
    exact ⟨(p, q), decodePair_eq_ok_iff.mpr ⟨hp, hq⟩⟩
  obtain ⟨decoded, hdec⟩ := mapM_exists_ok hdecodes
  have hlength : decoded.length = pairs.length := by
    rw [EthLib.Base.mapM_ok_length hdec, List.length_map]
  -- Each decoded point represents the same discrete logarithm as the encoded one.
  have ha' : a.length = decoded.length := ha.trans hlength.symm
  have hb' : b.length = decoded.length := hb.trans hlength.symm
  have hrep' : ∀ i (hi : i < decoded.length),
      G1.Represents (decoded[i]).1 (a[i]'(ha' ▸ hi)) ∧
        G2.Represents (decoded[i]).2 (b[i]'(hb' ▸ hi)) := by
    intro i hi
    have hi' : i < pairs.length := hlength ▸ hi
    have hget := mapM_ok_getElem hdec i (by simpa using hi')
    rw [List.getElem_map] at hget
    obtain ⟨h1, h2⟩ := decodePair_eq_ok_iff.mp hget
    obtain ⟨hP, hQ⟩ := hrep i hi'
    obtain ⟨p, hp, hpt⟩ := bytesToG1_g1ToBytes hP.1 fun _ =>
      (G1.inSubgroup_iff_exists_represents hP.1).mpr ⟨_, hP⟩
    obtain ⟨q, hq, hqt⟩ := bytesToG2_g2ToBytes hQ.1 fun _ =>
      (G2.inSubgroup_iff_exists_represents hQ.1).mpr ⟨_, hQ⟩
    rw [h1] at hp
    cases hp
    rw [h2] at hq
    cases hq
    exact ⟨⟨valid_of_bytesToG1_eq_ok h1, hpt.trans hP.2⟩,
      ⟨valid_of_bytesToG2_eq_ok h2, hqt.trans hQ.2⟩⟩
  have hcheck : pairingCheck decoded.toArray = decide ((List.zipWith (· * ·) a b).sum = 0) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hlaws.pairingCheck_iff decoded a b ha' hb' hrep'
  refine (bls12Pairing_eq_ok_iff data gas _).mpr ⟨?_, hk ▸ hgas, _, decoded, ?_, hdec, ?_⟩
  · rw [hsize, LENGTH_PER_PAIRING_PAIR]
    omega
  · rw [hchunks]
    exact unpad_encodePairs pairs
  · rw [hcheck]

/-! ## Both outputs are reached -/

/-- Under the pairing law, the check of the generators `(g1, g2)` returns the word 0.

The product is `e(g1, g2)`, which is not 1. -/
theorem bls12Pairing_generators (hlaws : PairingLaws) {gas : Nat}
    (hgas : bls12PairingGas 1 ≤ gas) :
    bls12Pairing ⟨(padG1 (g1ToBytes G1.generator) ++ padG2 (g2ToBytes G2.generator)).toArray⟩ gas =
      .ok ⟨(boolWord false).toArray⟩ := by
  have h := bls12Pairing_encodePairs hlaws (pairs := [(G1.generator, G2.generator)])
    (List.cons_ne_nil _ _) (a := [1]) (b := [1]) rfl rfl (fun i hi => by
      match i, hi with
      | 0, _ => exact ⟨G1.represents_generator, G2.represents_generator⟩) hgas
  have hsum : (List.zipWith (· * ·) [(1 : Fr)] [1]).sum ≠ 0 := by simp
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    decide_eq_false hsum] at h
  exact h

/-- Under the pairing law, the check of `(g1, g2)` and `(-g1, g2)` returns the word 1.

The product is `e(g1, g2) * e(g1, g2)^(-1) = 1`. -/
theorem bls12Pairing_generator_neg (hlaws : PairingLaws) {gas : Nat}
    (hgas : bls12PairingGas 2 ≤ gas) :
    bls12Pairing ⟨(padG1 (g1ToBytes G1.generator) ++ padG2 (g2ToBytes G2.generator) ++
        (padG1 (g1ToBytes (G1.neg G1.generator)) ++ padG2 (g2ToBytes G2.generator))).toArray⟩ gas =
      .ok ⟨(boolWord true).toArray⟩ := by
  have h := bls12Pairing_encodePairs hlaws
    (pairs := [(G1.generator, G2.generator), (G1.neg G1.generator, G2.generator)])
    (List.cons_ne_nil _ _) (a := [1, -1]) (b := [1, 1]) rfl rfl (fun i hi => by
      match i, hi with
      | 0, _ => exact ⟨G1.represents_generator, G2.represents_generator⟩
      | 1, _ => exact ⟨G1.represents_generator.neg, G2.represents_generator⟩) hgas
  have hsum : (List.zipWith (· * ·) [(1 : Fr), -1] [1, 1]).sum = 0 := by simp
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    decide_eq_true hsum] at h
  exact h

end EthLib.Execution.Evm.Precompiles.Bls12381
