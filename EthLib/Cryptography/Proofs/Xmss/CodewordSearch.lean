module

public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Proofs.Xmss.CodeSize
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Convert
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.RandomOracle

/-!
# Proofs: the codeword search rarely fails, in the random-oracle model

To sign, a one-time key hashes the message under up to `2^32` randomizers, one after another.

It keeps the first whose 16-byte digest is a codeword, and signing fails if none is.

Here the hash is a random oracle, and its cache holds none of the trial inputs yet.

The trial inputs are distinct, so the trials see fresh, independent, uniform digests.

Exactly `|C|` of the `2^128` digests are codewords.

So all trials fail with probability `(1 - |C| / 2^128)^(2^32)`, exactly.

One trial succeeds with probability `|C| / 2^128 = 2^-20.0045`, about one in 1,051,863.

So `2^32` trials expect 4083.2 codewords, and all fail with probability below `exp(-4000)`.

That is below `2^-5770`.

The bound is for one search, so for one layer of a signature.

Whether the signer's cache holds a trial input when the search starts is not proved here.

An empty cache holds none, and a corollary states the bound from it.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants
open OracleSpec OracleComp ENNReal

/-! ## Digests and their digits -/

/-- There are `2^128` digests of 16 bytes. -/
theorem card_digest : Fintype.card Digest = 2 ^ 128 := by
  rw [Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun, Fintype.card_fin,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, DIGEST_LEN]
  norm_num

/-- A digest is the base-4 number its 64 digits spell. -/
theorem bytesToUint_eq_sum_digits (d : Digest) :
    bytesToUint d = ∑ i : Fin DIGITS, ((Internal.digits d)[i] : ℕ) * 4 ^ i.val := by
  have hlt : bytesToUint d < 4 ^ DIGITS := by
    have := Base.bytesToUint_lt d
    simpa [DIGEST_LEN, DIGITS] using this
  have hall := sum_base_digits_eq_mod 4 (bytesToUint d) DIGITS
  rw [Nat.mod_eq_of_lt hlt] at hall
  rw [← hall, ← Fin.sum_univ_eq_sum_range (fun r => bytesToUint d / 4 ^ r % 4 * 4 ^ r)]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- Every string of 64 digits is the digits of exactly one digest. -/
theorem digits_bijective : Function.Bijective (Internal.digits) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun d d' h => ?_, ?_⟩
  · have : bytesToUint d = bytesToUint d' := by
      rw [bytesToUint_eq_sum_digits d, bytesToUint_eq_sum_digits d', h]
    rw [← Base.uintToBytes_bytesToUint d, ← Base.uintToBytes_bytesToUint d', this]
  · rw [card_digest, Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, CHAIN_LENGTH, DIGITS]
    norm_num

/-- Exactly `|C|` digests are codewords.

A codeword's digest is unique, and padding a codeword with 6 zero digits gives its digest. -/
theorem card_codeword : Nat.card {d : Digest // (codeword? d).isSome} = CODE_SIZE := by
  classical
  let e : {d : Digest // (codeword? d).isSome}
      ≃ {x : Vector (Fin CHAIN_LENGTH) V // Internal.digitSum x = TARGET_SUM} :=
    Equiv.ofBijective
      (fun d => ⟨(codeword? d.1).get d.2,
        (codeword?_eq_some (Option.some_get d.2).symm).2.2⟩) ⟨fun d d' h => ?_, fun x => ?_⟩
  · rw [Nat.card_congr e, card_onTarget]
  · apply Subtype.ext
    have h' := congrArg Subtype.val h
    simp only at h'
    have h1 : codeword? d.1 = some ((codeword? d'.1).get d'.2) := by
      rw [← h']
      exact (Option.some_get _).symm
    exact eq_of_codeword h1 (Option.some_get _).symm
  · obtain ⟨y, hy⟩ := digits_bijective.2
      (Vector.ofFn fun i : Fin DIGITS => if h : i.val < V then x.1[i.val] else ⟨0, by decide⟩)
    have hcw : codeword? y = some x.1 := by
      simp only [codeword?, hy]
      simp only [List.all_eq_true, beq_iff_eq, Bool.and_eq_true]
      simp
      refine ⟨fun z hz => ?_, x.2⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
      simp [List.getElem_drop]
    refine ⟨⟨y, by rw [hcw]; rfl⟩, Subtype.ext ?_⟩
    simp [hcw]

/-- The other `2^128 - |C|` digests are not codewords. -/
theorem card_not_codeword : Nat.card {d : Digest // codeword? d = none} = 2 ^ 128 - CODE_SIZE := by
  have h := Nat.card_congr (Equiv.sumCompl fun d : Digest => (codeword? d).isSome)
  rw [Nat.card_sum, card_codeword, Nat.card_eq_fintype_card (α := Digest), card_digest] at h
  rw [← h, Nat.add_sub_cancel_left]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun d => by simp)

/-- The first half of a uniform 32-byte answer is a uniform 16-byte digest. -/
theorem prEvent_halfOf_ofOutput (P : Digest → Prop) :
    Pr{let u ← $ᵗ XmssSecurity.HashOutput}[P (halfOf 0 (Unforgeability.ofOutput u))]
      = (Nat.card {d : Digest // P d} : ℝ≥0∞) / 2 ^ 128 := by
  classical
  simp only [Unforgeability.halfOf_zero_ofOutput]
  rw [← prEvent_map ($ᵗ XmssSecurity.HashOutput) XmssSecurity.truncateHash
      (fun b => P (Unforgeability.ofDigest b)),
    EvalDistEq.prEvent_eq XmssSecurity.Rom.evalDist_truncate_uniformHashOutput,
    SampleableType.prEvent_uniformSample, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have hc : Nat.card {b : XmssSecurity.Digest // P (Unforgeability.ofDigest b)} =
      Nat.card {d : Digest // P d} :=
    Nat.card_congr
      { toFun := fun b => ⟨Unforgeability.ofDigest b.1, b.2⟩
        invFun := fun d => ⟨Unforgeability.toDigest d.1, by simpa using d.2⟩
        left_inv := fun b => by simp
        right_inv := fun d => by simp }
  rw [hc]
  congr 1
  norm_num [XmssSecurity.digestBits]

/-- One fresh trial misses the code with probability `1 - |C| / 2^128`. -/
theorem prEvent_not_codeword :
    Pr{let u ← $ᵗ XmssSecurity.HashOutput}[codeword? (halfOf 0 (Unforgeability.ofOutput u)) = none]
      = ((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  rw [prEvent_halfOf_ofOutput (fun d => codeword? d = none), card_not_codeword]

/-- Distinct trials below `2^32` have distinct randomizers. -/
theorem trialRandomizer_inj (base : Randomizer) {j j' : ℕ} (hj : j < 2 ^ 32) (hj' : j' < 2 ^ 32)
    (h : trialRandomizer base j = trialRandomizer base j') : j = j' := by
  have := congrArg bytesToUint h
  simp only [trialRandomizer, Base.bytesToUint_uintToBytes, RANDOMIZER_LEN] at this
  have hb := Base.bytesToUint_lt base
  simp only [RANDOMIZER_LEN] at hb
  omega

/-- **All `2^32` trials miss the code with probability `(1 - |C| / 2^128)^(2^32)`.**

The hash is a lazily sampled random oracle, and the search starts from any cache.

The cache must hold none of the `2^32` inputs that the trials hash.

The randomizer base, the message, the key and its layer are arbitrary. -/
theorem prEvent_findCodeword_none (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (cache : XmssSecurity.HashSpec.QueryCache)
    (hfresh : ∀ j < MAX_RANDOMIZER_TRIALS,
      cache (thInput pp (addrMsg layer e) (msg ++ packBytes (trialRandomizer base j))).data.toList
        = none) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl (Internal.findCodeword
        Unforgeability.queryH pp layer e msg base 0 MAX_RANDOMIZER_TRIALS)).run' cache}[z = none]
      = (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ MAX_RANDOMIZER_TRIALS := by
  rw [← prEvent_not_codeword]
  refine Wots.prEvent_findFirst_romImpl_none (trialRandomizer base)
    (fun rho => (thInput pp (addrMsg layer e) (msg ++ packBytes rho)).data.toList)
    (fun u => codeword? (halfOf 0 (Unforgeability.ofOutput u))) _ (fun rho => ?_) _ 0 cache
    (fun j j' _ hj _ hj' h => ?_) (fun j _ hj => hfresh j (by omega))
  · simp only [messageDigest, th, Unforgeability.queryH, XmssSecurity.Concrete.oracleHash,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    rfl
  · have hin := (thInput_inj (ByteArray.ext (Array.toList_inj.mp h))).2.2
    have hrho := packBytes_injective (byteArray_append_inj hin rfl).2
    exact trialRandomizer_inj base (by simpa [MAX_RANDOMIZER_TRIALS] using hj)
      (by simpa [MAX_RANDOMIZER_TRIALS] using hj') hrho

/-- The fraction `(2^n - C) / 2^n` is `1 - C / 2^n`, as an extended real. -/
theorem ofReal_one_sub_div (C n : ℕ) (hC : C ≤ 2 ^ n) :
    (((2 ^ n - C : ℕ) : ℝ≥0∞) / 2 ^ n) = ENNReal.ofReal (1 - (C : ℝ) / 2 ^ n) := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h : (1 : ℝ) - C / 2 ^ n = ((2 ^ n - C : ℕ) : ℝ) / 2 ^ n := by
    rw [Nat.cast_sub hC]
    field_simp
    push_cast
    ring
  rw [h, ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- With uniform digests, all `2^32` trials miss the code with probability below `exp(-4000)`.

`(1 - p)^(2^32) <= exp(-p)^(2^32) = exp(-2^32 p)`, and `2^32 p >= 4000`. -/
theorem all_trials_fail_probability :
    (1 - (CODE_SIZE : ℝ) / 2 ^ 128) ^ MAX_RANDOMIZER_TRIALS ≤ Real.exp (-4000) := by
  set p : ℝ := (CODE_SIZE : ℝ) / 2 ^ 128
  have hmean : (4000 : ℝ) ≤ 2 ^ 32 * p := by
    simp only [p, CODE_SIZE]
    norm_num
  have hp : 0 ≤ 1 - p := by
    simp only [p, CODE_SIZE]
    norm_num
  calc (1 - p) ^ MAX_RANDOMIZER_TRIALS
      ≤ Real.exp (-p) ^ MAX_RANDOMIZER_TRIALS :=
        pow_le_pow_left₀ hp (by linarith [Real.add_one_le_exp (-p)]) _
    _ = Real.exp (-(2 ^ 32 * p)) := by
        rw [← Real.exp_nat_mul, MAX_RANDOMIZER_TRIALS]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (-4000) := Real.exp_le_exp.mpr (by linarith)

/-- **All `2^32` trials miss the code with probability below `exp(-4000)`.**

The hypotheses are those of the exact probability above. -/
theorem prEvent_findCodeword_none_le (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (cache : XmssSecurity.HashSpec.QueryCache)
    (hfresh : ∀ j < MAX_RANDOMIZER_TRIALS,
      cache (thInput pp (addrMsg layer e) (msg ++ packBytes (trialRandomizer base j))).data.toList
        = none) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl (Internal.findCodeword
        Unforgeability.queryH pp layer e msg base 0 MAX_RANDOMIZER_TRIALS)).run' cache}[z = none]
      ≤ ENNReal.ofReal (Real.exp (-4000)) := by
  rw [prEvent_findCodeword_none pp layer e msg base cache hfresh,
    ofReal_one_sub_div _ _ (by simp [CODE_SIZE]), ← ENNReal.ofReal_pow (by norm_num [CODE_SIZE])]
  exact ENNReal.ofReal_le_ofReal all_trials_fail_probability

/-- From an empty cache, all `2^32` trials miss the code with probability below `exp(-4000)`. -/
theorem prEvent_findCodeword_none_le_empty (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl (Internal.findCodeword
        Unforgeability.queryH pp layer e msg base 0 MAX_RANDOMIZER_TRIALS)).run' ∅}[z = none]
      ≤ ENNReal.ofReal (Real.exp (-4000)) :=
  prEvent_findCodeword_none_le pp layer e msg base ∅ fun _ _ => rfl

end EthLib.Cryptography.Xmss
