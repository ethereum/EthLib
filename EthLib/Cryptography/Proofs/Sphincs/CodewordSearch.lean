module

public import EthLib.Cryptography.Sphincs.Ots
public import EthLib.Cryptography.Proofs.Sphincs.CodeSize
public import EthLib.Cryptography.Proofs.Sphincs.TweakableHash
public import EthLib.Cryptography.Proofs.HashSig
public import EthLib.Cryptography.Proofs.HashSig.Bytes
public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Proofs.Wots.TargetSum

/-!
# Proofs: the counter search rarely fails, in the random-oracle model

To sign, a one-time key encodes the message under counters `0, 1, ...`, up to `2^32` of them.

It keeps the first counter whose 16-byte digest is a codeword, and signing fails if none is.

Here the hash is a random oracle, and its cache holds none of the trial inputs yet.

The counters give distinct inputs, so the trials see fresh, independent, uniform digests.

Exactly `|C|` of the `2^128` digests are codewords.

So all counters fail with probability `(1 - |C| / 2^128)^(2^32)`, exactly.

One counter succeeds with probability `|C| / 2^128 = 2^-13.84`, about one in 14,670.

So `2^32` counters expect 292,764.7 codewords, and all fail with probability below `exp(-2^18)`.

That is below `2^-378193`.

The bound is for one search, so for one one-time signature of the hypertree.

Whether the signer's cache holds a trial input when the search starts is not proved here.

An empty cache holds none, and a corollary states the bound from it.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp ENNReal

/-- Exactly `|C|` digests are codewords: a digest is its 64 digits. -/
theorem card_codeword : Nat.card {d : Digest // (codeword? d).isSome} = CODE_SIZE := by
  have hdig : Function.Bijective (Internal.digits) := Wots.digits4_bijective
  rw [← card_onTarget]
  exact Nat.card_congr ((Equiv.ofBijective _ hdig).subtypeEquiv fun d => codeword?_isSome_iff)

/-- The other `2^128 - |C|` digests are not codewords. -/
theorem card_not_codeword : Nat.card {d : Digest // codeword? d = none} = 2 ^ 128 - CODE_SIZE := by
  have h := Nat.card_congr (Equiv.sumCompl fun d : Digest => (codeword? d).isSome)
  rw [Nat.card_sum, card_codeword, Nat.card_eq_fintype_card (α := Digest),
    show Fintype.card Digest = 2 ^ 128 from Wots.card_bytes16] at h
  rw [← h, Nat.add_sub_cancel_left]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun d => by simp)

/-- The first 16 bytes of an oracle answer are the bytes of its low 128 bits. -/
theorem halfOf_zero_ofOutput (x : HashSig.HashOutput) :
    halfOf 0 (HashSig.ofOutput x) = HashSig.ofBV 16 (HashSig.truncateHash x) := by
  apply Vector.ext
  intro i hi
  simp only [N] at hi
  simp only [halfOf, Vector.getElem_ofFn]
  simp only [Fin.isValue, Fin.val_zero, Nat.mul_zero, Nat.zero_add]
  exact HashSig.getElem_ofOutput_of_lt x i hi

/-- One fresh counter misses the code with probability `1 - |C| / 2^128`. -/
theorem prEvent_not_codeword :
    Pr{let u ← $ᵗ HashSig.HashOutput}[
        codeword? (halfOf 0 (HashSig.ofOutput u)) = none]
      = ((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  rw [← card_not_codeword]
  simp only [halfOf_zero_ofOutput]
  exact HashSig.prEvent_ofBV_truncateHash (fun d => codeword? d = none)

/-- A trial below `2^32` is its own counter. -/
theorem toNat_ofNat_trial {j : ℕ} (hj : j < MAX_COUNTER_TRIALS) :
    (UInt32.ofNat j).toNat = j := by
  simp only [MAX_COUNTER_TRIALS] at hj
  simp only [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa using hj)

/-- **All `2^32` counters miss the code with probability `(1 - |C| / 2^128)^(2^32)`.**

The hash is a lazily sampled random oracle, and the search starts from any cache.

The cache must hold none of the `2^32` inputs that the counters hash.

The message and the key are arbitrary. -/
theorem prEvent_findCounter_none (pp : PublicParam) (key : OtsKey) (msg : ByteArray)
    (cache : HashSig.HashSpec.QueryCache)
    (hfresh : ∀ j < MAX_COUNTER_TRIALS,
      cache (thInput pp (addrEncoding key)
        (msg ++ packBytes (uintToBytes COUNTER_LEN j))).data.toList = none) :
    Pr{let z ← (simulateQ HashSig.HashSpec.romImpl (Internal.findCounter
        HashSig.queryH pp key msg 0 MAX_COUNTER_TRIALS)).run' cache}[z = none]
      = (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ MAX_COUNTER_TRIALS := by
  rw [← prEvent_not_codeword]
  refine Wots.prEvent_findFirst_romImpl_none UInt32.ofNat
    (fun c => (thInput pp (addrEncoding key)
      (msg ++ packBytes (uintToBytes COUNTER_LEN c.toNat))).data.toList)
    (fun u => codeword? (halfOf 0 (HashSig.ofOutput u))) _ (fun c => ?_) _ 0 cache
    (fun j j' _ hj _ hj' h => ?_) (fun j _ hj => ?_)
  · simp only [encode, th, thFull, HashSig.queryH, HashSig.oracleHash,
      map_eq_bind_pure_comp]
    rfl
  · have hin := (thInput_inj (ByteArray.ext (Array.toList_inj.mp h))).2.2
    have hc := Base.uintToBytes_inj (by simp [COUNTER_LEN]; omega) (by simp [COUNTER_LEN]; omega)
      (Base.packBytes_injective (HashSig.byteArray_append_inj hin rfl).2)
    rw [toNat_ofNat_trial (by omega), toNat_ofNat_trial (by omega)] at hc
    exact hc
  · rw [toNat_ofNat_trial (by omega)]
    exact hfresh j (by omega)

/-- **All `2^32` counters miss the code with probability below `exp(-2^18)`.**

The hypotheses are those of the exact probability above. -/
theorem prEvent_findCounter_none_le (pp : PublicParam) (key : OtsKey) (msg : ByteArray)
    (cache : HashSig.HashSpec.QueryCache)
    (hfresh : ∀ j < MAX_COUNTER_TRIALS,
      cache (thInput pp (addrEncoding key)
        (msg ++ packBytes (uintToBytes COUNTER_LEN j))).data.toList = none) :
    Pr{let z ← (simulateQ HashSig.HashSpec.romImpl (Internal.findCounter
        HashSig.queryH pp key msg 0 MAX_COUNTER_TRIALS)).run' cache}[z = none]
      ≤ ENNReal.ofReal (Real.exp (-(2 ^ 18))) := by
  rw [prEvent_findCounter_none pp key msg cache hfresh,
    HashSig.ofReal_one_sub_div _ _ (by simp [CODE_SIZE]),
    ← ENNReal.ofReal_pow (by norm_num [CODE_SIZE])]
  exact ENNReal.ofReal_le_ofReal all_counters_fail_probability

/-- From an empty cache, all `2^32` counters miss the code with probability below `exp(-2^18)`. -/
theorem prEvent_findCounter_none_le_empty (pp : PublicParam) (key : OtsKey) (msg : ByteArray) :
    Pr{let z ← (simulateQ HashSig.HashSpec.romImpl (Internal.findCounter
        HashSig.queryH pp key msg 0 MAX_COUNTER_TRIALS)).run' ∅}[z = none]
      ≤ ENNReal.ofReal (Real.exp (-(2 ^ 18))) :=
  prEvent_findCounter_none_le pp key msg ∅ fun _ _ => rfl

end EthLib.Cryptography.Sphincs
