module

public import EthLib.Execution.Evm.Precompiles.Ecrecover.Core
public import EthLib.Cryptography.Proofs.Secp256k1.Recovery

/-!
# Proofs: `Ecrecover.Core`

The precompile returns the address of a key that verifies the signature, or nothing.

- `compute_size`: the output is empty or 32 bytes.
- `compute_callData`: the call data of a signature reads back as that signature.
- `output_verify`: a nonempty output is the address of a key that verifies the signature.
- `output_of_verify`: every key that verifies a signature has its address returned for `v = 27` or `v = 28`, when `r + n >= p`.
- `output_neg_s`: `(v, r, s)` and `(55 - v, r, n - s)` give the same output, since a high `s` is accepted.
- `compute_congr`: only the first 128 bytes count, and a short input reads as zero-padded.
- `output_sign`: a signature made with a private key returns that key's address.
- `output_of_bad_v`, `output_of_range`, `output_of_recover_error`: the three causes of an empty output.
- `ecrecover_out_of_gas`, `ecrecover_ok`: the call fails exactly when the gas is below 3000.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Ecrecover

open EthLib.Cryptography.Secp256k1
open EthLib.Cryptography.Secp256k1.Ecdsa

/-- The call data of a signature: the hash, then `v`, `r` and `s` as 32-byte big-endian integers. -/
def callData (hash : Vector UInt8 32) (v r s : Nat) : ByteArray :=
  ⟨(hash.toList ++ toBytesBE 32 v ++ toBytesBE 32 r ++ toBytesBE 32 s).toArray⟩

/-- The 32 bytes a word reads from a list are its slice. -/
private theorem word_toList (l : List UInt8) (start : Nat) (h : start + 32 ≤ l.length) :
    (word ⟨l.toArray⟩ start).toList = (l.drop start).take 32 := by
  apply List.ext_getElem
  · simp
    omega
  · intro i h1 h2
    simp [word, byteAt]
    rw [List.getElem?_eq_getElem (by simp at h1; omega)]
    rfl

private theorem callData_length (hash : Vector UInt8 32) (v r s : Nat) :
    (hash.toList ++ toBytesBE 32 v ++ toBytesBE 32 r ++ toBytesBE 32 s).length = 128 := by
  simp [length_toBytesBE]

private theorem callData_list (hash : Vector UInt8 32) (v r s : Nat) :
    hash.toList ++ toBytesBE 32 v ++ toBytesBE 32 r ++ toBytesBE 32 s
      = hash.toList ++ (toBytesBE 32 v ++ (toBytesBE 32 r ++ toBytesBE 32 s)) := by
  simp only [List.append_assoc]

theorem word_callData_hash (hash : Vector UInt8 32) (v r s : Nat) : word (callData hash v r s) 0 = hash := by
  apply Vector.toList_inj.mp
  rw [callData, word_toList _ _ (by rw [callData_length]; omega), callData_list, List.drop_zero,
    List.take_left' (by simp)]

private theorem word_callData_v (hash : Vector UInt8 32) (v r s : Nat) :
    (word (callData hash v r s) 32).toList = toBytesBE 32 v := by
  rw [callData, word_toList _ _ (by rw [callData_length]; omega), callData_list,
    List.drop_left' (by simp), List.take_left' (length_toBytesBE 32 v)]

private theorem word_callData_r (hash : Vector UInt8 32) (v r s : Nat) :
    (word (callData hash v r s) 64).toList = toBytesBE 32 r := by
  rw [callData, word_toList _ _ (by rw [callData_length]; omega), callData_list,
    show (64 : Nat) = 32 + 32 from rfl, ← List.drop_drop, List.drop_left' (by simp),
    List.drop_left' (length_toBytesBE 32 v), List.take_left' (length_toBytesBE 32 r)]

private theorem word_callData_s (hash : Vector UInt8 32) (v r s : Nat) :
    (word (callData hash v r s) 96).toList = toBytesBE 32 s := by
  rw [callData, word_toList _ _ (by rw [callData_length]), callData_list,
    show (96 : Nat) = 32 + 32 + 32 from rfl, ← List.drop_drop, ← List.drop_drop, List.drop_left' (by simp),
    List.drop_left' (length_toBytesBE 32 v), List.drop_left' (length_toBytesBE 32 r),
    List.take_of_length_le (by rw [length_toBytesBE])]

/-- The call data of a signature reads back as that signature, when `v`, `r` and `s` are below `2^256`. -/
theorem compute_callData (hash : Vector UInt8 32) {v r s : Nat} (hv : v < 2 ^ 256) (hr : r < 2 ^ 256)
    (hs : s < 2 ^ 256) : compute (callData hash v r s) = output hash v r s := by
  unfold compute
  rw [word_callData_hash, word_callData_v, word_callData_r, word_callData_s, ofBytesBE_toBytesBE,
    ofBytesBE_toBytesBE, ofBytesBE_toBytesBE, Nat.mod_eq_of_lt (by simpa using hv),
    Nat.mod_eq_of_lt (by simpa using hr), Nat.mod_eq_of_lt (by simpa using hs)]

/-- The output is empty or 32 bytes. -/
theorem output_size (hash : Vector UInt8 32) (v r s : Nat) :
    (output hash v r s).size = 0 ∨ (output hash v r s).size = 32 := by
  unfold output
  split
  · split
    · right
      simp [ByteArray.size]
    · left
      rfl
  · left
    rfl

theorem compute_size (data : ByteArray) : (compute data).size = 0 ∨ (compute data).size = 32 :=
  output_size _ _ _ _

/-- Soundness: a nonempty output is the address of a key that verifies the signature. -/
theorem output_verify {hash : Vector UInt8 32} {v r s : Nat} (h : output hash v r s ≠ ByteArray.empty) :
    ∃ x y : Fp, verify (.affine x y) hash r s = true
      ∧ output hash v r s = ⟨(List.replicate 12 0 ++ (address x y).toList).toArray⟩ := by
  unfold output at h ⊢
  split at h
  · rename_i hv
    rw [dite_eq_left hv]
    split at h
    · rename_i x y heq
      exact ⟨x, y, verify_recover heq, rfl⟩
    · exact absurd rfl h
  · exact absurd rfl h

/-- Completeness: the address of a key that verifies a signature comes back for `v = 27` or `v = 28`.

The bound `p <= r + n` is the one of `recover_of_verify`. -/
theorem output_of_verify {x y : Fp} {hash : Vector UInt8 32} {r s : Nat}
    (hv : verify (.affine x y) hash r s = true) (hp : Fp.modulus ≤ r + Fn.modulus) :
    ∃ v, (v = 27 ∨ v = 28) ∧ output hash v r s = ⟨(List.replicate 12 0 ++ (address x y).toList).toArray⟩ := by
  obtain ⟨id, hid⟩ := recover_of_verify hv hp
  refine ⟨id.val + 27, by omega, ?_⟩
  unfold output
  rw [dite_eq_left (by omega)]
  have : (⟨id.val + 27 - 27, by omega⟩ : Fin 2) = id := Fin.ext (by simp)
  rw [this, hid]

/-- A high `s` is accepted: flipping `s` to `n - s` and `v` between 27 and 28 gives the same output. -/
theorem output_neg_s (hash : Vector UInt8 32) {v r s : Nat} (hv : v = 27 ∨ v = 28) (hs : 0 < s ∧ s < Fn.modulus) :
    output hash (55 - v) r (Fn.modulus - s) = output hash v r s := by
  unfold output
  rw [dite_eq_left (by omega), dite_eq_left hv]
  -- The id `55 - v - 27` is `1 - (v - 27)`.
  have hid : (⟨55 - v - 27, by omega⟩ : Fin 2) = 1 - ⟨v - 27, by omega⟩ := by
    rcases hv with rfl | rfl <;> rfl
  have hback : (1 : Fin 2) - (1 - ⟨v - 27, by omega⟩) = ⟨v - 27, by omega⟩ := by
    rcases hv with rfl | rfl <;> rfl
  rw [hid]
  -- Both recoveries give the same result: the same key, or both fail.
  cases h : recover hash r s ⟨v - 27, by omega⟩ with
  | ok q => rw [recover_neg_s h]
  | error e =>
    cases h' : recover hash r (Fn.modulus - s) (1 - ⟨v - 27, by omega⟩) with
    | error e' => rfl
    | ok q =>
      -- Flipping back would recover a key, a contradiction.
      have := recover_neg_s h'
      rw [show Fn.modulus - (Fn.modulus - s) = s by omega, hback, h] at this
      cases this

/-- Only the first 128 bytes count: two inputs that read the same there give the same output.

So data past 128 bytes is ignored, and a short input is read as if padded with zeros. -/
theorem compute_congr {d1 d2 : ByteArray} (h : ∀ i < 128, byteAt d1 i = byteAt d2 i) : compute d1 = compute d2 := by
  have hw : ∀ k, k ≤ 96 → word d1 k = word d2 k := fun k hk =>
    Vector.ext fun i hi => by simp only [word, Vector.getElem_ofFn]; exact h _ (by omega)
  unfold compute
  rw [hw 0 (by omega), hw 32 (by omega), hw 64 (by omega), hw 96 (by omega)]

/-- With too little gas, the call fails. -/
theorem ecrecover_out_of_gas (data : ByteArray) {gas : Nat} (h : gas < GAS_ECRECOVER) :
    ecrecover data gas = .error (.outOfGas GAS_ECRECOVER gas) := by
  rw [ecrecover, ite_eq_left h]

/-- With enough gas, the call succeeds, with the output of the operation. -/
theorem ecrecover_ok (data : ByteArray) {gas : Nat} (h : GAS_ECRECOVER ≤ gas) : ecrecover data gas = .ok (compute data) := by
  rw [ecrecover, ite_eq_right (by omega)]

/-! ## The three empty outputs -/

/-- A `v` other than 27 and 28 gives the empty output. -/
theorem output_of_bad_v (hash : Vector UInt8 32) {v : Nat} (r s : Nat) (hv : ¬(v = 27 ∨ v = 28)) :
    output hash v r s = ByteArray.empty := by
  rw [output, dite_eq_right hv]

/-- An `r` or an `s` outside `[1, n - 1]` gives the empty output. -/
theorem output_of_range (hash : Vector UInt8 32) (v : Nat) {r s : Nat}
    (h : ¬((0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus))) : output hash v r s = ByteArray.empty := by
  unfold output
  split
  · split
    · rename_i heq
      exact absurd (recover_range heq) h
    · rfl
  · rfl

/-- A recovery that fails gives the empty output. -/
theorem output_of_recover_error (hash : Vector UInt8 32) {v r s : Nat} (hv : v = 27 ∨ v = 28) {e}
    (h : recover hash r s ⟨v - 27, by omega⟩ = .error e) : output hash v r s = ByteArray.empty := by
  rw [output, dite_eq_left hv, h]

/-- A recovered key gives its address, left-padded to 32 bytes. -/
theorem output_of_recover (hash : Vector UInt8 32) {v r s : Nat} (hv : v = 27 ∨ v = 28) {x y : Fp}
    (h : recover hash r s ⟨v - 27, by omega⟩ = .ok (.affine x y)) :
    output hash v r s = ⟨(List.replicate 12 0 ++ (address x y).toList).toArray⟩ := by
  rw [output, dite_eq_left hv, h]

/-! ## The signer's address -/

/-- A signature made with the private key `d` returns the address of `d`.

The signer has the nonce `k`, `R = k G = (x, y)` with `x < n`, and `s = k^(-1) (e + x d)`.

Then `v = 27 + parity(y)`, as Appendix F of the Yellow Paper sets it. -/
theorem output_sign (d k : Fn) (hash : Vector UInt8 32) (hd : d ≠ 0) {x y : Fp}
    (hR : Point.mul k .generator = .affine x y) (hx : x.val < Fn.modulus) (hx0 : x.val ≠ 0)
    (hs : k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ x.val * d) ≠ 0) :
    ∃ a, addressOfPrivateKey d = some a ∧
      output hash (27 + (parityId y).val) x.val (k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ x.val * d)).val
        = ⟨(List.replicate 12 0 ++ a.toList).toArray⟩ := by
  have hrec := recover_sign d k hash hd hR hx hx0 hs
  have hv : 27 + (parityId y).val = 27 ∨ 27 + (parityId y).val = 28 := by omega
  have hid : (⟨27 + (parityId y).val - 27, by omega⟩ : Fin 2) = parityId y := Fin.ext (by simp)
  unfold addressOfPrivateKey
  cases hQ : Point.mul d .generator with
  | infinity => exact absurd hQ (mul_generator_ne_infinity hd)
  | affine qx qy =>
    refine ⟨address qx qy, rfl, ?_⟩
    rw [hQ] at hrec
    rw [output, dite_eq_left hv, hid, hrec]

end EthLib.Execution.Evm.Precompiles.Ecrecover
