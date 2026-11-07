module

public import EthLib.Cryptography.Aes.Gcm
public import EthLib.Cryptography.Proofs.Aes.Ctr

/-!
# Proofs: `Aes.Gcm`

Decryption of an honest ciphertext returns its plaintext.

Decryption accepts no tag other than the honest one.

Decryption returns a plaintext exactly when it encrypts to the given ciphertext and tag.

Both functions reject the 64-bit and 32-bit tags.

Under the length checks, the counters of the text differ from each other and from `J_0`.

Each holds for every forward cipher, so for AES under every key.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

/-- The length checks read the text only through its length. -/
theorem checkLengths_congr (t : Nat) (iv aad : ByteArray) {p c : ByteArray} (h : c.size = p.size) :
    checkLengths t iv c aad = checkLengths t iv p aad := by
  simp only [checkLengths, h]

/-- A tag has `t` bytes for every tag length of §5.2.1.2. -/
theorem size_tag (ciph : Block → Block) {t : Nat} (ht : t ∈ tagLengths) (H J0 : Block)
    (aad c : ByteArray) : (tag ciph t H J0 aad c).size = t := by
  have h16 : t ≤ 16 := by
    simp only [tagLengths, List.mem_cons, List.not_mem_nil, or_false] at ht
    omega
  unfold tag
  rw [ByteArray.size_extract, gctr, size_ctr]
  -- The block `S` has 16 bytes, so the tag keeps the first `t` of them.
  rw [show ∀ a : Array UInt8, (ByteArray.mk a).size = a.size from fun _ => rfl,
    Vector.size_toArray]
  omega

theorem mem_of_checkLengths {t : Nat} {iv text aad : ByteArray}
    (h : checkLengths t iv text aad = .ok ()) : t ∈ tagLengths := by
  unfold checkLengths at h
  by_cases hs : t ∈ shortTagLengths
  · simp [hs] at h
    contradiction
  by_cases ht : t ∈ tagLengths
  · exact ht
  · simp [hs, ht] at h
    contradiction

/-- The length checks reject a 64-bit or 32-bit tag before any other check. -/
theorem checkLengths_shortTag {t : Nat} (ht : t ∈ shortTagLengths) (iv text aad : ByteArray) :
    checkLengths t iv text aad = .error .shortTag := by
  simp [checkLengths, ht]
  rfl

/-- Encryption rejects a 64-bit or 32-bit tag, for every input. -/
theorem encrypt_shortTag (ciph : Block → Block) {t : Nat} (ht : t ∈ shortTagLengths)
    (iv p aad : ByteArray) : encrypt ciph t iv p aad = .error .shortTag := by
  simp only [encrypt, checkLengths_shortTag ht]
  rfl

/-- Decryption rejects a 64-bit or 32-bit tag, for every input. -/
theorem decrypt_shortTag (ciph : Block → Block) {t : Nat} (ht : t ∈ shortTagLengths)
    (iv c aad T : ByteArray) : decrypt ciph t iv c aad T = .error .shortTag := by
  simp only [decrypt, checkLengths_shortTag ht]
  rfl

/-- Decryption of an honest ciphertext and tag returns the plaintext, SP 800-38D §7.2. -/
theorem decrypt_encrypt (ciph : Block → Block) (t : Nat) (iv p aad c T : ByteArray)
    (h : encrypt ciph t iv p aad = .ok (c, T)) : decrypt ciph t iv c aad T = .ok p := by
  unfold encrypt at h
  cases hc : checkLengths t iv p aad with
  | error e =>
    rw [hc] at h
    cases h
  | ok u =>
    rw [hc] at h
    -- The ciphertext and the tag are the ones encryption computed.
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    have hs := size_ctr ciph 32 (inc 32 (preCounter (ciph zeroBlock) iv)) p
    unfold decrypt
    rw [gctr, checkLengths_congr t iv aad hs, hc]
    simp only [size_tag ciph (mem_of_checkLengths hc), gctr, ctr_ctr]
    rfl

/-- Decryption fails on every tag other than the honest one. -/
theorem decrypt_eq_ok (ciph : Block → Block) (t : Nat) (iv p aad c T T' q : ByteArray)
    (h : encrypt ciph t iv p aad = .ok (c, T)) (h' : decrypt ciph t iv c aad T' = .ok q) :
    T' = T := by
  unfold encrypt at h
  cases hc : checkLengths t iv p aad with
  | error e =>
    rw [hc] at h
    cases h
  | ok u =>
    rw [hc] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    have hs := size_ctr ciph 32 (inc 32 (preCounter (ciph zeroBlock) iv)) p
    unfold decrypt at h'
    rw [gctr, checkLengths_congr t iv aad hs, hc] at h'
    -- Decryption returns a plaintext only after its tag comparison succeeds.
    by_cases same : T' = tag ciph t (ciph zeroBlock) (preCounter (ciph zeroBlock) iv) aad
      (gctr ciph (inc 32 (preCounter (ciph zeroBlock) iv)) p)
    · exact same
    · rw [gctr] at same
      simp only [same, ite_false] at h'
      split at h' <;> cases h'

/-- A plaintext that decryption returns encrypts back to the ciphertext and the tag it was given.

So every pair `(c, T)` that decryption accepts is the encryption of its plaintext. -/
theorem encrypt_eq_ok_of_decrypt_eq_ok (ciph : Block → Block) (t : Nat)
    (iv c aad T p : ByteArray) (h : decrypt ciph t iv c aad T = .ok p) :
    encrypt ciph t iv p aad = .ok (c, T) := by
  unfold decrypt at h
  cases hc : checkLengths t iv c aad with
  | error e =>
    rw [hc] at h
    cases h
  | ok u =>
    rw [hc] at h
    -- The tag has `t` bytes, and it is the tag of the given ciphertext.
    by_cases hT : T.size = t
    · by_cases same : T = tag ciph t (ciph zeroBlock) (preCounter (ciph zeroBlock) iv) aad c
      · subst same
        -- The plaintext is the CTR decryption of the ciphertext.
        have hp : gctr ciph (inc 32 (preCounter (ciph zeroBlock) iv)) c = p := by
          simp only [hT, ite_true] at h
          exact Except.ok.inj h
        subst hp
        have hs : (gctr ciph (inc 32 (preCounter (ciph zeroBlock) iv)) c).size = c.size :=
          size_ctr ciph 32 _ c
        unfold encrypt
        rw [checkLengths_congr t iv aad hs, hc]
        simp only [gctr, ctr_ctr]
        rfl
      · simp only [hT, same, ite_true, ite_false] at h
        cases h
    · simp only [hT, ite_false] at h
      cases h

/-- Decryption returns `p` exactly when `p` encrypts to the ciphertext and tag, SP 800-38D §7. -/
theorem decrypt_eq_ok_iff (ciph : Block → Block) (t : Nat) (iv c aad T p : ByteArray) :
    decrypt ciph t iv c aad T = .ok p ↔ encrypt ciph t iv p aad = .ok (c, T) :=
  ⟨encrypt_eq_ok_of_decrypt_eq_ok ciph t iv c aad T p, decrypt_encrypt ciph t iv p aad c T⟩

/-- Two errors with one code are the same error. -/
theorem Error.code_injective (e₁ e₂ : Error) (h : e₁.code = e₂.code) : e₁ = e₂ := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [Error.code] at h; exact absurd h (by decide))

/-! ## Distinct counters

GCM encrypts block `k` of the text, counted from 0, under `J_0` incremented `k + 1` times.

`J_0` itself masks the tag, so it must differ from every counter of the text. -/

/-- A text that passes the length checks has at most `2^32 - 2` blocks, by §5.2.1.1. -/
theorem blocks_le_of_checkLengths {t : Nat} {iv text aad : ByteArray}
    (h : checkLengths t iv text aad = .ok ()) : (text.size + 15) / 16 ≤ 2 ^ 32 - 2 := by
  by_cases hlen : 8 * text.size ≤ 2 ^ 39 - 256
  · have h39 : (2 : Nat) ^ 39 - 256 = 549755813632 := by decide
    have h32 : (2 : Nat) ^ 32 - 2 = 4294967294 := by decide
    omega
  · -- Every branch of the checks then throws, so they cannot succeed.
    unfold checkLengths at h
    simp only [hlen] at h
    repeat' split at h
    all_goals first | contradiction | cases h

/-- Block `k` of GCTR from `inc_32(J_0)`, counted from 0, uses `J_0` incremented `k + 1` times.

It is block `k` of the text XORed with the cipher of that counter.

It holds for every `k`: past the last block of the text, both sides are empty. -/
theorem gctr_inc_block (ciph : Block → Block) (J0 : Block) (text : ByteArray) (k : Nat) :
    (((gctr ciph (inc 32 J0) text).data.toList).drop (16 * k)).take 16
      = List.zipWith (· ^^^ ·) ((text.data.toList.drop (16 * k)).take 16)
          (ciph (Nat.repeat (inc 32) (k + 1) J0)).toList := by
  rw [gctr, ctr_block ciph 32 (inc 32 J0) text k, repeat_apply_eq_repeat_succ]

/-- Under the length checks, no counter of the text is `J_0`, the counter of the tag. -/
theorem counter_ne_preCounter {t : Nat} {iv text aad : ByteArray}
    (h : checkLengths t iv text aad = .ok ()) (J0 : Block) {k : Nat}
    (hk : k < (text.size + 15) / 16) : Nat.repeat (inc 32) (k + 1) J0 ≠ J0 := by
  have hb := blocks_le_of_checkLengths h
  intro heq
  have := repeat_inc_injOn (by decide) J0 (i := k + 1) (j := 0) (by omega) (by decide) heq
  omega

/-- Under the length checks, two different blocks of the text have two different counters. -/
theorem counter_injOn {t : Nat} {iv text aad : ByteArray} (h : checkLengths t iv text aad = .ok ())
    (J0 : Block) {k k' : Nat} (hk : k < (text.size + 15) / 16) (hk' : k' < (text.size + 15) / 16)
    (heq : Nat.repeat (inc 32) (k + 1) J0 = Nat.repeat (inc 32) (k' + 1) J0) : k = k' := by
  have hb := blocks_le_of_checkLengths h
  have := repeat_inc_injOn (by decide) J0 (by omega) (by omega) heq
  omega

end EthLib.Cryptography.Aes.Gcm
