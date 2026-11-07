module

public import EthLib.Cryptography.Proofs.Secp256k1.Ecdh
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding
public import EthLib.Networking.Discv5.Handshake
public import EthLib.Networking.Proofs.Discv5.Identity

/-!
# `Networking.Proofs.Discv5.Handshake`

Node B accepts what node A sends in a handshake, and both sides derive the same session keys.

- The ECDH of the discv5 handshake is symmetric between two multiples of `G`.
- When step 3 succeeds for node A, step 4 succeeds for node B with the keys of node A.
- Two errors with one code come from one constructor.

The theorem assumes only that step 3 succeeded.

That success already holds the key agreement, the key derivation and the ID signature.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Discv5.Handshake

open EthLib.Networking.Discv5
open EthLib.Cryptography.Secp256k1
open EthLib.Cryptography.Secp256k1.Point
open EthLib.Networking.Proofs.Discv5.Identity

/-! ## Key agreement -/

/-- A key whose agreement with a multiple of `G` succeeds is not zero. -/
theorem ne_zero_of_ecdh_eq_ok {e b : Fn} {secret : ByteArray}
    (h : Discv5.ecdh e (mul b generator) = .ok secret) : e ≠ 0 := by
  rintro rfl
  -- The multiple `0 P` is `O`, and the agreement rejects it.
  have hzero := EthLib.Cryptography.Secp256k1.mul_zero_left (isOnCurve_mul b isOnCurve_generator)
  unfold Discv5.ecdh at h
  split at h
  · cases h
  split at h
  · cases h
  rw [hzero] at h
  cases h

/-- The agreement of `e` with `b G` gives the secret of `b` with `e G`. -/
theorem ecdh_mul_generator_symm {e b : Fn} {secret : ByteArray}
    (h : Discv5.ecdh e (mul b generator) = .ok secret) :
    Discv5.ecdh b (mul e generator) = .ok secret := by
  have hG := isOnCurve_generator
  have he := Ecdsa.mul_generator_ne_infinity (ne_zero_of_ecdh_eq_ok h)
  unfold Discv5.ecdh at h ⊢
  split at h
  · cases h
  -- Both points are multiples of `G` other than `O`, so only `e (b G) = b (e G)` is left.
  simp only [he, isOnCurve_mul _ hG, Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
  rw [mul_mul_generator_comm b e]
  exact h

/-! ## The two sides -/

/-- When step 3 succeeds for node A, step 4 succeeds for node B with the same session keys.

Node A has the static key `a`, and node B the static key `b`.

Each side knows the public key of the other, `a G` or `b G`. -/
theorem acceptHandshake_initiateHandshake {e a b : Fn} {challengeData : ByteArray}
    {nodeIdA nodeIdB : NodeId} {init : HandshakeInit}
    (h : initiateHandshake e a challengeData nodeIdA nodeIdB (mul b generator) = .ok init) :
    acceptHandshake b challengeData nodeIdA nodeIdB (mul a generator) init.ephemeralPubkey
      init.idSignature = .ok init.keys := by
  unfold initiateHandshake at h
  cases hs : Discv5.ecdh e (mul b generator) with
  | error err => simp [hs, Except.mapError, bind, Except.bind] at h
  | ok secret =>
    cases hk : deriveKeys secret challengeData nodeIdA nodeIdB with
    | error err => simp [hs, hk, Except.mapError, bind, Except.bind] at h
    | ok keys =>
      cases hsig : idSign a challengeData (mul e generator).encodeCompressed nodeIdB with
      | error err => simp [hs, hk, hsig, Except.mapError, bind, Except.bind] at h
      | ok signature =>
        simp only [hs, hk, hsig, Except.mapError, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at h
        subst h
        -- The ephemeral point is a multiple of `G` other than `O`, so it has 33 bytes.
        have hG := isOnCurve_generator
        have hon := isOnCurve_mul e hG
        have hne := Ecdsa.mul_generator_ne_infinity (ne_zero_of_ecdh_eq_ok hs)
        have hsize : (mul e generator).encodeCompressed.size = 33 := by
          cases hm : mul e generator with
          | infinity => exact absurd hm hne
          | affine x y => exact size_encodeCompressed x y
        simp only [acceptHandshake, idVerify_idSign hsig, hsize, decode_encodeCompressed hon hne,
          ecdh_mul_generator_symm hs, hk, Except.mapError, bind, Except.bind, ite_true]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Discv5.HandshakeError.code_injective
    (e₁ e₂ : HandshakeError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [HandshakeError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Discv5.Handshake
