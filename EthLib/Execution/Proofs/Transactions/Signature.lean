module

public import EthLib.Cryptography.Proofs.Secp256k1.Recovery
public import EthLib.Execution.Transactions.Signature

/-!
# Proofs: the sender of a transaction

A signature names no sender when `r` or `s` is out of range.

From Homestead, a high `s` names no sender either.

The `v` of a legacy transaction gives the chain and the recovery id, as EIP-155 lays them out.

A recovered sender is the address of a key that verifies the signature on the signing hash.

An honest signer is the sender of the transaction that it signs.

The signature of a transaction is not part of what it signs.

So changing the signature of a transaction leaves its signing hash as it was.

The chain that a legacy transaction reports is the chain that its signing hash covers.

A typed transaction reports the chain of its own field.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Cryptography.Secp256k1

/-! ## The ranges of `r` and `s` -/

/-- A first integer outside `[1, n - 1]` names no sender. -/
theorem recoverSender_r_out {fork : Fork} {tx : Transaction}
    (h : tx.r.toNat = 0 ∨ Fn.modulus ≤ tx.r.toNat) :
    recoverSender fork tx = .error .invalidSignature := by
  have hr : ¬ (0 < tx.r.toNat ∧ tx.r.toNat < Fn.modulus ∧ validS fork tx.s.toNat = true) := by
    omega
  simp only [recoverSender, hr, ↓reduceIte]

/-- A second integer of 0 names no sender. -/
theorem recoverSender_s_zero {fork : Fork} {tx : Transaction} (h : tx.s.toNat = 0) :
    recoverSender fork tx = .error .invalidSignature := by
  have hs : ¬ (0 < tx.r.toNat ∧ tx.r.toNat < Fn.modulus ∧ validS fork tx.s.toNat = true) := by
    simp [validS, h]
  simp only [recoverSender, hs, ↓reduceIte]

/-- A second integer of `n` or more names no sender, at every fork. -/
theorem recoverSender_s_ge {fork : Fork} {tx : Transaction} (h : Fn.modulus ≤ tx.s.toNat) :
    recoverSender fork tx = .error .invalidSignature := by
  have hs : ¬ (0 < tx.r.toNat ∧ tx.r.toNat < Fn.modulus ∧ validS fork tx.s.toNat = true) := by
    simp only [validS, Ecdsa.isLowS]
    split <;> simp <;> omega
  simp only [recoverSender, hs, ↓reduceIte]

/-- From Homestead, a second integer above `n / 2` names no sender. -/
theorem recoverSender_high_s {fork : Fork} {tx : Transaction} (hFork : fork ≥ .homestead)
    (h : Fn.modulus / 2 < tx.s.toNat) : recoverSender fork tx = .error .invalidSignature := by
  have hs : ¬ (0 < tx.r.toNat ∧ tx.r.toNat < Fn.modulus ∧ validS fork tx.s.toNat = true) := by
    simp only [validS, Ecdsa.isLowS, hFork, ↓reduceIte]
    simp
    omega
  simp only [recoverSender, hs, ↓reduceIte]

/-! ## The `v` of a legacy transaction -/

/-- A `v` of 27 signs no chain, with the recovery id 0. -/
theorem legacyRecovery_27 (fork : Fork) : legacyRecovery fork 27 = .ok (none, 0) := by
  simp [legacyRecovery]

/-- A `v` of 28 signs no chain, with the recovery id 1. -/
theorem legacyRecovery_28 (fork : Fork) : legacyRecovery fork 28 = .ok (none, 1) := by
  simp [legacyRecovery]

/-- From Spurious Dragon, `v = 35 + 2 c + y` signs the chain `c` with the recovery id `y`.

The chain is below 2^64. -/
theorem legacyRecovery_eip155 {fork : Fork} (hFork : fork ≥ .spuriousDragon) (c : Nat)
    (y : Fin 2) (hc : c < 2 ^ 64) :
    legacyRecovery fork (BitVec.ofNat 256 (35 + 2 * c + y.val)) =
      .ok (some (BitVec.ofNat 256 c), y) := by
  have hy := y.isLt
  have hv : (BitVec.ofNat 256 (35 + 2 * c + y.val)).toNat = 35 + 2 * c + y.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h27 : 35 + 2 * c + y.val ≠ 27 := by omega
  have h28 : 35 + 2 * c + y.val ≠ 28 := by omega
  have hc : (35 + 2 * c + y.val - 35) / 2 = c := by omega
  have h35 : 35 ≤ 35 + 2 * c + y.val ∧ (35 + 2 * c + y.val - 35) / 2 < 2 ^ 64 := by omega
  simp only [legacyRecovery, hv, h27, h28, hFork, h35, and_self, ↓reduceIte]
  have hParity : Fin.ofNat 2 ((35 + 2 * c + y.val - 35) % 2) = y := by
    apply Fin.ext
    simp only [Fin.val_ofNat]
    omega
  rw [hc, hParity]

/-- A `v` whose chain is 2^64 or more names no sender. -/
theorem legacyRecovery_chain_ge {fork : Fork} {v : U256} (h27 : v.toNat ≠ 27)
    (h28 : v.toNat ≠ 28) (hc : 2 ^ 64 ≤ (v.toNat - 35) / 2) :
    legacyRecovery fork v = .error .invalidSignature := by
  have : ¬(35 ≤ v.toNat ∧ (v.toNat - 35) / 2 < 2 ^ 64) := fun h => absurd h.2 (by omega)
  simp only [legacyRecovery, h27, h28, this, ↓reduceIte, ite_self]

/-- Before Spurious Dragon, a `v` other than 27 and 28 names no sender. -/
theorem legacyRecovery_pre155 {fork : Fork} (hFork : fork < .spuriousDragon) {v : U256}
    (h27 : v.toNat ≠ 27) (h28 : v.toNat ≠ 28) :
    legacyRecovery fork v = .error .invalidSignature := by
  have : ¬ fork ≥ .spuriousDragon := fun h => absurd (Nat.lt_of_lt_of_le hFork h) (Nat.lt_irrefl _)
  simp [legacyRecovery, h27, h28, this]

/-! ## The sender is the key that the signature recovers -/

/-- A sender is the address of the key that the signature recovers on the signing hash. -/
theorem recoverSender_eq_ok {fork : Fork} {tx : Transaction} {sender : Address}
    (h : recoverSender fork tx = .ok sender) :
    ∃ hash id x y, signingInput fork tx = .ok (hash, id) ∧
      Ecdsa.recover hash tx.r.toNat tx.s.toNat id = .ok (.affine x y) ∧
      sender = address x y := by
  unfold recoverSender at h
  split at h
  · cases hInput : signingInput fork tx with
    | error e => simp [hInput, bind, Except.bind] at h
    | ok input =>
      obtain ⟨hash, id⟩ := input
      simp only [hInput, bind, Except.bind] at h
      split at h
      · rename_i x y hRecover
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨hash, id, x, y, rfl, hRecover, h.symm⟩
      · cases h
  · cases h

/-- The recovery of a legacy `v` gives one result at every fork where it succeeds. -/
theorem legacyRecovery_eq_of_ok {fork fork' : Fork} {v : U256} {r r' : Option U256 × Fin 2}
    (h : legacyRecovery fork v = .ok r) (h' : legacyRecovery fork' v = .ok r') : r = r' := by
  unfold legacyRecovery at h h'
  split_ifs at h h' <;> simp_all

/-- The signing input of a transaction is one at every fork where it succeeds. -/
theorem signingInput_eq_of_ok {fork fork' : Fork} {tx : Transaction} {i i' : Hash32 × Fin 2}
    (h : signingInput fork tx = .ok i) (h' : signingInput fork' tx = .ok i') : i = i' := by
  cases tx with
  | legacy tx =>
    simp only [signingInput, bind, Except.bind] at h h'
    cases hr : legacyRecovery fork tx.v with
    | error e => simp [hr] at h
    | ok r =>
      cases hr' : legacyRecovery fork' tx.v with
      | error e => simp [hr'] at h'
      | ok r' =>
        obtain rfl := legacyRecovery_eq_of_ok hr hr'
        simp only [hr, hr'] at h h'
        rw [h] at h'
        exact Except.ok.inj h'
  | _ => simp only [signingInput] at h h'; rw [h] at h'; exact Except.ok.inj h'

/-- A signature names one sender at every fork where it names one. -/
theorem recoverSender_eq_of_ok {fork fork' : Fork} {tx : Transaction} {sender sender' : Address}
    (h : recoverSender fork tx = .ok sender) (h' : recoverSender fork' tx = .ok sender') :
    sender = sender' := by
  obtain ⟨hash, id, x, y, hi, hr, rfl⟩ := recoverSender_eq_ok h
  obtain ⟨hash', id', x', y', hi', hr', rfl⟩ := recoverSender_eq_ok h'
  cases signingInput_eq_of_ok hi hi'
  rw [hr] at hr'
  cases hr'
  rfl

/-- A sender is the address of a key that verifies the signature on the signing hash. -/
theorem recoverSender_verify {fork : Fork} {tx : Transaction} {sender : Address}
    (h : recoverSender fork tx = .ok sender) :
    ∃ hash id x y, signingInput fork tx = .ok (hash, id) ∧
      Ecdsa.verify (.affine x y) hash tx.r.toNat tx.s.toNat = true ∧
      sender = address x y := by
  obtain ⟨hash, id, x, y, hInput, hRecover, rfl⟩ := recoverSender_eq_ok h
  exact ⟨hash, id, x, y, hInput, Ecdsa.verify_recover hRecover, rfl⟩

/-- An honest signer is the sender.

The signer has the key `d` and the nonce `k`, and `R = k G` is `(x, y)` with `0 < x < n`.

The transaction carries `r = x`, the `s` of the signature and the parity of `y`.

When its `s` passes the rule of the fork, the sender is the address of `d G`. -/
theorem recoverSender_sign {fork : Fork} {tx : Transaction} {hash : Vector UInt8 32}
    (d k : Fn) (hd : d ≠ 0) {x y qx qy : Fp}
    (hR : Point.mul k .generator = .affine x y) (hx : x.val < Fn.modulus) (hx0 : x.val ≠ 0)
    (hs : k.inv * (Fin.ofNat _ (Ecdsa.hashToInt hash) + Fin.ofNat _ x.val * d) ≠ 0)
    (hQ : Point.mul d .generator = .affine qx qy)
    (hInput : signingInput fork tx = .ok (hash, Ecdsa.parityId y))
    (hr : tx.r.toNat = x.val)
    (hsTx : tx.s.toNat = (k.inv * (Fin.ofNat _ (Ecdsa.hashToInt hash) + Fin.ofNat _ x.val * d)).val)
    (hValid : validS fork tx.s.toNat = true) :
    recoverSender fork tx = .ok (address qx qy) := by
  have hRecover := Ecdsa.recover_sign d k hash hd hR hx hx0 hs
  have hRange : 0 < tx.r.toNat ∧ tx.r.toNat < Fn.modulus ∧ validS fork tx.s.toNat = true :=
    ⟨by omega, by omega, hValid⟩
  simp only [recoverSender, hRange, hInput, bind, Except.bind]
  rw [hr, hsTx, hRecover, hQ]
  rfl

/-! ## The chain of a legacy transaction -/

/-- A legacy transaction that reports no chain signs the hash of its six fields.

The chain that a transaction reports and the chain that its sender signed are read from one `v`.

So they agree. -/
theorem signingInput_legacy_no_chain {fork : Fork} {tx : LegacyTransaction} {hash : Hash32}
    {id : Fin 2} (h : signingInput fork (.legacy tx) = .ok (hash, id))
    (hc : Transaction.chainId fork (.legacy tx) = .ok none) :
    signingHashPre155 tx = .ok hash := by
  simp only [signingInput, bind, Except.bind] at h
  cases hv : legacyRecovery fork tx.v with
  | error e => simp only [hv] at h; cases h
  | ok r =>
    obtain ⟨chain, i⟩ := r
    obtain rfl : chain = none := by
      simp only [Transaction.chainId, hv, Functor.map, Except.map, Except.ok.injEq] at hc
      exact hc
    simp only [hv] at h
    cases hh : signingHashPre155 tx with
    | error e => simp only [hh, Except.mapError] at h; cases h
    | ok h' =>
      simp only [hh, Except.mapError, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      simp [h.1]

/-- A legacy transaction that reports the chain `c` signs the hash that covers `c`.

So it passes the chain check of a network only if its sender signed the chain of that network.

[EIP-155](https://eips.ethereum.org/EIPS/eip-155#specification) intends exactly that. -/
theorem signingInput_legacy_chain {fork : Fork} {tx : LegacyTransaction} {hash : Hash32}
    {id : Fin 2} {c : U256} (h : signingInput fork (.legacy tx) = .ok (hash, id))
    (hc : Transaction.chainId fork (.legacy tx) = .ok (some c)) :
    signingHash155 tx c = .ok hash := by
  simp only [signingInput, bind, Except.bind] at h
  cases hv : legacyRecovery fork tx.v with
  | error e => simp only [hv] at h; cases h
  | ok r =>
    obtain ⟨chain, i⟩ := r
    obtain rfl : chain = some c := by
      simp only [Transaction.chainId, hv, Functor.map, Except.map, Except.ok.injEq] at hc
      exact hc
    simp only [hv] at h
    cases hh : signingHash155 tx c with
    | error e => simp only [hh, Except.mapError] at h; cases h
    | ok h' =>
      simp only [hh, Except.mapError, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      simp [h.1]

/-- A transaction of type 1 reports the chain of its own field. -/
theorem chainId_accessList (fork : Fork) (tx : AccessListTransaction) :
    Transaction.chainId fork (.accessList tx) = .ok (some (.ofNat 256 tx.chainId.toNat)) := rfl

/-- A transaction of type 2 reports the chain of its own field. -/
theorem chainId_feeMarket (fork : Fork) (tx : FeeMarketTransaction) :
    Transaction.chainId fork (.feeMarket tx) = .ok (some (.ofNat 256 tx.chainId.toNat)) := rfl

/-- A transaction of type 3 reports the chain of its own field. -/
theorem chainId_blob (fork : Fork) (tx : BlobTransaction) :
    Transaction.chainId fork (.blob tx) = .ok (some (.ofNat 256 tx.chainId.toNat)) := rfl

/-- A transaction of type 4 reports the chain of its own field. -/
theorem chainId_setCode (fork : Fork) (tx : SetCodeTransaction) :
    Transaction.chainId fork (.setCode tx) = .ok (some (.ofNat 256 tx.chainId.toNat)) := rfl

/-! ## The signing hashes -/

/-- The signing hash of a legacy transaction that signs no chain ignores `v`, `r` and `s`. -/
theorem signingHashPre155_signature (tx : LegacyTransaction) (v r s : U256) :
    signingHashPre155 { tx with v := v, r := r, s := s } = signingHashPre155 tx := rfl

/-- The signing hash of a legacy transaction that signs a chain ignores `v`, `r` and `s`. -/
theorem signingHash155_signature (tx : LegacyTransaction) (chainId v r s : U256) :
    signingHash155 { tx with v := v, r := r, s := s } chainId = signingHash155 tx chainId := rfl

/-- The signing hash of a transaction of type 1 ignores the parity, `r` and `s`. -/
theorem signingHash2930_signature (tx : AccessListTransaction) (yParity r s : U256) :
    signingHash2930 { tx with yParity := yParity, r := r, s := s } = signingHash2930 tx := rfl

/-- The signing hash of a transaction of type 2 ignores the parity, `r` and `s`. -/
theorem signingHash1559_signature (tx : FeeMarketTransaction) (yParity r s : U256) :
    signingHash1559 { tx with yParity := yParity, r := r, s := s } = signingHash1559 tx := rfl

/-- The signing hash of a transaction of type 3 ignores the parity, `r` and `s`. -/
theorem signingHash4844_signature (tx : BlobTransaction) (yParity r s : U256) :
    signingHash4844 { tx with yParity := yParity, r := r, s := s } = signingHash4844 tx := rfl

/-- The signing hash of a transaction of type 4 ignores the parity, `r` and `s`. -/
theorem signingHash7702_signature (tx : SetCodeTransaction) (yParity r s : U256) :
    signingHash7702 { tx with yParity := yParity, r := r, s := s } = signingHash7702 tx := rfl

end EthLib.Execution.Transactions
