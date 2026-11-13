/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.Encoding
public import EthLib.Cryptography.Xmss.Ots
public import HashSig.GXMSS.Encoding.TargetSum

/-!
# EthLib decoding into the existing generic incomparable-encoding API

The source's 58 retained digits are represented as the existing generic codeword functions.
The decoder keeps its actual failure condition, including all six zero tail digits. Successful
words belong to the existing global target-sum code. Sampling and collision security are separate.
-/

public section

namespace EthereumXMSSHypertree.GenericEncoding

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants
open GXMSS.Encoding

/-- The source digit vectors and existing generic 58-digit base-four words contain the same data. -/
@[expose] def sourceCodewordEquiv : Vector (Fin 4) 58 ≃ Codeword 58 (2 ^ 2) where
  toFun digits := fun i => digits[i]
  invFun word := Vector.ofFn word
  left_inv digits := by
    apply Vector.ext
    intro i hi
    simp
  right_inv word := by
    funext i
    simp

/-- Every successful source decoder output belongs to the actual generic target-sum code. -/
theorem source_codeword_mem {digest : Digest} {digits : Vector (Fin CHAIN_LENGTH) V}
    (h : codeword? digest = some digits) :
    sourceCodewordEquiv digits ∈ TargetSum.code 58 2 106 := by
  change (∑ i : Fin V, (digits[i] : Nat)) = TARGET_SUM
  exact sum_of_codeword h

/-- The existing generic representation of an accepted source digest. -/
@[expose] def acceptedCodeword (digest : AcceptedDigest) : Codeword 58 (2 ^ 2) :=
  sourceCodewordEquiv (acceptedDigits digest)

/-- The represented accepted source digest lies in the existing generic code. -/
theorem acceptedCodeword_mem (digest : AcceptedDigest) :
    acceptedCodeword digest ∈ TargetSum.code 58 2 106 :=
  source_codeword_mem (codeword_acceptedDigits digest)

/-- Injectivity is restricted to digests accepted by the actual source decoder. -/
theorem acceptedCodeword_injective : Function.Injective acceptedCodeword := by
  intro digest digest' h
  exact acceptedDigits_injective (sourceCodewordEquiv.injective h)

/-- The actual generic global-code theorem gives both strict orientations for accepted digests. -/
theorem acceptedCodeword_incomparable (digest digest' : AcceptedDigest) (hne : digest ≠ digest') :
    IncomparableWords (acceptedCodeword digest) (acceptedCodeword digest') :=
  TargetSum.code_incomparable 58 2 106 (acceptedCodeword_mem digest)
    (acceptedCodeword_mem digest') (fun h => hne (acceptedCodeword_injective h))

/-- One actual generic codeword supplied by the first explicit accepted source digest. -/
@[expose] def firstCodeword : Codeword 58 (2 ^ 2) := acceptedCodeword acceptedExampleFirst

/-- A distinct actual generic codeword supplied by the second explicit accepted source digest. -/
@[expose] def secondCodeword : Codeword 58 (2 ^ 2) := acceptedCodeword acceptedExampleSecond

/-- The first explicit word belongs to the actual generic code. -/
theorem firstCodeword_mem : firstCodeword ∈ TargetSum.code 58 2 106 :=
  acceptedCodeword_mem acceptedExampleFirst

/-- The second explicit word belongs to the actual generic code. -/
theorem secondCodeword_mem : secondCodeword ∈ TargetSum.code 58 2 106 :=
  acceptedCodeword_mem acceptedExampleSecond

/-- The represented source witnesses remain distinct in the actual generic codeword type. -/
theorem codeword_examples_distinct : firstCodeword ≠ secondCodeword :=
  fun h => accepted_examples_distinct (acceptedCodeword_injective h)

/-- The existing generic code has at least two explicit words, without enumerating its domain. -/
theorem two_codewords : ∃ first second : Codeword 58 (2 ^ 2),
    first ∈ TargetSum.code 58 2 106 ∧ second ∈ TargetSum.code 58 2 106 ∧ first ≠ second :=
  ⟨firstCodeword, secondCodeword, firstCodeword_mem, secondCodeword_mem,
    codeword_examples_distinct⟩

/-- The concrete chain count and digit-bit parameter satisfy the generic positive premises. -/
theorem positive_parameters : 0 < (58 : Nat) ∧ 0 < (2 : Nat) := by decide

/-- The source decoder as the actual generic fallible incomparable encoding.

The fixed hash, source layer and message-byte representation are captured by the constructor.
The algorithm first runs the source message hash and then its complete `codeword?` test.
-/
@[expose] def sourceEncoding {M : Type} (H : ByteArray → Vector UInt8 32) (layer : Layer)
    (messageBytes : M → ByteArray) : IncomparableEncoding PublicParam M Randomizer UInt32 58 4 where
  code := TargetSum.code 58 2 106
  incomparable := TargetSum.code_incomparable 58 2 106
  encode pp msg rho epoch :=
    match h : codeword?
        ((messageDigest (pureHash H) pp layer epoch (messageBytes msg) rho).run) with
    | none => none
    | some digits => some ⟨sourceCodewordEquiv digits, source_codeword_mem h⟩

/-- Observing the actual generic encoding preserves the source decoder's exact optional output. -/
theorem sourceEncoding_value {M : Type} (H : ByteArray → Vector UInt8 32) (layer : Layer)
    (messageBytes : M → ByteArray) (pp : PublicParam) (msg : M) (rho : Randomizer)
    (epoch : UInt32) :
    (sourceEncoding H layer messageBytes).value pp msg rho epoch =
      (codeword? ((messageDigest (pureHash H) pp layer epoch (messageBytes msg) rho).run)).map
        sourceCodewordEquiv := by
  dsimp only [sourceEncoding, IncomparableEncoding.value]
  split
  · rename_i h
    conv_rhs => rw [h]
    rfl
  · rename_i digits h
    conv_rhs => rw [h]
    rfl

/-- The generic value fails exactly when the actual complete source decoder fails. -/
theorem sourceEncoding_value_eq_none_iff {M : Type} (H : ByteArray → Vector UInt8 32)
    (layer : Layer) (messageBytes : M → ByteArray) (pp : PublicParam) (msg : M)
    (rho : Randomizer) (epoch : UInt32) :
    (sourceEncoding H layer messageBytes).value pp msg rho epoch = none ↔
      codeword? ((messageDigest (pureHash H) pp layer epoch (messageBytes msg) rho).run) =
        none := by
  rw [sourceEncoding_value]
  exact Option.map_eq_none_iff

/-- A successful generic value retains the actual successful source-output equation. -/
theorem sourceEncoding_value_eq_some_iff {M : Type} (H : ByteArray → Vector UInt8 32)
    (layer : Layer) (messageBytes : M → ByteArray) (pp : PublicParam) (msg : M)
    (rho : Randomizer) (epoch : UInt32) (word : Codeword 58 4) :
    (sourceEncoding H layer messageBytes).value pp msg rho epoch = some word ↔
      ∃ digits, codeword? ((messageDigest (pureHash H) pp layer epoch (messageBytes msg) rho).run) =
        some digits ∧ sourceCodewordEquiv digits = word := by
  rw [sourceEncoding_value]
  exact Option.map_eq_some_iff

/-- Successful generic outputs retain all six source zero-tail constraints. -/
theorem sourceEncoding_success_tail_zero {M : Type} (H : ByteArray → Vector UInt8 32)
    (layer : Layer) (messageBytes : M → ByteArray) (pp : PublicParam) (msg : M)
    (rho : Randomizer) (epoch : UInt32) {word : Codeword 58 4}
    (h : (sourceEncoding H layer messageBytes).value pp msg rho epoch = some word)
    (i : Nat) (hlo : 58 ≤ i) (hhi : i < 64) :
    EthLib.Base.bytesToUint
      ((messageDigest (pureHash H) pp layer epoch (messageBytes msg) rho).run) / 4 ^ i % 4 = 0 := by
  obtain ⟨digits, hsource, _⟩ :=
    (sourceEncoding_value_eq_some_iff H layer messageBytes pp msg rho epoch word).1 h
  exact (codeword?_eq_some hsource).2.1 i hlo hhi

/-- A nonzero omitted source digit forces generic returned failure. -/
theorem sourceEncoding_rejects_nonzero_tail {M : Type} (H : ByteArray → Vector UInt8 32)
    (layer : Layer) (messageBytes : M → ByteArray) (pp : PublicParam) (msg : M)
    (rho : Randomizer) (epoch : UInt32) (i : Nat) (hlo : 58 ≤ i) (hhi : i < 64)
    (hne : EthLib.Base.bytesToUint
      ((messageDigest (pureHash H) pp layer epoch (messageBytes msg) rho).run) / 4 ^ i % 4 ≠ 0) :
    (sourceEncoding H layer messageBytes).value pp msg rho epoch = none := by
  cases h : (sourceEncoding H layer messageBytes).value pp msg rho epoch with
  | none => rfl
  | some word =>
    exact (hne (sourceEncoding_success_tail_zero H layer messageBytes pp msg rho epoch h
      i hlo hhi)).elim

/-- The bottom source fibre contains exactly the source 32-byte messages. -/
@[expose] def bottomEncoding (H : ByteArray → Vector UInt8 32) :
    IncomparableEncoding PublicParam Message Randomizer UInt32 58 4 :=
  sourceEncoding H .bottom packBytes

/-- The top source fibre contains exactly the source 16-byte digest messages. -/
@[expose] def topEncoding (H : ByteArray → Vector UInt8 32) :
    IncomparableEncoding PublicParam Digest Randomizer UInt32 58 4 :=
  sourceEncoding H .top packBytes

end EthereumXMSSHypertree.GenericEncoding
