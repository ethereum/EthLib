/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trail of Bits
-/

module
public import EthLib.Cryptography.Proofs.Xmss.Encoding

/-!
# Accepted EthLib target-sum digests

The 58 retained digits determine an accepted digest because its six omitted digits are zero.
This assertion is restricted to accepted digests; truncation of arbitrary digests loses 12 bits.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- Digests accepted by the source target-sum decoder. -/
@[expose] def AcceptedDigest := {d : Digest // (codeword? d).isSome}

/-- The source decoder's 58 digits of an accepted digest. -/
@[expose] def acceptedDigits (d : AcceptedDigest) : Vector (Fin CHAIN_LENGTH) V :=
  (codeword? d.val).get d.property

/-- The retained digits are the actual successful decoder output. -/
theorem codeword_acceptedDigits (d : AcceptedDigest) :
    codeword? d.val = some (acceptedDigits d) := by
  exact (Option.some_get d.property).symm

/-- Accepted digests with the same retained digits are equal. -/
theorem acceptedDigits_injective : Function.Injective acceptedDigits := by
  intro d d' h
  apply Subtype.ext
  have h' := codeword_acceptedDigits d'
  rw [← h] at h'
  exact eq_of_codeword (codeword_acceptedDigits d) h'

/-- Accepted digits sum to 106. -/
theorem acceptedDigits_sum (d : AcceptedDigest) :
    ∑ i : Fin V, ((acceptedDigits d)[i] : Nat) = 106 :=
  sum_of_codeword (codeword_acceptedDigits d)

/-- All six omitted two-bit digits of an accepted digest are zero. -/
theorem accepted_tail_zero (d : AcceptedDigest) (i : Nat) (hlo : 58 ≤ i) (hhi : i < 64) :
    EthLib.Base.bytesToUint d.val / 4 ^ i % 4 = 0 :=
  (codeword?_eq_some (codeword_acceptedDigits d)).2.1 i hlo hhi

/-- Distinct accepted digests have a smaller digit in each orientation. -/
theorem acceptedDigits_incomparable (d d' : AcceptedDigest) (hne : d ≠ d') :
    (∃ i : Fin V, ((acceptedDigits d)[i] : Nat) < ((acceptedDigits d')[i] : Nat)) ∧
      (∃ i : Fin V, ((acceptedDigits d')[i] : Nat) < ((acceptedDigits d)[i] : Nat)) := by
  apply codeword_incomparable (codeword_acceptedDigits d) (codeword_acceptedDigits d')
  exact fun h => hne (acceptedDigits_injective h)

/-- Both the chain count and the number of chain steps are positive. -/
theorem encoding_parameters_positive : 0 < V ∧ 0 < CHAIN_LENGTH - 1 := by decide

/-- One accepted digest has 35 low digits equal to three, followed by a one. -/
@[expose] def acceptedExampleFirst : AcceptedDigest :=
  ⟨EthLib.Base.uintToBytes 16 (2 * 4 ^ 35 - 1), by decide⟩

/-- A second accepted digest moves the isolated one one digit upward. -/
@[expose] def acceptedExampleSecond : AcceptedDigest :=
  ⟨EthLib.Base.uintToBytes 16 (4 ^ 36 + 4 ^ 35 - 1), by decide⟩

/-- The accepted domain contains at least two distinct digests. -/
theorem accepted_examples_distinct : acceptedExampleFirst ≠ acceptedExampleSecond := by
  intro h
  have hval := congrArg (fun d : AcceptedDigest => EthLib.Base.bytesToUint d.val) h
  change EthLib.Base.bytesToUint (EthLib.Base.uintToBytes 16 (2 * 4 ^ 35 - 1)) =
    EthLib.Base.bytesToUint (EthLib.Base.uintToBytes 16 (4 ^ 36 + 4 ^ 35 - 1)) at hval
  simp only [EthLib.Base.bytesToUint_uintToBytes] at hval
  norm_num at hval

end EthereumXMSSHypertree
