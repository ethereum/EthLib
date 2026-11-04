module

public import EthLib.Cryptography.Sphincs.Digest

/-!
# Proofs: `Sphincs.Digest`

The fields read from the message digest are its low 266 bits, with no overlap and no gap.

```text
    LE^-1(D) mod 2^266 = idx + sum_{kappa < 24} leaf_kappa * 2^(26 + 10 kappa)
```

So the index and the 24 leaves together carry exactly the digest's low 266 bits.

A uniform digest then gives a uniform index and 24 independent uniform leaves.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- The digest's index has 26 bits. -/
theorem digestIndex_lt (d : MessageDigest) : digestIndex d < 2 ^ HEIGHT :=
  Nat.mod_lt _ (by decide)

/-- The low `26 + 10k` bits of a number are its index and its first `k` leaves. -/
theorem mod_eq_index_add_leaves (n : Nat) : ∀ k : Nat,
    n % 2 ^ (HEIGHT + FORS_HEIGHT * k)
      = n % 2 ^ HEIGHT
        + ((List.range k).map fun kappa =>
            n / 2 ^ (HEIGHT + FORS_HEIGHT * kappa) % 2 ^ FORS_HEIGHT
              * 2 ^ (HEIGHT + FORS_HEIGHT * kappa)).sum := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    -- One more leaf is 10 more bits above the ones already read.
    rw [List.range_succ, List.map_append, List.sum_append_nat, ← Nat.add_assoc, ← ih,
      List.map_singleton, List.sum_singleton, Nat.mul_succ, ← Nat.add_assoc, Nat.pow_add,
      Nat.mod_mul]
    exact congrArg _ (Nat.mul_comm _ _)

/-- The digest's low 266 bits are its index and its 24 leaves, each in its own place. -/
theorem digest_fields (d : MessageDigest) :
    bytesToUint d % 2 ^ DIGEST_BITS
      = digestIndex d
        + ((List.finRange FORS_TREES).map fun kappa : Fin FORS_TREES =>
            ((digestLeaves d)[kappa] : Nat) * 2 ^ (HEIGHT + FORS_HEIGHT * kappa.val)).sum := by
  rw [DIGEST_BITS, Nat.mul_comm FORS_TREES, mod_eq_index_add_leaves, digestIndex,
    Nat.add_left_cancel_iff]
  refine congrArg List.sum (List.ext_getElem (by simp) fun i _ _ => ?_)
  simp [digestLeaves]

/-- Two digests with the same index and the same leaves agree on their low 266 bits. -/
theorem digest_fields_inj {d d' : MessageDigest} (hidx : digestIndex d = digestIndex d')
    (hleaves : digestLeaves d = digestLeaves d') :
    bytesToUint d % 2 ^ DIGEST_BITS = bytesToUint d' % 2 ^ DIGEST_BITS := by
  rw [digest_fields, digest_fields, hidx, hleaves]

end EthLib.Cryptography.Sphincs
