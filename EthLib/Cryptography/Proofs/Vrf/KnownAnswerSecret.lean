import EthLib.Cryptography.Proofs.Vrf.Kernel

/-!
# Proofs: VRF tree known answers for the leaf secrets

One seed, whose byte `k` is `(17 k + 9) mod 256`.

Its secrets and outputs at indices 0 and `2^32 - 1` were computed outside EthLib, with Keccak-256 from RustCrypto's `sha3` crate.

The kernel checks every answer, with no `native_decide`.
-/

namespace EthLib.Cryptography.Vrf.KnownAnswer

open EthLib.Cryptography.Vrf

/-- The index is written least significant byte first. -/
theorem indexBytes_example : indexBytes 0x01020304 = #v[0x04, 0x03, 0x02, 0x01] := by
  decide +kernel

/-- The seed: a fixed byte pattern, for this test only. -/
def seed : Seed :=
  Vector.ofFn fun k => UInt8.ofNat (17 * k.val + 9)

/-- The secret at index 0, computed outside EthLib. -/
def seedSecretZero : Digest :=
  #v[0x13, 0x9c, 0xc9, 0xc3, 0x98, 0xfc, 0x8a, 0xab, 0x72, 0xbb, 0x6e, 0xc8, 0x3f, 0x82, 0x13, 0x57,
    0x9d, 0xd2, 0x17, 0x47, 0x9f, 0xcd, 0x0a, 0x1b, 0x53, 0x6d, 0xba, 0xec, 0x42, 0x4e, 0xe1, 0xac]

/-- The secret at index 0 is the one computed outside EthLib. -/
theorem secret_zero : secret seed 0 = seedSecretZero := by
  rw [Kernel.secret_eq]
  decide +kernel

/-- The output at index 0, computed outside EthLib. -/
def seedOutputZero : Digest :=
  #v[0xc3, 0x7e, 0xa9, 0xb1, 0x68, 0xdc, 0x90, 0x33, 0xf3, 0x0d, 0xf8, 0xf1, 0x61, 0x26, 0xf1, 0xcb,
    0x29, 0x52, 0x20, 0x3b, 0xa9, 0x40, 0x8e, 0x77, 0xec, 0x48, 0x27, 0x04, 0x69, 0x2f, 0x7f, 0x50]

/-- The output at index 0 is the one computed outside EthLib. -/
theorem evaluate_zero : evaluate seed 0 = seedOutputZero := by
  rw [evaluate, Kernel.outputHash_eq, Kernel.secret_eq]
  decide +kernel

/-- The secret at index `2^32 - 1`, computed outside EthLib. -/
def seedSecretLast : Digest :=
  #v[0x49, 0x30, 0x6e, 0xbc, 0xa1, 0x2a, 0x70, 0x66, 0x5b, 0xec, 0xba, 0xf9, 0xbe, 0xc1, 0x34, 0x53,
    0xb4, 0xc2, 0x53, 0xa9, 0x88, 0x3b, 0xb8, 0x11, 0x15, 0xa0, 0x2d, 0x9d, 0xbc, 0x58, 0xf6, 0xd2]

/-- The secret at index `2^32 - 1` is the one computed outside EthLib. -/
theorem secret_last : secret seed 0xFFFFFFFF = seedSecretLast := by
  rw [Kernel.secret_eq]
  decide +kernel

/-- The output at index `2^32 - 1`, computed outside EthLib. -/
def seedOutputLast : Digest :=
  #v[0xba, 0x9e, 0x18, 0x1f, 0x73, 0xe4, 0x44, 0x9b, 0x96, 0xbf, 0x18, 0x1e, 0xd8, 0x34, 0x9c, 0x9e,
    0xe9, 0x11, 0xd0, 0xc5, 0x2e, 0x55, 0x2f, 0x67, 0x7f, 0xbc, 0x8e, 0xe3, 0xed, 0xc3, 0x31, 0xdf]

/-- The output at index `2^32 - 1` is the one computed outside EthLib. -/
theorem evaluate_last : evaluate seed 0xFFFFFFFF = seedOutputLast := by
  rw [evaluate, Kernel.outputHash_eq, Kernel.secret_eq]
  decide +kernel

end EthLib.Cryptography.Vrf.KnownAnswer
