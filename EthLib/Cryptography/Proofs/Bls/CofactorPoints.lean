module

public import EthLib.Cryptography.Proofs.Bls.CofactorCertificateHelpers
public import EthLib.Cryptography.Proofs.Bls.CofactorPrimes

/-!
# Proofs: torsion witnesses on the BLS12-381 twist

Each point below lies on the twist, and its order is a prime that divides the cofactor of `G2`.

For each point, the proofs check four facts:

- the point is on the twist;
- it is not the point at infinity;
- its prime times the point is the point at infinity;
- the cofactor clearing of [RFC 9380 Appendix G.3][g3] sends it to the point at infinity.

The first, third and fourth are computed by the kernel in the model of `Fp`.

Each coordinate is written as two halves of 192 bits, so that each line stays short.

[g3]: https://www.rfc-editor.org/rfc/rfc9380#appendix-G.3
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

/-! ### First `13`-torsion witness -/

def q13 : G2 :=
  ⟨⟨Fp.ofNat (0x9d9acc6dfec295b33b81207e234d0806642df2fc6b3dce1 * 2 ^ 192 +
      0x4c0c3ecc7380a280338c1b757d0411eaec597b1f6547a4fe),
    Fp.ofNat (0x150a3bc83828ad1e76601cd7f02dd2b6cf3d796cb9d253fb * 2 ^ 192 +
      0x4890132f540cd4e032b00cb52033eb04480ae31d5cb2b534)⟩,
   ⟨Fp.ofNat (0x8ada15e1e4735ad3f01ae17ee6542ce9652e750d75cffb7 * 2 ^ 192 +
      0x3ebc9d71035c3ae58048a69fdb2d35c24e3ad0cd808417d8),
    Fp.ofNat (0xdb4455cc6d2ff32aa963071c7fc86975cb5d752d469fe40 * 2 ^ 192 +
      0xf20f446eab1efea8eec5e4775531abd37f9adbb9773ab715)⟩, Fp2.one⟩

theorem q13_valid : G2.Valid q13 :=
  G2.valid_of_affine_equation (by decide_eq_at_model [G2.map_bTwist])

theorem q13_nonzero : G2.toPoint q13 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q13_valid).mpr hz
  exact Bool.noConfusion h

theorem q13_annihilator : 13 • G2.toPoint q13 = 0 :=
  nsmul_zero_cert q13 q13_valid 13 5 (by decide)
    (by decide_g2_at_model [q13])

theorem q13_clear_zero : (clearAux q13).isInfinity = true := by
  decide_g2_at_model [q13, map_clearAux]

/-! ### First `23`-torsion witness -/

def q23 : G2 :=
  ⟨⟨Fp.ofNat (0x11cc8a1d961dee48fe32a3667f2b08b0368bf805d3519904 * 2 ^ 192 +
      0x267298eb9b6d18f4d1b2785d9f5d017097e910d7031260ce),
    Fp.ofNat (0x123f01c22fba16ed19c6308005e3c39f73f5e5713e948faf * 2 ^ 192 +
      0x4a636c8893f702a83278fe6097a651af7bb68f405b48f0c7)⟩,
   ⟨Fp.ofNat (0x55a433eb6245a85ef04448a52d4eb8f8641fe91f0e6e940 * 2 ^ 192 +
      0xa7f8392bdfc00b437023dc2998c29ac724be5d171ca1a792),
    Fp.ofNat (0xd33996ffad8ca6f60dae49d256ff29f93622effba220aa0 * 2 ^ 192 +
      0x1350d043eb42d256f6e3742a64aa2f7815bc52fc1f235fb8)⟩, Fp2.one⟩

theorem q23_valid : G2.Valid q23 :=
  G2.valid_of_affine_equation (by decide_eq_at_model [G2.map_bTwist])

theorem q23_nonzero : G2.toPoint q23 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q23_valid).mpr hz
  exact Bool.noConfusion h

theorem q23_annihilator : 23 • G2.toPoint q23 = 0 :=
  nsmul_zero_cert q23 q23_valid 23 6 (by decide)
    (by decide_g2_at_model [q23])

theorem q23_clear_zero : (clearAux q23).isInfinity = true := by
  decide_g2_at_model [q23, map_clearAux]

/-! ### Second independent `13`-torsion witness -/

def independent13 : G2 :=
  ⟨⟨Fp.ofNat (0x1897f02086681d6d60b80d64d9a42f0709f08602ec28801f * 2 ^ 192 +
      0xe25b2e6aab9ffbc598d23cd1f83b44beafbf84e886015d90),
    Fp.ofNat (0x133318d1f7362db44ed5b1aa6c9a11ec59103106d7519d0 * 2 ^ 192 +
      0x89b4bf7d2c2a342fd4f1b7b9a7e0fe14cf7d0f266d5f3ec5)⟩,
   ⟨Fp.ofNat (0xe4373c89afb21b5d2e36727bac0d67bda530dc9a7777cf0 * 2 ^ 192 +
      0x0bd59ddfa8e25211d35d521e701f5083560d65f0d23a7d3d),
    Fp.ofNat (0x79967f9eee9359b7aa8aa461bfdb83674f8fca32d7f7c0c * 2 ^ 192 +
      0xacb3cb5f51b5e711ea3416c76a8e307380e4d29e084c0a79)⟩, Fp2.one⟩

theorem independent13_valid : G2.Valid independent13 :=
  G2.valid_of_affine_equation (by decide_eq_at_model [G2.map_bTwist])

theorem independent13_nonzero : G2.toPoint independent13 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero independent13_valid).mpr hz
  exact Bool.noConfusion h

theorem independent13_annihilator : 13 • G2.toPoint independent13 = 0 :=
  nsmul_zero_cert independent13 independent13_valid 13 5 (by decide)
    (by decide_g2_at_model [independent13])

theorem independent13_clear_zero : (clearAux independent13).isInfinity = true := by
  decide_g2_at_model [independent13, map_clearAux]

/-! ### Second independent `23`-torsion witness -/

def independent23 : G2 :=
  ⟨⟨Fp.ofNat (0x119b712b7eda2d2e45e2941d522fe83bbf8a94d9c3759b26 * 2 ^ 192 +
      0x10a6ab9c99d0fd85c3a975aaead1a363a15ed9abe9398695),
    Fp.ofNat (0x1717fbc75f2940d63ac66e12990a8fe239f243265761137a * 2 ^ 192 +
      0xd60f8e4a245219adcf0f5a76ce5c9b1f2609a2f61f96ea57)⟩,
   ⟨Fp.ofNat (0x9932e5ac945f0804d54f6e4601cd26b9c9a7b9f4f377257 * 2 ^ 192 +
      0xd4a8db1bf0a6d6476f66a4cffbbcc9621d7cd1f66d01fec1),
    Fp.ofNat (0x15ba5a1237993b0f15569f1e734d9eb46d2f7fac612f6cfe * 2 ^ 192 +
      0xdb8175a4dbe3237b38c6189232d00caf08832a9a05117298)⟩, Fp2.one⟩

theorem independent23_valid : G2.Valid independent23 :=
  G2.valid_of_affine_equation (by decide_eq_at_model [G2.map_bTwist])

theorem independent23_nonzero : G2.toPoint independent23 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero independent23_valid).mpr hz
  exact Bool.noConfusion h

theorem independent23_annihilator : 23 • G2.toPoint independent23 = 0 :=
  nsmul_zero_cert independent23 independent23_valid 23 6 (by decide)
    (by decide_g2_at_model [independent23])

theorem independent23_clear_zero : (clearAux independent23).isInfinity = true := by
  decide_g2_at_model [independent23, map_clearAux]

/-! ### `2713`-torsion witness -/

def q2713 : G2 :=
  ⟨⟨Fp.ofNat (0xd83fc431c8a881941f19a2c49ceb641da44d2198d5cc6f8 * 2 ^ 192 +
      0x8deb141062f6578a1353ea26f781aee8ff9b20ab3cffc284),
    Fp.ofNat (0x13d4dacc5b45b8f2ecbd062ff564dd3bfee16f8bc1ee11b3 * 2 ^ 192 +
      0x5eee76bb6146aa3a88e817d47a14b2d5ba2476fbe5207ef2)⟩,
   ⟨Fp.ofNat (0xe6d6d00f9bb6036ca4c8d9cc24e199eed139598e566cf4 * 2 ^ 192 +
      0x76ff025fe1af7695a7427eea9a433230a1c4de3aac0e4d56),
    Fp.ofNat (0x1b057971f763a49a19e2953c8716f9ac8c05df834ce3de6 * 2 ^ 192 +
      0x67ac2d91f3274f0541df893e278c0b2551d915b447a16ffb)⟩, Fp2.one⟩

theorem q2713_valid : G2.Valid q2713 :=
  G2.valid_of_affine_equation (by decide_eq_at_model [G2.map_bTwist])

theorem q2713_nonzero : G2.toPoint q2713 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q2713_valid).mpr hz
  exact Bool.noConfusion h

theorem q2713_annihilator : 2713 • G2.toPoint q2713 = 0 :=
  nsmul_zero_cert q2713 q2713_valid 2713 13 (by decide)
    (by decide_g2_at_model [q2713])

theorem q2713_clear_zero : (clearAux q2713).isInfinity = true := by
  decide_g2_at_model [q2713, map_clearAux]

/-! ### `11953`-torsion witness -/

def q11953 : G2 :=
  ⟨⟨Fp.ofNat (0x159c161aab2f107b258b6d1677fa3fcc59ca7fd655186864 * 2 ^ 192 +
      0xe4e4986853db50ade19fd086bde3fd4fcaf341a82ee554e0),
    Fp.ofNat (0x4df4d4b4c3e5fb239e1beb154a19252a0d108ce83b1a91 * 2 ^ 192 +
      0x726e2cde046ff40fbad4f3f12f1d9ab5f13a8c75cc0036b9)⟩,
   ⟨Fp.ofNat (0x75b50435f8497fdd99fa917202fb3961a09e4b0f39ee274 * 2 ^ 192 +
      0x429e2ed75b10a076791e5941778e18929aab10056386c4cd),
    Fp.ofNat (0xec0c81775ea51821e5a2c97e617d7430dabed7eded67d15 * 2 ^ 192 +
      0x483c573ccf14c76e9288a697eba520e5ef19b05ef24bfecd)⟩, Fp2.one⟩

theorem q11953_valid : G2.Valid q11953 :=
  G2.valid_of_affine_equation (by decide_eq_at_model [G2.map_bTwist])

theorem q11953_nonzero : G2.toPoint q11953 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q11953_valid).mpr hz
  exact Bool.noConfusion h

theorem q11953_annihilator : 11953 • G2.toPoint q11953 = 0 :=
  nsmul_zero_cert q11953 q11953_valid 11953 15 (by decide)
    (by decide_g2_at_model [q11953])

theorem q11953_clear_zero : (clearAux q11953).isInfinity = true := by
  decide_g2_at_model [q11953, map_clearAux]

/-! ### `262069`-torsion witness -/

def q262069 : G2 :=
  ⟨⟨Fp.ofNat (0x2e54cbc39827008a39c631d164182d14e1466a30036ad5b * 2 ^ 192 +
      0xa6c5028c5fad08f7d20e13cb2b878496e156a8036bb68136),
    Fp.ofNat (0x42c08c86cb6d79796ac9b649ca13726350715aa02da5c4d * 2 ^ 192 +
      0x39798bc077895b478501d898cd807c58fd532c4c99428a2d)⟩,
   ⟨Fp.ofNat (0x17f89ecf22ca211f960a793af22bc0806959a1211aedfca0 * 2 ^ 192 +
      0x694eb05e5102e658ee5ddb2d73c025f4f75db51d745fd2a7),
    Fp.ofNat (0x17f8bc00b9885bd22edf4d7b928187a2289ecb305d38b3b5 * 2 ^ 192 +
      0x541e1f7bf7e235598e948c834644464c03ca5b6915ae234f)⟩, Fp2.one⟩

theorem q262069_valid : G2.Valid q262069 :=
  G2.valid_of_affine_equation (by decide_eq_at_model [G2.map_bTwist])

theorem q262069_nonzero : G2.toPoint q262069 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero q262069_valid).mpr hz
  exact Bool.noConfusion h

theorem q262069_annihilator : 262069 • G2.toPoint q262069 = 0 :=
  nsmul_zero_cert q262069 q262069_valid 262069 19 (by decide)
    (by decide_g2_at_model [q262069])

theorem q262069_clear_zero : (clearAux q262069).isInfinity = true := by
  decide_g2_at_model [q262069, map_clearAux]

/-! ### Large prime-torsion witness -/

def large : G2 :=
  ⟨⟨Fp.ofNat (0xa581c9e7690a91705449870cc48d7f600e6771533f3fb50 * 2 ^ 192 +
      0xd3c715d0196ad8563182cf3515e9575ff9ad966351d2a16d),
    Fp.ofNat (0x1172ac3eec3ee71bd700854f8c8ce05888f5d15f45d34053 * 2 ^ 192 +
      0x2fd1db35a406d1aab87fc9263f0743c885b59de9942c2484)⟩,
   ⟨Fp.ofNat (0xdfd63a64c1c35333cdc4f73491a4142cd2dcbae92d409e8 * 2 ^ 192 +
      0xdcf7c70b347786a7f4987c91e997d0e27665be7d8d9e1856),
    Fp.ofNat (0x13ca3a9afa928c4fb6daac16000c48b05f69f4f86e88cfdf * 2 ^ 192 +
      0x7ee5c6b4ecebe029e0d6d23b88d3897a86ec2e650cfe68bd)⟩, Fp2.one⟩

theorem large_valid : G2.Valid large :=
  G2.valid_of_affine_equation (by decide_eq_at_model [G2.map_bTwist])

theorem large_nonzero : G2.toPoint large ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero large_valid).mpr hz
  exact Bool.noConfusion h

theorem large_annihilator : CofactorPrimes.largePrime • G2.toPoint large = 0 :=
  nsmul_zero_cert large large_valid _ 449 (by decide +kernel)
    (by decide_g2_at_model [large])

theorem large_clear_zero : (clearAux large).isInfinity = true := by
  decide_g2_at_model [large, map_clearAux]

end EthLib.Cryptography.Bls.CofactorCertificate
