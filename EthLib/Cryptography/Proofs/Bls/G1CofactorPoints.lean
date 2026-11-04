module

public import EthLib.Cryptography.Proofs.Bls.G1Rotation
public import EthLib.Cryptography.Proofs.Bls.Compress

/-!
# Proofs: torsion points of `G1` for the cofactor

The cofactor of `G1` is `h = 3 * 11^2 * 10177^2 * 859267^2 * 52437899^2`.

Here is a point of order `3`, and two independent points of order `q` for each other prime `q`.

The kernel checks each order and each sum of a point and its rotations.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1Rotation

open G1

-- The certificates evaluate the curve arithmetic on 381-bit coordinates.
set_option maxRecDepth 8000

/-! ### Order 3 -/

/-- The point `(0, 2)`, of order `3`. -/
def p3 : G1 := ⟨Fp.zero, Fp.ofNat 2, Fp.one⟩

theorem p3_valid : Valid p3 := valid_of_affine_eq (by decide)

theorem p3_torsion : 3 • toPoint p3 = 0 :=
  nsmul_zero_cert p3_valid 3 2 (by decide) (by decide +kernel)

theorem p3_ne_zero : toPoint p3 ≠ 0 := toPoint_ne_zero p3_valid

/-! ### Order 11 -/

/-- A point of order `11`. -/
def p11 : G1 :=
  ⟨Fp.ofNat (0x3f71f11906b170ed96f69490726ef9306c224d4a2b4d8d9 * 2 ^ 192 +
      0x70feca92b4d8d208eccb74cf3b4c831f1247e6609708996c),
    Fp.ofNat (0x66ad6e999f120eab9207d5d1e434f360b68c699084f3e86 * 2 ^ 192 +
      0x80006e10211952be0d5ce9d52dbc224d61fefd7765c8e669), Fp.one⟩

/-- The rotation of the point of order `11`. -/
def q11 : G1 :=
  ⟨Fp.ofNat (0x176453223f6e552ba89ef7d714f4a1af42a606054986b375 * 2 ^ 192 +
      0x606501c96069c030b9b58ecda0035a2b7fbcabc7df755577),
    Fp.ofNat (0x66ad6e999f120eab9207d5d1e434f360b68c699084f3e86 * 2 ^ 192 +
      0x80006e10211952be0d5ce9d52dbc224d61fefd7765c8e669), Fp.one⟩

/-- The double rotation of the point of order `11`. -/
def r11 : G1 :=
  ⟨Fp.ofNat (0x18a6b1a0a32660fa1428ee4c6a7bc86c7f866c2fface992f * 2 ^ 192 +
      0xfcfdd8e5d81f5a0e96d6fc60875822b4e1f96dd789816673),
    Fp.ofNat (0x66ad6e999f120eab9207d5d1e434f360b68c699084f3e86 * 2 ^ 192 +
      0x80006e10211952be0d5ce9d52dbc224d61fefd7765c8e669), Fp.one⟩

theorem p11_valid : Valid p11 := valid_of_affine_eq (by decide)

theorem q11_valid : Valid q11 := valid_of_affine_eq (by decide)

private theorem r11_valid : Valid r11 := valid_of_affine_eq (by decide)

theorem p11_torsion : 11 • toPoint p11 = 0 :=
  nsmul_zero_cert p11_valid 11 4 (by decide) (by decide +kernel)

theorem q11_torsion : 11 • toPoint q11 = 0 :=
  nsmul_zero_cert q11_valid 11 4 (by decide) (by decide +kernel)

theorem p11_ne_zero : toPoint p11 ≠ 0 := toPoint_ne_zero p11_valid

/-- The point of order `11` and its rotation are independent. -/
theorem q11_not_nsmul (i : Fin 11) : toPoint q11 ≠ i.val • toPoint p11 :=
  not_nsmul_of_rotation (by norm_num) p11_valid q11_valid r11_valid
    (eq_of_decide (by decide)) (eq_of_decide (by decide)) p11_torsion
    (sum_zero_cert p11_valid q11_valid r11_valid (by decide +kernel))
    (fun i _ hd => absurd hd (not_dvd_of_nonresidue (by norm_num) (by decide) (by decide)
      (fuel := 4) (by decide) (by decide +kernel) i)) i

/-! ### Order 10177 -/

/-- A point of order `10177`. -/
def p10177 : G1 :=
  ⟨Fp.ofNat (0x19047b0df533b31c20e000422904bd515a002a9adda1c84b * 2 ^ 192 +
      0x93e7c364df5c757233f66fc5400dc994694fd5811ff0c0d3),
    Fp.ofNat (0xfb6c6bc741ce191f849ef07e10deae221513c7e76791dbb * 2 ^ 192 +
      0x38190d88079be8d30cc117ff129051c902b90fee55abae0b), Fp.one⟩

/-- The rotation of the point of order `10177`. -/
def q10177 : G1 :=
  ⟨Fp.ofNat (0x6a7d66bf656e4584c5ad6f0ee94ff195ce8fd15ac54e6cd * 2 ^ 192 +
      0x1e0b48b58e668d3be119c2eb8a01b02b95d70656d243b662),
    Fp.ofNat (0xfb6c6bc741ce191f849ef07e10deae221513c7e76791dbb * 2 ^ 192 +
      0x38190d88079be8d30cc117ff129051c902b90fee55abae0b), Fp.one⟩

/-- The double rotation of the point of order `10177`. -/
def r10177 : G1 :=
  ⟨Fp.ofNat (0x1455d25a877535c028fc78396efd9d4412056f595d137666 * 2 ^ 192 +
      0x1c6e99277f9ee99a2847cd4c9898863f74d724280dcade21),
    Fp.ofNat (0xfb6c6bc741ce191f849ef07e10deae221513c7e76791dbb * 2 ^ 192 +
      0x38190d88079be8d30cc117ff129051c902b90fee55abae0b), Fp.one⟩

theorem p10177_valid : Valid p10177 := valid_of_affine_eq (by decide)

theorem q10177_valid : Valid q10177 := valid_of_affine_eq (by decide)

private theorem r10177_valid : Valid r10177 := valid_of_affine_eq (by decide)

theorem p10177_torsion : 10177 • toPoint p10177 = 0 :=
  nsmul_zero_cert p10177_valid 10177 14 (by decide) (by decide +kernel)

theorem q10177_torsion : 10177 • toPoint q10177 = 0 :=
  nsmul_zero_cert q10177_valid 10177 14 (by decide) (by decide +kernel)

theorem p10177_ne_zero : toPoint p10177 ≠ 0 := toPoint_ne_zero p10177_valid

/-- The point of order `10177` and its rotation are independent. -/
theorem q10177_not_nsmul (i : Fin 10177) : toPoint q10177 ≠ i.val • toPoint p10177 :=
  not_nsmul_of_rotation (by norm_num) p10177_valid q10177_valid r10177_valid
    (eq_of_decide (by decide)) (eq_of_decide (by decide)) p10177_torsion
    (sum_zero_cert p10177_valid q10177_valid r10177_valid (by decide +kernel))
    (fun i hi hd => by
      rcases eq_root_of_dvd (l1 := 4773) (l2 := 5403) (by norm_num) (by decide) (by decide)
        (by decide) (by decide) hi hd with rfl | rfl
      · exact nsmul_ne_cert p10177_valid q10177_valid 4773 14 (by decide) (by decide +kernel)
      · exact nsmul_ne_cert p10177_valid q10177_valid 5403 14 (by decide) (by decide +kernel)) i

/-! ### Order 859267 -/

/-- A point of order `859267`. -/
def p859267 : G1 :=
  ⟨Fp.ofNat (0x1527e854158f21dfd9bf9e28e1962d4d8c81a813b16975fa * 2 ^ 192 +
      0xf4d4fa23bfe623e1093ed778a8881e2614d41fc37c1e72c6),
    Fp.ofNat (0x1615dac9c1350255f9fe5f24d9124d0939b802da057165aa * 2 ^ 192 +
      0x7d76505e764422598049883c86f7068c5b9b7e57e19245e0), Fp.one⟩

/-- The rotation of the point of order `859267`. -/
def q859267 : G1 :=
  ⟨Fp.ofNat (0xa67c7c40c706f157e51f3f6e5854ae12332975632b58072 * 2 ^ 192 +
      0x5e618af956f85da6ebdf7569e27ec9943a2bfcc0869c9542),
    Fp.ofNat (0x1615dac9c1350255f9fe5f24d9124d0939b802da057165aa * 2 ^ 192 +
      0x7d76505e764422598049883c86f7068c5b9b7e57e19245e0), Fp.one⟩

/-- The double rotation of the point of order `859267`. -/
def r859267 : G1 :=
  ⟨Fp.ofNat (0x147273bc51003c3f3e25bd4cbf7be180193a57a002eb2f11 * 2 ^ 192 +
      0x7b2b2024d6836ac04839b31ad7a1184524fde37bfd444d4e),
    Fp.ofNat (0x1615dac9c1350255f9fe5f24d9124d0939b802da057165aa * 2 ^ 192 +
      0x7d76505e764422598049883c86f7068c5b9b7e57e19245e0), Fp.one⟩

theorem p859267_valid : Valid p859267 := valid_of_affine_eq (by decide)

theorem q859267_valid : Valid q859267 := valid_of_affine_eq (by decide)

private theorem r859267_valid : Valid r859267 := valid_of_affine_eq (by decide)

theorem p859267_torsion : 859267 • toPoint p859267 = 0 :=
  nsmul_zero_cert p859267_valid 859267 20 (by decide) (by decide +kernel)

theorem q859267_torsion : 859267 • toPoint q859267 = 0 :=
  nsmul_zero_cert q859267_valid 859267 20 (by decide) (by decide +kernel)

theorem p859267_ne_zero : toPoint p859267 ≠ 0 := toPoint_ne_zero p859267_valid

/-- The point of order `859267` and its rotation are independent. -/
theorem q859267_not_nsmul (i : Fin 859267) : toPoint q859267 ≠ i.val • toPoint p859267 :=
  not_nsmul_of_rotation (by norm_num) p859267_valid q859267_valid r859267_valid
    (eq_of_decide (by decide)) (eq_of_decide (by decide)) p859267_torsion
    (sum_zero_cert p859267_valid q859267_valid r859267_valid (by decide +kernel))
    (fun i hi hd => by
      rcases eq_root_of_dvd (l1 := 119571) (l2 := 739695) (by norm_num) (by decide) (by decide)
        (by decide) (by decide) hi hd with rfl | rfl
      · exact nsmul_ne_cert p859267_valid q859267_valid 119571 20 (by decide) (by decide +kernel)
      · exact nsmul_ne_cert p859267_valid q859267_valid 739695 20 (by decide) (by decide +kernel)) i

/-! ### Order 52437899 -/

/-- A point of order `52437899`. -/
def p52437899 : G1 :=
  ⟨Fp.ofNat (0x5c22819c8235a0d4cd82e964b045c74ad19dff8646cd7c2 * 2 ^ 192 +
      0x8426922f6971c10a69ce1f716de98569cd90ee8850522107),
    Fp.ofNat (0x137d0f9322d15d4f815a42f1cf1f72e3e8dc540c109d81a3 * 2 ^ 192 +
      0xf83589c754f0630921fe40a30bac497306d460537f490049), Fp.one⟩

/-- The rotation of the point of order `52437899`. -/
def q52437899 : G1 :=
  ⟨Fp.ofNat (0x193ad5062b72f8d75a2da89723cc5c369ab265859bba380c * 2 ^ 192 +
      0x5a0302ad4b9617c7c81f9d6e70a32039c4417759680ec51f),
    Fp.ofNat (0x137d0f9322d15d4f815a42f1cf1f72e3e8dc540c109d81a3 * 2 ^ 192 +
      0xf83589c754f0630921fe40a30bac497306d460537f490049), Fp.one⟩

/-- The double rotation of the point of order `52437899`. -/
def r52437899 : G1 :=
  ⟨Fp.ofNat (0x150526b47f697a4fef31783f17c6a1038122518be6e315af * 2 ^ 192 +
      0xf0381065385a13760b6a431d841b5a5be22b9a1e479e6f30),
    Fp.ofNat (0x137d0f9322d15d4f815a42f1cf1f72e3e8dc540c109d81a3 * 2 ^ 192 +
      0xf83589c754f0630921fe40a30bac497306d460537f490049), Fp.one⟩

theorem p52437899_valid : Valid p52437899 := valid_of_affine_eq (by decide)

theorem q52437899_valid : Valid q52437899 := valid_of_affine_eq (by decide)

private theorem r52437899_valid : Valid r52437899 := valid_of_affine_eq (by decide)

theorem p52437899_torsion : 52437899 • toPoint p52437899 = 0 :=
  nsmul_zero_cert p52437899_valid 52437899 26 (by decide) (by decide +kernel)

theorem q52437899_torsion : 52437899 • toPoint q52437899 = 0 :=
  nsmul_zero_cert q52437899_valid 52437899 26 (by decide) (by decide +kernel)

theorem p52437899_ne_zero : toPoint p52437899 ≠ 0 := toPoint_ne_zero p52437899_valid

/-- The point of order `52437899` and its rotation are independent. -/
theorem q52437899_not_nsmul (i : Fin 52437899) : toPoint q52437899 ≠ i.val • toPoint p52437899 :=
  not_nsmul_of_rotation (by norm_num) p52437899_valid q52437899_valid r52437899_valid
    (eq_of_decide (by decide)) (eq_of_decide (by decide)) p52437899_torsion
    (sum_zero_cert p52437899_valid q52437899_valid r52437899_valid (by decide +kernel))
    (fun i _ hd => absurd hd (not_dvd_of_nonresidue (by norm_num) (by decide) (by decide)
      (fuel := 26) (by decide) (by decide +kernel) i)) i

end EthLib.Cryptography.Bls.G1Rotation
