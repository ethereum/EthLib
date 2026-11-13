module

public import EthLib.Cryptography.X25519
public import EthLib.Cryptography.Proofs.Pratt
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime

/-!
# Proofs: the field of Curve25519

The modulus `2^255 - 19` of [RFC 7748 §4.1][rfc] is prime.

A Pratt certificate proves it, checked by the kernel.

So `Fp` is the field `ZMod (2^255 - 19)`, and the identity map carries each operation over.

[rfc]: https://www.rfc-editor.org/rfc/rfc7748#section-4.1
-/

@[expose] public section

namespace EthLib.Cryptography.X25519

-- The kernel evaluates each power check by `decide`, which recurses deeply.
set_option maxRecDepth 8000

/-- `132049` is prime, with witness `26`. -/
private theorem prime_132049 : Nat.Prime 132049 :=
  Pratt.prime_of_lucas 132049 26 256 [(2, 4), (3, 2), (7, 1), (131, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `1923133` is prime, with witness `2`. -/
private theorem prime_1923133 : Nat.Prime 1923133 :=
  Pratt.prime_of_lucas 1923133 2 256 [(2, 2), (3, 1), (43, 1), (3727, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `430751` is prime, with witness `17`. -/
private theorem prime_430751 : Nat.Prime 430751 :=
  Pratt.prime_of_lucas 430751 17 256 [(2, 1), (5, 3), (1723, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `31757755568855353` is prime, with witness `10`. -/
private theorem prime_31757755568855353 : Nat.Prime 31757755568855353 :=
  Pratt.prime_of_lucas 31757755568855353 10 256
    [(2, 3), (3, 1), (31, 1), (107, 1), (223, 1), (4153, 1), (430751, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_430751)
    (by decide) (by decide)

/-- `569003` is prime, with witness `2`. -/
private theorem prime_569003 : Nat.Prime 569003 :=
  Pratt.prime_of_lucas 569003 2 256 [(2, 1), (7, 1), (97, 1), (419, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `2773320623` is prime, with witness `5`. -/
private theorem prime_2773320623 : Nat.Prime 2773320623 :=
  Pratt.prime_of_lucas 2773320623 5 256 [(2, 1), (2437, 1), (569003, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_569003)
    (by decide) (by decide)

/-- `72106336199` is prime, with witness `7`. -/
private theorem prime_72106336199 : Nat.Prime 72106336199 :=
  Pratt.prime_of_lucas 72106336199 7 256 [(2, 1), (13, 1), (2773320623, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_2773320623)
    (by decide) (by decide)

/-- `8574133` is prime, with witness `2`. -/
private theorem prime_8574133 : Nat.Prime 8574133 :=
  Pratt.prime_of_lucas 8574133 2 256
    [(2, 2), (3, 1), (7, 1), (103, 1), (991, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `1919519569386763` is prime, with witness `2`. -/
private theorem prime_1919519569386763 : Nat.Prime 1919519569386763 :=
  Pratt.prime_of_lucas 1919519569386763 2 256
    [(2, 1), (3, 1), (7, 1), (19, 1), (47, 2), (127, 1), (8574133, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_8574133)
    (by decide) (by decide)

/-- `75445702479781427272750846543864801` is prime, with witness `7`. -/
private theorem prime_75445702479781427272750846543864801 :
    Nat.Prime 75445702479781427272750846543864801 :=
  Pratt.prime_of_lucas 75445702479781427272750846543864801 7 256
    [(2, 5), (3, 2), (5, 2), (75707, 1), (72106336199, 1), (1919519569386763, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_72106336199
    · exact prime_1919519569386763)
    (by decide) (by decide)

/-- The large factor of `p - 1` is prime, with witness `2`.

It is `74058212732561358302231226437062788676166966415465897661863160754340907`. -/
private theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907 :
    Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 :=
  Pratt.prime_of_lucas 74058212732561358302231226437062788676166966415465897661863160754340907 2 256
    [(2, 1), (3, 1), (353, 1), (57467, 1), (132049, 1), (1923133, 1), (31757755568855353, 1),
     (75445702479781427272750846543864801, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_132049
    · exact prime_1923133
    · exact prime_31757755568855353
    · exact prime_75445702479781427272750846543864801)
    (by decide) (by decide)

/-- `2^255 - 19` is prime, by Lucas' test with witness `2` on a factored `p - 1`. -/
theorem modulus_prime : Nat.Prime modulus :=
  Pratt.prime_of_lucas modulus 2 256
    [(2, 2), (3, 1), (65147, 1),
     (74058212732561358302231226437062788676166966415465897661863160754340907, 1)]
    (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_74058212732561358302231226437062788676166966415465897661863160754340907)
    (by decide) (by decide)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fp` is `ZMod modulus` as a ring.

The map is the identity, so it carries every operation over, and the algebra of `ZMod` applies. -/
def toZMod : Fp ≃+* ZMod modulus := RingEquiv.refl _

end EthLib.Cryptography.X25519
