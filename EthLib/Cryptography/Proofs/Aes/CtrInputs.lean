module

public import EthLib.Cryptography.Proofs.Aes.Ctr

/-!
# Proofs: the inputs of the CTR known answers

The CTR examples of [SP 800-38A](https://doi.org/10.6028/NIST.SP.800-38A) F.5 share these inputs.

The kernel runs the first two blocks of each example, so that each file stays near 3 GB.

The second counter already carries into byte 14, since the counter increments over the whole block.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes

/-- The initial counter of every example of F.5. -/
def f5Counter : Block :=
  #v[0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff]

/-- The first two plaintext blocks of every example of F.5. -/
def f5Plaintext : ByteArray := ⟨#[
  0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
  0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51]⟩

end EthLib.Cryptography.Aes
