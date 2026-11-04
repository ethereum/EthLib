module

public import EthLib.Cryptography.Bls.Pairing
public import EthLib.Cryptography.Proofs.Bls.Fp12

/-!
# Proofs: the Miller loop of the generators

The kernel runs the Miller loop on the two generators.

Its value is a checkpoint for the pairing of the generators, not a check of its own.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.PairingKnownAnswer

/-- An element of `Fp` from its high 64 and low 32 hexadecimal digits, as the draft prints it. -/
def coeff (hi lo : Nat) : Fp := Fp.ofNat (hi * 2 ^ 128 + lo)

/-- The Miller loop of the generators, as EthLib computes it. -/
def millerGenerators : Fp12 :=
  ⟨⟨⟨coeff 0x144abb1a97a3d65527f2a479175a569855eeda1a0e616cfdc258bdb1c8b9fa09
          0x6ad09965fd55f9801343d28e92e6640b,
        coeff 0x13413bd2925a9e1b08112f7f4e35d5813c459301afd9b9fbc9764fa22aa315cc
          0x2dce1b336faff13a4d7f97b73a87a737⟩,
      ⟨coeff 0x1061bed179b9d8d27ccb35aeb12e95b39e524f50fa674db41c90542ffa28c661
          0xa2f75846365765403354400ca26e00f2,
        coeff 0x1927491641e856fb775de263f806a58db114870fe05a58c85edfce0b8378c53c
          0x486244480d13fee441ebbe35dde4520e⟩,
      ⟨coeff 0x01a542de4684f6373e2a21d822117173950bff0915eb782c284b2afa32c9ffed
          0x3a168c2ac29c427e095a2f06f209db39,
        coeff 0x170e1174852d019b09b0da3c14841d6cdd4b79171b9e3e6a1e7efbd5d2a6de5e
          0x2cd8853e4f98d0e32156c3319c9f3191⟩⟩,
    ⟨⟨coeff 0x111758fd4779b9d7eda010f36caabfea0c08b6703f38849acf110661c09aa1d8
          0x70d747518e310505f3342294588fb886,
        coeff 0x13dd0d23fe6b205afc16bd7f54193917adb5a1faff0b2f7ed7f786357f5ae1ea
          0xce5bd97858230cc0352b88c97bbef640⟩,
      ⟨coeff 0x0315d01b5d309e53bc4b7533c57146890a33c101cca9d8675fc099f9b80a6f8e
          0x25c61610c25299ea9ab42c9ea16eabb0,
        coeff 0x0cbccf94f2a6bcc12d54395ad34d72e308d2b753adce82cd21e864d7bdbc5dfd
          0xd093caa671baba5189ceb2764a4664ff⟩,
      ⟨coeff 0x0ced20608aa7112c205ee7a703c2e77f96d1aef6fd865caafcb4a363d2f9de8e
          0xcc3acf61f888c8eedb1483397ba6438b,
        coeff 0x10c839fd7d6519131e14836b595789b7121ba39388491a972b713f92f9c75d36
          0x12a4758fe5614d7877cdaf2292b7dcf2⟩⟩⟩

/-- The Miller loop of the generators. -/
theorem millerLoop_generators :
    millerLoop blsX (Embedded.ofG2 G2.generator) (Embedded.ofG1 G1.generator) =
      millerGenerators := by
  decide +kernel

end EthLib.Cryptography.Bls.PairingKnownAnswer
