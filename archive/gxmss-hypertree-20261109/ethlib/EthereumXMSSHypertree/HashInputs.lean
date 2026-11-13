/-
Copyright (c) 2026 Trail of Bits.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Trail of Bits
-/

module
public import EthLib.Cryptography.Proofs.Xmss.Address
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import EthLib.Cryptography.Xmss.Tree

/-!
# EthLib full hash inputs

Every tweakable input has the fixed public-parameter and address prefixes. A chain index is
encoded in the payload, while the physical chain address carries the step position.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- The complete input of one source chain step, including its payload chain index. -/
@[expose] def chainInput (pp : PublicParam) (layer : Layer) (e : UInt32)
    (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) : ByteArray :=
  thInput pp (addrChain layer e mu)
    (packBytes value ++ packBytes (EthLib.Base.uintToBytes 16 i.val))

/-- The source chain call hashes the complete chain input. -/
theorem chainStep_input {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) :
    chainStep H pp layer e i mu value =
      (do return halfOf 0 (← H (chainInput pp layer e i mu value))) := rfl

/-- The source message call hashes message bytes followed by the randomizer. -/
theorem messageDigest_input {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) :
    messageDigest H pp layer e msg rho =
      (do return halfOf 0 (← H (packBytes pp ++ packBytes (addrMsg layer e) ++
        (msg ++ packBytes rho)))) := rfl

/-- The source leaf call hashes its 58 ordered chain ends. -/
theorem otsLeafHash_input {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (ends : Vector Digest V) :
    otsLeafHash H pp layer e ends =
      (do return halfOf 0 (← H (packBytes pp ++ packBytes (addrLeaf layer e) ++
        packDigests ends))) := rfl

/-- The source node call hashes left then right, using the source's bounded conversions. -/
theorem nodeHash_input {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (layer : Layer)
    (level j : Nat) (left right : Digest) :
    nodeHash H pp layer level j left right =
      (do return halfOf 0 (← H (packBytes pp ++
        packBytes (addrNode layer (Fin.ofNat _ level) (UInt32.ofNat j)) ++
        (packBytes left ++ packBytes right)))) := rfl

/-- A seed derivation hashes the seed before the requested suffix. -/
theorem seedPrf_input {m : Type → Type} (H : ByteArray → m (Vector UInt8 32))
    (seed : Seed) (pp : PublicParam) (address : Address) (suffix : ByteArray) :
    seedPrf H seed pp address suffix =
      H (packBytes pp ++ packBytes address ++ (packBytes seed ++ suffix)) := rfl

/-- Equal complete chain inputs determine every legal source coordinate and the chain value. -/
theorem chainInput_inj {pp pp' : PublicParam} {layer layer' : Layer} {e e' : UInt32}
    {i i' : Fin V} {mu mu' : Fin (CHAIN_LENGTH - 1)} {value value' : Digest}
    (h : chainInput pp layer e i mu value = chainInput pp' layer' e' i' mu' value') :
    pp = pp' ∧ layer = layer' ∧ e = e' ∧ i = i' ∧ mu = mu' ∧ value = value' := by
  obtain ⟨hpp, ha, hpayload⟩ := thInput_inj h
  obtain ⟨hl, he, hmu⟩ := addrChain_inj.mp ha
  obtain ⟨hv, hi⟩ := EthLib.Cryptography.HashSig.byteArray_append_inj hpayload (by simp)
  have hi := packBytes_injective hi
  have hi := EthLib.Base.uintToBytes_inj (k := 16)
    (by have := i.isLt; simp only [V] at this; omega)
    (by have := i'.isLt; simp only [V] at this; omega) hi
  exact ⟨hpp, hl, he, Fin.ext hi, hmu, packBytes_injective hv⟩

/-- Different legal type codes separate full inputs, regardless of payload or parameter. -/
theorem fullInput_ne_of_type_ne {pp pp' : PublicParam} {kind kind' : AddressType}
    (mu mu' : Fin 8) (hi hi' : Fin (2 ^ 24)) (lo lo' : UInt32)
    (payload payload' : ByteArray) (hne : kind ≠ kind') :
    thInput pp (encodeAddress kind.code mu hi lo) payload ≠
      thInput pp' (encodeAddress kind'.code mu' hi' lo') payload' := by
  intro h
  have hcode := (encodeAddress_inj.mp (thInput_inj h).2.1).1
  exact hne (AddressType.code_injective hcode)

end EthereumXMSSHypertree
