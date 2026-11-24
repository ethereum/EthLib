module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Bytes
public import EthLib.Cryptography.Proofs.Xmss.Address

/-!
# Proofs: EthLib's addresses are the model's

The model writes an address as the bytes of four fields, `tau`, `mu`, `hi` and `lo`.

EthLib's address of the same call has the same 16 bytes.

In both, the bytes are `lo` (4), `hi` (3), `tau + 32 mu` (1), then 8 zero bytes.

The top layer sets bit 23 of `hi`, the model's top flag.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.HashSig (toList_toLE append_ofNat)

/-! ## The encoding -/

/-- The encoding of an address has the model's bytes for its four fields. -/
theorem toList_encode (address : Address) :
    Hash.Keccak.lanesBytes address.encode.toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields address.tau.val address.mu.val address.hi.val
            address.lo.toNat) := by
  -- The address is a concatenation of 4 + 3 + 1 + 8 bytes, which is its length constant.
  rw [Hash.Keccak.lanesBytes_lanes2, Address.bytes_encode]
  simp only [toList_toLE, XmssSecurity.fieldBytes,
    XmssSecurity.tweakFields,
    append_ofNat address.tau.val address.mu.val address.tau.isLt address.mu.isLt]
  rfl

/-! ## The addresses of a key

`2^23 l` is the flag of layer `l` in `hi`.

It is zero at the bottom, and the model's top flag at the top. -/

theorem toList_encode_chain (layer : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1)) :
    Hash.Keccak.lanesBytes (Address.chain layer e mu).encode.toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 1 mu.val (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [toList_encode]
  simp [Address.tau, Address.mu, Address.hi, Address.lo, layerHi]

theorem toList_encode_leaf (layer : Layer) (e : UInt32) :
    Hash.Keccak.lanesBytes (Address.leaf layer e).encode.toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 2 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [toList_encode]
  simp [Address.tau, Address.mu, Address.hi, Address.lo, layerHi]

theorem toList_encode_msg (layer : Layer) (e : UInt32) :
    Hash.Keccak.lanesBytes (Address.msg layer e).encode.toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 12 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [toList_encode]
  simp [Address.tau, Address.mu, Address.hi, Address.lo, layerHi]

theorem toList_encode_rnd (layer : Layer) (e : UInt32) :
    Hash.Keccak.lanesBytes (Address.rnd layer e).encode.toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 7 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [toList_encode]
  simp [Address.tau, Address.mu, Address.hi, Address.lo, layerHi]

/-- The parent at level `level`, `level >= 1`, carries the level in `hi`. -/
theorem toList_encode_node (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : UInt32) :
    Hash.Keccak.lanesBytes (Address.node layer level j).encode.toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 3 0 (2 ^ 23 * layer.toNat + level.val) j.toNat) := by
  rw [toList_encode]
  simp [Address.tau, Address.mu, Address.hi, Address.lo, layerHi, Nat.add_comm]

theorem toList_encode_prf (layer : Layer) (e : UInt32) (j : Fin (V / 2)) :
    Hash.Keccak.lanesBytes (Address.prf layer e j).encode.toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 0 0 (2 ^ 23 * layer.toNat + j.val) e.toNat) := by
  rw [toList_encode]
  simp [Address.tau, Address.mu, Address.hi, Address.lo, layerHi, Nat.add_comm]

theorem toList_encode_param :
    Hash.Keccak.lanesBytes Address.param.encode.toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 5 0 0 0) := by
  rw [toList_encode]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability
