module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Bytes
public import EthLib.Cryptography.Proofs.Xmss.Address

/-!
# Proofs: EthLib's addresses are the model's

The model writes an address as the bytes of four fields, `tau`, `mu`, `hi` and `lo`.

EthLib's address of the same call has the same 16 bytes.

```text
    [ lo: 4 | hi: 3 | tau + 32 mu: 1 | zero: 8 ]     both
```

The top layer sets bit 23 of `hi`, the model's top flag.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.HashSig (toList_uintToBytes append_ofNat)

/-! ## The encoding -/

/-- EthLib's address encoding lists the bytes of the model's, for the same four fields. -/
theorem toList_encodeAddress (tau : Fin 32) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    Hash.Keccak.lanesBytes (encodeAddress tau mu hi lo).toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields tau.val mu.val hi.val lo.toNat) := by
  -- The address is a concatenation of 4 + 3 + 1 + 8 bytes, which is its length constant.
  rw [Hash.Keccak.lanesBytes_lanes2, bytes_encodeAddress]
  simp only [toList_uintToBytes, XmssSecurity.fieldBytes,
    XmssSecurity.tweakFields, append_ofNat tau.val mu.val tau.isLt mu.isLt]
  rfl

/-- The address of a call site has the model's bytes for its four fields. -/
theorem toList_encode (site : CallSite) :
    Hash.Keccak.lanesBytes site.encode.toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields site.tau.val site.mu.val site.hi.val site.lo.toNat) :=
  toList_encodeAddress _ _ _ _

/-! ## The addresses of a key

`2^23 l` is the flag of layer `l` in `hi`.

It is zero at the bottom, and the model's top flag at the top. -/

theorem toList_addrChain (layer : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1)) :
    Hash.Keccak.lanesBytes (addrChain layer e mu).toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 1 mu.val (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrChain, toList_encode]
  simp [CallSite.tau, CallSite.mu, CallSite.hi, CallSite.lo, layerHi,
    AddressType.code]

theorem toList_addrLeaf (layer : Layer) (e : UInt32) :
    Hash.Keccak.lanesBytes (addrLeaf layer e).toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 2 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrLeaf, toList_encode]
  simp [CallSite.tau, CallSite.mu, CallSite.hi, CallSite.lo, layerHi,
    AddressType.code]

theorem toList_addrMsg (layer : Layer) (e : UInt32) :
    Hash.Keccak.lanesBytes (addrMsg layer e).toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 12 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrMsg, toList_encode]
  simp [CallSite.tau, CallSite.mu, CallSite.hi, CallSite.lo, layerHi,
    AddressType.code]

theorem toList_addrRnd (layer : Layer) (e : UInt32) :
    Hash.Keccak.lanesBytes (addrRnd layer e).toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 7 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrRnd, toList_encode]
  simp [CallSite.tau, CallSite.mu, CallSite.hi, CallSite.lo, layerHi,
    AddressType.code]

/-- The parent at level `level`, `level >= 1`, carries the level in `hi`. -/
theorem toList_addrNode (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : UInt32) :
    Hash.Keccak.lanesBytes (addrNode layer level j).toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 3 0 (2 ^ 23 * layer.toNat + level.val) j.toNat) := by
  rw [addrNode, toList_encode]
  simp [CallSite.tau, CallSite.mu, CallSite.hi, CallSite.lo, layerHi,
    AddressType.code, Nat.add_comm]

theorem toList_addrPrf (layer : Layer) (e : UInt32) (j : Fin (V / 2)) :
    Hash.Keccak.lanesBytes (addrPrf layer e j).toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 0 0 (2 ^ 23 * layer.toNat + j.val) e.toNat) := by
  rw [addrPrf, toList_encode]
  simp [CallSite.tau, CallSite.mu, CallSite.hi, CallSite.lo, layerHi,
    AddressType.code, Nat.add_comm]

theorem toList_addrParam :
    Hash.Keccak.lanesBytes addrParam.toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 5 0 0 0) := by
  rw [addrParam, toList_encode]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability
