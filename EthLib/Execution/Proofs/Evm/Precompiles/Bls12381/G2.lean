module

public import EthLib.Execution.Evm.Precompiles.Bls12381.G2
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Encoding

/-!
# Proofs: `Evm.Precompiles.Bls12381.G2`

- G2ADD rejects any length other than 512 bytes before it charges gas, and then runs out of gas below its price.
- Every encoded G2 point, and so every output of G2ADD, has 256 bytes.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (natToBytes_length)
open EthLib.Cryptography.Bls (G2)

/-- The raw bytes of a G2 point have 192 bytes, and its padded encoding 256. -/
theorem length_padG2_g2ToBytes (point : G2) : (padG2 (g2ToBytes point)).length = 256 := by
  simp [padG2, g2ToBytes, zeroPad, PAD_BYTES, natToBytes_length]

/-- G2ADD rejects any length other than 512 bytes, whatever the gas. -/
theorem bls12G2Add_invalidInputLength {data : ByteArray} (hsize : data.size ≠ 512) (gas : Nat) :
    bls12G2Add data gas = .error (.invalidInputLength data.size) := by
  simp [bls12G2Add, hsize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- G2ADD runs out of gas below its price. -/
theorem bls12G2Add_outOfGas {data : ByteArray} (hsize : data.size = 512) {gas : Nat}
    (hgas : gas < GAS_G2ADD) :
    bls12G2Add data gas = .error (.outOfGas GAS_G2ADD gas) := by
  simp [bls12G2Add, hsize, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Every output of G2ADD has 256 bytes. -/
theorem bls12G2Add_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G2Add data gas = .ok out) :
    out.size = 256 := by
  simp only [bls12G2Add, bind, throw, throwThe, MonadExceptOf.throw] at h
  -- Past the two checks, the output is the padded encoding of a sum.
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_padG2_g2ToBytes]

end EthLib.Execution.Evm.Precompiles.Bls12381
