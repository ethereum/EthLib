module

public import EthLib.Execution.Evm.Precompiles.Bls12381.G1
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Encoding

/-!
# Proofs: `Evm.Precompiles.Bls12381.G1`

- G1ADD rejects any length other than 256 bytes before it charges gas, and then runs out of gas below its price.
- Every encoded G1 point, and so every output of G1ADD, has 128 bytes.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (natToBytes_length)
open EthLib.Cryptography.Bls (G1)

/-- The raw bytes of a G1 point have 96 bytes, and its padded encoding 128. -/
theorem length_padG1_g1ToBytes (point : G1) : (padG1 (g1ToBytes point)).length = 128 := by
  simp [padG1, g1ToBytes, zeroPad, PAD_BYTES, natToBytes_length]

/-- G1ADD rejects any length other than 256 bytes, whatever the gas. -/
theorem bls12G1Add_invalidInputLength {data : ByteArray} (hsize : data.size ≠ 256) (gas : Nat) :
    bls12G1Add data gas = .error (.invalidInputLength data.size) := by
  simp [bls12G1Add, hsize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- G1ADD runs out of gas below its price. -/
theorem bls12G1Add_outOfGas {data : ByteArray} (hsize : data.size = 256) {gas : Nat}
    (hgas : gas < GAS_G1ADD) :
    bls12G1Add data gas = .error (.outOfGas GAS_G1ADD gas) := by
  simp [bls12G1Add, hsize, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Every output of G1ADD has 128 bytes. -/
theorem bls12G1Add_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G1Add data gas = .ok out) :
    out.size = 128 := by
  simp only [bls12G1Add, bind, throw, throwThe, MonadExceptOf.throw] at h
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
  simp [ByteArray.size, length_padG1_g1ToBytes]

end EthLib.Execution.Evm.Precompiles.Bls12381
