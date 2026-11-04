module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Hash.Keccak

/-!
# Exports: Keccak

The C exports of Keccak-256 and of the Keccak-f[1600] permutation, for the Python bindings.

Keccak-256 is total, so its export has no error path.

The permutation takes a state of exactly 200 bytes, and its export rejects any other length.

Keccak has no error type, so that rejection has code 0.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

open EthLib.Exports (Result)

open EthLib.Cryptography.Hash.Keccak

/-- The 32-byte Keccak-256 digest of a message of any length, FIPS 202 with Keccak's padding. -/
@[export eth_keccak256]
def keccak256 (data : ByteArray) : ByteArray :=
  ⟨(EthLib.Cryptography.Hash.Keccak.keccak256 data).toArray⟩

/-- Keccak-f[1600] of a 200-byte state string, as a 200-byte state string.

Lane `i` is bytes `8i` to `8i + 7` of the string, the first least significant (FIPS 202 §3.1.3).

Any other length is an error. -/
@[export eth_keccak_f1600]
def keccakF1600 (state : ByteArray) : Result ByteArray := do
  if state.size ≠ 8 * LANES then
    throw (0, s!"Keccak-f[1600]: the state must be 200 bytes, got {state.size}")
  let bytes := state.data.toList
  -- Lane `i` reads its own 8 bytes.
  let lane (i : Nat) : UInt64 := Internal.laneAt (bytes.drop (8 * i))
  let A : State := ⟨lane 0, lane 1, lane 2, lane 3, lane 4, lane 5, lane 6, lane 7, lane 8,
    lane 9, lane 10, lane 11, lane 12, lane 13, lane 14, lane 15, lane 16, lane 17, lane 18,
    lane 19, lane 20, lane 21, lane 22, lane 23, lane 24⟩
  let B := keccakF A
  -- Each output lane writes 8 bytes, the least significant first.
  let out := [B.a0, B.a1, B.a2, B.a3, B.a4, B.a5, B.a6, B.a7, B.a8, B.a9, B.a10, B.a11, B.a12,
    B.a13, B.a14, B.a15, B.a16, B.a17, B.a18, B.a19, B.a20, B.a21, B.a22, B.a23,
    B.a24].flatMap Internal.bytesOfLane
  return ⟨out.toArray⟩

end EthLib.Cryptography.Hash.Exports
