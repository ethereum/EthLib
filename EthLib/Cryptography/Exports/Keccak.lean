module

public import EthLib.Cryptography.Hash.Keccak

/-!
# Exports: Keccak

The C exports of Keccak-256 and of the Keccak-f[1600] permutation, for the Python bindings.

Keccak-256 is total, so its export has no `IO` error path.

The permutation takes a state of exactly 200 bytes, and its export rejects any other length.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

open EthLib.Cryptography.Hash.Keccak

/-- The 32-byte Keccak-256 digest of a message of any length, FIPS 202 with Keccak's padding. -/
@[export eth_keccak256]
def keccak256 (data : ByteArray) : ByteArray :=
  ⟨(EthLib.Cryptography.Hash.Keccak.keccak256 data).toArray⟩

/-- Keccak-f[1600] of a 200-byte state string, as a 200-byte state string.

Lane `i` is bytes `8i` to `8i + 7` of the string, the first least significant (FIPS 202 §3.1.3).

Any other length is an error. -/
@[export eth_keccak_f1600]
def keccakF1600 (state : ByteArray) : IO ByteArray := do
  if state.size ≠ 8 * LANES then
    throw (IO.userError s!"Keccak-f[1600]: the state must be 200 bytes, got {state.size}")
  let bytes := state.data.toList
  -- Each lane reads its own 8 bytes.
  let lanes : State := Vector.ofFn fun i => Internal.laneOfBytes ((bytes.drop (8 * i.val)).take 8)
  -- Each output lane writes 8 bytes, the least significant first.
  let out := (keccakF lanes).toList.flatMap fun lane =>
    (List.range 8).map fun j => (lane >>> UInt64.ofNat (8 * j)).toUInt8
  return ⟨out.toArray⟩

end EthLib.Cryptography.Hash.Exports
