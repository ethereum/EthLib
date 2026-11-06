module

public import EthLib.Engine.Json
public import EthLib.Base.Hex
public import EthLib.Base.Except

/-!
# Proofs: the JSON decoders

The decoders read the value of a hex digit from its ASCII byte.

They read back each digit that the hex encoder writes.

Those digits are lowercase, so this holds whether or not the decoders accept uppercase.

A decoder that checks a bound returns only values within it.

A number that the decoder checks against `2^bits` is below `2^bits`.

So a 64-bit number holds the decoded value, without wrapping.

A byte string decoded with a limit on its size has at most that many bytes.
-/

public section

namespace EthLib.Engine.Json

open EthLib.Base

/-- The decoders read the value of each digit that the hex encoder writes. -/
theorem hexValue_hexDigitChar (upper : Bool) (n : Fin 16) :
    hexValue upper (hexDigitChar n).toUInt8 = some n.val.toUInt8 := by
  decide +revert

/-- A decoded number is below the bound that the decoder checks. -/
theorem lt_of_quantity {what : String} {bits : Nat} {j : Lean.Json} {value : Nat}
    (h : quantity what bits j = .ok value) : value < 2 ^ bits := by
  unfold quantity at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  -- The checks for no digits and for a leading zero reject, so neither is the success.
  split at h
  · cases h
  split at h
  · cases h
  -- Whatever the digit loop returns, the last step compares it with the bound.
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h
    assumption
  · cases h

/-- A decoded 64-bit number is the decoded value, which is below `2^64` and so does not wrap. -/
theorem quantity_of_uint64 {what : String} {j : Lean.Json} {x : UInt64}
    (h : uint64 what j = .ok x) : quantity what 64 j = .ok x.toNat := by
  unfold uint64 at h
  obtain ⟨value, hq, hx⟩ := bind_ok_iff.mp h
  cases hx
  -- The value is below `2^64`, so its conversion keeps it.
  rw [hq, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (lt_of_quantity hq)]

/-- A byte string decoded with a limit has at most that many bytes. -/
theorem size_le_of_bytesMax {what : String} {n : Nat} {j : Lean.Json} {b : ByteArray}
    (h : bytesMax what n j = .ok b) : b.size ≤ n := by
  unfold bytesMax at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  split at h
  · cases h
    assumption
  · cases h

end EthLib.Engine.Json
