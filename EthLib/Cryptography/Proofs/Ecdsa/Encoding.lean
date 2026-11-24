module

public import EthLib.Cryptography.Ecdsa.Encoding
import EthLib.Base.Proofs.ByteOrder
import EthLib.Base.Proofs.Bytes

/-!
# Proofs: reading and writing an ECDSA signature

A buffer reads as a signature exactly when it has 64 bytes.

Its first 32 bytes then give `r`, and the rest give `s`.

Writing two integers and reading them back gives each one modulo `2^256`.

Every signature is the bytes of its own two integers.

Below `2^256`, the bytes determine the two integers, and the buffer reads back as them.
-/

@[expose] public section

namespace EthLib.Cryptography.Ecdsa

/-- A buffer reads as a signature exactly when it has the length of one.

Its first 32 bytes then give `r`, and the rest give `s`. -/
theorem read?_eq (b : ByteArray) :
    read? b = if b.size = SIGNATURE_LEN then
      some (Base.ByteOrder.ofBE (b.data.toList.take 32),
        Base.ByteOrder.ofBE (b.data.toList.drop 32))
    else none := by
  by_cases h : b.size = SIGNATURE_LEN
  · simp [read?, Base.exactBytes?_of_size_eq h, toNats, h]
  · simp [read?, Base.exactBytes?_of_size_ne h, h]

/-- The bytes of `r` and `s` read back as `r` and `s`, each modulo `2^256`. -/
@[simp] theorem toNats_toBytes (r s : Nat) :
    toNats (toBytes r s) = (r % 256 ^ 32, s % 256 ^ 32) := by
  have hr := Base.ByteOrder.length_toList_toBE 32 r
  simp [toNats, toBytes, List.take_left' hr, List.drop_left' hr]

/-- A list of `n` bytes is the `n` big-endian bytes of the integer that it reads as. -/
private theorem toList_toBE_ofBE {n : Nat} {l : List UInt8} (h : l.length = n) :
    (Base.ByteOrder.toBE n (Base.ByteOrder.ofBE l)).toList = l := by
  have := congrArg Vector.toList
    (Base.ByteOrder.toBE_ofBE (⟨l.toArray, by simp [h]⟩ : Vector UInt8 n))
  simpa using this

/-- Each integer is written modulo `2^256`, so reducing it first changes no byte. -/
@[simp] theorem toBytes_mod (r s : Nat) :
    toBytes (r % 256 ^ 32) (s % 256 ^ 32) = toBytes r s := by
  simp only [toBytes, Base.ByteOrder.toBE_mod]

/-- Every signature is the bytes of its own two integers. -/
@[simp] theorem toBytes_toNats (sig : Vector UInt8 SIGNATURE_LEN) :
    toBytes (toNats sig).1 (toNats sig).2 = sig := by
  apply Vector.toList_inj.mp
  have hl : sig.toList.length = 64 := by rw [Vector.length_toList]; rfl
  -- The first 32 bytes give `r` and the last 32 give `s`, and each is written back as it was.
  simp only [toBytes, toNats, Vector.toList_mk]
  rw [toList_toBE_ofBE (by simp [hl]), toList_toBE_ofBE (by simp [hl]), List.take_append_drop]

/-- Two pairs of integers below `2^256` with the same bytes are the same pair. -/
theorem toBytes_inj {r s r' s' : Nat} (hr : r < 2 ^ 256) (hs : s < 2 ^ 256)
    (hr' : r' < 2 ^ 256) (hs' : s' < 2 ^ 256) (h : toBytes r s = toBytes r' s') :
    r = r' ∧ s = s' := by
  have hn := congrArg toNats h
  simp only [toNats_toBytes, Prod.mk.injEq] at hn
  have e : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  rw [e, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hr',
    Nat.mod_eq_of_lt hs'] at hn
  exact hn

/-- The bytes of a signature, as a buffer, read as its two integers. -/
@[simp] theorem read?_packBytes (sig : Vector UInt8 SIGNATURE_LEN) :
    read? (Base.packBytes sig) = some (toNats sig) := by
  simp [read?]

/-- The bytes of two integers below `2^256`, as a buffer, read as those integers. -/
theorem read?_packBytes_toBytes {r s : Nat} (hr : r < 2 ^ 256) (hs : s < 2 ^ 256) :
    read? (Base.packBytes (toBytes r s)) = some (r, s) := by
  have e : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  rw [read?_packBytes, toNats_toBytes, e, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs]

/-- The bytes before the recovery id are the bytes of the signature. -/
@[simp] theorem take_toRecoverableBytes (r s : Nat) (odd : Bool) :
    ((toRecoverableBytes r s odd).take SIGNATURE_LEN : Vector UInt8 SIGNATURE_LEN) =
      toBytes r s := by
  -- The cast that remains is between two forms of the same length.
  simp [toRecoverableBytes, Vector.take_eq_extract]
  rfl

/-- The last byte is the recovery id. -/
@[simp] theorem getElem_toRecoverableBytes (r s : Nat) (odd : Bool) :
    (toRecoverableBytes r s odd)[SIGNATURE_LEN] = if odd then 1 else 0 :=
  Vector.getElem_push_eq

end EthLib.Cryptography.Ecdsa
