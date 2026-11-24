module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Vrf.KeyGen
public import EthLib.Cryptography.Vrf.Serialization

/-!
# Exports: the VRF tree

The C exports of the VRF tree, for the Python bindings.
-/

public section

namespace EthLib.Cryptography.Vrf.Exports

open EthLib.Exports (Result UnreadArgument toResult)

open EthLib.Cryptography.Vrf
open EthLib.Cryptography.Vrf.Constants

/-- The output of an opening at an index under a root, or no bytes when verification rejects.

A root of another length than 32 rejects.

So do an opening of another length than 1056 and an index from `2^32` on. -/
@[export eth_vrf_verify]
def verify (root : ByteArray) (index : UInt64) (opening : ByteArray) : ByteArray :=
  -- Verification never fails: it returns the 32-byte output, or no bytes when it rejects.
  match verifyBytes root index.toNat opening with
  | some output => packBytes output
  | none => ByteArray.empty

/-- A 32-byte seed, or an error for any other length. -/
def readSeed (bytes : ByteArray) : Result Seed :=
  -- The failure has code 0, since no error type of the specification covers it.
  toResult none (Base.exactBytes VRF_SEED_SIZE bytes fun size =>
    UnreadArgument.mk s!"bad seed size: {size}, expected {VRF_SEED_SIZE}")

/-- The secret of an index, from a seed.

The seed is secret: EthLib makes no constant-time claim. -/
@[export eth_vrf_secret]
def secret (seed : ByteArray) (index : UInt32) : Result ByteArray := do
  return packBytes (Vrf.secret (← readSeed seed) index)

/-- The output at an index, from a seed.

The seed is secret: EthLib makes no constant-time claim. -/
@[export eth_vrf_evaluate]
def evaluate (seed : ByteArray) (index : UInt32) : Result ByteArray := do
  return packBytes (Vrf.evaluate (← readSeed seed) index)

/-- 32 bytes, or an error that names the argument for any other length. -/
def readDigest (name : String) (bytes : ByteArray) : Result Digest :=
  -- The failure has code 0, since no error type of the specification covers it.
  toResult none (Base.exactBytes VRF_HASH_SIZE bytes fun size =>
    UnreadArgument.mk s!"bad {name} size: {size}, expected {VRF_HASH_SIZE}")

/-- An output mixed with randomness, or an error if either is not 32 bytes.

The randomness must become known only after the root is registered. -/
@[export eth_vrf_mix]
def mix (output randomness : ByteArray) : Result ByteArray := do
  return packBytes (mixOutput (← readDigest "output" output) (← readDigest "randomness" randomness))

end EthLib.Cryptography.Vrf.Exports
