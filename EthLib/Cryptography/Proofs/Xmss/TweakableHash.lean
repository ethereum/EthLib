module

public import EthLib.Cryptography.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.Xmss.Types
public import EthLib.Cryptography.Proofs.Hash.Keccak.Lanes
import EthLib.Cryptography.Proofs.Xmss.Address

/-!
# Proofs: the leanXMSS tweakable hash

A hash input determines its public parameter, its address and its payload.

So two calls hash the same lanes only when they are the same call.

A derivation from the seed with an empty suffix hashes `P | A | S`.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- The first half of a hash value is its first two lanes. -/
@[simp] theorem halfOf_zero (full : Lanes4) : halfOf 0 full = ⟨full.w0, full.w1⟩ :=
  rfl

/-- The last half of a hash value is its last two lanes. -/
@[simp] theorem halfOf_one (full : Lanes4) : halfOf 1 full = ⟨full.w2, full.w3⟩ :=
  rfl

/-- The scheme's hash of a string of lanes is Keccak-256 of the bytes of the lanes. -/
theorem hash_bytes (input : Array UInt64) :
    (hash input).bytes = Hash.Keccak.keccak256 ⟨(Hash.Keccak.lanesBytes input).toArray⟩ :=
  Hash.Keccak.keccak256Lanes_lanesBytes input

/-- A hash input is the lanes of the parameter, then of the address, then the payload. -/
theorem thInput_eq_append (publicParam : PublicParam) (address : Address)
    (payload : Array UInt64) :
    thInput publicParam address payload
      = publicParam.toArray ++ address.encode.toArray ++ payload :=
  rfl

/-- `P | A | M` determines `P`, the address whose encoding is `A`, and `M`. -/
theorem thInput_inj {publicParam publicParam' : PublicParam} {a a' : Address} {m m' : Array UInt64}
    (h : thInput publicParam a m = thInput publicParam' a' m') : publicParam = publicParam'
      ∧ a = a' ∧ m = m' := by
  -- The first four lanes are the two fixed-size prefixes, the rest is the payload.
  obtain ⟨hpre, hm⟩ := Array.append_inj h rfl
  simp only [List.toArray, Array.mk.injEq, List.cons.injEq, and_true] at hpre
  obtain ⟨h1, h2, h3, h4⟩ := hpre
  -- Distinct addresses have distinct encodings.
  refine ⟨by cases publicParam; cases publicParam'; simp_all, Address.encode_injective ?_, hm⟩
  generalize a.encode = x at *
  generalize a'.encode = y at *
  cases x; cases y; simp_all

/-- A derivation with an empty suffix hashes `P | A | S`.

The public parameter and the chain starts are halves of such derivations. -/
theorem seedPrf_empty {m : Type → Type} (H : Array UInt64 → m Lanes4) (s : Seed)
    (publicParam : PublicParam) (address : Address) :
    seedPrf H s publicParam address #[] = H (thInput publicParam address s.toArray) := by
  simp only [seedPrf, Array.append_empty]

end EthLib.Cryptography.Xmss
