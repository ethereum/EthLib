module

public import EthLib.Cryptography.Xmss.Address
public import EthLib.Cryptography.Proofs.Xmss.Types
public import EthLib.Cryptography.Proofs.Xmss.Words
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: leanXMSS addresses

Distinct addresses have distinct encodings.

- The first lane of an address determines its four fields.
- The type codes are distinct, so two kinds of call never share an address.
- The top layer's flag is a separate bit, so the two layers never share an address.
- The other fields hold the arguments of the call.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## The encoding -/

/-- The first lane of an address is the integer `lo + 2^32 hi + 2^56 (tau + 32 mu)`.

The three fields fill disjoint bits, so the OR of the lane is their sum. -/
theorem Address.toNat_encode_lo (address : Address) :
    address.encode.lo.toNat =
      address.lo.toNat + 2 ^ 32 * address.hi.val
        + 2 ^ 56 * (address.tau.val + 32 * address.mu.val) := by
  have hlo : address.lo.toNat < 2 ^ 32 := address.lo.toNat_lt_size
  have hhi := address.hi.isLt
  have ht : address.tau.val + 32 * address.mu.val < 2 ^ 8 := by
    have := address.tau.isLt; have := address.mu.isLt; omega
  simp only [Address.encode, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
    UInt32.toNat_toUInt64]
  generalize address.lo.toNat = a at *
  generalize address.hi.val = b at *
  generalize address.tau.val + 32 * address.mu.val = c at *
  -- Each field is below `2^64`, and so is each shifted field.
  rw [Nat.mod_eq_of_lt (by omega : b < 2 ^ 64), Nat.mod_eq_of_lt (by omega : c < 2 ^ 64)]
  simp only [show UInt64.toNat 32 = 32 from rfl, show UInt64.toNat 56 = 56 from rfl,
    Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
  -- Each OR adds a field above the bits filled so far.
  rw [Nat.or_comm a, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
  simp only [Nat.shiftLeft_eq]
  omega

/-- The bytes of an address's lanes are its four fields, each in its own little-endian bytes. -/
theorem Address.bytes_encode (address : Address) :
    address.encode.bytes.toList =
      (Base.ByteOrder.toLE 4 address.lo.toNat).toList
        ++ (Base.ByteOrder.toLE 3 address.hi.val).toList
        ++ (Base.ByteOrder.toLE 1 (address.tau.val + 32 * address.mu.val)).toList
        ++ (Base.ByteOrder.toLE 8 0).toList := by
  have hlo : address.lo.toNat < 2 ^ 32 := address.lo.toNat_lt_size
  have hhi := address.hi.isLt
  have ht : address.tau.val + 32 * address.mu.val < 2 ^ 8 := by
    have := address.tau.isLt; have := address.mu.isLt; omega
  -- Both are the bytes of `lo + 2^32 hi + 2^56 (tau + 32 mu)`, the high lane being zero.
  have hn : Hash.Keccak.Lanes2.toNat address.encode =
      address.lo.toNat + 2 ^ 32 * address.hi.val
        + 2 ^ 56 * (address.tau.val + 32 * address.mu.val) := by
    rw [Hash.Keccak.Lanes2.toNat, Address.toNat_encode_lo]
    simp [Address.encode]
  rw [Hash.Keccak.Lanes2.bytes_eq_toLE, hn]
  generalize address.lo.toNat = a at *
  generalize address.hi.val = b at *
  generalize address.tau.val + 32 * address.mu.val = c at *
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [Vector.length_toList] at h1
  apply UInt8.toNat_inj.mp
  simp only [Vector.getElem_toList, Base.ByteOrder.toLE_eq_div, Vector.getElem_ofFn]
  interval_cases j <;> simp [UInt8.toNat_ofNat'] <;> omega

/-! ## The two layers -/

/-- `hi_l(a)` determines both the layer and `a`. -/
theorem layerHi_inj {layer layer' : Layer} {a a' : Fin (2 ^ 23)} :
    layerHi layer a = layerHi layer' a' ↔ layer = layer' ∧ a = a' := by
  constructor
  · intro h
    have h := congrArg Fin.val h
    simp only [layerHi] at h
    -- Bit 23 is the layer, the 23 bits below it are `a`.
    have ha := a.isLt
    have ha' := a'.isLt
    cases layer <;> cases layer' <;> simp only [Layer.toNat] at h <;>
      first
      | exact ⟨rfl, Fin.ext (by omega)⟩
      | omega
  · rintro ⟨rfl, rfl⟩
    rfl

/-- An address whose `hi` carries one layer is not a message address of the other layer. -/
theorem Address.ne_msg_of_hi {layer layer' : Layer} {address : Address} {a : Fin (2 ^ 23)}
    (haddress : address.hi = layerHi layer a) (hl : layer ≠ layer') (e' : UInt32) :
    address ≠ .msg layer' e' := fun h =>
  -- The message address carries `hi_l'(0)`, and `hi` determines its layer.
  hl (layerHi_inj.mp (haddress.symm.trans (congrArg Address.hi h))).1

/-! ## Distinct addresses have distinct encodings -/

/-- Two addresses with the same encoding are the same address.

- Bytes 0 to 3 hold `lo`, and bytes 4 to 6 hold `hi`.
- Byte 7 holds `tau + 32 mu`, and bytes 8 to 15 are zero.
- The type code `tau` tells the kinds of call apart, and the other fields hold the arguments.
-/
theorem Address.encode_injective : Function.Injective Address.encode := by
  intro a b h
  -- The first lane is the integer of bytes 0 to 7, and each field is below its range.
  have h := congrArg (fun x => x.lo.toNat) h
  simp only [Address.toNat_encode_lo] at h
  have := a.lo.toNat_lt_size
  have := b.lo.toNat_lt_size
  have := a.hi.isLt
  have := b.hi.isLt
  have := a.tau.isLt
  have := b.tau.isLt
  have := a.mu.isLt
  have := b.mu.isLt
  simp only [UInt32.size] at *
  -- `tau < 32` is the remainder by 32 and `mu` the quotient.
  have htau : a.tau = b.tau := Fin.ext (by omega)
  have hmu : a.mu = b.mu := Fin.ext (by omega)
  have hhi : a.hi = b.hi := Fin.ext (by omega)
  have hlo : a.lo = b.lo := UInt32.toNat_inj.mp (by omega)
  clear h
  -- Each field reads one argument of the call, or a constant.
  cases a <;> cases b <;>
    simp only [Address.tau, Address.mu, Address.hi, Address.lo] at htau hmu hhi hlo <;>
    simp_all [Fin.castLE_inj] <;>
    -- Left: the same kind of call on both sides, and `hi` splits into the layer and the rest.
    · obtain ⟨hl, ha⟩ := layerHi_inj.mp hhi
      simp_all [Fin.castLE_inj]

end EthLib.Cryptography.Xmss
