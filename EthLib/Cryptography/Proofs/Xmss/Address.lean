module

public import EthLib.Cryptography.Xmss.Address
public import EthLib.Cryptography.Proofs.Xmss.Types
public import EthLib.Cryptography.Proofs.Xmss.Words
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: leanXMSS addresses

Distinct call sites have distinct addresses.

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
theorem CallSite.toNat_encode_lo (site : CallSite) :
    site.encode.lo.toNat =
      site.lo.toNat + 2 ^ 32 * site.hi.val + 2 ^ 56 * (site.tau.val + 32 * site.mu.val) := by
  have hlo : site.lo.toNat < 2 ^ 32 := site.lo.toNat_lt_size
  have hhi := site.hi.isLt
  have ht : site.tau.val + 32 * site.mu.val < 2 ^ 8 := by
    have := site.tau.isLt; have := site.mu.isLt; omega
  simp only [CallSite.encode, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
    UInt32.toNat_toUInt64]
  generalize site.lo.toNat = a at *
  generalize site.hi.val = b at *
  generalize site.tau.val + 32 * site.mu.val = c at *
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
theorem CallSite.bytes_encode (site : CallSite) :
    site.encode.bytes.toList =
      (uintToBytes 4 site.lo.toNat).toList ++ (uintToBytes 3 site.hi.val).toList
        ++ (uintToBytes 1 (site.tau.val + 32 * site.mu.val)).toList
        ++ (uintToBytes 8 0).toList := by
  have hlo : site.lo.toNat < 2 ^ 32 := site.lo.toNat_lt_size
  have hhi := site.hi.isLt
  have ht : site.tau.val + 32 * site.mu.val < 2 ^ 8 := by
    have := site.tau.isLt; have := site.mu.isLt; omega
  -- Both are the bytes of `lo + 2^32 hi + 2^56 (tau + 32 mu)`, the high lane being zero.
  have hn : Hash.Keccak.Lanes2.toNat site.encode =
      site.lo.toNat + 2 ^ 32 * site.hi.val + 2 ^ 56 * (site.tau.val + 32 * site.mu.val) := by
    rw [Hash.Keccak.Lanes2.toNat, CallSite.toNat_encode_lo]
    simp [CallSite.encode]
  rw [Hash.Keccak.Lanes2.bytes_eq_uintToBytes, hn]
  generalize site.lo.toNat = a at *
  generalize site.hi.val = b at *
  generalize site.tau.val + 32 * site.mu.val = c at *
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [Vector.length_toList] at h1
  apply UInt8.toNat_inj.mp
  simp only [Vector.getElem_toList, Base.uintToBytes_eq_div, Vector.getElem_ofFn]
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

/-- A call site whose `hi` carries one layer is not a message call site of the other layer. -/
theorem CallSite.ne_msg_of_hi {layer layer' : Layer} {site : CallSite} {a : Fin (2 ^ 23)}
    (hsite : site.hi = layerHi layer a) (hl : layer ≠ layer') (e' : UInt32) :
    site ≠ .msg layer' e' := fun h =>
  -- The message call site carries `hi_l'(0)`, and `hi` determines its layer.
  hl (layerHi_inj.mp (hsite.symm.trans (congrArg CallSite.hi h))).1

/-! ## Distinct call sites have distinct addresses -/

/-- Two call sites with the same address are the same call site.

- Bytes 0 to 3 hold `lo`, and bytes 4 to 6 hold `hi`.
- Byte 7 holds `tau + 32 mu`, and bytes 8 to 15 are zero.
- The type code `tau` tells the kinds of call apart, and the other fields hold the arguments.
-/
theorem CallSite.encode_injective : Function.Injective CallSite.encode := by
  intro a b h
  -- The first lane is the integer of bytes 0 to 7, and each field is below its range.
  have h := congrArg (fun x => x.lo.toNat) h
  simp only [CallSite.toNat_encode_lo] at h
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
    simp only [CallSite.tau, CallSite.mu, CallSite.hi, CallSite.lo] at htau hmu hhi hlo <;>
    simp_all [Fin.castLE_inj] <;>
    -- Left: the same kind of call on both sides, and `hi` splits into the layer and the rest.
    · obtain ⟨hl, ha⟩ := layerHi_inj.mp hhi
      simp_all [Fin.castLE_inj]

end EthLib.Cryptography.Xmss
