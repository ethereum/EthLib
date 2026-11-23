module

public import EthLib.Cryptography.Xmss.Address
public import EthLib.Cryptography.Proofs.Xmss.Types
public import EthLib.Cryptography.Proofs.Xmss.Words
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: leanXMSS addresses

Distinct call sites have distinct addresses.

- The encoding is injective on its four fields.
- The type codes are distinct, so two address types never share an address.
- The top layer's flag is a separate bit, so the two layers never share an address.
- Each address of a key determines its own arguments.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## The encoding is injective -/

/-- The first lane of an address is the integer `lo + 2^32 hi + 2^56 (tau + 32 mu)`.

The three fields fill disjoint bits, so the OR of the lane is their sum. -/
theorem toNat_encodeAddress_lo (tau : Fin 32) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    (encodeAddress tau mu hi lo).lo.toNat =
      lo.toNat + 2 ^ 32 * hi.val + 2 ^ 56 * (tau.val + 32 * mu.val) := by
  have hlo : lo.toNat < 2 ^ 32 := lo.toNat_lt_size
  have hhi := hi.isLt
  have ht : tau.val + 32 * mu.val < 2 ^ 8 := by have := tau.isLt; have := mu.isLt; omega
  simp only [encodeAddress, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
    UInt32.toNat_toUInt64]
  generalize lo.toNat = a at *
  generalize hi.val = b at *
  generalize tau.val + 32 * mu.val = c at *
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
theorem bytes_encodeAddress (tau : Fin 32) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    (encodeAddress tau mu hi lo).bytes.toList =
      (uintToBytes 4 lo.toNat).toList ++ (uintToBytes 3 hi.val).toList
        ++ (uintToBytes 1 (tau.val + 32 * mu.val)).toList ++ (uintToBytes 8 0).toList := by
  have hlo : lo.toNat < 2 ^ 32 := lo.toNat_lt_size
  have hhi := hi.isLt
  have ht : tau.val + 32 * mu.val < 2 ^ 8 := by have := tau.isLt; have := mu.isLt; omega
  -- Both are the bytes of `lo + 2^32 hi + 2^56 (tau + 32 mu)`, the high lane being zero.
  have hn : Hash.Keccak.Lanes2.toNat (encodeAddress tau mu hi lo) =
      lo.toNat + 2 ^ 32 * hi.val + 2 ^ 56 * (tau.val + 32 * mu.val) := by
    rw [Hash.Keccak.Lanes2.toNat, toNat_encodeAddress_lo]
    simp [encodeAddress]
  rw [Hash.Keccak.Lanes2.bytes_eq_uintToBytes, hn]
  generalize lo.toNat = a at *
  generalize hi.val = b at *
  generalize tau.val + 32 * mu.val = c at *
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [Vector.length_toList] at h1
  apply UInt8.toNat_inj.mp
  simp only [Vector.getElem_toList, Base.uintToBytes_eq_div, Vector.getElem_ofFn]
  interval_cases j <;> simp [UInt8.toNat_ofNat'] <;> omega

/-- The 16 bytes of an address determine its type, position and both fields.

- Bytes 0 to 3 hold `lo`, and bytes 4 to 6 hold `hi`.
- Byte 7 holds `tau + 32 mu`, and bytes 8 to 15 are zero.
-/
theorem encodeAddress_inj {tau tau' : Fin 32} {mu mu' : Fin 8} {hi hi' : Fin (2 ^ 24)}
    {lo lo' : UInt32} :
    encodeAddress tau mu hi lo = encodeAddress tau' mu' hi' lo' ↔
      tau = tau' ∧ mu = mu' ∧ hi = hi' ∧ lo = lo' := by
  constructor
  · intro h
    -- The first lane is the integer of bytes 0 to 7, and each field is below its range.
    have h := congrArg (fun a => a.lo.toNat) h
    simp only [toNat_encodeAddress_lo] at h
    have := lo.toNat_lt_size
    have := lo'.toNat_lt_size
    have := hi.isLt
    have := hi'.isLt
    have := tau.isLt
    have := tau'.isLt
    have := mu.isLt
    have := mu'.isLt
    simp only [UInt32.size] at *
    -- `tau < 32` is the remainder by 32 and `mu` the quotient.
    refine ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega),
      UInt32.toNat_inj.mp (by omega)⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- Addresses whose types differ are different addresses. -/
theorem encodeAddress_ne_of_type_ne {tau tau' : Fin 32} (mu mu' : Fin 8) (hi hi' : Fin (2 ^ 24))
    (lo lo' : UInt32) (h : tau ≠ tau') :
    encodeAddress tau mu hi lo ≠ encodeAddress tau' mu' hi' lo' :=
  fun same => h (encodeAddress_inj.mp same).1

/-- The seven address types have seven different codes. -/
theorem AddressType.code_injective : Function.Injective AddressType.code := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

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

/-! ## Distinct call sites have distinct addresses -/

/-- Two call sites with the same address are the same call site.

The type code tells the kinds apart, and the other fields hold the arguments. -/
theorem CallSite.encode_injective : Function.Injective CallSite.encode := by
  intro a b h
  -- The address determines its four fields.
  obtain ⟨htau, hmu, hhi, hlo⟩ := encodeAddress_inj.mp h
  -- Each field reads one argument of the call, or a constant.
  cases a <;> cases b <;>
    simp only [CallSite.tau, CallSite.mu, CallSite.hi, CallSite.lo, AddressType.code]
      at htau hmu hhi hlo <;>
    simp_all [Fin.castLE_inj] <;>
    -- Left: the same kind of call on both sides, and `hi` splits into the layer and the rest.
    · obtain ⟨hl, ha⟩ := layerHi_inj.mp hhi
      simp_all [Fin.castLE_inj]

/-! ## Each address determines its arguments -/

/-- A chain-start address names its layer, key and pair of chains. -/
theorem addrPrf_inj {layer layer' : Layer} {e e' : UInt32} {j j' : Fin (V / 2)} :
    addrPrf layer e j = addrPrf layer' e' j' ↔ layer = layer' ∧ e = e' ∧ j = j' := by
  simp only [addrPrf, CallSite.encode_injective.eq_iff, CallSite.prf.injEq]

/-- A chain-step address names its layer, key and position. -/
theorem addrChain_inj {layer layer' : Layer} {e e' : UInt32} {mu mu' : Fin (CHAIN_LENGTH - 1)} :
    addrChain layer e mu = addrChain layer' e' mu' ↔ layer = layer' ∧ e = e' ∧ mu = mu' := by
  simp only [addrChain, CallSite.encode_injective.eq_iff, CallSite.chain.injEq]

/-- A leaf address names its layer and key. -/
theorem addrLeaf_inj {layer layer' : Layer} {e e' : UInt32} :
    addrLeaf layer e = addrLeaf layer' e' ↔ layer = layer' ∧ e = e' := by
  simp only [addrLeaf, CallSite.encode_injective.eq_iff, CallSite.leaf.injEq]

/-- A node address names its layer, level and index. -/
theorem addrNode_inj {layer layer' : Layer} {level level' : Fin (LAYER_HEIGHT + 1)}
    {j j' : UInt32} :
    addrNode layer level j = addrNode layer' level' j' ↔
      layer = layer' ∧ level = level' ∧ j = j' := by
  simp only [addrNode, CallSite.encode_injective.eq_iff, CallSite.node.injEq]

/-- A randomizer-base address names its layer and key. -/
theorem addrRnd_inj {layer layer' : Layer} {e e' : UInt32} :
    addrRnd layer e = addrRnd layer' e' ↔ layer = layer' ∧ e = e' := by
  simp only [addrRnd, CallSite.encode_injective.eq_iff, CallSite.rnd.injEq]

/-- A digest address names its layer and key. -/
theorem addrMsg_inj {layer layer' : Layer} {e e' : UInt32} :
    addrMsg layer e = addrMsg layer' e' ↔ layer = layer' ∧ e = e' := by
  simp only [addrMsg, CallSite.encode_injective.eq_iff, CallSite.msg.injEq]

end EthLib.Cryptography.Xmss
