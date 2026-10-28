import EthLib.Cryptography.Xmss.Address
import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: `Xmss.Address`

Distinct call sites have distinct addresses.

- The encoding is injective on its four fields.
- The type codes are distinct, so two address types never share an address.
- The top layer's flag is a separate bit, so the two layers never share an address.
- Each address of a key determines its own arguments.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## The encoding is injective -/

/-- Two concatenations with first parts of the same length agree part by part. -/
private theorem vector_append_inj {n m : Nat} {a c : Vector UInt8 n} {b d : Vector UInt8 m}
    (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  -- Compare the underlying arrays, whose first parts have the same size.
  have := congrArg Vector.toArray h
  simp only [Vector.toArray_append] at this
  obtain ⟨ha, hb⟩ := Array.append_inj this (by simp)
  exact ⟨Vector.toArray_inj.mp ha, Vector.toArray_inj.mp hb⟩

/-- Equal little-endian encodings of two integers below `256^k` mean equal integers. -/
private theorem littleEndian_inj {k x y : Nat} (hx : x < 256 ^ k) (hy : y < 256 ^ k)
    (h : littleEndian k x = littleEndian k y) : x = y := by
  -- Reading the bytes back returns each integer, unchanged by the bound.
  have := congrArg fromLittleEndian h
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this

/-- The 16 bytes of an address determine its type, position and both fields.

```text
    bytes 0-3   lo
    bytes 4-6   hi
    byte  7     tau + 32 mu
    bytes 8-15  zero
```
-/
theorem encodeAddress_inj {tau tau' : Fin 32} {mu mu' : Fin 8} {hi hi' : Fin (2 ^ 24)}
    {lo lo' : UInt32} :
    encodeAddress tau mu hi lo = encodeAddress tau' mu' hi' lo' ↔
      tau = tau' ∧ mu = mu' ∧ hi = hi' ∧ lo = lo' := by
  constructor
  · intro h
    -- Peel the zero tail, then the type byte, then the two fields.
    obtain ⟨h, -⟩ := vector_append_inj h
    obtain ⟨h, htype⟩ := vector_append_inj h
    obtain ⟨hlo, hhi⟩ := vector_append_inj h
    -- Each field is below the range its bytes cover.
    have lo_eq := littleEndian_inj lo.toNat_lt_size lo'.toNat_lt_size hlo
    have hi_eq := littleEndian_inj (k := 3) hi.isLt hi'.isLt hhi
    have type_eq := littleEndian_inj (k := 1)
      (by have := tau.isLt; have := mu.isLt; omega)
      (by have := tau'.isLt; have := mu'.isLt; omega) htype
    -- `tau < 32` is the remainder by 32 and `mu` the quotient.
    refine ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext hi_eq, UInt32.toNat_inj.mp lo_eq⟩
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

/-! ## Each address determines its arguments -/

/-- A chain-start address names its layer, key and pair of chains. -/
theorem addrPrf_inj {layer layer' : Layer} {e e' : UInt32} {j j' : Fin (V / 2)} :
    addrPrf layer e j = addrPrf layer' e' j' ↔ layer = layer' ∧ e = e' ∧ j = j' := by
  constructor
  · intro h
    obtain ⟨-, -, hhi, he⟩ := encodeAddress_inj.mp h
    obtain ⟨hl, hj⟩ := layerHi_inj.mp hhi
    exact ⟨hl, he, Fin.ext (by simpa using congrArg Fin.val hj)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- A chain-step address names its layer, key and position. -/
theorem addrChain_inj {layer layer' : Layer} {e e' : UInt32} {mu mu' : Fin (CHAIN_LENGTH - 1)} :
    addrChain layer e mu = addrChain layer' e' mu' ↔ layer = layer' ∧ e = e' ∧ mu = mu' := by
  constructor
  · intro h
    obtain ⟨-, hmu, hhi, he⟩ := encodeAddress_inj.mp h
    exact ⟨(layerHi_inj.mp hhi).1, he, Fin.ext (by simpa using congrArg Fin.val hmu)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- A leaf address names its layer and key. -/
theorem addrLeaf_inj {layer layer' : Layer} {e e' : UInt32} :
    addrLeaf layer e = addrLeaf layer' e' ↔ layer = layer' ∧ e = e' := by
  constructor
  · intro h
    obtain ⟨-, -, hhi, he⟩ := encodeAddress_inj.mp h
    exact ⟨(layerHi_inj.mp hhi).1, he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A node address names its layer, level and index. -/
theorem addrNode_inj {layer layer' : Layer} {level level' : Fin (LAYER_HEIGHT + 1)}
    {j j' : UInt32} :
    addrNode layer level j = addrNode layer' level' j' ↔
      layer = layer' ∧ level = level' ∧ j = j' := by
  constructor
  · intro h
    obtain ⟨-, -, hhi, hj⟩ := encodeAddress_inj.mp h
    obtain ⟨hl, hlevel⟩ := layerHi_inj.mp hhi
    exact ⟨hl, Fin.ext (by simpa using congrArg Fin.val hlevel), hj⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- A randomizer-base address names its layer and key. -/
theorem addrRnd_inj {layer layer' : Layer} {e e' : UInt32} :
    addrRnd layer e = addrRnd layer' e' ↔ layer = layer' ∧ e = e' := by
  constructor
  · intro h
    obtain ⟨-, -, hhi, he⟩ := encodeAddress_inj.mp h
    exact ⟨(layerHi_inj.mp hhi).1, he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A digest address names its layer and key. -/
theorem addrMsg_inj {layer layer' : Layer} {e e' : UInt32} :
    addrMsg layer e = addrMsg layer' e' ↔ layer = layer' ∧ e = e' := by
  constructor
  · intro h
    obtain ⟨-, -, hhi, he⟩ := encodeAddress_inj.mp h
    exact ⟨(layerHi_inj.mp hhi).1, he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## Known answer -/

/-- One address, worked out by hand from the encoding.

```text
    lo  = 0x89abcdef     ->  ef cd ab 89
    hi  = 0x123456       ->  56 34 12
    tau = 19, mu = 5     ->  19 + 32 * 5 = 179 = b3
    then eight zero bytes
```
-/
theorem encodeAddress_known_answer :
    encodeAddress 19 5 ⟨0x123456, by decide⟩ 0x89abcdef =
      #v[0xef, 0xcd, 0xab, 0x89, 0x56, 0x34, 0x12, 0xb3, 0, 0, 0, 0, 0, 0, 0, 0] := by
  -- `decide` cannot find the instance: the literal has length `16` and `Address` has
  -- length `ADDRESS_LEN`, which instance search does not unfold. Both sides reduce to the
  -- same vector, so `rfl` closes it.
  rfl

/-- The top layer sets bit 23 of `hi`, the top bit of byte 6. -/
theorem addrLeaf_top_known_answer :
    addrLeaf .top 0x0102 =
      #v[0x02, 0x01, 0, 0, 0, 0, 0x80, 0x02, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rfl

end EthLib.Cryptography.Xmss
