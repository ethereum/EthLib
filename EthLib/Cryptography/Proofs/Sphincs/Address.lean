import EthLib.Cryptography.Sphincs.Address
import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: `Sphincs.Address`

Distinct call sites have distinct addresses.

- The encoding is injective on its six fields.
- The type codes are distinct, so two address types never share an address.
- Each address of a key determines its own arguments, the layer and the tree included.
- A FORS address determines its instance, its tree and its position.
- A digest address determines its call.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## The encoding is injective -/

/-- Two concatenations with first parts of the same length agree part by part. -/
theorem vector_append_inj {n m : Nat} {a c : Vector UInt8 n} {b d : Vector UInt8 m}
    (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  -- Compare the underlying arrays, whose first parts have the same size.
  have := congrArg Vector.toArray h
  simp only [Vector.toArray_append] at this
  obtain ⟨ha, hb⟩ := Array.append_inj this (by simp)
  exact ⟨Vector.toArray_inj.mp ha, Vector.toArray_inj.mp hb⟩

/-- Equal little-endian encodings of two integers below `256^k` mean equal integers. -/
theorem littleEndian_inj {k x y : Nat} (hx : x < 256 ^ k) (hy : y < 256 ^ k)
    (h : littleEndian k x = littleEndian k y) : x = y := by
  -- Reading the bytes back returns each integer, unchanged by the bound.
  have := congrArg fromLittleEndian h
  simpa [Xmss.fromLittleEndian_littleEndian, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this

/-- The 16 bytes of an address determine all six of its fields.

```text
    bytes 0-3    lo
    bytes 4-6    hi
    byte  7      type + 32 step
    byte  8      layer
    bytes 9-12   tree
    bytes 13-15  zero
```
-/
theorem encodeAddress_inj {type type' : Fin 32} {step step' : Fin 8} {layer layer' : Fin 256}
    {tree tree' : UInt32} {hi hi' : Fin (2 ^ 24)} {lo lo' : UInt32} :
    encodeAddress type step layer tree hi lo = encodeAddress type' step' layer' tree' hi' lo' ↔
      type = type' ∧ step = step' ∧ layer = layer' ∧ tree = tree' ∧ hi = hi' ∧ lo = lo' := by
  constructor
  · intro h
    -- Peel the zero tail, then the tree, the layer, the type byte and the two fields.
    obtain ⟨h, -⟩ := vector_append_inj h
    obtain ⟨h, htree⟩ := vector_append_inj h
    obtain ⟨h, hlayer⟩ := vector_append_inj h
    obtain ⟨h, htype⟩ := vector_append_inj h
    obtain ⟨hlo, hhi⟩ := vector_append_inj h
    -- Each field is below the range its bytes cover.
    have lo_eq := littleEndian_inj lo.toNat_lt_size lo'.toNat_lt_size hlo
    have hi_eq := littleEndian_inj (k := 3) hi.isLt hi'.isLt hhi
    have tree_eq := littleEndian_inj tree.toNat_lt_size tree'.toNat_lt_size htree
    have layer_eq := littleEndian_inj (k := 1) layer.isLt layer'.isLt hlayer
    have type_eq := littleEndian_inj (k := 1)
      (by have := type.isLt; have := step.isLt; omega)
      (by have := type'.isLt; have := step'.isLt; omega) htype
    -- `type < 32` is the remainder by 32 and `step` the quotient.
    refine ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext layer_eq, UInt32.toNat_inj.mp tree_eq,
      Fin.ext hi_eq, UInt32.toNat_inj.mp lo_eq⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

/-- Addresses whose types differ are different addresses, whatever their other fields. -/
theorem encodeAddress_ne_of_type_ne {type type' : Fin 32} (step step' : Fin 8) (layer layer' : Fin 256)
    (tree tree' : UInt32) (hi hi' : Fin (2 ^ 24)) (lo lo' : UInt32) (h : type ≠ type') :
    encodeAddress type step layer tree hi lo ≠ encodeAddress type' step' layer' tree' hi' lo' :=
  fun same => h (encodeAddress_inj.mp same).1

/-- The eleven address types have eleven different codes. -/
theorem AddressType.code_injective : Function.Injective AddressType.code := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-! ## The hypertree -/

/-- The three layers have three different numbers. -/
theorem Layer.toNat_injective : Function.Injective Layer.toNat := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- A number below `2^32` survives the trip through a 32-bit word. -/
theorem uint32_ofNat_inj {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32)
    (h : UInt32.ofNat x = UInt32.ofNat y) : x = y := by
  have := congrArg UInt32.toNat h
  rwa [UInt32.toNat_ofNat_of_lt' hx, UInt32.toNat_ofNat_of_lt' hy] at this

/-- A key whose tree and leaf fit their 32-bit fields. -/
def OtsKey.Fits (key : OtsKey) : Prop :=
  key.tree < 2 ^ 32 ∧ key.leaf < 2 ^ 32

/-- A key address determines its type, step, key and `hi`. -/
theorem keyAddress_inj {type type' : AddressType} {step step' : Fin 8} {key key' : OtsKey}
    {hi hi' : Fin (2 ^ 24)} (hk : key.Fits) (hk' : key'.Fits)
    (h : keyAddress type step key hi = keyAddress type' step' key' hi') :
    type = type' ∧ step = step' ∧ key = key' ∧ hi = hi' := by
  obtain ⟨htype, hstep, hlayer, htree, hhi, hleaf⟩ := encodeAddress_inj.mp h
  refine ⟨AddressType.code_injective htype, hstep, ?_, hhi⟩
  -- The layer byte, the tree and the leaf rebuild the key.
  have hl := Layer.toNat_injective (congrArg Fin.val hlayer)
  have ht := uint32_ofNat_inj hk.1 hk'.1 htree
  have he := uint32_ofNat_inj hk.2 hk'.2 hleaf
  cases key
  cases key'
  simp_all

/-- A chain-start address names its key and its pair of chains. -/
theorem addrPrf_inj {key key' : OtsKey} {j j' : Fin (V / 2)} (hk : key.Fits) (hk' : key'.Fits)
    (h : addrPrf key j = addrPrf key' j') : key = key' ∧ j = j' := by
  obtain ⟨-, -, hkey, hhi⟩ := keyAddress_inj hk hk' h
  exact ⟨hkey, Fin.ext (by simpa [forsLeafPosition] using congrArg Fin.val hhi)⟩

/-- A chain-step address names its key, its chain and the position the step leaves. -/
theorem addrChain_inj {key key' : OtsKey} {i i' : Fin V} {mu mu' : Fin (CHAIN_LENGTH - 1)}
    (hk : key.Fits) (hk' : key'.Fits) (h : addrChain key i mu = addrChain key' i' mu') :
    key = key' ∧ i = i' ∧ mu = mu' := by
  obtain ⟨-, hstep, hkey, hhi⟩ := keyAddress_inj hk hk' h
  exact ⟨hkey, Fin.ext (by simpa using congrArg Fin.val hhi),
    Fin.ext (by simpa using congrArg Fin.val hstep)⟩

/-- A leaf address names its key. -/
theorem addrLeaf_inj {key key' : OtsKey} (hk : key.Fits) (hk' : key'.Fits)
    (h : addrLeaf key = addrLeaf key') : key = key' :=
  (keyAddress_inj hk hk' h).2.2.1

/-- An encoding address names its key. -/
theorem addrEncoding_inj {key key' : OtsKey} (hk : key.Fits) (hk' : key'.Fits)
    (h : addrEncoding key = addrEncoding key') : key = key' :=
  (keyAddress_inj hk hk' h).2.2.1

/-- A node address names its layer, its tree, its level and its index. -/
theorem addrNode_inj {layer layer' : Layer} {tree tree' j j' : Nat}
    {level level' : Fin (TOP_HEIGHT + 1)} (ht : tree < 2 ^ 32) (ht' : tree' < 2 ^ 32)
    (hj : j < 2 ^ 32) (hj' : j' < 2 ^ 32)
    (h : addrNode layer tree level j = addrNode layer' tree' level' j') :
    layer = layer' ∧ tree = tree' ∧ level = level' ∧ j = j' := by
  obtain ⟨-, -, hlayer, htree, hhi, hlo⟩ := encodeAddress_inj.mp h
  exact ⟨Layer.toNat_injective (congrArg Fin.val hlayer), uint32_ofNat_inj ht ht' htree,
    Fin.ext (by simpa [forsLeafPosition] using congrArg Fin.val hhi), uint32_ofNat_inj hj hj' hlo⟩

/-! ## The message digest -/

/-- The two digest calls have distinct addresses. -/
theorem addrMsg_inj {call call' : Fin DIGEST_CALLS} (h : addrMsg call = addrMsg call') :
    call = call' := by
  obtain ⟨-, -, -, -, hhi, -⟩ := encodeAddress_inj.mp h
  -- The call number is the field `hi`.
  exact Fin.ext (by simpa using congrArg Fin.val hhi)

/-! ## FORS -/

/-- `kappa + 64 p` determines the tree and the position. -/
theorem forsHi_inj {kappa kappa' : Fin FORS_TREES} {p p' : Fin (16 * 2 ^ FORS_HEIGHT)}
    (h : forsHi kappa p = forsHi kappa' p') : kappa = kappa' ∧ p = p' := by
  have h := congrArg Fin.val h
  simp only [forsHi] at h
  -- The tree is the remainder by 64, the position the quotient.
  have := kappa.isLt
  have := kappa'.isLt
  simp only [FORS_TREES] at *
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- `lambda + 16 j` determines the level and the node. -/
theorem forsNodePosition_inj {level level' : Fin 16} {j j' : Fin (2 ^ FORS_HEIGHT)}
    (h : forsNodePosition level j = forsNodePosition level' j') : level = level' ∧ j = j' := by
  have h := congrArg Fin.val h
  simp only [forsNodePosition] at h
  -- The level is the remainder by 16, the node the quotient.
  have := level.isLt
  have := level'.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- A FORS secret address names its instance, its tree and its pair of leaves. -/
theorem addrForsPrf_inj {idx idx' : Nat} {kappa kappa' : Fin FORS_TREES}
    {p p' : Fin (2 ^ FORS_HEIGHT / 2)} (hi : idx < 2 ^ 32) (hi' : idx' < 2 ^ 32)
    (h : addrForsPrf idx kappa p = addrForsPrf idx' kappa' p') :
    idx = idx' ∧ kappa = kappa' ∧ p = p' := by
  obtain ⟨-, -, -, -, hhi, hlo⟩ := encodeAddress_inj.mp h
  obtain ⟨hk, hp⟩ := forsHi_inj hhi
  exact ⟨uint32_ofNat_inj hi hi' hlo, hk, Fin.ext (by simpa [forsLeafPosition] using congrArg Fin.val hp)⟩

/-- A FORS leaf address names its instance, its tree and its leaf. -/
theorem addrForsLeaf_inj {idx idx' : Nat} {kappa kappa' : Fin FORS_TREES}
    {l l' : Fin (2 ^ FORS_HEIGHT)} (hi : idx < 2 ^ 32) (hi' : idx' < 2 ^ 32)
    (h : addrForsLeaf idx kappa l = addrForsLeaf idx' kappa' l') :
    idx = idx' ∧ kappa = kappa' ∧ l = l' := by
  obtain ⟨-, -, -, -, hhi, hlo⟩ := encodeAddress_inj.mp h
  obtain ⟨hk, hl⟩ := forsHi_inj hhi
  exact ⟨uint32_ofNat_inj hi hi' hlo, hk, Fin.ext (by simpa [forsLeafPosition] using congrArg Fin.val hl)⟩

/-- A FORS node address names its instance, its tree, its level and its node. -/
theorem addrForsNode_inj {idx idx' : Nat} {kappa kappa' : Fin FORS_TREES} {level level' : Fin 16}
    {j j' : Fin (2 ^ FORS_HEIGHT)} (hi : idx < 2 ^ 32) (hi' : idx' < 2 ^ 32)
    (h : addrForsNode idx kappa level j = addrForsNode idx' kappa' level' j') :
    idx = idx' ∧ kappa = kappa' ∧ level = level' ∧ j = j' := by
  obtain ⟨-, -, -, -, hhi, hlo⟩ := encodeAddress_inj.mp h
  obtain ⟨hk, hpos⟩ := forsHi_inj hhi
  obtain ⟨hl, hj⟩ := forsNodePosition_inj hpos
  exact ⟨uint32_ofNat_inj hi hi' hlo, hk, hl, hj⟩

/-! ## Known answers -/

/-- One address with every field set, worked out by hand from the encoding.

- `lo = 0x89abcdef` gives the bytes `ef cd ab 89`.
- `hi = 0x123456` gives `56 34 12`.
- Type 17 and step 5 give `17 + 32 * 5 = 177`, the byte `b1`.
- Layer 2 gives `02`.
- `tree = 0x0a0b0c0d` gives `0d 0c 0b 0a`.
- Three zero bytes end it.
-/
theorem encodeAddress_known_answer :
    encodeAddress 17 5 2 0x0a0b0c0d ⟨0x123456, by decide⟩ 0x89abcdef =
      #v[0xef, 0xcd, 0xab, 0x89, 0x56, 0x34, 0x12, 0xb1, 0x02, 0x0d, 0x0c, 0x0b, 0x0a, 0, 0, 0] := by
  -- The literal has length `16` and `Address` has length `ADDRESS_LEN`.
  -- Instance search does not unfold that constant, so `decide` finds no instance.
  -- Both sides reduce to the same vector, so `rfl` closes it.
  rfl

/-- Step 2 of chain 5 of leaf 3 of middle tree 9.

```text
    lo = 3, hi = 5, type 1 + 32 * 2 = 65, layer 1, tree 9
```
-/
theorem addrChain_known_answer :
    addrChain ⟨.middle, 9, 3⟩ ⟨5, by decide⟩ ⟨2, by decide⟩
      = #v[3, 0, 0, 0, 5, 0, 0, 65, 1, 9, 0, 0, 0, 0, 0, 0] := by
  rfl

/-- Call 1 of the message digest.

```text
    lo = 0, hi = 1, type 12
```
-/
theorem addrMsg_known_answer :
    addrMsg ⟨1, by decide⟩ = #v[0, 0, 0, 0, 1, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rfl

/-- Node 7 on level 4 of FORS tree 18 of instance `0xABCDEF`.

```text
    lo = 0xabcdef, hi = 18 + 64 * (4 + 16 * 7) = 7442 = 0x001d12, type 17
```
-/
theorem addrForsNode_known_answer :
    addrForsNode 0xABCDEF ⟨18, by decide⟩ 4 ⟨7, by decide⟩
      = #v[0xef, 0xcd, 0xab, 0, 0x12, 0x1d, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rfl

end EthLib.Cryptography.Sphincs
