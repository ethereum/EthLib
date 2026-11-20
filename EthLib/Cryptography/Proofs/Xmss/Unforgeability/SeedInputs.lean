module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Scheme
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.HashSig.Bytes
public import EthLib.Cryptography.Proofs.DerivationTable

/-!
# Hash inputs of the two hidden seeds

The leanXMSS draft in "Hashing and parameters" puts each secret in a fixed byte range.
A public hash input therefore fixes at most one candidate for each secret.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open XmssSecurity (HashSpec HashOutput MasterSeed seedHashInput)

/-- `S` is the hash at `"leanXMSS" | S_0`. -/
def seedEncoding : SecretEncoding HashSpec MasterSeed Unit HashOutput where
  enc s0 _ := seedHashInput s0
  range_eq _ _ := rfl
  injective _ _ _ _ := rfl

/-- The input of `S` fixes `S_0`. -/
theorem seedHashInput_inj {s0 s0' : MasterSeed} (h : seedHashInput s0 = seedHashInput s0') :
    s0 = s0' := by
  have bytes : HashSig.bytesLE 32 s0 = HashSig.bytesLE 32 s0' := List.append_cancel_left h
  apply HashSig.ofBV_inj (n := 32) (by decide)
  apply Vector.toList_inj.mp
  simpa only [HashSig.toList_ofBV] using bytes

/-- There are `2^256` seeds `S_0`. -/
theorem natCard_masterSeed : Nat.card MasterSeed = 2 ^ 256 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_bitVec]

/-- A given input is the input of `S` for a uniform `S_0` with probability at most `2^-256`. -/
theorem prEvent_mem_range_seedEncoding_le (t : HashSig.HashInput) :
    Pr{let s0 ← XmssSecurity.sampleMasterSeed}[t ∈ Set.range (seedEncoding.enc s0)] ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let := SampleableType.ofFintype MasterSeed
  have h := prEvent_mem_range_enc_le seedEncoding
    (fun _ _ _ _ h => seedHashInput_inj h) t
  rw [natCard_masterSeed, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- What a derivation from the scheme seed reads: a parameter, an address and a suffix. -/
abbrev PrfInput := PublicParam × Address × ByteArray

/-- A derivation from `S` is the hash at `P | A | S | suffix`.

The secret is the first hop's table of one entry, the answer that `S` is. -/
def prfEncoding : SecretEncoding HashSpec (Unit → HashOutput) PrfInput HashOutput where
  enc f x := (thInput x.1 x.2.1 (packBytes (ofOutput (f ())) ++ x.2.2)).data.toList
  range_eq _ _ := rfl
  injective f x y h := by
    obtain ⟨pp, a, m⟩ := x
    obtain ⟨pp', a', m'⟩ := y
    obtain ⟨hpp, ha, hm⟩ := thInput_inj (ByteArray.ext (Array.toList_inj.mp h))
    obtain ⟨-, hm⟩ := HashSig.byteArray_append_inj hm rfl
    exact Prod.ext hpp (Prod.ext ha hm)

/-- An input fixes the table of the first hop, which it encodes in its seed. -/
theorem prfEncoding_fix (f f' : Unit → HashOutput) (x x' : PrfInput)
    (h : prfEncoding.enc f x = prfEncoding.enc f' x') : f = f' := by
  obtain ⟨-, -, hm⟩ := thInput_inj (ByteArray.ext (Array.toList_inj.mp h))
  obtain ⟨hs, -⟩ := HashSig.byteArray_append_inj hm (by simp)
  funext u
  exact HashSig.ofBV_inj (n := 32) (by simp [HashSig.hashOutputBits])
    (packBytes_injective hs)

/-- There are `2^256` tables of the first hop. -/
theorem natCard_table : Nat.card (Unit → HashOutput) = 2 ^ 256 := by
  rw [Nat.card_fun, Nat.card_unique (α := Unit), pow_one, Nat.card_eq_fintype_card,
    Fintype.card_bitVec]
  rfl

/-- A given input encodes a derivation under a uniform table with probability `<= 2^-256`. -/
theorem prEvent_mem_range_prfEncoding_le (t : HashSig.HashInput) :
    Pr{let f ← $ᵗ (Unit → HashOutput)}[t ∈ Set.range (prfEncoding.enc f)] ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have h := prEvent_mem_range_enc_le prfEncoding prfEncoding_fix t
  rw [natCard_table, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

end EthLib.Cryptography.Xmss.Unforgeability
