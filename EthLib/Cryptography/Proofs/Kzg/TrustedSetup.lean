module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Base.Proofs.MapM
public import EthLib.Cryptography.Kzg.TrustedSetup
public import EthLib.Cryptography.Proofs.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.G2Compress
public import EthLib.Cryptography.Proofs.Bls.G2Validity
public import EthLib.Cryptography.Proofs.Kzg.BitReversal

/-!
# Proofs: the decoded trusted setup

A setup is valid when each of its points is a point of its curve.

Every setup that the decoder returns is valid.

Each decoded byte string and each decoded `G2` point comes from the encoding at its position.

Validity says nothing about the subgroup, which the decoder does not check.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open EthLib.Base (array_mapM_ok array_mapM_ok_mem packBytes exactBytes? packBytes_injective
  size_packBytes)

/-- Each point of the setup is a point of its curve. -/
structure TrustedSetup.Valid (s : TrustedSetup) : Prop where
  g1LagrangeBrp : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Valid s.g1LagrangeBrp[i]
  g1Monomial : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Valid s.g1Monomial[i]
  g2Monomial : ∀ i : Fin KZG_SETUP_G2_LENGTH, G2.Valid s.g2Monomial[i]

/-- A setup string decodes to a `G1` point exactly when it is a compressed point of 48 bytes. -/
theorem TrustedSetup.decodeG1_eq_ok {b : ByteArray} {p : G1} :
    TrustedSetup.decodeG1 b = .ok p ↔ ∃ v, packBytes v = b ∧ G1.uncompress v = .ok p := by
  unfold TrustedSetup.decodeG1
  by_cases hsz : b.size = 48
  · rw [Base.exactBytes?_of_size_eq hsz]
    dsimp only
    rw [Base.mapError_ok_iff]
    refine ⟨fun h => ⟨_, rfl, h⟩, fun ⟨v, hv, h⟩ => ?_⟩
    -- The vector with the bytes of `b` is `v`, since their bytes agree.
    rwa [show (⟨b.data, hsz⟩ : Vector UInt8 48) = v from packBytes_injective hv.symm]
  · rw [Base.exactBytes?_of_size_ne hsz]
    dsimp only
    refine ⟨fun h => (by cases h), fun ⟨v, hv, _⟩ => absurd ?_ hsz⟩
    rw [← hv, size_packBytes]

/-- A point that decodes to a G1 point of the setup is valid. -/
private theorem valid_of_toG1 {b : ByteArray} {p : G1} (h : TrustedSetup.decodeG1 b = .ok p) :
    G1.Valid p := by
  obtain ⟨v, -, hu⟩ := TrustedSetup.decodeG1_eq_ok.mp h
  exact G1.uncompress_valid hu

/-- A setup string decodes to a `G2` point exactly when it is a compressed point of 96 bytes. -/
theorem TrustedSetup.decodeG2_eq_ok {b : ByteArray} {p : G2} :
    TrustedSetup.decodeG2 b = .ok p ↔ ∃ v, packBytes v = b ∧ G2.uncompress v = .ok p := by
  unfold TrustedSetup.decodeG2
  by_cases hsz : b.size = 96
  · rw [Base.exactBytes?_of_size_eq hsz]
    dsimp only
    rw [Base.mapError_ok_iff]
    refine ⟨fun h => ⟨_, rfl, h⟩, fun ⟨v, hv, h⟩ => ?_⟩
    -- The vector with the bytes of `b` is `v`, since their bytes agree.
    rwa [show (⟨b.data, hsz⟩ : Vector UInt8 96) = v from packBytes_injective hv.symm]
  · rw [Base.exactBytes?_of_size_ne hsz]
    dsimp only
    refine ⟨fun h => (by cases h), fun ⟨v, hv, _⟩ => absurd ?_ hsz⟩
    rw [← hv, size_packBytes]

/-- A point that decodes to a G2 point of the setup is valid. -/
private theorem valid_of_toG2 {b : ByteArray} {p : G2} (h : TrustedSetup.decodeG2 b = .ok p) :
    G2.Valid p := by
  obtain ⟨v, -, hu⟩ := TrustedSetup.decodeG2_eq_ok.mp h
  rcases G2.uncompress_valid hu with rfl | ⟨hz, htwist⟩
  · exact G2.valid_zero
  · exact G2.valid_of_isOnTwist_of_z_one hz htwist

/-- Every setup that the decoder returns is valid. -/
theorem TrustedSetup.ofBytes_valid {g1LagrangeBytes g1MonomialBytes g2MonomialBytes : Array ByteArray}
    {s : TrustedSetup} (h : TrustedSetup.ofBytes g1LagrangeBytes g1MonomialBytes g2MonomialBytes = .ok s) :
    s.Valid := by
  unfold TrustedSetup.ofBytes at h
  dsimp only at h
  -- Each list decodes, or the decoder fails.
  cases h₁ : g1LagrangeBytes.mapM TrustedSetup.decodeG1 with
  | error e => rw [h₁] at h; cases h
  | ok lagrange =>
  cases h₂ : g1MonomialBytes.mapM TrustedSetup.decodeG1 with
  | error e => rw [h₁, h₂] at h; cases h
  | ok monomial =>
  cases h₃ : g2MonomialBytes.mapM TrustedSetup.decodeG2 with
  | error e => rw [h₁, h₂, h₃] at h; cases h
  | ok monomial2 =>
  rw [h₁, h₂, h₃] at h
  dsimp only [bind, Except.bind] at h
  -- Only the branch with three correct lengths returns a setup.
  split at h
  · rename_i hl
    split at h
    · rename_i hm
      split at h
      · rename_i hm2
        cases h
        refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
        · -- A bit-reversed point is a decoded point at a reversed index.
          have hsz : lagrange.size = 2 ^ 12 := hl
          have key : ∀ j (hj : j < (bitReversalPermutation lagrange).size),
              G1.Valid (bitReversalPermutation lagrange)[j] := by
            intro j hj
            rw [getElem_bitReversalPermutation, hsz]
            have hr : reverseBits j (2 ^ 12) < lagrange.size := by
              rw [hsz]
              exact reverseBits_lt_two_pow _ _
            rw [getElem!_pos lagrange _ hr]
            obtain ⟨b, -, hb⟩ := array_mapM_ok_mem h₁ _ (Array.getElem_mem hr)
            exact valid_of_toG1 hb
          exact key i.val (by rw [size_bitReversalPermutation, hl]; exact i.isLt)
        · have hi : i.val < monomial.size := by rw [hm]; exact i.isLt
          obtain ⟨b, -, hb⟩ := array_mapM_ok_mem h₂ _ (Array.getElem_mem hi)
          exact valid_of_toG1 hb
        · have hi : i.val < monomial2.size := by rw [hm2]; exact i.isLt
          obtain ⟨b, -, hb⟩ := array_mapM_ok_mem h₃ _ (Array.getElem_mem hi)
          exact valid_of_toG2 hb
      · cases h
    · cases h
  · cases h

/-- Each monomial point of `G1` in a decoded setup decodes from one of the given encodings. -/
theorem TrustedSetup.ofBytes_g1Monomial_mem
    {g1LagrangeBytes g1MonomialBytes g2MonomialBytes : Array ByteArray} {s : TrustedSetup}
    (h : TrustedSetup.ofBytes g1LagrangeBytes g1MonomialBytes g2MonomialBytes = .ok s)
    (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    ∃ b ∈ g1MonomialBytes, TrustedSetup.decodeG1 b = .ok s.g1Monomial[i] := by
  unfold TrustedSetup.ofBytes at h
  dsimp only at h
  cases h₁ : g1LagrangeBytes.mapM TrustedSetup.decodeG1 with
  | error e => rw [h₁] at h; cases h
  | ok lagrange =>
  cases h₂ : g1MonomialBytes.mapM TrustedSetup.decodeG1 with
  | error e => rw [h₁, h₂] at h; cases h
  | ok monomial =>
  cases h₃ : g2MonomialBytes.mapM TrustedSetup.decodeG2 with
  | error e => rw [h₁, h₂, h₃] at h; cases h
  | ok monomial2 =>
  rw [h₁, h₂, h₃] at h
  dsimp only [bind, Except.bind] at h
  split at h
  · split at h
    · rename_i hm
      split at h
      · cases h
        have hi : i.val < monomial.size := by rw [hm]; exact i.isLt
        obtain ⟨b, hmem, hb⟩ := array_mapM_ok_mem h₂ _ (Array.getElem_mem hi)
        exact ⟨b, hmem, hb⟩
      · cases h
    · cases h
  · cases h

/-- Each string of a decoded list gives the byte string at its position. -/
theorem TrustedSetup.hexListToBytes_getElem {hex : Array String} {bytes : Array ByteArray}
    (h : TrustedSetup.hexListToBytes hex = .ok bytes) :
    bytes.size = hex.size ∧
      ∀ (i : Nat) (hi : i < hex.size), TrustedSetup.hexToBytes? hex[i] = some bytes[i]! := by
  obtain ⟨hsize, hget⟩ := array_mapM_ok h
  refine ⟨hsize, fun i hi => ?_⟩
  have hj : i < bytes.size := hsize ▸ hi
  have he := hget i hi hj
  rw [getElem!_pos bytes i hj]
  split at he
  · rename_i b hb
    rw [hb, Except.ok.inj he]
  · cases he

/-- Each `G2` point of a decoded setup is the decoding of the string at its position. -/
theorem TrustedSetup.ofBytes_g2Monomial
    {g1LagrangeBytes g1MonomialBytes g2MonomialBytes : Array ByteArray} {s : TrustedSetup}
    (h : TrustedSetup.ofBytes g1LagrangeBytes g1MonomialBytes g2MonomialBytes = .ok s)
    (i : Nat) (hi : i < KZG_SETUP_G2_LENGTH) :
    ∃ hb : i < g2MonomialBytes.size,
      TrustedSetup.decodeG2 g2MonomialBytes[i] = .ok (s.g2Monomial[i]'hi) := by
  unfold TrustedSetup.ofBytes at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i monomial2 h₃
  split at h
  · split at h
    · split at h
      · rename_i hsz
        cases h
        obtain ⟨hcsz, hc⟩ := array_mapM_ok h₃
        have hm : i < monomial2.size := by rw [hsz]; exact hi
        have hb : i < g2MonomialBytes.size := by rw [← hcsz]; exact hm
        exact ⟨hb, hc i hb hm⟩
      · cases h
    · cases h
  · cases h

/-- The embedded setup, when it decodes, is valid. -/
theorem TrustedSetup.ofHex_valid {s : TrustedSetup} (h : TrustedSetup.ofHex = .ok s) :
    s.Valid := by
  unfold TrustedSetup.ofHex at h
  -- The three lists stay abstract, so no step evaluates the decoding.
  generalize TrustedSetup.hexListToBytes TrustedSetupData.g1LagrangeHex = a at h
  generalize TrustedSetup.hexListToBytes TrustedSetupData.g1MonomialHex = b at h
  generalize TrustedSetup.hexListToBytes TrustedSetupData.g2MonomialHex = c at h
  cases a with
  | error e => cases h
  | ok x =>
  cases b with
  | error e => cases h
  | ok y =>
  cases c with
  | error e => cases h
  | ok z => exact ofBytes_valid h

/-- In a valid setup, each monomial G1 point is valid, read by array position. -/
theorem TrustedSetup.Valid.g1Monomial_getElem! {s : TrustedSetup} (h : s.Valid) {t : Nat}
    (ht : t < FIELD_ELEMENTS_PER_BLOB) : G1.Valid s.g1Monomial.toArray[t]! := by
  rw [getElem!_pos s.g1Monomial.toArray t (by simpa using ht)]
  exact h.g1Monomial ⟨t, ht⟩

end EthLib.Cryptography.Kzg
