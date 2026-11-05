module

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

Validity says nothing about the subgroup, which the decoder does not check.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal

/-- Each point of the setup is a point of its curve. -/
structure TrustedSetup.Valid (s : TrustedSetup) : Prop where
  g1LagrangeBrp : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Valid s.g1LagrangeBrp[i]
  g1Monomial : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Valid s.g1Monomial[i]
  g2Monomial : ∀ i : Fin KZG_SETUP_G2_LENGTH, G2.Valid s.g2Monomial[i]

/-- Every output of a successful map over an array is the image of some input. -/
theorem mem_of_mapM_ok {ε α β : Type} {f : α → Except ε β} {xs : Array α}
    {ys : Array β} (h : xs.mapM f = .ok ys) : ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok zs =>
    rw [hl] at h
    have hys : zs.toArray = ys := Except.ok.inj h
    subst hys
    intro y hy
    obtain ⟨x, hmem, hx⟩ := Base.mapM_ok_mem hl y (List.mem_toArray.mp hy)
    exact ⟨x, Array.mem_toList_iff.mp hmem, hx⟩

/-- A point that decodes to a G1 point of the setup is valid. -/
private theorem valid_of_toG1 {b : ByteArray} {p : G1}
    (h : ((Bls.G1.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup) = .ok p) :
    G1.Valid p := by
  cases hu : Bls.G1.uncompress b with
  | error e => rw [hu] at h; cases h
  | ok q =>
    rw [hu] at h
    cases h
    exact G1.uncompress_valid hu

/-- A point that decodes to a G2 point of the setup is valid. -/
private theorem valid_of_toG2 {b : ByteArray} {p : G2}
    (h : ((Bls.G2.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup) = .ok p) :
    G2.Valid p := by
  cases hu : Bls.G2.uncompress b with
  | error e => rw [hu] at h; cases h
  | ok q =>
    rw [hu] at h
    cases h
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
  cases h₁ : g1LagrangeBytes.mapM fun b =>
      (Bls.G1.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup with
  | error e => rw [h₁] at h; cases h
  | ok lagrange =>
  cases h₂ : g1MonomialBytes.mapM fun b =>
      (Bls.G1.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup with
  | error e => rw [h₁, h₂] at h; cases h
  | ok monomial =>
  cases h₃ : g2MonomialBytes.mapM fun b =>
      (Bls.G2.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup with
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
            obtain ⟨b, -, hb⟩ := mem_of_mapM_ok h₁ _ (Array.getElem_mem hr)
            exact valid_of_toG1 hb
          exact key i.val (by rw [size_bitReversalPermutation, hl]; exact i.isLt)
        · have hi : i.val < monomial.size := by rw [hm]; exact i.isLt
          obtain ⟨b, -, hb⟩ := mem_of_mapM_ok h₂ _ (Array.getElem_mem hi)
          exact valid_of_toG1 hb
        · have hi : i.val < monomial2.size := by rw [hm2]; exact i.isLt
          obtain ⟨b, -, hb⟩ := mem_of_mapM_ok h₃ _ (Array.getElem_mem hi)
          exact valid_of_toG2 hb
      · cases h
    · cases h
  · cases h

/-- Each monomial point of `G1` in a decoded setup decodes from one of the given encodings. -/
theorem TrustedSetup.ofBytes_g1Monomial_mem
    {g1LagrangeBytes g1MonomialBytes g2MonomialBytes : Array ByteArray} {s : TrustedSetup}
    (h : TrustedSetup.ofBytes g1LagrangeBytes g1MonomialBytes g2MonomialBytes = .ok s)
    (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    ∃ b ∈ g1MonomialBytes, G1.uncompress b = .ok s.g1Monomial[i] := by
  unfold TrustedSetup.ofBytes at h
  dsimp only at h
  cases h₁ : g1LagrangeBytes.mapM fun b =>
      (Bls.G1.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup with
  | error e => rw [h₁] at h; cases h
  | ok lagrange =>
  cases h₂ : g1MonomialBytes.mapM fun b =>
      (Bls.G1.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup with
  | error e => rw [h₁, h₂] at h; cases h
  | ok monomial =>
  cases h₃ : g2MonomialBytes.mapM fun b =>
      (Bls.G2.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup with
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
        obtain ⟨b, hmem, hb⟩ := mem_of_mapM_ok h₂ _ (Array.getElem_mem hi)
        refine ⟨b, hmem, ?_⟩
        cases hu : Bls.G1.uncompress b with
        | error e => rw [hu] at hb; cases hb
        | ok q => rw [hu] at hb; cases hb; rfl
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
