module

public import EthLib.Networking.Libp2p.Upgrade
public import EthLib.Networking.Proofs.Libp2p.Multistream

/-!
# Proofs: the upgrade of a TCP connection

Two consensus nodes on TCP always agree on Noise, then on a multiplexer.

The multiplexer is yamux when both support it, and mplex otherwise.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.Upgrade

open EthLib.Networking.Libp2p
open EthLib.Networking.Libp2p.Upgrade

/-- The upgrade between any two profiles gives Noise, then yamux if both support it, else mplex. -/
theorem upgrade_eq (dialer listener : TcpProfile) :
    upgrade dialer listener = some (noiseId,
      if dialer.supportsYamux && listener.supportsYamux then Yamux.protocolId
      else Mplex.protocolId) := by
  have h1 : noiseId ≠ Multistream.notAvailable := fun h => by
    unfold noiseId Multistream.notAvailable at h
    simp only [String.toUTF8_eq_toByteArray, String.toByteArray_inj] at h
    exact absurd h (by decide)
  have h2 : Yamux.protocolId ≠ Multistream.notAvailable := fun h => by
    unfold Yamux.protocolId Multistream.notAvailable at h
    simp only [String.toUTF8_eq_toByteArray, String.toByteArray_inj] at h
    exact absurd h (by decide)
  have h3 : Mplex.protocolId ≠ Multistream.notAvailable := fun h => by
    unfold Mplex.protocolId Multistream.notAvailable at h
    simp only [String.toUTF8_eq_toByteArray, String.toByteArray_inj] at h
    exact absurd h (by decide)
  have h4 : Yamux.protocolId ≠ Mplex.protocolId := fun h => by
    unfold Yamux.protocolId Mplex.protocolId at h
    simp only [String.toUTF8_eq_toByteArray, String.toByteArray_inj] at h
    exact absurd h (by decide)
  have hsec : Multistream.negotiate securityProposals securityProposals = some noiseId := by
    rw [Proofs.Libp2p.Multistream.negotiate_eq_find (by simp [securityProposals, h1.symm])]
    have : Multistream.supports securityProposals noiseId = true :=
      Proofs.Libp2p.Multistream.supports_iff.2 (by simp [securityProposals])
    simp only [securityProposals] at this ⊢
    simp [this]
  have hmux : ∀ p ∈ dialer.muxers, p ≠ Multistream.notAvailable := by
    intro p hp
    simp only [TcpProfile.muxers] at hp
    split at hp <;> simp at hp <;> rcases hp with rfl | rfl <;> assumption
  have hna : Multistream.notAvailable ∉ dialer.muxers := fun h => hmux _ h rfl
  have h5 : Yamux.protocolId.data ≠ Mplex.protocolId.data := fun e => h4 (ByteArray.ext e)
  obtain ⟨dy⟩ := dialer
  obtain ⟨ly⟩ := listener
  simp only [upgrade, hsec, Proofs.Libp2p.Multistream.negotiate_eq_find hna]
  cases dy <;> cases ly <;> simp [TcpProfile.muxers, Multistream.supports, h5]

end EthLib.Networking.Proofs.Libp2p.Upgrade
