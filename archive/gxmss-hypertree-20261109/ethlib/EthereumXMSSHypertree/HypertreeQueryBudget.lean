/-
Copyright (c) 2026 Matthias Meijers.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.HypertreeGameTransport
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Query budgets of the actual named source-adversary lift

The signing adapter issues one query at the unchanged oracle index and maps
only its response. Source query bounds transfer without overhead, for any
predicate on the shared ambient/signing query domain.
-/

public section

namespace EthereumXMSSHypertree.HypertreeQueryBudget

open EthLib.Cryptography.Xmss ConcreteHypertree HypertreeGameTransport
open OracleComp OracleSpec SyncSignatureUnforgeability

/-- Ambient draws and signing requests share this unchanged domain in both games. -/
abbrev QueryDomain := Nat ⊕ (Epoch × Message)

/-- The source-signature adversary's oracle specification. -/
abbrev SourceSpec := unifSpec + signingSpec Epoch Message Signature

/-- The actual named lifted adversary's oracle specification. -/
abbrev GenericSpec := unifSpec + signingSpec Epoch Message GenericSignature

/-- Every adapter request makes exactly one query at its original index, with no hidden request. -/
theorem signingAdapter_query_bound_iff (query : QueryDomain) (predicate : QueryDomain → Prop)
    [DecidablePred predicate] (budget : Nat) :
    IsQueryBoundP (signingAdapter query) predicate budget ↔
      (predicate query → 0 < budget) := by
  cases query with
  | inl query =>
    exact isQueryBoundP_query_iff predicate (Sum.inl query) budget
  | inr request =>
    rcases request with ⟨ep, msg⟩
    rw [signingAdapter, isQueryBoundP_map_iff]
    exact isQueryBoundP_query_iff predicate (Sum.inr (ep, msg)) budget

/-- One source request costs one unit exactly when its unchanged query index is charged. -/
theorem signingAdapter_query_bound (query : QueryDomain) (predicate : QueryDomain → Prop)
    [DecidablePred predicate] :
    IsQueryBoundP (signingAdapter query) predicate (if predicate query then 1 else 0) := by
  rw [signingAdapter_query_bound_iff]
  intro h
  simp [h]

/-- Every adaptive source query bound transfers through the actual adapter without overhead. -/
theorem simulate_signingAdapter_query_bound {A : Type} (program : OracleComp SourceSpec A)
    (predicate : QueryDomain → Prop) [DecidablePred predicate] (budget : Nat)
    (h : IsQueryBoundP program predicate budget) :
    IsQueryBoundP (simulateQ signingAdapter program) predicate budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure result => simp
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    cases query with
    | inl query =>
      rw [signingAdapter, isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun response => ih response _ (h.2 response)⟩
    | inr request =>
      rcases request with ⟨ep, msg⟩
      rw [signingAdapter, bind_map_left, isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun response => ih (response.map (signatureToSource ep)) _
        (h.2 (response.map (signatureToSource ep)))⟩

/-- Public-key conversion and final forgery stripping add no queries to the named adversary. -/
theorem liftedAdversary_query_bound
    (adv : Adversary unifSpec PublicKey Epoch Message Signature)
    (predicate : QueryDomain → Prop) [DecidablePred predicate] (budget : Nat)
    (h : ∀ pk, IsQueryBoundP (adv.forge pk) predicate budget) (pk : GenericPublicKey) :
    IsQueryBoundP ((liftedAdversary adv).forge pk) predicate budget := by
  rw [liftedAdversary, isQueryBoundP_map_iff]
  exact simulate_signingAdapter_query_bound _ predicate budget (h (publicKeyToSource pk))

/-- Charge exactly signing-oracle requests, including duplicate epochs and failed responses. -/
@[expose] def SigningRequest : QueryDomain → Prop
  | .inl _ => False
  | .inr _ => True

/-- Signing-request membership is decidable from its query-domain tag. -/
instance : DecidablePred SigningRequest
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Charge exactly ambient uniform-oracle requests. -/
@[expose] def AmbientRequest : QueryDomain → Prop
  | .inl _ => True
  | .inr _ => False

/-- Ambient-request membership is decidable from its query-domain tag. -/
instance : DecidablePred AmbientRequest
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- The named lift preserves a bound on all source signing requests without overhead. -/
theorem liftedAdversary_signing_requests
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) (budget : Nat)
    (h : ∀ pk, IsQueryBoundP (adv.forge pk) SigningRequest budget) (pk : GenericPublicKey) :
    IsQueryBoundP ((liftedAdversary adv).forge pk) SigningRequest budget :=
  liftedAdversary_query_bound adv SigningRequest budget h pk

/-- The named lift preserves a bound on all ambient uniform requests without overhead. -/
theorem liftedAdversary_ambient_requests
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) (budget : Nat)
    (h : ∀ pk, IsQueryBoundP (adv.forge pk) AmbientRequest budget) (pk : GenericPublicKey) :
    IsQueryBoundP ((liftedAdversary adv).forge pk) AmbientRequest budget :=
  liftedAdversary_query_bound adv AmbientRequest budget h pk

/-- Charging every oracle index gives the named lift the same combined request budget. -/
theorem liftedAdversary_all_requests
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) (budget : Nat)
    (h : ∀ pk, IsQueryBoundP (adv.forge pk) (fun _ => True) budget) (pk : GenericPublicKey) :
    IsQueryBoundP ((liftedAdversary adv).forge pk) (fun _ => True) budget :=
  liftedAdversary_query_bound adv (fun _ => True) budget h pk

end EthereumXMSSHypertree.HypertreeQueryBudget
