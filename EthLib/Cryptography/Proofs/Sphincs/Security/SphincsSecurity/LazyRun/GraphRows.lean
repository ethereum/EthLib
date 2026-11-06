module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.Graph
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.GraphView.Sampling

/-!
# Graph labels and the hidden-row oracle

This module connects the labels of the graph preparation with the hidden-row oracle.

The secret coordinates come from the secret tables.

All other coordinates and the high bits come from the prepared hash labels.
-/

@[expose] public section

open OracleComp OracleSpec
namespace SphincsSecurity.Security.HiddenGraph

variable [Params]
open Graph
-- The byte lemmas must see the digest width as `8 * 16` to match.
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

def coordinates
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : ForsSecrets)
    (labels : CanonicalGraphLabels) : Table
  | .chain lay tree leaf chainIdx position =>
      if h : position.val = 0 then otsSecret lay tree leaf chainIdx
      else truncateHash (labels (.chain lay tree leaf chainIdx
        ⟨position.val - 1, by
          have := position.isLt; simp only [chainLength, winternitzBits] at *; omega⟩))
  | .fors index κ leaf position =>
      if position.val = 0 then ftsSecret index κ leaf
      else truncateHash (labels (.fleaf index κ leaf))

def highHalves (labels : CanonicalGraphLabels) (address : Address) : Prefix.High :=
  (splitHashOutput digestBits (labels address.position)).2

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : ForsSecrets)
  (labels : CanonicalGraphLabels)

theorem coordinates_outgoing (address : Address) :
    coordinates otsSecret ftsSecret labels address.outputCoordinate =
      truncateHash (labels address.position) := by
  cases address with
  | chain lay tree leaf chainIdx step =>
      fin_cases step <;> rfl
  | fleaf index κ leaf => rfl

/-- The input of an address at its table coordinate is the canonical input of its position. -/
theorem coordinates_input (address : Address) :
    input parameter (address, coordinates otsSecret ftsSecret labels address.inputCoordinate) =
      canonicalGraphInput parameter otsSecret ftsSecret address.position labels := by
  cases address with
  | chain lay tree leaf chainIdx step =>
      fin_cases step <;>
        simp [input, Address.inputCoordinate, Address.position, coordinates, canonicalGraphInput,
          canonicalGraphSlots, Position.domain, Position.children, chainLength, winternitzBits]
  | fleaf index κ leaf =>
      simp [input, Address.inputCoordinate, Address.position, coordinates, canonicalGraphInput,
        canonicalGraphSlots, Position.domain]

attribute [local irreducible] canonicalGraphInput canonicalGraphSlots

/-- Programming the graph keeps an entry that already holds the label of its position. -/
theorem programGraphCache_preserves_label (positions : List Position)
    (cache : QueryCache HashSpec) (position : Position)
    (hcache : cache (canonicalGraphInput parameter otsSecret ftsSecret position labels) =
      some (labels position)) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache
      (canonicalGraphInput parameter otsSecret ftsSecret position labels) =
        some (labels position) := by
  induction positions generalizing cache with
  | nil => exact hcache
  | cons first rest ih =>
      apply ih
      change (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret first labels)
        (labels first)) (canonicalGraphInput parameter otsSecret ftsSecret position labels) = _
      by_cases heq : position = first
      · subst first
        exact QueryCache.cacheQuery_self _ _ _
      · rw [QueryCache.cacheQuery_of_ne]
        · exact hcache
        · exact canonicalGraphInput_separated parameter otsSecret ftsSecret position first heq
            labels labels

/-- The programmed cache answers the canonical input of each listed position with its label. -/
theorem programGraphCache_label (positions : List Position) (cache : QueryCache HashSpec)
    (position : Position) (hposition : position ∈ positions) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache
      (canonicalGraphInput parameter otsSecret ftsSecret position labels) =
        some (labels position) := by
  induction positions generalizing cache with
  | nil => simp at hposition
  | cons first rest ih =>
      rcases List.mem_cons.mp hposition with heq | hrest
      · subst first
        exact programGraphCache_preserves_label parameter otsSecret ftsSecret labels rest
          (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret position labels)
            (labels position)) position (QueryCache.cacheQuery_self _ _ _)
      · exact ih _ hrest

theorem programGraphCache_preserves_other (positions : List Position)
    (cache : QueryCache HashSpec) (bytes : HashInput)
    (hmiss : ∀ position ∈ positions,
      bytes ≠ canonicalGraphInput parameter otsSecret ftsSecret position labels) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache bytes =
      cache bytes := by
  induction positions generalizing cache with
  | nil => rfl
  | cons first rest ih =>
      change Graph.programGraphCache parameter otsSecret ftsSecret rest labels
        (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret first labels)
          (labels first)) bytes = _
      rw [ih _ (fun position hp => hmiss position (List.mem_cons_of_mem _ hp))]
      exact QueryCache.cacheQuery_of_ne _ _ (hmiss first List.mem_cons_self)

/-- A noncanonical payload at an address differs from the canonical input of every position.

The positions include the tree and leaf-compression inputs, which hold several digests. -/
theorem row_miss_all_inputs (address : Address) (value : Digest)
    (hmiss : value ≠ coordinates otsSecret ftsSecret labels address.inputCoordinate)
    (position : Position) :
    input parameter (address, value) ≠
      canonicalGraphInput parameter otsSecret ftsSecret position labels := by
  intro heq
  have hposition : address.position = position := by
    have heq' := heq
    unfold input canonicalGraphInput at heq'
    have hfields := (tweakableInput_injective heq').1
    exact Position.domain_injective
      (hashFields_injective address.position.domain_inRange position.domain_inRange hfields)
  subst position
  rw [← coordinates_input parameter otsSecret ftsSecret labels address] at heq
  exact hmiss (congrArg Prod.snd (input_injective parameter heq))

theorem programGraphCache_row_miss (positions : List Position) (cache : QueryCache HashSpec)
    (address : Address) (value : Digest)
    (hmiss : value ≠ coordinates otsSecret ftsSecret labels address.inputCoordinate) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache
      (input parameter (address, value)) = cache (input parameter (address, value)) :=
  programGraphCache_preserves_other parameter otsSecret ftsSecret labels positions cache _
    (fun position _ =>
      row_miss_all_inputs parameter otsSecret ftsSecret labels address value hmiss position)

/-- The programmed cache answers the canonical payload of a listed address with its label.

It answers every other payload of that address from the original cache. -/
theorem programGraphCache_row_lookup (positions : List Position) (cache : QueryCache HashSpec)
    (address : Address) (hposition : address.position ∈ positions) (value : Digest) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache
      (input parameter (address, value)) =
        if value = coordinates otsSecret ftsSecret labels address.inputCoordinate then
          some (labels address.position) else cache (input parameter (address, value)) := by
  by_cases heq : value = coordinates otsSecret ftsSecret labels address.inputCoordinate
  · rw [ite_eq_left heq, heq, coordinates_input]
    exact programGraphCache_label parameter otsSecret ftsSecret labels positions cache _ hposition
  · rw [ite_eq_right heq]
    exact programGraphCache_row_miss parameter otsSecret ftsSecret labels positions cache address
      value heq

end SphincsSecurity.Security.HiddenGraph
