module

public import EthLib.Execution.Exports.Trie
import all EthLib.Execution.Exports.Trie

/-!
# Proofs: `Execution.Exports.Trie`

The root export returns the root of the trie that sets the decoded pairs in order.

So the binding and soundness theorems for such tries apply to its output.

The library of the exports holds this module, since a proof module fails to load compiled exports.
-/

@[expose] public section

namespace EthLib.Execution.Trie.Exports

open EthLib.Base
open EthLib.Serialization.Rlp (Item)

/-- With the pairs decoded, the export is the match on the root of their trie. -/
private theorem rootExport_eq {secured : UInt8} {input : ByteArray} {items : List Item}
    {pairs : List (ByteArray × ByteArray)}
    (hitems : readList input "pairs" = .ok items) (hpairs : items.mapM ofPairItem = .ok pairs) :
    rootExport secured input =
      match root Cryptography.Hash.Keccak.keccak256
          (pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured != 0, []⟩) with
      | .ok hash => return ⟨hash.toArray⟩
      | .error e => throw (e.code, s!"trie has no root: {repr e}") := by
  simp only [rootExport, hitems, hpairs, bind, Except.bind]
  rfl

/-- A root that the export returns has 32 bytes. -/
theorem size_of_rootExport {secured : UInt8} {input out : ByteArray}
    (h : rootExport secured input = .ok out) : out.size = 32 := by
  unfold rootExport at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
        exact Vector.size_toArray _
      · cases h
    · cases h

/-- The root export returns the root of the trie that sets the decoded pairs in order.

The trie starts empty, and it hashes its keys when the flag is not 0. -/
theorem root_of_rootExport {secured : UInt8} {input out : ByteArray} {items : List Item}
    {pairs : List (ByteArray × ByteArray)}
    (hitems : readList input "pairs" = .ok items) (hpairs : items.mapM ofPairItem = .ok pairs)
    (h : rootExport secured input = .ok out) :
    root Cryptography.Hash.Keccak.keccak256
        (pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured != 0, []⟩) =
      .ok ⟨out.data, size_of_rootExport h⟩ := by
  rw [rootExport_eq hitems hpairs] at h
  split at h
  · rename_i hash hr
    cases h
    rw [hr]
  · cases h

/-- When that trie has a root, the root export returns it. -/
theorem rootExport_of_root {secured : UInt8} {input : ByteArray} {items : List Item}
    {pairs : List (ByteArray × ByteArray)} {hash : Hash32}
    (hitems : readList input "pairs" = .ok items) (hpairs : items.mapM ofPairItem = .ok pairs)
    (hroot : root Cryptography.Hash.Keccak.keccak256
        (pairs.foldl (fun trie (key, value) => trieSet trie key value) ⟨secured != 0, []⟩) =
      .ok hash) :
    rootExport secured input = .ok ⟨hash.toArray⟩ := by
  rw [rootExport_eq hitems hpairs, hroot]
  rfl

end EthLib.Execution.Trie.Exports
