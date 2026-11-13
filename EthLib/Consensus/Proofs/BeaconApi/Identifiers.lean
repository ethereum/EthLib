module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.Proofs.ForkChoice.Store
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonHex
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonLaws

/-!
# Proofs: the identifiers of the Beacon API

Each identifier reads back from its text, and a text that is no identifier gives code 400.

The head that the API names is the head of the fork choice.

A slot names the block at that slot on the chain of the head.

On a chain that holds the finalized block, every block at or below it counts as finalized.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Serialization.Ssz

/-- Each character of the decimal text of a number is a digit. -/
private theorem isDigit_of_mem_toString {n : Nat} {c : Char} (h : c ∈ (toString n).toList) :
    c.isDigit = true := by
  rw [Nat.toString_eq_repr, Nat.toList_repr] at h
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-- The decimal text of a number is no text that holds a character other than a digit. -/
private theorem toString_ne_of_mem {n : Nat} {text : String} {c : Char}
    (mem : c ∈ text.toList) (notDigit : c.isDigit = false) : toString n ≠ text := by
  intro h
  rw [← h] at mem
  rw [isDigit_of_mem_toString mem] at notDigit
  exact Bool.noConfusion notDigit

/-- A slot written in decimal reads back as that slot. -/
private theorem parseUInt64_print (slot : UInt64) :
    parseUInt64 (toString slot.toNat) = some slot := by
  have lt : slot.toNat < UInt64.size := slot.toNat_lt_size
  unfold parseUInt64
  rw [readNat_str]
  simp [lt]

/-- A slot or an index reads only from its plain decimal text, with no sign or leading zero. -/
theorem parseUInt64_print_of_some {text : String} {n : UInt64}
    (parsed : parseUInt64 text = some n) : toString n.toNat = text := by
  unfold parseUInt64 at parsed
  split at parsed
  · rename_i m read
    simp only [readNat] at read
    split at read
    · rename_i same
      cases read
      split at parsed
      · rename_i lt
        cases parsed
        rw [UInt64.toNat_ofNat_of_lt' lt]
        simpa using same
      · cases parsed
    · cases read
  · cases parsed

/-- The hex text of bytes is no decimal number. -/
private theorem parseUInt64_toHex (data : Bytes) : parseUInt64 (toHex data) = none := by
  have mem : 'x' ∈ (toHex data).toList := by
    unfold toHex; rw [Base.toList_hexString]; simp
  unfold parseUInt64
  split
  · rename_i n h
    simp only [readNat] at h
    split at h
    · rename_i eq
      exact absurd (by simpa using eq) (toString_ne_of_mem mem (by decide))
    · cases h
  · rfl

/-- The hex text of bytes reads back as those bytes when the count fits. -/
private theorem parseHexBytes_toHex {count : Nat} (data : Vector UInt8 count) :
    parseHexBytes count (toHex data.toArray) = some data := by
  simp [parseHexBytes, ofHex_toHex]

/-- The hex text of bytes is none of the words, which start with a letter. -/
private theorem toHex_ne_word (data : Bytes) {word : String} (c : Char)
    (first : word.toList.head? = some c)
    (notZero : c ≠ '0') : toHex data ≠ word := by
  intro h
  have := congrArg (fun t => t.toList.head?) h
  unfold toHex at this
  rw [Base.toList_hexString, first] at this
  simp at this
  exact notZero this.symm

/-- A state identifier reads back from its text. -/
theorem parseStateId_print (id : StateId) : parseStateId (printStateId id) = .ok id := by
  cases id with
  | head | genesis | finalized | justified => simp [parseStateId, printStateId]
  | slot slot =>
    have h1 : toString slot.toNat ≠ "head" := toString_ne_of_mem (c := 'h') (by decide) (by decide)
    have h2 : toString slot.toNat ≠ "genesis" :=
      toString_ne_of_mem (c := 'g') (by decide) (by decide)
    have h3 : toString slot.toNat ≠ "finalized" :=
      toString_ne_of_mem (c := 'f') (by decide) (by decide)
    have h4 : toString slot.toNat ≠ "justified" :=
      toString_ne_of_mem (c := 'j') (by decide) (by decide)
    simp only [printStateId, parseStateId, eq_false h1, eq_false h2, eq_false h3, eq_false h4,
      ↓reduceIte, parseUInt64_print]
  | root root =>
    have h1 : toHex root.toArray ≠ "head" := toHex_ne_word _ 'h' (by decide) (by decide)
    have h2 : toHex root.toArray ≠ "genesis" := toHex_ne_word _ 'g' (by decide) (by decide)
    have h3 : toHex root.toArray ≠ "finalized" := toHex_ne_word _ 'f' (by decide) (by decide)
    have h4 : toHex root.toArray ≠ "justified" := toHex_ne_word _ 'j' (by decide) (by decide)
    simp [printStateId, parseStateId, h1, h2, h3, h4,
      parseUInt64_toHex, parseHexBytes_toHex]

/-- A block identifier reads back from its text. -/
theorem parseBlockId_print (id : BlockId) : parseBlockId (printBlockId id) = .ok id := by
  cases id with
  | head | genesis | finalized => simp [parseBlockId, printBlockId]
  | slot slot =>
    have h1 : toString slot.toNat ≠ "head" := toString_ne_of_mem (c := 'h') (by decide) (by decide)
    have h2 : toString slot.toNat ≠ "genesis" :=
      toString_ne_of_mem (c := 'g') (by decide) (by decide)
    have h3 : toString slot.toNat ≠ "finalized" :=
      toString_ne_of_mem (c := 'f') (by decide) (by decide)
    simp only [printBlockId, parseBlockId, eq_false h1, eq_false h2, eq_false h3, ↓reduceIte,
      parseUInt64_print]
  | root root =>
    have h1 : toHex root.toArray ≠ "head" := toHex_ne_word _ 'h' (by decide) (by decide)
    have h2 : toHex root.toArray ≠ "genesis" := toHex_ne_word _ 'g' (by decide) (by decide)
    have h3 : toHex root.toArray ≠ "finalized" := toHex_ne_word _ 'f' (by decide) (by decide)
    simp [printBlockId, parseBlockId, h1, h2, h3,
      parseUInt64_toHex, parseHexBytes_toHex]

/-- A validator identifier reads back from its text. -/
theorem parseValidatorId_print (id : ValidatorId) :
    parseValidatorId (printValidatorId id) = .ok id := by
  cases id with
  | index index => simp only [printValidatorId, parseValidatorId, parseUInt64_print]
  | pubkey pubkey =>
    simp only [printValidatorId, parseValidatorId, parseUInt64_toHex, parseHexBytes_toHex]

/-- A text that names no state gives an error with code 400. -/
theorem parseStateId_error_code {text : String} {error : ErrorMessage}
    (refused : parseStateId text = .error error) : error.code = 400 := by
  unfold parseStateId at refused
  repeat' split at refused
  all_goals (cases refused; try rfl)

/-- A text that names no block gives an error with code 400. -/
theorem parseBlockId_error_code {text : String} {error : ErrorMessage}
    (refused : parseBlockId text = .error error) : error.code = 400 := by
  unfold parseBlockId at refused
  repeat' split at refused
  all_goals (cases refused; try rfl)

/-- A text that names no validator gives an error with code 400. -/
theorem parseValidatorId_error_code {text : String} {error : ErrorMessage}
    (refused : parseValidatorId text = .error error) : error.code = 400 := by
  unfold parseValidatorId at refused
  repeat' split at refused
  all_goals (cases refused; try rfl)

variable {preset : Preset} {fork : Base.Fork}

/-- The head that the API names is the root of the head of the fork choice. -/
theorem resolveBlockId_head (config : Config) (store : Store preset fork) :
    resolveBlockId config store .head = (store.getHead config).toOption.map (·.root) := rfl

/-- A slot names a known block at that slot, the ancestor of the head at the slot. -/
theorem resolveBlockId_slot {config : Config} {store : Store preset fork} {slot : Slot}
    {root : Root} (resolved : resolveBlockId config store (.slot slot) = some root) :
    ∃ head node block, store.getHead config = .ok head ∧
      store.getAncestor ⟨head.root, .pending⟩ slot = .ok node ∧ node.root = root ∧
      store.blocks[root]? = some block ∧ block.slot = slot := by
  simp only [resolveBlockId, headRoot, blockAtSlot] at resolved
  cases hh : store.getHead config with
  | error e => simp [hh, Except.toOption] at resolved
  | ok head =>
    cases ha : store.getAncestor ⟨head.root, .pending⟩ slot with
    | error e => simp [hh, ha, Except.toOption] at resolved
    | ok node =>
      cases hb : store.blocks[node.root]? with
      | none => simp [hh, ha, hb, Except.toOption] at resolved
      | some block =>
        by_cases hs : block.slot = slot
        · simp [hh, ha, hb, hs, Except.toOption] at resolved
          exact ⟨head, node, block, rfl, ha, resolved, resolved ▸ hb, hs⟩
        · simp [hh, ha, hb, hs, Except.toOption] at resolved

/-- A block on the chain of a head, at or below the finalized block on that chain, is finalized.

The finalized block must be the ancestor of the head at some slot at or above the block. -/
theorem isFinalizedRoot_of_slot_le {store : Store preset fork} {head root : Root}
    {final ancestor : ForkChoiceNode} {block : BeaconBlock preset fork} {finalSlot : Slot}
    (finalOnChain : store.getAncestor ⟨head, .pending⟩ finalSlot = .ok final)
    (finalRoot : final.root = store.finalizedCheckpoint.root)
    (found : store.blocks[root]? = some block) (le : block.slot ≤ finalSlot)
    (onChain : store.getAncestor ⟨head, .pending⟩ block.slot = .ok ancestor)
    (ancestorRoot : ancestor.root = root) :
    isFinalizedRoot store root = true := by
  have trans := Store.getAncestor_trans le finalOnChain
  rw [onChain] at trans
  have rootEq := Store.getAncestor_root (store := store) final .pending block.slot
  rw [← trans] at rootEq
  rw [finalRoot] at rootEq
  unfold isFinalizedRoot
  rw [found]
  cases h : store.getAncestor ⟨store.finalizedCheckpoint.root, .pending⟩ block.slot with
  | error e =>
    rw [h] at rootEq
    simp [Functor.map, Except.map] at rootEq
  | ok node =>
    rw [h] at rootEq
    have same : ancestor.root = node.root := by simpa [Functor.map, Except.map] using rootEq
    simp [h, ← same, ancestorRoot]

end EthLib.Consensus.BeaconApi
