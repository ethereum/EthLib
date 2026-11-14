module

public import EthLib.Consensus.BeaconApi.Spelling
public import EthLib.Consensus.Proofs.BeaconApi.Encoding
public import EthLib.Consensus.Proofs.Containers.BuilderApi
public import EthLib.Serialization.Proofs.Ssz.Typed.Text

/-!
# Proofs: a builder configuration reads back from its JSON

A builder entry and a builder configuration decode back from their untyped values.

The JSON writer never fails on them, and the reader gives back what it wrote.

Their URL is text, so SSZ bytes that are not UTF-8 fit their declaration and are refused.

So the two types are not lawful, and these theorems stand in for the general ones.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Cryptography.Bls Serialization.Ssz SszType

/-- A head that reads back, before fields that read back, reads back with them. -/
private theorem ofValues_pair {α β : Type} [SszType α] [SszFields β] (a : α) (b : β)
    (head : ofValue (toValue a) = .ok a)
    (tail : SszFields.ofValues (SszFields.toValues b) = .ok b) :
    SszFields.ofValues (SszFields.toValues (a, b)) = .ok (a, b) := by
  simp [SszFields.toValues, SszFields.ofValues, head, tail, bind, Except.bind, pure, Except.pure]

/-- The SSZ type of a builder entry is well formed. -/
theorem BuilderEntry.wellFormed : (desc BuilderEntry).wellFormed = .ok () := by
  have names : firstDuplicate ["url", "auth", "builder_pubkeys", "max_execution_payment",
      "min_bid", "builder_boost_factor"] = none := by decide
  have tail := LawfulSszFields.allWellFormed
    (β := SignedBuilderRequestAuth × SszList BLSPubkey MAX_BUILDER_PUBKEYS × Gwei × Gwei × UInt64)
  simp [desc, SszFields.descs, Desc.wellFormed, MAX_BUILDER_URL_SIZE, names,
    Desc.allWellFormed, bind, Except.bind] at tail ⊢
  exact tail

/-- A builder entry stands for a value that its SSZ type admits. -/
theorem BuilderEntry.fits (entry : BuilderEntry) : Fits (desc BuilderEntry) (toValue entry) := by
  obtain ⟨count, each⟩ := LawfulSszFields.fits (β := SignedBuilderRequestAuth ×
    SszList BLSPubkey MAX_BUILDER_PUBKEYS × Gwei × Gwei × UInt64)
    (entry.auth, entry.builderPubkeys, entry.maxExecutionPayment, entry.minBid,
      entry.builderBoostFactor)
  refine .container (by simp [desc, toValue, SszFields.descs, SszFields.toValues]) ?_
  intro pair mem
  change pair ∈ (_ :: _).zip (_ :: _) at mem
  rcases List.mem_cons.mp mem with rfl | mem
  · exact SszString.fits entry.url
  · exact each pair mem

/-- Decoding the untyped value of a builder entry gives back the entry. -/
theorem BuilderEntry.ofValue_toValue (entry : BuilderEntry) :
    ofValue (toValue entry) = .ok entry := by
  have rest := LawfulSszFields.ofValues_toValues (β := SignedBuilderRequestAuth ×
    SszList BLSPubkey MAX_BUILDER_PUBKEYS × Gwei × Gwei × UInt64)
    (entry.auth, entry.builderPubkeys, entry.maxExecutionPayment, entry.minBid,
      entry.builderBoostFactor)
  have whole : SszFields.ofValues (SszFields.toValues (β := SszString MAX_BUILDER_URL_SIZE ×
      SignedBuilderRequestAuth × SszList BLSPubkey MAX_BUILDER_PUBKEYS × Gwei × Gwei × UInt64)
      (entry.url, entry.auth, entry.builderPubkeys, entry.maxExecutionPayment, entry.minBid,
        entry.builderBoostFactor)) = .ok (entry.url, entry.auth, entry.builderPubkeys,
        entry.maxExecutionPayment, entry.minBid, entry.builderBoostFactor) := by
    exact ofValues_pair _ _ (SszString.ofValue_toValue _) rest
  change (fun (url, auth, builderPubkeys, maxExecutionPayment, minBid, builderBoostFactor) =>
    (⟨url, auth, builderPubkeys, maxExecutionPayment, minBid, builderBoostFactor⟩ :
      BuilderEntry)) <$> SszFields.ofValues (SszFields.toValues (entry.url, entry.auth,
        entry.builderPubkeys, entry.maxExecutionPayment, entry.minBid,
        entry.builderBoostFactor)) = _
  rw [whole]
  rfl

/-- The SSZ type of a builder configuration is well formed. -/
theorem BuilderConfig.wellFormed : (desc BuilderConfig).wellFormed = .ok () := by
  have names : firstDuplicate ["min_bid", "builder_boost_factor", "builders"] = none := by
    decide
  have entry := BuilderEntry.wellFormed
  show (Desc.container ["min_bid", "builder_boost_factor", "builders"]
    [desc Gwei, desc UInt64, .list (desc BuilderEntry) MAX_BUILDER_ENTRIES]).wellFormed = _
  have word : Desc.uint64.wellFormed = .ok () := rfl
  generalize desc BuilderEntry = element at entry ⊢
  simp [desc, Desc.wellFormed, names, Desc.allWellFormed, MAX_BUILDER_ENTRIES, entry, word, bind,
    Except.bind]

/-- A builder configuration stands for a value that its SSZ type admits. -/
theorem BuilderConfig.fits (config : BuilderConfig) :
    Fits (desc BuilderConfig) (toValue config) := by
  refine .container (by simp [desc, toValue, SszFields.descs, SszFields.toValues]) ?_
  intro pair mem
  simp only [desc, toValue, SszFields.descs, SszFields.toValues, List.zip_cons_cons,
    List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact .uint (by simpa [UInt64.size] using UInt64.toNat_lt_size config.minBid)
  · exact .uint (by simpa [UInt64.size] using UInt64.toNat_lt_size config.builderBoostFactor)
  · refine .list (by simpa using config.builders.bound) ?_
    intro value mem
    obtain ⟨entry, -, rfl⟩ := List.mem_map.mp mem
    exact BuilderEntry.fits entry

/-- Decoding the untyped value of a builder configuration gives back the configuration. -/
theorem BuilderConfig.ofValue_toValue (config : BuilderConfig) :
    ofValue (toValue config) = .ok config := by
  have items := ofElements_map_of BuilderEntry.ofValue_toValue config.builders.data.toList
  have list : ofValue (toValue config.builders) = .ok config.builders := by
    change (do
      let items ← ofElements (config.builders.data.toList.map toValue)
      if within : items.size ≤ MAX_BUILDER_ENTRIES then
        return (⟨items, within⟩ : SszList BuilderEntry MAX_BUILDER_ENTRIES)
      else throw (Err.overLimit MAX_BUILDER_ENTRIES items.size) : Except Err _) = _
    rw [items]
    simp [bind, Except.bind, config.builders.bound]
    rfl
  have tail := ofValues_pair (α := UInt64) config.builderBoostFactor config.builders
    (LawfulSszType.ofValue_toValue _) (by simpa [SszFields.toValues, SszFields.ofValues] using list)
  have whole := ofValues_pair (α := Gwei) config.minBid (config.builderBoostFactor, config.builders)
    (LawfulSszType.ofValue_toValue _) tail
  change (fun (minBid, builderBoostFactor, builders) =>
    (⟨minBid, builderBoostFactor, builders⟩ : BuilderConfig)) <$>
      SszFields.ofValues (SszFields.toValues (config.minBid, config.builderBoostFactor,
        config.builders)) = _
  rw [whole]
  rfl

/-- The JSON writer never fails on a builder entry. -/
theorem BuilderEntry.toApiJson_total (entry : BuilderEntry) :
    ∃ document, toApiJson entry = .ok document :=
  jsonOf_ok BuilderEntry.wellFormed (BuilderEntry.fits entry) _

/-- The reader gives back every builder entry that the writer writes. -/
theorem BuilderEntry.ofApiJson_toApiJson {entry : BuilderEntry} {document : Json}
    (wrote : toApiJson entry = .ok document) : ofApiJson BuilderEntry document = .ok entry := by
  have back := valueOf_jsonOf _ BuilderEntry.wellFormed _ _ document (BuilderEntry.fits entry)
    wrote
  simp only [ofApiJson, back]
  exact BuilderEntry.ofValue_toValue entry

/-- The JSON writer never fails on a builder configuration. -/
theorem BuilderConfig.toApiJson_total (config : BuilderConfig) :
    ∃ document, toApiJson config = .ok document :=
  jsonOf_ok BuilderConfig.wellFormed (BuilderConfig.fits config) _

/-- The reader gives back every builder configuration that the writer writes. -/
theorem BuilderConfig.ofApiJson_toApiJson {config : BuilderConfig} {document : Json}
    (wrote : toApiJson config = .ok document) :
    ofApiJson BuilderConfig document = .ok config := by
  have back := valueOf_jsonOf _ BuilderConfig.wellFormed _ _ document
    (BuilderConfig.fits config) wrote
  simp only [ofApiJson, back]
  exact BuilderConfig.ofValue_toValue config

end EthLib.Consensus.BeaconApi
