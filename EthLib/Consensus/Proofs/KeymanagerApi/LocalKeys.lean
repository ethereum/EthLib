module

public import EthLib.Consensus.KeymanagerApi.LocalKeys
public import EthLib.Consensus.Proofs.SlashingProtection

/-!
# Proofs: importing keystores through the Keymanager API

A call that succeeds gives one status for each keystore.

A key with the status imported is held afterwards, and no key held before is removed.

The record refuses afterwards every message that it refused before.

A key imported with slashing protection data refuses every message that its entries refuse.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography Cryptography.Bls

variable {text : JsonText} {limits : Keystore.KdfLimits} {file : Option Interchange}

/-! ## One keystore after another -/

/-- One status for each keystore. -/
theorem length_importAll (state : KeyState) (pairs : List (String × String)) :
    (importAll text limits file state pairs).1.length = pairs.length := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨keystore, password⟩ := pair
    simp [importAll, ih]

/-- The keys held before one keystore are held after it, in the same order, first. -/
theorem localKeys_prefix_importKeystore (state : KeyState) (keystore password : String) :
    state.localKeys <+: (importKeystore text limits file state keystore password).2.localKeys := by
  unfold importKeystore
  split
  · exact List.prefix_refl _
  · split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _

/-- The keys held before the keystores are held after them, in the same order, first. -/
theorem localKeys_prefix_importAll (state : KeyState) (pairs : List (String × String)) :
    state.localKeys <+: (importAll text limits file state pairs).2.localKeys := by
  induction pairs generalizing state with
  | nil => exact List.prefix_refl _
  | cons pair rest ih =>
    obtain ⟨keystore, password⟩ := pair
    exact (localKeys_prefix_importKeystore state keystore password).trans (ih _)

/-- An import of keystores leaves the remote keys as they were. -/
theorem remoteKeys_importAll (state : KeyState) (pairs : List (String × String)) :
    (importAll text limits file state pairs).2.remoteKeys = state.remoteKeys := by
  induction pairs generalizing state with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨keystore, password⟩ := head
    simp only [importAll]
    rw [ih]
    unfold importKeystore
    split
    · rfl
    · split <;> rfl

/-- The status of one keystore is imported exactly when it decrypts to a key not active. -/
theorem importKeystore_eq_imported_iff {state : KeyState} {keystore password : String} :
    (importKeystore text limits file state keystore password).1 = .imported ↔
      ∃ key, decodeKeystore text limits keystore password = .ok key ∧
        state.isActive key.pubkey = false := by
  unfold importKeystore
  split
  · simp_all
  · rename_i key decoded
    split <;> simp_all

/-- The status of one keystore is a duplicate exactly when it decrypts to a key already active. -/
theorem importKeystore_eq_duplicate_iff {state : KeyState} {keystore password : String} :
    (importKeystore text limits file state keystore password).1 = .duplicate ↔
      ∃ key, decodeKeystore text limits keystore password = .ok key ∧
        state.isActive key.pubkey = true := by
  unfold importKeystore
  split
  · simp_all
  · rename_i key decoded
    split <;> simp_all

/-- A key is active after one keystore exactly when it was before, or that keystore imported it. -/
theorem isActive_importKeystore {state : KeyState} {keystore password : String}
    {pubkey : BLSPubkey} :
    (importKeystore text limits file state keystore password).2.isActive pubkey = true ↔
      state.isActive pubkey = true ∨
        ((importKeystore text limits file state keystore password).1 = .imported ∧
          ∃ key, decodeKeystore text limits keystore password = .ok key ∧ key.pubkey = pubkey) := by
  unfold importKeystore
  split
  · simp_all
  · rename_i key decoded
    split
    · simp_all
    · simp [KeyState.isActive, List.any_append, decoded]

/-- A key is active after the keystores exactly when it was before, or one of them imported it. -/
theorem isActive_importAll (state : KeyState) (pairs : List (String × String))
    (pubkey : BLSPubkey) :
    (importAll text limits file state pairs).2.isActive pubkey = true ↔
      state.isActive pubkey = true ∨
        ∃ (i : Nat) (pair : String × String) (key : LocalKey), pairs[i]? = some pair ∧
          (importAll text limits file state pairs).1[i]? = some ImportStatus.imported ∧
          decodeKeystore text limits pair.1 pair.2 = .ok key ∧ key.pubkey = pubkey := by
  induction pairs generalizing state with
  | nil => simp [importAll]
  | cons pair rest ih =>
    obtain ⟨keystore, password⟩ := pair
    simp only [importAll]
    rw [ih, isActive_importKeystore]
    constructor
    · rintro ((held | ⟨imported, key, decoded, rfl⟩) | ⟨i, pair, key, found, status, decoded, rfl⟩)
      · exact .inl held
      · exact .inr ⟨0, (keystore, password), key, rfl, by simp [imported], decoded, rfl⟩
      · exact .inr ⟨i + 1, pair, key, by simpa using found, by simpa using status, decoded, rfl⟩
    · rintro (held | ⟨i, pair, key, found, status, decoded, rfl⟩)
      · exact .inl (.inl held)
      · cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found status
          subst found
          exact .inl (.inr ⟨status, key, decoded, rfl⟩)
        | succ i =>
          exact .inr ⟨i, pair, key, by simpa using found, by simpa using status, decoded, rfl⟩

/-- A keystore is a duplicate exactly when its key was active before the keystores.

The other case is that a keystore before it imported that key. -/
theorem duplicate_iff_importAll (state : KeyState) (pairs : List (String × String)) (i : Nat)
    (pair : String × String) (found : pairs[i]? = some pair) :
    (importAll text limits file state pairs).1[i]? = some .duplicate ↔
      ∃ key, decodeKeystore text limits pair.1 pair.2 = .ok key ∧
        (state.isActive key.pubkey = true ∨
          ∃ j < i, ∃ earlier other, pairs[j]? = some earlier ∧
            (importAll text limits file state pairs).1[j]? = some .imported ∧
            decodeKeystore text limits earlier.1 earlier.2 = .ok other ∧
            other.pubkey = key.pubkey) := by
  induction pairs generalizing state i with
  | nil => simp at found
  | cons first rest ih =>
    obtain ⟨keystore, password⟩ := first
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp only [importAll, List.getElem?_cons_zero, Option.some.injEq,
        importKeystore_eq_duplicate_iff, Nat.not_lt_zero, false_and, exists_false, or_false]
    | succ i =>
      simp only [List.getElem?_cons_succ] at found
      simp only [importAll, List.getElem?_cons_succ]
      rw [ih _ i found]
      constructor
      · rintro ⟨key, decoded, active | ⟨j, lt, earlier, other, at_j, status, decodedOther, same⟩⟩
        · refine ⟨key, decoded, ?_⟩
          rcases isActive_importKeystore.mp active with held | ⟨imported, other, decodedOther, same⟩
          · exact .inl held
          · exact .inr ⟨0, Nat.zero_lt_succ _, (keystore, password), other, rfl,
              by simp [imported], decodedOther, same⟩
        · exact ⟨key, decoded, .inr ⟨j + 1, Nat.succ_lt_succ lt, earlier, other,
            by simpa using at_j,
            by simpa using status, decodedOther, same⟩⟩
      · rintro ⟨key, decoded, active | ⟨j, lt, earlier, other, at_j, status, decodedOther, same⟩⟩
        · refine ⟨key, decoded, .inl (isActive_importKeystore.mpr (.inl active))⟩
        · cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at at_j status
            subst at_j
            exact ⟨key, decoded, .inl (isActive_importKeystore.mpr
              (.inr ⟨status, other, decodedOther, same⟩))⟩
          | succ j =>
            exact ⟨key, decoded, .inr ⟨j, Nat.lt_of_succ_lt_succ lt, earlier, other,
              by simpa using at_j, by simpa using status, decodedOther, same⟩⟩

/-- A keystore of the request with the status imported holds a key that is active afterwards. -/
theorem exists_mem_localKeys_importAll (state : KeyState) (pairs : List (String × String)) (i : Nat)
    (pair : String × String) (found : pairs[i]? = some pair)
    (imported : (importAll text limits file state pairs).1[i]? = some .imported) :
    ∃ key, decodeKeystore text limits pair.1 pair.2 = .ok key ∧
      key ∈ (importAll text limits file state pairs).2.localKeys := by
  induction pairs generalizing state i with
  | nil => simp at found
  | cons first rest ih =>
    obtain ⟨keystore, password⟩ := first
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp only [importAll, List.getElem?_cons_zero, Option.some.injEq] at imported
      obtain ⟨key, decoded, inactive⟩ := importKeystore_eq_imported_iff.mp imported
      refine ⟨key, decoded, (localKeys_prefix_importAll _ rest).subset ?_⟩
      simp [decoded, inactive]
    | succ i =>
      simp only [List.getElem?_cons_succ] at found
      simp only [importAll, List.getElem?_cons_succ] at imported ⊢
      exact ih _ i found imported

/-! ## The record -/

/-- The record after a key is imported accepts a block only if the record before accepts it. -/
theorem checkBlock_of_loadProtection {held : Interchange} {owner pubkey : BLSPubkey} {slot : Slot}
    {root : Root} (passed : (loadProtection file owner held).checkBlock pubkey slot root = .ok ()) :
    held.checkBlock pubkey slot root = .ok () := by
  cases file with
  | none => exact passed
  | some data =>
    simp only [loadProtection] at passed
    split at passed
    · exact passed
    · exact EthLib.Consensus.checkBlock_of_importFile passed

/-- The record after a key is imported accepts a vote only if the record before accepts it. -/
theorem checkAttestation_of_loadProtection {held : Interchange} {owner pubkey : BLSPubkey}
    {source target : Epoch} {root : Root}
    (passed : (loadProtection file owner held).checkAttestation pubkey source target root =
      .ok ()) :
    held.checkAttestation pubkey source target root = .ok () := by
  cases file with
  | none => exact passed
  | some data =>
    simp only [loadProtection] at passed
    split at passed
    · exact passed
    · exact EthLib.Consensus.checkAttestation_of_importFile passed

/-- The record after one keystore is the record before it, or that record after a key's import. -/
theorem protection_importKeystore (state : KeyState) (keystore password : String) :
    (importKeystore text limits file state keystore password).2.protection = state.protection ∨
      ∃ key, (importKeystore text limits file state keystore password).1 = .imported ∧
        decodeKeystore text limits keystore password = .ok key ∧
        (importKeystore text limits file state keystore password).2.protection =
          loadProtection file key.pubkey state.protection := by
  unfold importKeystore
  split
  · exact .inl rfl
  · rename_i key decoded
    split
    · exact .inl rfl
    · exact .inr ⟨key, rfl, decoded, rfl⟩

/-- The record after a keystore with the status imported is the record after its key's import. -/
theorem protection_importKeystore_of_imported {state : KeyState} {keystore password : String}
    {key : LocalKey}
    (imported : (importKeystore text limits file state keystore password).1 = .imported)
    (decoded : decodeKeystore text limits keystore password = .ok key) :
    (importKeystore text limits file state keystore password).2.protection =
      loadProtection file key.pubkey state.protection := by
  simp only [importKeystore, decoded] at imported ⊢
  split at imported <;> simp_all

/-- A property of records that each import of a key keeps backwards holds before the keystores.

It holds there whenever it holds after them. -/
theorem accepts_of_importAll {accepts : Interchange → Prop}
    (back : ∀ owner held, accepts (loadProtection file owner held) → accepts held)
    {state : KeyState} {pairs : List (String × String)}
    (passed : accepts (importAll text limits file state pairs).2.protection) :
    accepts state.protection := by
  induction pairs generalizing state with
  | nil => exact passed
  | cons first rest ih =>
    obtain ⟨keystore, password⟩ := first
    have earlier := ih (state := (importKeystore text limits file state keystore password).2) passed
    rcases protection_importKeystore (text := text) (limits := limits) (file := file) state
      keystore password with same | ⟨key, -, -, loaded⟩
    · rwa [same] at earlier
    · rw [loaded] at earlier
      exact back _ _ earlier

/-- After the keystores, the record accepts a block only if the record before accepts it. -/
theorem checkBlock_of_importAll {state : KeyState} {pairs : List (String × String)}
    {pubkey : BLSPubkey} {slot : Slot} {root : Root}
    (passed : (importAll text limits file state pairs).2.protection.checkBlock pubkey slot root =
      .ok ()) :
    state.protection.checkBlock pubkey slot root = .ok () :=
  accepts_of_importAll (accepts := fun record => record.checkBlock pubkey slot root = .ok ())
    (fun _ _ accepted => checkBlock_of_loadProtection accepted) passed

/-- After the keystores, the record accepts a vote only if the record before accepts it. -/
theorem checkAttestation_of_importAll {state : KeyState} {pairs : List (String × String)}
    {pubkey : BLSPubkey} {source target : Epoch} {root : Root}
    (passed : (importAll text limits file state pairs).2.protection.checkAttestation pubkey source
      target root = .ok ()) :
    state.protection.checkAttestation pubkey source target root = .ok () :=
  accepts_of_importAll
    (accepts := fun record => record.checkAttestation pubkey source target root = .ok ())
    (fun _ _ accepted => checkAttestation_of_loadProtection accepted) passed

/-- A property that each import of a key keeps backwards holds after each imported key's import.

It must hold after the keystores. -/
theorem exists_loadProtection_of_importAll {accepts : Interchange → Prop} {data : Interchange}
    (back : ∀ owner held, accepts (loadProtection (some data) owner held) → accepts held)
    {state : KeyState} {pairs : List (String × String)} {i : Nat} {pair : String × String}
    {key : LocalKey} (found : pairs[i]? = some pair)
    (imported : (importAll text limits (some data) state pairs).1[i]? = some .imported)
    (decoded : decodeKeystore text limits pair.1 pair.2 = .ok key)
    (passed : accepts (importAll text limits (some data) state pairs).2.protection) :
    ∃ held, accepts (loadProtection (some data) key.pubkey held) := by
  induction pairs generalizing state i with
  | nil => simp at found
  | cons first rest ih =>
    obtain ⟨keystore, password⟩ := first
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp only [importAll, List.getElem?_cons_zero, Option.some.injEq] at imported passed
      have earlier := accepts_of_importAll back passed
      rw [protection_importKeystore_of_imported imported decoded] at earlier
      exact ⟨_, earlier⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at found
      simp only [importAll, List.getElem?_cons_succ] at imported passed
      exact ih found imported passed

/-- After a key is imported with data, the record limits the blocks of that key.

A block that it accepts meets conditions 1 and 2 of EIP-3076 against those blocks in the data. -/
theorem checkBlockSigning_of_loadProtection {data held : Interchange} {pubkey : BLSPubkey}
    {slot : Slot} {root : Root}
    (passed : (loadProtection (some data) pubkey held).checkBlock pubkey slot root = .ok ()) :
    checkBlockSigning (data.blocksOf pubkey) slot root = .ok () := by
  rw [← blocksOf_entriesOf (keys := [pubkey]) (List.mem_singleton_self pubkey)]
  simp only [loadProtection] at passed
  split at passed
  · rename_i empty
    have none : (data.entriesOf [pubkey]).data = [] := List.isEmpty_iff.mp empty
    simp [Interchange.blocksOf, none, checkBlockSigning, checkBlockSlot, minBlockSlot, ensure,
      bind, Except.bind]
  · exact checkBlockSigning_of_foldl_importFile (files := [data.entriesOf [pubkey]]) passed _
      (by simp)

/-- After a key is imported with data, the record limits the votes of that key.

A vote that it accepts meets conditions 3, 4 and 5 of EIP-3076 against those votes in the data. -/
theorem checkAttestationSigning_of_loadProtection {data held : Interchange} {pubkey : BLSPubkey}
    {source target : Epoch} {root : Root}
    (passed : (loadProtection (some data) pubkey held).checkAttestation pubkey source target root =
      .ok ()) :
    checkAttestationSigning (data.attestationsOf pubkey) source target root = .ok () := by
  rw [← attestationsOf_entriesOf (keys := [pubkey]) (List.mem_singleton_self pubkey)]
  simp only [loadProtection] at passed
  split at passed
  · rename_i empty
    have none : (data.entriesOf [pubkey]).data = [] := List.isEmpty_iff.mp empty
    simp [Interchange.attestationsOf, none, checkAttestationSigning, checkSourceEpoch,
      checkTargetEpoch, minSourceEpoch, minTargetEpoch, ensure, bind, Except.bind]
  · exact checkAttestationSigning_of_foldl_importFile (files := [data.entriesOf [pubkey]]) passed _
      (by simp)

/-- After a key is imported with data, a block that the record accepts is after the key's blocks.

Those are the blocks of the key in the data. -/
theorem lt_slot_of_loadProtection {data held : Interchange} {pubkey : BLSPubkey} {slot : Slot}
    {root : Root}
    (passed : (loadProtection (some data) pubkey held).checkBlock pubkey slot root = .ok ()) :
    ∀ old ∈ data.blocksOf pubkey, old.slot < slot := by
  rw [← blocksOf_entriesOf (keys := [pubkey]) (List.mem_singleton_self pubkey)]
  simp only [loadProtection] at passed
  split at passed
  · rename_i empty
    have none : (data.entriesOf [pubkey]).data = [] := List.isEmpty_iff.mp empty
    simp [Interchange.blocksOf, none]
  · intro old member
    exact lt_slot_of_importFile passed old (List.mem_append_right _ member)

/-- After a key is imported with data, a vote that the record accepts has a source at least each.

Each is the source of a vote of the key in the data. -/
theorem le_sourceEpoch_of_loadProtection {data held : Interchange} {pubkey : BLSPubkey}
    {source target : Epoch} {root : Root}
    (passed : (loadProtection (some data) pubkey held).checkAttestation pubkey source target root =
      .ok ()) :
    ∀ old ∈ data.attestationsOf pubkey, old.sourceEpoch ≤ source := by
  rw [← attestationsOf_entriesOf (keys := [pubkey]) (List.mem_singleton_self pubkey)]
  simp only [loadProtection] at passed
  split at passed
  · rename_i empty
    have none : (data.entriesOf [pubkey]).data = [] := List.isEmpty_iff.mp empty
    simp [Interchange.attestationsOf, none]
  · intro old member
    exact le_sourceEpoch_of_importFile passed old (List.mem_append_right _ member)

/-- After a key is imported with data, a vote that the record accepts has a target after each.

Each is the target of a vote of the key in the data. -/
theorem lt_targetEpoch_of_loadProtection {data held : Interchange} {pubkey : BLSPubkey}
    {source target : Epoch} {root : Root}
    (passed : (loadProtection (some data) pubkey held).checkAttestation pubkey source target root =
      .ok ()) :
    ∀ old ∈ data.attestationsOf pubkey, old.targetEpoch < target := by
  rw [← attestationsOf_entriesOf (keys := [pubkey]) (List.mem_singleton_self pubkey)]
  simp only [loadProtection] at passed
  split at passed
  · rename_i empty
    have none : (data.entriesOf [pubkey]).data = [] := List.isEmpty_iff.mp empty
    simp [Interchange.attestationsOf, none]
  · intro old member
    exact lt_targetEpoch_of_importFile passed old (List.mem_append_right _ member)

/-! ## The call -/

variable {state new : KeyState} {request : ImportKeystoresRequest} {statuses : List ImportStatus}

/-- A request whose lists of keystores and passwords differ in length is refused. -/
theorem importKeystores_eq_error_of_length_ne
    (mismatch : request.keystores.length ≠ request.passwords.length) :
    importKeystores text limits state request =
      .error (.lengthMismatch request.keystores.length request.passwords.length) := by
  simp [importKeystores, mismatch, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A call that succeeds had lists of equal length, and processed each keystore in order.

The data that it loads is the slashing protection data of the request, when a keystore is sent. -/
private theorem importKeystores_eq_ok
    (call : importKeystores text limits state request = .ok (statuses, new)) :
    request.keystores.length = request.passwords.length ∧
      ∃ file, (statuses, new) =
          importAll text limits file state (request.keystores.zip request.passwords) ∧
        (request.keystores ≠ [] → ∀ data, request.slashingProtection = some (.ok data) →
          file = some data) := by
  unfold importKeystores at call
  by_cases equal : request.keystores.length = request.passwords.length
  · refine ⟨equal, ?_⟩
    by_cases empty : request.keystores = []
    · have noPasswords : request.passwords.length = 0 := by simpa [empty] using equal.symm
      simp [empty, noPasswords, pure, Except.pure] at call
      obtain ⟨rfl, rfl⟩ := call
      exact ⟨none, by simp [empty, importAll], fun nonempty => absurd empty nonempty⟩
    · cases sent : request.slashingProtection with
      | none =>
        simp [equal, empty, sent, bind, Except.bind, pure, Except.pure] at call
        exact ⟨none, call.symm, fun _ data absent => by simp at absent⟩
      | some read =>
        cases read with
        | error error => simp [equal, empty, sent, bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at call
        | ok data =>
          simp [equal, empty, sent, bind, Except.bind, pure, Except.pure] at call
          refine ⟨some data, call.symm, fun _ other present => ?_⟩
          simp only [Option.some.injEq, Except.ok.injEq] at present
          subst present
          rfl
  · simp [equal, bind, Except.bind] at call

/-- A call that succeeds gives one status for each keystore. -/
theorem length_of_importKeystores
    (call : importKeystores text limits state request = .ok (statuses, new)) :
    statuses.length = request.keystores.length := by
  obtain ⟨equal, file, eq, -⟩ := importKeystores_eq_ok call
  have := length_importAll (text := text) (limits := limits) (file := file) state
    (request.keystores.zip request.passwords)
  rw [← eq] at this
  simpa [List.length_zip, equal] using this

/-- A call that succeeds removes no key: the keys held before come first, in the same order. -/
theorem localKeys_prefix_of_importKeystores
    (call : importKeystores text limits state request = .ok (statuses, new)) :
    state.localKeys <+: new.localKeys := by
  obtain ⟨-, file, eq, -⟩ := importKeystores_eq_ok call
  have := localKeys_prefix_importAll (text := text) (limits := limits) (file := file) state
    (request.keystores.zip request.passwords)
  rwa [← eq] at this

/-- A keystore with the status imported holds a key that the client holds afterwards. -/
theorem mem_localKeys_of_importKeystores {i : Nat} {keystore password : String}
    (call : importKeystores text limits state request = .ok (statuses, new))
    (atKeystore : request.keystores[i]? = some keystore)
    (atPassword : request.passwords[i]? = some password)
    (imported : statuses[i]? = some .imported) :
    ∃ key, decodeKeystore text limits keystore password = .ok key ∧ key ∈ new.localKeys := by
  obtain ⟨-, file, eq, -⟩ := importKeystores_eq_ok call
  have found : (request.keystores.zip request.passwords)[i]? = some (keystore, password) := by
    simp [List.getElem?_zip_eq_some, atKeystore, atPassword]
  have := exists_mem_localKeys_importAll (text := text) (limits := limits) (file := file) state _ i
    _ found
  rw [← eq] at this
  exact this imported

/-- A keystore is a duplicate exactly when its key was held before the call.

The other case is that a keystore before it in the request imported that key. -/
theorem duplicate_iff_of_importKeystores {i : Nat} {keystore password : String}
    (call : importKeystores text limits state request = .ok (statuses, new))
    (atKeystore : request.keystores[i]? = some keystore)
    (atPassword : request.passwords[i]? = some password) :
    statuses[i]? = some .duplicate ↔
      ∃ key, decodeKeystore text limits keystore password = .ok key ∧
        (state.isActive key.pubkey = true ∨
          ∃ j < i, ∃ earlierKeystore earlierPassword other,
            request.keystores[j]? = some earlierKeystore ∧
            request.passwords[j]? = some earlierPassword ∧ statuses[j]? = some .imported ∧
            decodeKeystore text limits earlierKeystore earlierPassword = .ok other ∧
            other.pubkey = key.pubkey) := by
  obtain ⟨-, file, eq, -⟩ := importKeystores_eq_ok call
  have found : (request.keystores.zip request.passwords)[i]? = some (keystore, password) := by
    simp [List.getElem?_zip_eq_some, atKeystore, atPassword]
  have := duplicate_iff_importAll (text := text) (limits := limits) (file := file) state _ i _ found
  rw [← eq] at this
  rw [this]
  simp only [List.getElem?_zip_eq_some, Prod.exists]
  constructor
  · rintro ⟨key, decoded, held | ⟨j, lt, earlierKeystore, earlierPassword, other, ⟨atK, atP⟩,
      status, decodedOther, same⟩⟩
    · exact ⟨key, decoded, .inl held⟩
    · exact ⟨key, decoded, .inr ⟨j, lt, earlierKeystore, earlierPassword, other, atK, atP, status,
        decodedOther, same⟩⟩
  · rintro ⟨key, decoded, held | ⟨j, lt, earlierKeystore, earlierPassword, other, atK, atP,
      status, decodedOther, same⟩⟩
    · exact ⟨key, decoded, .inl held⟩
    · exact ⟨key, decoded, .inr ⟨j, lt, earlierKeystore, earlierPassword, other, ⟨atK, atP⟩,
        status, decodedOther, same⟩⟩

/-- After a call that succeeds, the record refuses every block that it refused before. -/
theorem checkBlock_of_importKeystores {pubkey : BLSPubkey} {slot : Slot} {root : Root}
    (call : importKeystores text limits state request = .ok (statuses, new))
    (passed : new.protection.checkBlock pubkey slot root = .ok ()) :
    state.protection.checkBlock pubkey slot root = .ok () := by
  obtain ⟨-, file, eq, -⟩ := importKeystores_eq_ok call
  have : new = (importAll text limits file state (request.keystores.zip request.passwords)).2 := by
    rw [← eq]
  subst this
  exact checkBlock_of_importAll passed

/-- After a call that succeeds, the record refuses every vote that it refused before. -/
theorem checkAttestation_of_importKeystores {pubkey : BLSPubkey} {source target : Epoch}
    {root : Root} (call : importKeystores text limits state request = .ok (statuses, new))
    (passed : new.protection.checkAttestation pubkey source target root = .ok ()) :
    state.protection.checkAttestation pubkey source target root = .ok () := by
  obtain ⟨-, file, eq, -⟩ := importKeystores_eq_ok call
  have : new = (importAll text limits file state (request.keystores.zip request.passwords)).2 := by
    rw [← eq]
  subst this
  exact checkAttestation_of_importAll passed

/-- After a call, a property that each import of a key keeps backwards holds after an import.

It must hold after the call, and the import is that of a key imported with the request's data. -/
private theorem exists_loadProtection_of_importKeystores {accepts : Interchange → Prop}
    {data : Interchange} {i : Nat} {keystore password : String} {key : LocalKey}
    (back : ∀ owner held, accepts (loadProtection (some data) owner held) → accepts held)
    (call : importKeystores text limits state request = .ok (statuses, new))
    (atKeystore : request.keystores[i]? = some keystore)
    (atPassword : request.passwords[i]? = some password)
    (imported : statuses[i]? = some .imported)
    (sent : request.slashingProtection = some (.ok data))
    (decoded : decodeKeystore text limits keystore password = .ok key)
    (passed : accepts new.protection) :
    ∃ held, accepts (loadProtection (some data) key.pubkey held) := by
  obtain ⟨-, file, eq, loads⟩ := importKeystores_eq_ok call
  have nonempty : request.keystores ≠ [] := by
    intro empty
    simp [empty] at atKeystore
  have := loads nonempty data sent
  subst this
  have found : (request.keystores.zip request.passwords)[i]? = some (keystore, password) := by
    simp [List.getElem?_zip_eq_some, atKeystore, atPassword]
  rw [show statuses = (importAll text limits (some data) state _).1 by rw [← eq]] at imported
  rw [show new = (importAll text limits (some data) state _).2 by rw [← eq]] at passed
  exact exists_loadProtection_of_importAll back found imported decoded passed

/-- After a call, a block that the record accepts, of a key imported with data, meets two rules.

They are conditions 1 and 2 of EIP-3076 against the blocks of the key in the data. -/
theorem checkBlockSigning_of_importKeystores {i : Nat} {keystore password : String}
    {data : Interchange} {key : LocalKey} {slot : Slot} {root : Root}
    (call : importKeystores text limits state request = .ok (statuses, new))
    (atKeystore : request.keystores[i]? = some keystore)
    (atPassword : request.passwords[i]? = some password)
    (imported : statuses[i]? = some .imported)
    (sent : request.slashingProtection = some (.ok data))
    (decoded : decodeKeystore text limits keystore password = .ok key)
    (passed : new.protection.checkBlock key.pubkey slot root = .ok ()) :
    checkBlockSigning (data.blocksOf key.pubkey) slot root = .ok () := by
  obtain ⟨_, accepted⟩ := exists_loadProtection_of_importKeystores
    (accepts := fun record => record.checkBlock key.pubkey slot root = .ok ())
    (fun _ _ accepted => checkBlock_of_loadProtection accepted) call atKeystore atPassword
    imported sent decoded passed
  exact checkBlockSigning_of_loadProtection accepted

/-- After a call, a block that the record accepts, of a key imported with data, is after its blocks.

Those are the blocks of the key in the data. -/
theorem lt_slot_of_importKeystores {i : Nat} {keystore password : String}
    {data : Interchange} {key : LocalKey} {slot : Slot} {root : Root}
    (call : importKeystores text limits state request = .ok (statuses, new))
    (atKeystore : request.keystores[i]? = some keystore)
    (atPassword : request.passwords[i]? = some password)
    (imported : statuses[i]? = some .imported)
    (sent : request.slashingProtection = some (.ok data))
    (decoded : decodeKeystore text limits keystore password = .ok key)
    (passed : new.protection.checkBlock key.pubkey slot root = .ok ()) :
    ∀ old ∈ data.blocksOf key.pubkey, old.slot < slot := by
  obtain ⟨_, accepted⟩ := exists_loadProtection_of_importKeystores
    (accepts := fun record => record.checkBlock key.pubkey slot root = .ok ())
    (fun _ _ accepted => checkBlock_of_loadProtection accepted) call atKeystore atPassword
    imported sent decoded passed
  exact lt_slot_of_loadProtection accepted

/-- After a call, a vote that the record accepts, of a key imported with data, meets three rules.

They are conditions 3, 4 and 5 of EIP-3076 against the votes of the key in the data. -/
theorem checkAttestationSigning_of_importKeystores {i : Nat} {keystore password : String}
    {data : Interchange} {key : LocalKey} {source target : Epoch} {root : Root}
    (call : importKeystores text limits state request = .ok (statuses, new))
    (atKeystore : request.keystores[i]? = some keystore)
    (atPassword : request.passwords[i]? = some password)
    (imported : statuses[i]? = some .imported)
    (sent : request.slashingProtection = some (.ok data))
    (decoded : decodeKeystore text limits keystore password = .ok key)
    (passed : new.protection.checkAttestation key.pubkey source target root = .ok ()) :
    checkAttestationSigning (data.attestationsOf key.pubkey) source target root = .ok () := by
  obtain ⟨_, accepted⟩ := exists_loadProtection_of_importKeystores
    (accepts := fun record => record.checkAttestation key.pubkey source target root = .ok ())
    (fun _ _ accepted => checkAttestation_of_loadProtection accepted) call atKeystore atPassword
    imported sent decoded passed
  exact checkAttestationSigning_of_loadProtection accepted

/-- After a call, a vote that the record accepts, of a key imported with data, is after its votes.

Its source is at least, and its target after, those of each vote of the key in the data. -/
theorem sourceEpoch_targetEpoch_of_importKeystores {i : Nat} {keystore password : String}
    {data : Interchange} {key : LocalKey} {source target : Epoch} {root : Root}
    (call : importKeystores text limits state request = .ok (statuses, new))
    (atKeystore : request.keystores[i]? = some keystore)
    (atPassword : request.passwords[i]? = some password)
    (imported : statuses[i]? = some .imported)
    (sent : request.slashingProtection = some (.ok data))
    (decoded : decodeKeystore text limits keystore password = .ok key)
    (passed : new.protection.checkAttestation key.pubkey source target root = .ok ()) :
    ∀ old ∈ data.attestationsOf key.pubkey,
      old.sourceEpoch ≤ source ∧ old.targetEpoch < target := by
  obtain ⟨_, accepted⟩ := exists_loadProtection_of_importKeystores
    (accepts := fun record => record.checkAttestation key.pubkey source target root = .ok ())
    (fun _ _ accepted => checkAttestation_of_loadProtection accepted) call atKeystore atPassword
    imported sent decoded passed
  exact fun old member => ⟨le_sourceEpoch_of_loadProtection accepted old member,
    lt_targetEpoch_of_loadProtection accepted old member⟩

/-- A request with no keystore succeeds with no status, whatever its slashing protection data. -/
theorem importKeystores_of_keystores_eq_nil (empty : request.keystores = [])
    (noPasswords : request.passwords = []) :
    importKeystores text limits state request = .ok ([], state) := by
  simp [importKeystores, empty, noPasswords, pure, Except.pure]

/-! ## The response -/

/-- A request whose lists differ in length gets HTTP 400, and the state does not change. -/
theorem postKeystores_of_length_ne {body : Json}
    (read : readImportKeystoresRequest text body = .ok request)
    (mismatch : request.keystores.length ≠ request.passwords.length) :
    (postKeystores text limits state body).1.status = 400 ∧
      (postKeystores text limits state body).2 = state := by
  simp [postKeystores, read, importKeystores_eq_error_of_length_ne mismatch, badRequest]

/-- The call that imports keystores leaves the remote keys as they were. -/
theorem remoteKeys_postKeystores (state : KeyState) (body : Json) :
    (postKeystores text limits state body).2.remoteKeys = state.remoteKeys := by
  unfold postKeystores
  split
  · rfl
  · split
    · rfl
    · rfl
    · rename_i call
      obtain ⟨-, file, eq, -⟩ := importKeystores_eq_ok call
      rw [show _ = _ from congrArg Prod.snd eq]
      exact remoteKeys_importAll state _

end EthLib.Consensus.KeymanagerApi
