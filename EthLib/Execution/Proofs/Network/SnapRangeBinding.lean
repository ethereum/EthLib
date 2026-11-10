module

public import EthLib.Execution.Proofs.Network.SnapRange
public import EthLib.Execution.Proofs.Trie.RangeBinding

/-!
# Proofs: a valid snap range answer is the trie between its ends

A valid AccountRange answer gives each account hash between its ends the value of the state trie.

A valid StorageRanges answer does the same for each storage trie it covers.

The source is [`caps/snap.md`][snap], sections "AccountRange (0x01)" and "StorageRanges (0x03)".

[snap]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md

The tries are secured: each key is the hash of an address or of a slot key.

The value of an account in the trie is its full encoding, which the answer sends in slim form.

Otherwise a search returns a collision of Keccak-256, as for a range of any trie.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Cryptography.Hash.Keccak

/-- Take a map of the accounts that gives each one its hash and its full form.

When it succeeds, it keeps the accounts with a full form, in order.

The hashes of its outputs are those of the accounts, in order.

The value of a hash among its outputs is then the full form of the account with that hash. -/
private theorem mapM_fullAccount {ε : Type} {convert : RangeEntry → Except ε (Hash32 × ByteArray)}
    (hconvert : ∀ account entry, convert account = .ok entry →
      fullAccount account.data = some entry.2 ∧ entry.1 = account.hash) :
    {accounts : List RangeEntry} → {entries : List (Hash32 × ByteArray)} →
      accounts.mapM convert = .ok entries →
      entries = accounts.filterMap (fun account =>
          (fullAccount account.data).map fun value => (account.hash, value)) ∧
        entries.map Prod.fst = accounts.map RangeEntry.hash ∧
        ∀ key, (entries.find? fun entry => entry.1 = key).map Prod.snd =
          (accounts.find? fun account => account.hash = key).bind fun account =>
            fullAccount account.data
  | [], entries, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | account :: rest, entries, h => by
    obtain ⟨⟨digest, value⟩, others, hhead, htail, rfl⟩ := mapM_cons_ok.mp h
    obtain ⟨hfull, hhash⟩ := hconvert account _ hhead
    subst hhash
    obtain ⟨hothers, hhashes, hfind⟩ := mapM_fullAccount hconvert htail
    refine ⟨by simp [hothers, hfull], by simp [hhashes], fun key => ?_⟩
    by_cases hkey : account.hash = key
    · simp [hkey, hfull]
    · simp [hkey, hfind key]

/-- Soundness of an AccountRange answer that is not the empty reply.

It gives each account hash between its ends the full account of the state trie with that hash.

When the answer reaches the end of the trie, each hash need only follow the start.

The keys of the state trie must be distinct.

Otherwise the range search returns a collision in the plain trie of the hashed keys.

Or the state trie has two keys with one hash, which the key search returns. -/
theorem verifyAccountRange_sound {data : List (ByteArray × ByteArray)} {root' start : Hash32}
    {accounts : List RangeEntry} {proof : List ByteArray} {answer : RangeAnswer}
    (hroot : root keccak256 ⟨true, data⟩ = .ok root') (hkeys : (data.map Prod.fst).Nodup)
    (hverify : verifyAccountRange root' start accounts proof = .ok answer)
    (hstate : answer ≠ .noState) (key : Hash32)
    (hstart : bytesToNibbleList ⟨start.toArray⟩ ≤ bytesToNibbleList ⟨key.toArray⟩)
    (hlast : answer = .toEnd ∨ accounts.getLast?.all fun last =>
      bytesToNibbleList ⟨key.toArray⟩ ≤ bytesToNibbleList ⟨last.hash.toArray⟩) :
    (data.find? fun entry => decide ((show Hash32 from keccak256 entry.1) = key)).map Prod.snd =
        ((accounts.find? fun account => account.hash = key).bind fun account =>
          fullAccount account.data) ∨
      (∃ pair, findRangeCollision keccak256
        ⟨false, data.map fun entry => (⟨(keccak256 entry.1).toArray⟩, entry.2)⟩ root' start
        (accounts.filterMap fun account =>
          (fullAccount account.data).map fun value => (account.hash, value))
        proof key = some pair ∧ IsCollision keccak256 pair) ∨
      ∃ pair, findPathCollision keccak256 ⟨true, data⟩ = some pair ∧
        IsCollision keccak256 pair := by
  unfold verifyAccountRange at hverify
  by_cases hempty : (accounts.isEmpty && proof.isEmpty) = true
  · -- The empty reply is excluded.
    simp only [hempty, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hverify
    exact absurd hverify.symm hstate
  · simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hverify
    obtain ⟨entries, hmap, hrest⟩ := bind_ok_iff.mp hverify
    obtain ⟨more, hmore, hanswer⟩ := bind_ok_iff.mp hrest
    rw [mapError_ok_iff] at hmore
    simp only [pure, Except.pure, Except.ok.injEq] at hanswer
    -- Each account converts to its hash and its full form.
    obtain ⟨hentries, hhashes, hfind⟩ := mapM_fullAccount (fun account entry hentry => by
      split at hentry
      · rename_i value hfull
        simp only [pure, Except.pure, Except.ok.injEq] at hentry
        exact ⟨by rw [hfull, ← hentry], by rw [← hentry]⟩
      · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hentry) hmap
    have hlast' : more = false ∨ entries.getLast?.all fun last =>
        bytesToNibbleList ⟨key.toArray⟩ ≤ bytesToNibbleList ⟨last.1.toArray⟩ := by
      rcases hlast with hend | hall
      · subst hend
        cases more
        · exact .inl rfl
        · simp [RangeAnswer.ofMore] at hanswer
      · refine .inr ?_
        have hget := congrArg List.getLast? hhashes
        rw [List.getLast?_map, List.getLast?_map] at hget
        cases hentry : entries.getLast? with
        | none => rfl
        | some last =>
          cases haccount : accounts.getLast? with
          | none =>
            rw [hentry, haccount] at hget
            cases hget
          | some account =>
            rw [hentry, haccount, Option.map_some, Option.map_some, Option.some.injEq] at hget
            rw [haccount] at hall
            simpa [hget] using hall
    rcases verifyRange_sound_secured keccak256 hroot hkeys hmore key hstart hlast' with
      hvalue | hfound | hfound
    · exact .inl (by rw [← hfind key]; exact hvalue)
    · exact .inr (.inl (by rw [← hentries]; exact hfound))
    · exact .inr (.inr hfound)

/-- A range checked with no proof shows that no key follows it. -/
private theorem verifyRange_nil {hash : ByteArray → Hash32} {root start : Hash32}
    {entries : List (Hash32 × ByteArray)} {more : Bool}
    (h : verifyRange hash root start entries [] = .ok more) : more = false := by
  unfold verifyRange at h
  simp only [List.isEmpty_nil, ↓reduceIte] at h
  repeat' split at h
  all_goals simp_all [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, pure,
    Except.pure, bind, Except.bind]

/-- A list of zero nibbles is at most any list that is no shorter. -/
private theorem zeros_le : (zeros path : List Nibble) → (∀ nibble ∈ zeros, nibble = 0) →
    zeros.length ≤ path.length → zeros ≤ path
  | [], _, _, _ => List.nil_le _
  | _ :: _, [], _, hlength => by simp at hlength
  | zero :: zeros, nibble :: path, hzeros, hlength => by
    rw [List.forall_mem_cons] at hzeros
    obtain ⟨rfl, hzeros⟩ := hzeros
    rw [List.cons_le_cons_iff]
    by_cases hnibble : nibble = 0
    · exact .inr ⟨hnibble.symm, zeros_le zeros path hzeros (by simpa using hlength)⟩
    · exact .inl (Fin.pos_iff_ne_zero.mpr hnibble)

/-- A step whose value is dropped succeeds only when the step succeeds. -/
private theorem exists_ok_of_discard {ε α : Type} {x : Except ε α}
    (h : discard x = .ok ()) : ∃ value, x = .ok value := by
  cases x
  · simp [discard, Functor.mapConst, Except.map] at h
  · exact ⟨_, rfl⟩

/-- Soundness of one range of a StorageRanges answer that is not the empty reply.

The ranges are those of the answer, or one empty range when it holds a proof alone.

It gives each slot hash of the range the value of the storage trie of its account with that hash.

Each range but the last is a whole trie, so this holds for every hash.

Requested accounts after the last range get no answer.

The last range starts at the starting hash for one account, and at the zero hash for several.

It holds for each hash from there to its last slot, or to the end when the answer says so.

The keys of the storage trie must be distinct.

Otherwise the range search returns a collision in the plain trie of the hashed keys.

Or the storage trie has two keys with one hash, which the key search returns. -/
theorem verifyStorageRanges_sound {roots : List Hash32} {start : Hash32}
    {slots ranges : List (List RangeEntry)} {proof : List ByteArray} {answer : RangeAnswer}
    (hverify : verifyStorageRanges roots start slots proof = .ok answer)
    (hstate : answer ≠ .noState) (hranges : ranges = if slots.isEmpty then [[]] else slots)
    {index : Nat} {range : List RangeEntry} {root' : Hash32}
    (hrange : ranges[index]? = some range) (hrootIndex : roots[index]? = some root')
    {data : List (ByteArray × ByteArray)}
    (hroot : root keccak256 ⟨true, data⟩ = .ok root') (hkeys : (data.map Prod.fst).Nodup)
    (key : Hash32)
    (hkey : index + 1 < ranges.length ∨
      (bytesToNibbleList ⟨(if roots.length = 1 then start else Vector.replicate 32 0).toArray⟩ ≤
          bytesToNibbleList ⟨key.toArray⟩ ∧
        (answer = .toEnd ∨ range.getLast?.all fun last =>
          bytesToNibbleList ⟨key.toArray⟩ ≤ bytesToNibbleList ⟨last.hash.toArray⟩))) :
    (data.find? fun entry => decide ((show Hash32 from keccak256 entry.1) = key)).map Prod.snd =
        (range.find? fun slot => slot.hash = key).map RangeEntry.data ∨
      (∃ pair, findRangeCollision keccak256
        ⟨false, data.map fun entry => (⟨(keccak256 entry.1).toArray⟩, entry.2)⟩ root'
        (if roots.length = 1 then start else Vector.replicate 32 0)
        (range.map fun slot => (slot.hash, slot.data))
        (if index + 1 < ranges.length then [] else proof) key = some pair ∧
        IsCollision keccak256 pair) ∨
      ∃ pair, findPathCollision keccak256 ⟨true, data⟩ = some pair ∧
        IsCollision keccak256 pair := by
  unfold verifyStorageRanges at hverify
  by_cases hempty : (slots.isEmpty && proof.isEmpty) = true
  · -- The empty reply is excluded.
    simp only [hempty, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hverify
    exact absurd hverify.symm hstate
  simp only [hempty, Bool.false_eq_true, ↓reduceIte, ← hranges] at hverify
  by_cases hmany : roots.length < ranges.length
  · simp [hmany, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, bind,
      Except.bind] at hverify
  simp only [hmany, ↓reduceIte] at hverify
  obtain ⟨⟨⟩, hloop, hfinal⟩ := bind_ok_iff.mp hverify
  rw [forIn_unit_ok_iff (fun _ hstep => by
    obtain ⟨_, -, hstep⟩ := bind_ok_iff.mp hstep
    cases hstep)] at hloop
  -- The range is the one of its account.
  have hzip : (roots.zip ranges)[index]? = some (root', range) :=
    List.getElem?_zip_eq_some.mpr ⟨hrootIndex, hrange⟩
  have hindex : index < ranges.length := (List.getElem?_eq_some_iff.mp hrange).1
  have hlength : (roots.zip ranges).length = ranges.length := by
    rw [List.length_zip]
    omega
  -- The soundness of the range, whatever its proof.
  have hsound : ∀ part more, verifyRange keccak256 root'
      (if roots.length = 1 then start else Vector.replicate 32 0)
      (range.map fun slot => (slot.hash, slot.data)) part = .ok more →
      bytesToNibbleList ⟨(if roots.length = 1 then start else Vector.replicate 32 0).toArray⟩ ≤
        bytesToNibbleList ⟨key.toArray⟩ →
      (more = false ∨ range.getLast?.all fun last =>
        bytesToNibbleList ⟨key.toArray⟩ ≤ bytesToNibbleList ⟨last.hash.toArray⟩) →
      (data.find? fun entry => decide ((show Hash32 from keccak256 entry.1) = key)).map
          Prod.snd = (range.find? fun slot => slot.hash = key).map RangeEntry.data ∨
        (∃ pair, findRangeCollision keccak256
          ⟨false, data.map fun entry => (⟨(keccak256 entry.1).toArray⟩, entry.2)⟩ root'
          (if roots.length = 1 then start else Vector.replicate 32 0)
          (range.map fun slot => (slot.hash, slot.data)) part key = some pair ∧
          IsCollision keccak256 pair) ∨
        ∃ pair, findPathCollision keccak256 ⟨true, data⟩ = some pair ∧
          IsCollision keccak256 pair := by
    intro part more hcheck hstart hlast
    have hlast' : more = false ∨ (range.map fun slot => (slot.hash, slot.data)).getLast?.all
        fun last => bytesToNibbleList ⟨key.toArray⟩ ≤ bytesToNibbleList ⟨last.1.toArray⟩ := by
      rw [List.getLast?_map]
      cases hget : range.getLast? with
      | none => simp
      | some last =>
        rw [hget] at hlast
        simpa using hlast
    rcases verifyRange_sound_secured keccak256 hroot hkeys hcheck key hstart hlast' with
      hvalue | hfound | hfound
    · refine .inl ?_
      rw [hvalue, List.find?_map, Option.map_map]
      rfl
    · exact .inr (.inl hfound)
    · exact .inr (.inr hfound)
  by_cases hidx : index + 1 < ranges.length
  · -- A range before the last is a whole trie, checked with no proof.
    simp only [hidx, ↓reduceIte]
    have hmem : (root', range) ∈ (roots.zip ranges).dropLast := by
      refine List.mem_of_getElem? (show (roots.zip ranges).dropLast[index]? = _ from ?_)
      rw [List.getElem?_dropLast, hlength]
      simp only [show index < ranges.length - 1 by omega, ↓reduceIte]
      exact hzip
    obtain ⟨_, hdiscard, -⟩ := bind_ok_iff.mp (hloop _ hmem)
    obtain ⟨more, hcheck⟩ := exists_ok_of_discard hdiscard
    rw [mapError_ok_iff] at hcheck
    refine hsound [] more hcheck ?_ (.inl (verifyRange_nil hcheck))
    -- Several accounts start at the zero hash, which no hash precedes.
    simp only [show roots.length ≠ 1 by omega, ↓reduceIte]
    apply zeros_le
    · simp [bytesToNibbleList, highNibble, lowNibble]
    · simp [length_bytesToNibbleList, ByteArray.size]
  · -- The last range is checked with the proof.
    have hget : (roots.zip ranges).getLast? = some (root', range) := by
      rw [List.getLast?_eq_getElem?, hlength, show ranges.length - 1 = index by omega]
      exact hzip
    rw [hget] at hfinal
    obtain ⟨more, hcheck, hanswer⟩ := bind_ok_iff.mp hfinal
    rw [mapError_ok_iff] at hcheck
    simp only [pure, Except.pure, Except.ok.injEq] at hanswer
    simp only [hidx, ↓reduceIte]
    obtain ⟨hstart, hlast⟩ := hkey.resolve_left hidx
    refine hsound proof more hcheck hstart ?_
    rcases hlast with hend | hall
    · subst hend
      cases more
      · exact .inl rfl
      · simp [RangeAnswer.ofMore] at hanswer
    · exact .inr hall

end EthLib.Execution.Network
