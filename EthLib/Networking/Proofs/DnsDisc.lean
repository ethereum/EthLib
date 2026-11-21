module

public import EthLib.Networking.DnsDisc
public import EthLib.Base.Proofs.Base32
public import EthLib.Base.Proofs.Base64
public import EthLib.Base.Proofs.Bytes
public import EthLib.Networking.Proofs.Enr.Record
public import EthLib.Networking.Proofs.Rlpx.Handshake
public import Std.Data.String.ToNat

/-!
# Proofs: the entries of a node list

The text of an entry and the entry determine each other.

So a resolver that changes the text of an entry changes the entry, and its hash name with it.

The name of an entry has 26 characters.

A root signed with a private key verifies under the compressed public key of that key.

Two resolvers that serve one root, and whose lists both resolve, give the same list.

Otherwise the code finds two texts with one truncated hash, which is a collision of Keccak-256.

A list resolves only from a root that the key signed, with a sequence number not below the last.
-/

@[expose] public section

namespace EthLib.Networking.DnsDisc

open EthLib.Base
open EthLib.Cryptography.Secp256k1

/-- The entries for which the text round trip holds.

A link names a point of the curve, and a record reads back from its own bytes. -/
def Entry.Valid : Entry → Prop
  | .link url => (Point.decode ⟨url.key.toArray⟩).toBool = true
  | .enr record => ∀ bytes, record.encode = .ok bytes → Enr.decode bytes = .ok record
  | _ => True

/-! ## Prefixes -/

/-- A list that starts with a prefix leaves what follows the prefix. -/
theorem dropPrefix_append : (p cs : List Char) → dropPrefix p (p ++ cs) = some cs
  | [], _ => rfl
  | c :: p, cs => by simp [dropPrefix, dropPrefix_append p cs]

/-- A list that a prefix leaves a rest of is the prefix, then that rest. -/
theorem eq_append_of_dropPrefix : (p cs rest : List Char) → dropPrefix p cs = some rest →
    cs = p ++ rest
  | [], cs, rest, h => by
    simp only [dropPrefix, Option.some.injEq] at h
    simp [h]
  | c :: p, d :: cs, rest, h => by
    simp only [dropPrefix] at h
    split at h
    · rename_i same
      simp [same, eq_append_of_dropPrefix p cs rest h]
    · cases h
  | _ :: _, [], _, h => by simp [dropPrefix] at h

/-- The characters of the prefix of a root. -/
theorem ROOT_PREFIX_eq :
    ROOT_PREFIX = ['e', 'n', 'r', 't', 'r', 'e', 'e', '-', 'r', 'o', 'o', 't', ':', 'v', '1', ' ',
      'e', '='] := by
  decide

/-- The characters of the prefix of a branch. -/
theorem BRANCH_PREFIX_eq :
    BRANCH_PREFIX =
      ['e', 'n', 'r', 't', 'r', 'e', 'e', '-', 'b', 'r', 'a', 'n', 'c', 'h', ':'] := by
  decide

/-- The characters of the prefix of a URL. -/
theorem URL_PREFIX_eq : URL_PREFIX = ['e', 'n', 'r', 't', 'r', 'e', 'e', ':', '/', '/'] := by
  decide

/-- A branch does not start with the prefix of a root. -/
theorem dropPrefix_root_branch (cs : List Char) :
    dropPrefix ROOT_PREFIX (BRANCH_PREFIX ++ cs) = none := by
  simp [ROOT_PREFIX_eq, BRANCH_PREFIX_eq, dropPrefix]

/-- A link does not start with the prefix of a root. -/
theorem dropPrefix_root_url (cs : List Char) :
    dropPrefix ROOT_PREFIX (URL_PREFIX ++ cs) = none := by
  simp [ROOT_PREFIX_eq, URL_PREFIX_eq, dropPrefix]

/-- A link does not start with the prefix of a branch. -/
theorem dropPrefix_branch_url (cs : List Char) :
    dropPrefix BRANCH_PREFIX (URL_PREFIX ++ cs) = none := by
  simp [BRANCH_PREFIX_eq, URL_PREFIX_eq, dropPrefix]

/-- A record does not start with the prefix of a root. -/
theorem dropPrefix_root_enr (cs : List Char) :
    dropPrefix ROOT_PREFIX (Enr.TEXT_PREFIX ++ cs) = none := by
  simp [ROOT_PREFIX_eq, Enr.TEXT_PREFIX, dropPrefix]

/-- A record does not start with the prefix of a branch. -/
theorem dropPrefix_branch_enr (cs : List Char) :
    dropPrefix BRANCH_PREFIX (Enr.TEXT_PREFIX ++ cs) = none := by
  simp [BRANCH_PREFIX_eq, Enr.TEXT_PREFIX, dropPrefix]

/-- A record does not start with the prefix of a link. -/
theorem dropPrefix_url_enr (cs : List Char) :
    dropPrefix URL_PREFIX (Enr.TEXT_PREFIX ++ cs) = none := by
  simp [URL_PREFIX_eq, Enr.TEXT_PREFIX, dropPrefix]

/-! ## Fields -/

/-- The name of a hash has 26 characters. -/
theorem Hash.length_toText (h : Hash) : h.toText.length = HASH_TEXT_SIZE := by
  rw [Hash.toText, Base32.length_encodeList, Vector.length_toList]
  rfl

/-- A hash reads back from its name. -/
theorem Hash.ofText_toText (h : Hash) : Hash.ofText h.toText = .ok h := by
  simp [Hash.ofText, Hash.toText, Base32.decodeList_encodeList, Except.mapError, bind,
    Except.bind, Vector.toList]

/-- The name of a hash is the only text that reads as that hash. -/
theorem Hash.toText_of_ofText {cs : List Char} {h : Hash} (hh : Hash.ofText cs = .ok h) :
    h.toText = cs := by
  simp only [Hash.ofText, bind_ok_iff] at hh
  obtain ⟨bytes, hb, hx⟩ := hh
  cases hd : Base32.decodeList 0 cs with
  | error e => simp [hd, Except.mapError] at hb
  | ok b =>
    simp only [hd, Except.mapError, Except.ok.injEq] at hb
    subst hb
    rw [exactBytes_eq_ok_iff] at hx
    have same : h.toList = b := by simp [Vector.toList, hx]
    rw [Hash.toText, same, Base32.encodeList_of_decodeList hd]

/-- A signature reads back from its base64 text. -/
theorem signatureOf_encodeList (sig : Vector UInt8 65) :
    signatureOf (Base64.encodeList sig.toList) = .ok sig := by
  simp [signatureOf, Base64.decodeList_encodeList, Except.mapError, bind, Except.bind,
    Vector.toList]

/-- The base64 text of a signature is the only text that reads as that signature. -/
theorem encodeList_of_signatureOf {cs : List Char} {sig : Vector UInt8 65}
    (h : signatureOf cs = .ok sig) : Base64.encodeList sig.toList = cs := by
  simp only [signatureOf, bind_ok_iff] at h
  obtain ⟨bytes, hb, hx⟩ := h
  cases hd : Base64.decodeList 0 cs with
  | error e => simp [hd, Except.mapError] at hb
  | ok b =>
    simp only [hd, Except.mapError, Except.ok.injEq] at hb
    subst hb
    rw [exactBytes_eq_ok_iff] at hx
    have same : sig.toList = b := by simp [Vector.toList, hx]
    rw [same, Base64.encodeList_decodeList _ _ hd]

/-- A sequence number reads back from its decimal text. -/
theorem seqOf_repr (n : Nat) : seqOf (Nat.repr n).toList = .ok n := by
  simp only [seqOf, String.ofList_toList, Nat.toNat?_repr]
  rfl

/-- The decimal text of a sequence number is the only text that reads as that number. -/
theorem repr_of_seqOf {cs : List Char} {n : Nat} (h : seqOf cs = .ok n) :
    (Nat.repr n).toList = cs := by
  unfold seqOf at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-! ## Roots -/

/-- The text of a root after its prefix. -/
theorem Root.dropPrefix_toText (r : Root) :
    dropPrefix ROOT_PREFIX r.toText = some (r.enrRoot.toText ++ " l=".toList ++
      r.linkRoot.toText ++ " seq=".toList ++ (Nat.repr r.seq).toList ++ " sig=".toList ++
      Base64.encodeList r.signature.toList) := by
  simp only [Root.toText, signedText, List.append_assoc, dropPrefix_append]

/-- A root reads back from its text after its prefix. -/
theorem Root.parseFields_toText (r : Root) :
    Root.parseFields (r.enrRoot.toText ++ " l=".toList ++ r.linkRoot.toText ++ " seq=".toList ++
      (Nat.repr r.seq).toList ++ " sig=".toList ++ Base64.encodeList r.signature.toList) =
      .ok r := by
  obtain ⟨e, l, seq, sig⟩ := r
  have he := Hash.length_toText e
  have hl := Hash.length_toText l
  -- The sequence number is what lies before the last 92 characters.
  have hlen : ((Nat.repr seq).toList ++ (" sig=".toList ++ Base64.encodeList sig.toList)).length -
      (5 + SIGNATURE_TEXT_SIZE) = (Nat.repr seq).toList.length := by
    simp only [List.length_append, Base64.length_encodeList, Vector.length_toList,
      SIGNATURE_TEXT_SIZE]
    have : " sig=".toList.length = 5 := by decide
    omega
  simp only [Root.parseFields, List.append_assoc, List.take_left' he, List.drop_left' he,
    Hash.ofText_toText, dropPrefix_append, List.take_left' hl, List.drop_left' hl, bind,
    Except.bind, hlen, List.take_left', List.drop_left', seqOf_repr, signatureOf_encodeList]
  rfl

/-- The text after the prefix of a root that reads as a root is the rest of its text. -/
theorem Root.toText_of_parseFields {rest : List Char} {r : Root}
    (h : Root.parseFields rest = .ok r) : r.toText = ROOT_PREFIX ++ rest := by
  simp only [Root.parseFields, bind_ok_iff] at h
  obtain ⟨e, he, h⟩ := h
  split at h
  case h_2 => cases h
  rename_i rest2 h2
  rw [bind_ok_iff] at h
  obtain ⟨l, hl, h⟩ := h
  split at h
  case h_2 => cases h
  rename_i rest3 h3
  generalize ht : rest3.length - (5 + SIGNATURE_TEXT_SIZE) = tail at h
  split at h
  case h_2 => cases h
  rename_i sig h4
  simp only [bind_ok_iff] at h
  obtain ⟨seq, hs, signature, hg, h⟩ := h
  cases h
  -- Each field is the text that it reads from, and the separators are between them.
  rw [← List.take_append_drop HASH_TEXT_SIZE rest, ← Hash.toText_of_ofText he,
    eq_append_of_dropPrefix _ _ _ h2, ← List.take_append_drop HASH_TEXT_SIZE rest2,
    ← Hash.toText_of_ofText hl, eq_append_of_dropPrefix _ _ _ h3,
    ← List.take_append_drop tail rest3, ← repr_of_seqOf hs, eq_append_of_dropPrefix _ _ _ h4,
    ← encodeList_of_signatureOf hg]
  simp only [Root.toText, signedText, List.append_assoc]

/-! ## URLs -/

/-- A URL reads back from its text after its prefix, when its key is a point of the curve. -/
theorem Url.parseFields_toText {url : Url}
    (valid : (Point.decode ⟨url.key.toArray⟩).toBool = true) :
    Url.parseFields (Base32.encodeList url.key.toList ++ '@' :: url.domain.toList) = .ok url := by
  have hk : (Base32.encodeList url.key.toList).length = KEY_TEXT_SIZE := by
    rw [Base32.length_encodeList, Vector.length_toList]
    rfl
  simp only [Url.parseFields, List.take_left' hk, List.drop_left' hk, Base32.decodeList_encodeList]
  simp [Except.mapError, bind, Except.bind, Vector.toList, valid, pure, Except.pure]

/-- The text after the prefix of a URL that reads as a URL is the rest of its text. -/
theorem Url.toText_of_parseFields {rest : List Char} {url : Url}
    (h : Url.parseFields rest = .ok url) : url.toText = URL_PREFIX ++ rest := by
  simp only [Url.parseFields, bind_ok_iff] at h
  obtain ⟨bytes, hb, key, hkey, h⟩ := h
  by_cases hp : (Point.decode ⟨key.toArray⟩).toBool = true
  · simp only [hp, ite_true] at h
    split at h
    · rename_i domain hd
      cases h
      cases hdec : Base32.decodeList 0 (rest.take KEY_TEXT_SIZE) with
      | error e => simp [hdec, Except.mapError] at hb
      | ok b =>
        simp only [hdec, Except.mapError, Except.ok.injEq] at hb
        subst hb
        rw [exactBytes_eq_ok_iff] at hkey
        have same : key.toList = b := by simp [Vector.toList, hkey]
        -- The key is the text before `@`, and the domain the text after it.
        rw [← List.take_append_drop KEY_TEXT_SIZE rest, hd,
          ← Base32.encodeList_of_decodeList hdec, ← same]
        simp [Url.toText]
    · cases h
  · simp [hp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-! ## Branches -/

/-- The hashes of a branch have no characters only when there are none. -/
theorem hashesText_eq_nil {hs : List Hash} (h : hashesText hs = []) : hs = [] := by
  match hs, h with
  | [], _ => rfl
  | [x], h =>
    have := Hash.length_toText x
    simp only [hashesText] at h
    simp [h, HASH_TEXT_SIZE] at this
  | _ :: _ :: _, h => simp [hashesText] at h

/-- A non-empty list of hashes reads back from its text. -/
theorem hashesOf_hashesText : (hs : List Hash) → hs ≠ [] → hashesOf (hashesText hs) = .ok hs
  | [], h => absurd rfl h
  | [x], _ => by
    have hx := Hash.length_toText x
    rw [hashesOf]
    simp only [hashesText, List.take_of_length_le (Nat.le_of_eq hx), Hash.ofText_toText]
    split
    · rfl
    · rename_i hd
      simp [List.drop_of_length_le (Nat.le_of_eq hx)] at hd
    · rename_i other _
      exact absurd (List.drop_of_length_le (Nat.le_of_eq hx)) other
  | x :: y :: more, _ => by
    have hx := Hash.length_toText x
    have ih := hashesOf_hashesText (y :: more) (by simp)
    have ht : hashesText (x :: y :: more) = x.toText ++ ',' :: hashesText (y :: more) := by
      simp [hashesText]
    rw [hashesOf]
    simp only [ht, List.take_left' hx, Hash.ofText_toText]
    split
    · rename_i hd
      simp [ht, List.drop_left' hx] at hd
    · rename_i rest hd
      simp only [ht, List.drop_left' hx, List.cons.injEq, true_and] at hd
      subst hd
      simp [ih, bind, Except.bind, pure, Except.pure]
    · rename_i _ other
      exact absurd (by rw [ht, List.drop_left' hx]) (other _)

/-- A text that reads as hashes reads as at least one. -/
theorem ne_nil_of_hashesOf {cs : List Char} {hs : List Hash} (h : hashesOf cs = .ok hs) :
    hs ≠ [] := by
  rw [hashesOf, bind_ok_iff] at h
  obtain ⟨x, -, h⟩ := h
  split at h
  · cases h
    simp
  · rw [bind_ok_iff] at h
    obtain ⟨_, -, h⟩ := h
    cases h
    simp
  · cases h

/-- The text of hashes is the only text that reads as those hashes. -/
theorem hashesText_of_hashesOf {cs : List Char} {hs : List Hash} (h : hashesOf cs = .ok hs) :
    hashesText hs = cs := by
  rw [hashesOf, bind_ok_iff] at h
  obtain ⟨x, hx, h⟩ := h
  have first := Hash.toText_of_ofText hx
  split at h
  · rename_i hd
    cases h
    rw [← List.take_append_drop HASH_TEXT_SIZE cs, hd, ← first]
    simp [hashesText]
  · rename_i rest hd
    rw [bind_ok_iff] at h
    obtain ⟨more, hmore, h⟩ := h
    cases h
    have : rest.length < cs.length := by
      have := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at this
      omega
    have tail := hashesText_of_hashesOf hmore
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil (ne_nil_of_hashesOf hmore)
    -- The first hash, a comma, and the text of the others.
    rw [← List.take_append_drop HASH_TEXT_SIZE cs, hd, ← first, ← tail]
    simp [hashesText]
  · cases h
termination_by cs.length

/-- The hashes of a branch read back from their text. -/
theorem branchOf_hashesText (hs : List Hash) : branchOf (hashesText hs) = .ok hs := by
  by_cases empty : hs = []
  · subst empty
    rfl
  · have text : hashesText hs ≠ [] := fun h => empty (hashesText_eq_nil h)
    simp only [branchOf, text, ↓reduceIte, hashesOf_hashesText hs empty]

/-- The text of the hashes of a branch is the only text that reads as those hashes. -/
theorem hashesText_of_branchOf {cs : List Char} {hs : List Hash} (h : branchOf cs = .ok hs) :
    hashesText hs = cs := by
  unfold branchOf at h
  split at h
  · rename_i empty
    cases h
    simp [hashesText, empty]
  · exact hashesText_of_hashesOf h

/-- The name of an entry has 26 characters. -/
theorem length_subdomain (text : String) : (subdomain text).length = HASH_TEXT_SIZE := by
  rw [subdomain, String.length_ofList, Hash.length_toText]

/-- An entry reads back from its text.

A link must name a point of the curve, and a record must be one that the decoder accepts. -/
theorem Entry.parse_toText {e : Entry} {text : String} (h : e.toText = .ok text)
    (valid : e.Valid) : Entry.parse text = .ok e := by
  cases e with
  | root r =>
    simp only [Entry.toText, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Entry.parse, String.toList_ofList, Root.dropPrefix_toText,
      Root.parseFields_toText]
    rfl
  | branch hashes =>
    simp only [Entry.toText, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Entry.parse, String.toList_ofList, dropPrefix_root_branch, dropPrefix_append,
      branchOf_hashesText]
    rfl
  | link url =>
    simp only [Entry.toText, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Entry.parse, String.toList_ofList, Url.toText, List.append_assoc,
      dropPrefix_root_url, dropPrefix_branch_url, dropPrefix_append, Url.parseFields_toText valid]
    rfl
  | enr record =>
    simp only [Entry.toText] at h
    cases ht : record.toText with
    | error e => simp [ht, Except.mapError] at h
    | ok t =>
    simp only [ht, Except.mapError, Except.ok.injEq] at h
    subst h
    have ht' := ht
    simp only [Enr.Enr.toText, bind_ok_iff] at ht'
    obtain ⟨bytes, hb, hs⟩ := ht'
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    -- The record reads back from its bytes, so from its text.
    obtain ⟨-, size, sorted, id⟩ := (Enr.decode_eq_ok_iff bytes record).mp (valid bytes hb)
    have back := Enr.fromText_toText record t bytes hb ht size sorted id
    have chars : t.toList = Enr.TEXT_PREFIX ++ (Base64.encode bytes).toList := by
      rw [← hs, String.toList_append, String.toList_ofList]
    simp only [Entry.parse, chars, dropPrefix_root_enr, dropPrefix_branch_enr,
      dropPrefix_url_enr, dropPrefix_append, back]
    rfl

/-- The text of an entry is the only text that reads as that entry. -/
theorem Entry.toText_of_parse {text : String} {e : Entry} (h : Entry.parse text = .ok e) :
    e.toText = .ok text := by
  unfold Entry.parse at h
  split at h
  · rename_i rest hd
    cases hp : Root.parseFields rest with
    | error err => simp [hp, Functor.map, Except.map] at h
    | ok r =>
      simp only [hp, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      simp only [Entry.toText, Root.toText_of_parseFields hp, ← eq_append_of_dropPrefix _ _ _ hd,
        String.ofList_toList]
      rfl
  split at h
  · rename_i rest hd
    cases hp : branchOf rest with
    | error err => simp [hp, Functor.map, Except.map] at h
    | ok hashes =>
      simp only [hp, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      simp only [Entry.toText, hashesText_of_branchOf hp, ← eq_append_of_dropPrefix _ _ _ hd,
        String.ofList_toList]
      rfl
  split at h
  · rename_i rest hd
    cases hp : Url.parseFields rest with
    | error err => simp [hp, Functor.map, Except.map] at h
    | ok url =>
      simp only [hp, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      simp only [Entry.toText, Url.toText_of_parseFields hp, ← eq_append_of_dropPrefix _ _ _ hd,
        String.ofList_toList]
      rfl
  split at h
  · cases hp : Enr.fromText text with
    | error err => simp [hp, Except.mapError, Functor.map, Except.map] at h
    | ok record =>
      simp only [hp, Except.mapError, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      simp [Entry.toText, Enr.toText_of_fromText hp, Except.mapError]
  · cases h

/-- A URL reads back from its text, when its key is a point of the curve. -/
theorem Url.parse_toText {url : Url} (valid : (Point.decode ⟨url.key.toArray⟩).toBool = true) :
    Url.parse (String.ofList url.toText) = .ok url := by
  simp only [Url.parse, String.toList_ofList, Url.toText, List.append_assoc, dropPrefix_append]
  exact Url.parseFields_toText valid

/-- The text of a URL is the only text that reads as that URL. -/
theorem Url.toText_of_parse {text : String} {url : Url} (h : Url.parse text = .ok url) :
    String.ofList url.toText = text := by
  unfold Url.parse at h
  split at h
  · rename_i rest hd
    rw [Url.toText_of_parseFields h, ← eq_append_of_dropPrefix _ _ _ hd, String.ofList_toList]
  · cases h

/-- A root signed with a private key verifies under the compressed public key of that key. -/
theorem Root.verify_sign {sk : Fn} {enrRoot linkRoot : Hash} {seq : Nat} {r : Root}
    {key : Vector UInt8 33} (h : Root.sign sk enrRoot linkRoot seq = .ok r)
    (hkey : (⟨key.toArray⟩ : ByteArray) = (Point.mul sk Point.generator).encodeCompressed) :
    r.verify key = true := by
  simp only [Root.sign, bind_ok_iff] at h
  obtain ⟨sig, hs, h⟩ := h
  cases h
  cases hsig : Ecdsa.sign sk (signingHash enrRoot linkRoot seq) with
  | error e => simp [hsig, Except.mapError] at hs
  | ok sig' =>
    simp only [hsig, Except.mapError, Except.ok.injEq] at hs
    subst hs
    simp [Root.verify, Rlpx.recoverSigner_signatureBytes hsig, hkey]

/-- Two errors with one code come from one constructor. -/
theorem DnsError.code_injective (e₁ e₂ : DnsError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [DnsError.code] at h; exact absurd h (by decide))

/-! ## Resolving a list -/

/-- Two walks from one state find the same, or the search finds a collision on their way. -/
theorem walk_binds {lookup1 lookup2 : String → Option String} {domain : String} :
    (budget : Nat) → (pending : List (Subtree × Hash)) → (visited : List Hash) →
      (found : Found) → {found1 found2 : Found} →
      walk lookup1 domain budget pending visited found = .ok found1 →
      walk lookup2 domain budget pending visited found = .ok found2 →
      found1 = found2 ∨ ∃ pair, walkCollision lookup1 lookup2 domain budget pending visited =
        some pair ∧ IsCollision pair := by
  intro budget
  induction budget with
  | zero =>
    intro pending visited found found1 found2 h1 h2
    cases pending with
    | nil => simp only [walk] at h1 h2; cases h1; cases h2; exact .inl rfl
    | cons _ _ => simp [walk] at h1
  | succ budget ih =>
    intro pending visited found found1 found2 h1 h2
    rcases pending with _ | ⟨⟨tree, hash⟩, pending⟩
    · simp only [walk] at h1 h2; cases h1; cases h2; exact .inl rfl
    by_cases hv : hash ∈ visited
    · simp only [walk, hv, ↓reduceIte] at h1 h2
      simp only [walkCollision, hv, ↓reduceIte]
      exact ih pending visited found h1 h2
    simp only [walk, hv, ↓reduceIte] at h1 h2
    simp only [walkCollision, hv, ↓reduceIte]
    rcases hl1 : lookup1 (nameOf hash domain) with _ | text1
    · simp [hl1] at h1
    rcases hl2 : lookup2 (nameOf hash domain) with _ | text2
    · simp [hl2] at h2
    simp only [hl1, hl2] at h1 h2 ⊢
    by_cases hh1 : hashOf text1 = hash
    swap
    · simp [hh1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h1
    by_cases hh2 : hashOf text2 = hash
    swap
    · simp [hh2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h2
    simp only [hh1, hh2, ↓reduceIte] at h1 h2
    by_cases he : text1 = text2
    swap
    · exact .inr ⟨(text1, text2), by simp [he, hh1, hh2], he, hh1.trans hh2.symm⟩
    subst he
    simp only [↓reduceIte]
    rcases hp : Entry.parse text1 with err | entry
    · simp [hp, bind, Except.bind] at h1
    simp only [hp, bind, Except.bind] at h1 h2 ⊢
    cases entry <;> cases tree <;>
      try first
        | exact ih _ _ _ h1 h2
        | (simp [throw, throwThe, MonadExceptOf.throw] at h1; done)
    -- A record under the root of records: the walk goes on only when it verifies.
    rename_i record
    by_cases hr : Enr.verifyV4 record = true
    · simp only [hr, ↓reduceIte] at h1 h2
      exact ih _ _ _ h1 h2
    · simp [hr, throw, throwThe, MonadExceptOf.throw] at h1

/-- A resolved list comes from a signed root at its domain and from the walk of its subtrees. -/
theorem resolve_ok {lookup : String → Option String} {key : Vector UInt8 33} {seenSeq : Nat}
    {domain : String} {budget : Nat} {list : Nat × Found}
    (h : resolve lookup key seenSeq domain budget = .ok list) :
    ∃ text root found, lookup domain = some text ∧ Entry.parse text = .ok (.root root) ∧
      root.verify key = true ∧ seenSeq ≤ root.seq ∧
      walk lookup domain budget [(.records, root.enrRoot), (.links, root.linkRoot)] [] ⟨[], []⟩ =
        .ok found ∧ list = (root.seq, found) := by
  unfold resolve at h
  rcases hl : lookup domain with _ | text
  · simp [hl, throw, throwThe, MonadExceptOf.throw] at h
  rcases hp : Entry.parse text with err | entry
  · simp [hl, hp, bind, Except.bind] at h
  cases entry with
  | root root =>
    by_cases hv : root.verify key = true
    swap
    · simp [hl, hp, hv, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    by_cases hs : seenSeq ≤ root.seq
    swap
    · simp [hl, hp, hv, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    rcases hw : walk lookup domain budget [(.records, root.enrRoot), (.links, root.linkRoot)] []
      ⟨[], []⟩ with err | found
    · simp [hl, hp, hv, hs, hw, bind, Except.bind] at h
    simp [hl, hp, hv, hs, hw, bind, Except.bind, pure, Except.pure] at h
    exact ⟨text, root, found, rfl, hp, hv, hs, hw, h.symm⟩
  | _ => simp [hl, hp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- The search for a collision between a lookup and itself finds nothing, from any state. -/
theorem walkCollision_self (lookup : String → Option String) (domain : String) :
    (budget : Nat) → (pending : List (Subtree × Hash)) → (visited : List Hash) →
      walkCollision lookup lookup domain budget pending visited = none := by
  intro budget
  induction budget with
  | zero => intro pending visited; cases pending <;> rfl
  | succ budget ih =>
    intro pending visited
    rcases pending with _ | ⟨⟨tree, hash⟩, pending⟩
    · rfl
    simp only [walkCollision]
    split
    · exact ih _ _
    split
    · rename_i text1 text2 h1 h2
      obtain rfl : text1 = text2 := Option.some.inj (h1.symm.trans h2)
      simp only [↓reduceIte]
      split <;> exact ih _ _
    · rfl

/-- Two resolvers that serve one root give one list, or the search finds a collision.

One root means the same subtree hashes and sequence number, whatever the text of its signature.

So a resolver that changes any entry below a signed root makes the walk fail or breaks Keccak-256.
-/
theorem resolve_binds {lookup1 lookup2 : String → Option String} {key : Vector UInt8 33}
    {seenSeq : Nat} {domain : String} {budget : Nat} {list1 list2 : Nat × Found}
    (same : rootFields lookup1 domain = rootFields lookup2 domain)
    (h1 : resolve lookup1 key seenSeq domain budget = .ok list1)
    (h2 : resolve lookup2 key seenSeq domain budget = .ok list2) :
    list1 = list2 ∨ ∃ pair, findCollision lookup1 lookup2 domain budget = some pair ∧
      IsCollision pair := by
  obtain ⟨text1, root1, found1, hl1, hp1, -, -, hw1, rfl⟩ := resolve_ok h1
  obtain ⟨text2, root2, found2, hl2, hp2, -, -, hw2, rfl⟩ := resolve_ok h2
  -- Both lookups give one root fields, so the two walks start from one state.
  have r1 : rootFields lookup1 domain = some (root1.enrRoot, root1.linkRoot, root1.seq) := by
    simp [rootFields, hl1, hp1]
  have r2 : rootFields lookup2 domain = some (root2.enrRoot, root2.linkRoot, root2.seq) := by
    simp [rootFields, hl2, hp2]
  rw [r1, r2] at same
  simp only [Option.some.injEq, Prod.mk.injEq] at same
  obtain ⟨e1, e2, e3⟩ := same
  rw [← e1, ← e2] at hw2
  rcases walk_binds budget _ _ _ hw1 hw2 with he | ⟨pair, hc, hpair⟩
  · exact .inl (by rw [he, e3])
  · refine .inr ⟨pair, ?_, hpair⟩
    simp only [findCollision, r1]
    exact hc

/-- A pair that the search finds from any state is a collision. -/
theorem isCollision_of_walkCollision {lookup1 lookup2 : String → Option String}
    {domain : String} {pair : String × String} :
    (budget : Nat) → (pending : List (Subtree × Hash)) → (visited : List Hash) →
      walkCollision lookup1 lookup2 domain budget pending visited = some pair →
      IsCollision pair := by
  intro budget
  induction budget with
  | zero => intro pending visited h; cases pending <;> cases h
  | succ budget ih =>
    intro pending visited h
    rcases pending with _ | ⟨⟨tree, hash⟩, pending⟩
    · cases h
    simp only [walkCollision] at h
    split at h
    · exact ih _ _ h
    split at h
    · rename_i text1 text2 _ _
      by_cases he : text1 = text2
      · simp only [he, ↓reduceIte] at h
        split at h <;> exact ih _ _ h
      · by_cases hh : hashOf text1 = hashOf text2
        · simp only [he, hh, ↓reduceIte, Option.some.injEq] at h
          subst h
          exact ⟨he, hh⟩
        · simp [he, hh] at h
    · cases h

/-- A pair that the search finds is a collision, with no other condition. -/
theorem isCollision_of_findCollision {lookup1 lookup2 : String → Option String} {domain : String}
    {budget : Nat} {pair : String × String}
    (h : findCollision lookup1 lookup2 domain budget = some pair) : IsCollision pair := by
  unfold findCollision at h
  split at h
  · exact isCollision_of_walkCollision _ _ _ h
  · cases h

/-- The search finds nothing when both lookups are one, so a found collision is not a given. -/
theorem findCollision_self (lookup : String → Option String) (domain : String) (budget : Nat) :
    findCollision lookup lookup domain budget = none := by
  unfold findCollision
  split
  · exact walkCollision_self _ _ _ _ _
  · rfl

/-- A list resolves only with a sequence number at least the one seen last. -/
theorem le_seq_of_resolve {lookup : String → Option String} {key : Vector UInt8 33}
    {seenSeq : Nat} {domain : String} {budget : Nat} {list : Nat × Found}
    (h : resolve lookup key seenSeq domain budget = .ok list) : seenSeq ≤ list.1 := by
  obtain ⟨-, root, -, -, -, -, hs, -, rfl⟩ := resolve_ok h
  exact hs

/-- A list resolves only from a root at its domain whose signature verifies under the key.

The list has the sequence number of that root. -/
theorem verify_of_resolve {lookup : String → Option String} {key : Vector UInt8 33}
    {seenSeq : Nat} {domain : String} {budget : Nat} {list : Nat × Found}
    (h : resolve lookup key seenSeq domain budget = .ok list) :
    ∃ text root, lookup domain = some text ∧ Entry.parse text = .ok (.root root) ∧
      root.verify key = true ∧ root.seq = list.1 := by
  obtain ⟨text, root, -, hl, hp, hv, -, -, rfl⟩ := resolve_ok h
  exact ⟨text, root, hl, hp, hv, rfl⟩

end EthLib.Networking.DnsDisc
