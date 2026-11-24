module

public import EthLib.Networking.DnsDisc
public import EthLib.Networking.Proofs.Encoding.Base32
public import EthLib.Base.Proofs.Base64
public import EthLib.Base.Proofs.Bytes
public import EthLib.Base.Proofs.List
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
open EthLib.Networking.Encoding
open EthLib.Cryptography.Secp256k1

/-- The entries for which the text round trip holds.

A link names a point of the curve, and a record reads back from its own bytes. -/
def Entry.Valid : Entry → Prop
  | .link url => (Point.decode ⟨url.key.toArray⟩).toBool = true
  | .enr record => ∀ bytes, record.encode = .ok bytes → Enr.decode bytes = .ok record
  | _ => True

/-! ## Prefixes -/

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
    dropPrefix? ROOT_PREFIX (BRANCH_PREFIX ++ cs) = none := by
  simp [ROOT_PREFIX_eq, BRANCH_PREFIX_eq, dropPrefix?]

/-- A link does not start with the prefix of a root. -/
theorem dropPrefix_root_url (cs : List Char) :
    dropPrefix? ROOT_PREFIX (URL_PREFIX ++ cs) = none := by
  simp [ROOT_PREFIX_eq, URL_PREFIX_eq, dropPrefix?]

/-- A link does not start with the prefix of a branch. -/
theorem dropPrefix_branch_url (cs : List Char) :
    dropPrefix? BRANCH_PREFIX (URL_PREFIX ++ cs) = none := by
  simp [BRANCH_PREFIX_eq, URL_PREFIX_eq, dropPrefix?]

/-- A record does not start with the prefix of a root. -/
theorem dropPrefix_root_enr (cs : List Char) :
    dropPrefix? ROOT_PREFIX (Enr.TEXT_PREFIX ++ cs) = none := by
  simp [ROOT_PREFIX_eq, Enr.TEXT_PREFIX, dropPrefix?]

/-- A record does not start with the prefix of a branch. -/
theorem dropPrefix_branch_enr (cs : List Char) :
    dropPrefix? BRANCH_PREFIX (Enr.TEXT_PREFIX ++ cs) = none := by
  simp [BRANCH_PREFIX_eq, Enr.TEXT_PREFIX, dropPrefix?]

/-- A record does not start with the prefix of a link. -/
theorem dropPrefix_url_enr (cs : List Char) :
    dropPrefix? URL_PREFIX (Enr.TEXT_PREFIX ++ cs) = none := by
  simp [URL_PREFIX_eq, Enr.TEXT_PREFIX, dropPrefix?]

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
  -- The digits of the decimal form give back the number.
  have digits : Nat.ofDigitChars 10 (Nat.repr n).toList 0 = n := by
    rw [Nat.toList_repr]
    exact Nat.ofDigitChars_toDigits (by decide) (by decide)
  simp only [seqOf, digits, ↓reduceIte]
  rfl

/-- The decimal text of a sequence number is the only text that reads as that number. -/
theorem repr_of_seqOf {cs : List Char} {n : Nat} (h : seqOf cs = .ok n) :
    (Nat.repr n).toList = cs := by
  unfold seqOf at h
  by_cases same : Nat.toDigits 10 (Nat.ofDigitChars 10 cs 0) = cs
  · simp only [Nat.toList_repr, same, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    rw [← h, Nat.toList_repr]
    exact same
  · simp [Nat.toList_repr, same, throw, throwThe, MonadExceptOf.throw] at h

/-! ## Roots -/

/-- The text of a root after its prefix. -/
theorem Root.dropPrefix_toText (r : Root) :
    dropPrefix? ROOT_PREFIX r.toText = some (r.enrRoot.toText ++ " l=".toList ++
      r.linkRoot.toText ++ " seq=".toList ++ (Nat.repr r.seq).toList ++ " sig=".toList ++
      Base64.encodeList r.signature.toList) := by
  simp only [Root.toText, signedText, List.append_assoc, dropPrefix?_append]

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
    Hash.ofText_toText, dropPrefix?_append, List.take_left' hl, List.drop_left' hl, bind,
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
    eq_append_of_dropPrefix? h2, ← List.take_append_drop HASH_TEXT_SIZE rest2,
    ← Hash.toText_of_ofText hl, eq_append_of_dropPrefix? h3,
    ← List.take_append_drop tail rest3, ← repr_of_seqOf hs, eq_append_of_dropPrefix? h4,
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
    simp only [Entry.parse, String.toList_ofList, dropPrefix_root_branch, dropPrefix?_append,
      branchOf_hashesText]
    rfl
  | link url =>
    simp only [Entry.toText, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Entry.parse, String.toList_ofList, Url.toText, List.append_assoc,
      dropPrefix_root_url, dropPrefix_branch_url, dropPrefix?_append, Url.parseFields_toText valid]
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
      dropPrefix_url_enr, dropPrefix?_append, back]
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
      simp only [Entry.toText, Root.toText_of_parseFields hp, ← eq_append_of_dropPrefix? hd,
        String.ofList_toList]
      rfl
  split at h
  · rename_i rest hd
    cases hp : branchOf rest with
    | error err => simp [hp, Functor.map, Except.map] at h
    | ok hashes =>
      simp only [hp, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      simp only [Entry.toText, hashesText_of_branchOf hp, ← eq_append_of_dropPrefix? hd,
        String.ofList_toList]
      rfl
  split at h
  · rename_i rest hd
    cases hp : Url.parseFields rest with
    | error err => simp [hp, Functor.map, Except.map] at h
    | ok url =>
      simp only [hp, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      simp only [Entry.toText, Url.toText_of_parseFields hp, ← eq_append_of_dropPrefix? hd,
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
  simp only [Url.parse, String.toList_ofList, Url.toText, List.append_assoc, dropPrefix?_append]
  exact Url.parseFields_toText valid

/-- The text of a URL is the only text that reads as that URL. -/
theorem Url.toText_of_parse {text : String} {url : Url} (h : Url.parse text = .ok url) :
    String.ofList url.toText = text := by
  unfold Url.parse at h
  split at h
  · rename_i rest hd
    rw [Url.toText_of_parseFields h, ← eq_append_of_dropPrefix? hd, String.ofList_toList]
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
    (budget : Nat) → (pending : List (Subtree × Hash)) → (visited : List (Subtree × Hash)) →
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
    by_cases hv : (tree, hash) ∈ visited
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
    (budget : Nat) → (pending : List (Subtree × Hash)) → (visited : List (Subtree × Hash)) →
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
    (budget : Nat) → (pending : List (Subtree × Hash)) → (visited : List (Subtree × Hash)) →
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

/-! ## The subtree of each entry -/

/-- The hashes reached from a hash, through the branches at their names. -/
inductive Reaches (lookup : String → Option String) (domain : String) (top : Hash) : Hash → Prop
  /-- The hash it starts from. -/
  | top : Reaches lookup domain top top
  /-- A hash of the branch at the name of a hash that the subtree reaches. -/
  | branch {hash next : Hash} {text : String} {hashes : List Hash} :
      Reaches lookup domain top hash → lookup (nameOf hash domain) = some text →
      Entry.parse text = .ok (.branch hashes) → next ∈ hashes → Reaches lookup domain top next

/-- The entries that a subtree may hold: branches, and its node records or its links. -/
def Subtree.Holds : Subtree → Entry → Prop
  | _, .branch _ => True
  | .records, .enr _ => True
  | .links, .link _ => True
  | _, _ => False

/-- Hashes read with their subtrees, each at a name whose entry that subtree may hold.

Each hash of a branch is read with the same subtree, or is still to read. -/
def Closed (lookup : String → Option String) (domain : String)
    (read pending : List (Subtree × Hash)) : Prop :=
  ∀ p ∈ read, ∃ text e, lookup (nameOf p.2 domain) = some text ∧ Entry.parse text = .ok e ∧
    p.1.Holds e ∧ ∀ hashes, e = .branch hashes → ∀ next ∈ hashes,
      (p.1, next) ∈ read ∨ (p.1, next) ∈ pending

/-- Take a walk that succeeds, from hashes read that each name an entry their subtree may hold.

The hashes of each branch read are read or still to read.

Then the walk reads every hash still to read, and leaves nothing of a branch unread. -/
theorem walk_closed {lookup : String → Option String} {domain : String} :
    (budget : Nat) → (pending visited : List (Subtree × Hash)) → (found : Found) →
      {result : Found} → walk lookup domain budget pending visited found = .ok result →
      Closed lookup domain visited pending →
      ∃ read, (∀ p, p ∈ visited ∨ p ∈ pending → p ∈ read) ∧ Closed lookup domain read [] := by
  intro budget
  induction budget with
  | zero =>
    intro pending visited found result h hc
    cases pending with
    | nil => exact ⟨visited, fun p hp => by simpa using hp, hc⟩
    | cons _ _ => simp [walk] at h
  | succ budget ih =>
    intro pending visited found result h hc
    rcases pending with _ | ⟨⟨tree, hash⟩, pending⟩
    · exact ⟨visited, fun p hp => by simpa using hp, hc⟩
    by_cases hv : (tree, hash) ∈ visited
    · simp only [walk, hv, ↓reduceIte] at h
      -- The hash is read already, so the hashes of each branch are read or still to read.
      have hc2 : Closed lookup domain visited pending := by
        intro p hp
        obtain ⟨text, e, hl, hpe, holds, hb⟩ := hc p hp
        refine ⟨text, e, hl, hpe, holds, fun hashes he next hn => ?_⟩
        rcases hb hashes he next hn with m | m
        · exact .inl m
        · rcases List.mem_cons.1 m with m | m
          · exact .inl (m ▸ hv)
          · exact .inr m
      obtain ⟨read, sub, closed⟩ := ih pending visited found h hc2
      refine ⟨read, fun p hp => sub p ?_, closed⟩
      rcases hp with hp | hp
      · exact .inl hp
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact .inl hv
        · exact .inr hp
    simp only [walk, hv, ↓reduceIte] at h
    rcases hl : lookup (nameOf hash domain) with _ | text
    · simp [hl] at h
    simp only [hl] at h
    by_cases hh : hashOf text = hash
    swap
    · simp [hh, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    simp only [hh, ↓reduceIte] at h
    rcases hp : Entry.parse text with err | entry
    · simp [hp, bind, Except.bind] at h
    simp only [hp, bind, Except.bind] at h
    -- The walk reads the hash, then goes on with every hash of its entry still to read.
    have step : ∀ next : List (Subtree × Hash), tree.Holds entry →
        (∀ hashes, entry = .branch hashes → ∀ n ∈ hashes, (tree, n) ∈ next) →
        (∀ p ∈ pending, p ∈ next) → ∀ found0,
        walk lookup domain budget next ((tree, hash) :: visited) found0 = .ok result →
        ∃ read, (∀ p, p ∈ visited ∨ p ∈ (tree, hash) :: pending → p ∈ read) ∧
          Closed lookup domain read [] := by
      intro next holds children rest found0 hw
      have hc2 : Closed lookup domain ((tree, hash) :: visited) next := by
        intro p hmem
        rcases List.mem_cons.1 hmem with rfl | hmem
        · exact ⟨text, entry, hl, hp, holds, fun hashes he n hn => .inr (children hashes he n hn)⟩
        obtain ⟨text2, e, hl2, hpe, holds2, hb⟩ := hc p hmem
        refine ⟨text2, e, hl2, hpe, holds2, fun hashes he n hn => ?_⟩
        rcases hb hashes he n hn with m | m
        · exact .inl (List.mem_cons_of_mem _ m)
        · rcases List.mem_cons.1 m with m | m
          · exact .inl (m ▸ List.mem_cons_self)
          · exact .inr (rest _ m)
      obtain ⟨read, sub, closed⟩ := ih next _ found0 hw hc2
      refine ⟨read, fun p hmem => sub p ?_, closed⟩
      rcases hmem with hmem | hmem
      · exact .inl (List.mem_cons_of_mem _ hmem)
      · rcases List.mem_cons.1 hmem with rfl | hmem
        · exact .inl List.mem_cons_self
        · exact .inr (rest _ hmem)
    cases entry with
    | branch hashes =>
      exact step _ (by cases tree <;> trivial)
        (fun _ he n hn => by
          cases he
          exact List.mem_append_left _ (List.mem_map_of_mem hn))
        (fun _ m => List.mem_append_right _ m) _ (by cases tree <;> exact h)
    | enr record =>
      cases tree with
      | records =>
        by_cases hr : Enr.verifyV4 record = true
        · simp only [hr, ↓reduceIte] at h
          exact step _ trivial (fun _ he => by cases he) (fun _ m => m) _ h
        · simp [hr, throw, throwThe, MonadExceptOf.throw] at h
      | links => simp [throw, throwThe, MonadExceptOf.throw] at h
    | link url =>
      cases tree with
      | records => simp [throw, throwThe, MonadExceptOf.throw] at h
      | links => exact step _ trivial (fun _ he => by cases he) (fun _ m => m) _ h
    | root r => cases tree <;> simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Take hashes read that leave nothing of a branch unread.

A hash reached from a hash read with a subtree is then read with that subtree. -/
theorem mem_of_reaches {lookup : String → Option String} {domain : String}
    {read : List (Subtree × Hash)} (closed : Closed lookup domain read []) {tree : Subtree}
    {top hash : Hash} (start : (tree, top) ∈ read) (reach : Reaches lookup domain top hash) :
    (tree, hash) ∈ read := by
  induction reach with
  | top => exact start
  | @branch hash next text hashes _ hl hp hn ih =>
    obtain ⟨text2, e, hl2, hp2, -, hb⟩ := closed _ ih
    obtain rfl : text2 = text := Option.some.inj (hl2.symm.trans hl)
    rw [hp] at hp2
    cases hp2
    rcases hb hashes rfl next hn with m | m
    · exact m
    · cases m

/-- A resolved list reads both subtrees of its root, and every hash that they reach. -/
theorem closed_of_resolve {lookup : String → Option String} {key : Vector UInt8 33}
    {seenSeq : Nat} {domain : String} {budget : Nat} {list : Nat × Found} {text : String}
    {root : Root} (h : resolve lookup key seenSeq domain budget = .ok list)
    (hl : lookup domain = some text) (hp : Entry.parse text = .ok (.root root)) :
    ∃ read, (.records, root.enrRoot) ∈ read ∧ (.links, root.linkRoot) ∈ read ∧
      Closed lookup domain read [] := by
  obtain ⟨text2, root2, found, hl2, hp2, -, -, hw, -⟩ := resolve_ok h
  obtain rfl : text2 = text := Option.some.inj (hl2.symm.trans hl)
  rw [hp] at hp2
  cases hp2
  obtain ⟨read, sub, closed⟩ := walk_closed budget _ [] _ hw (fun _ m => by cases m)
  exact ⟨read, sub _ (.inr (by simp)), sub _ (.inr (by simp)), closed⟩

/-- In a resolved list, each entry that the subtree of node records reaches is a branch or a record.

The root is the one at the domain of the list. -/
theorem records_of_resolve {lookup : String → Option String} {key : Vector UInt8 33}
    {seenSeq : Nat} {domain : String} {budget : Nat} {list : Nat × Found} {text : String}
    {root : Root} (h : resolve lookup key seenSeq domain budget = .ok list)
    (hl : lookup domain = some text) (hp : Entry.parse text = .ok (.root root)) {hash : Hash}
    {entryText : String} {e : Entry} (reach : Reaches lookup domain root.enrRoot hash)
    (he : lookup (nameOf hash domain) = some entryText) (hpe : Entry.parse entryText = .ok e) :
    (∃ hashes, e = .branch hashes) ∨ ∃ record, e = .enr record := by
  obtain ⟨read, start, -, closed⟩ := closed_of_resolve h hl hp
  obtain ⟨text2, e2, hl2, hp2, holds, -⟩ := closed _ (mem_of_reaches closed start reach)
  obtain rfl : text2 = entryText := Option.some.inj (hl2.symm.trans he)
  rw [hpe] at hp2
  cases hp2
  cases e <;> simp_all [Subtree.Holds]

/-- In a resolved list, each entry that the subtree of links reaches is a branch or a link.

The root is the one at the domain of the list. -/
theorem links_of_resolve {lookup : String → Option String} {key : Vector UInt8 33}
    {seenSeq : Nat} {domain : String} {budget : Nat} {list : Nat × Found} {text : String}
    {root : Root} (h : resolve lookup key seenSeq domain budget = .ok list)
    (hl : lookup domain = some text) (hp : Entry.parse text = .ok (.root root)) {hash : Hash}
    {entryText : String} {e : Entry} (reach : Reaches lookup domain root.linkRoot hash)
    (he : lookup (nameOf hash domain) = some entryText) (hpe : Entry.parse entryText = .ok e) :
    (∃ hashes, e = .branch hashes) ∨ ∃ url, e = .link url := by
  obtain ⟨read, -, start, closed⟩ := closed_of_resolve h hl hp
  obtain ⟨text2, e2, hl2, hp2, holds, -⟩ := closed _ (mem_of_reaches closed start reach)
  obtain rfl : text2 = entryText := Option.some.inj (hl2.symm.trans he)
  rw [hpe] at hp2
  cases hp2
  cases e <;> simp_all [Subtree.Holds]

end EthLib.Networking.DnsDisc
