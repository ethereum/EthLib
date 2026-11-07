module

public import EthLib.Networking.Gossip.Topic

/-!
# `Networking.Proofs.Gossip.Topic`

The parser of topic strings inverts the printer.

- Every topic string of a name without `/` parses back to its fork digest and its name.
- Every string that parses is the topic string of what it parses to.
- The same two facts hold for the subnet ID in the name of a subnet topic.
- Each parser accepts exactly what its printer writes, for a topic name without `/`.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Topic

open EthLib.Networking.Gossip

/-! ## Prefixes and suffixes -/

/-- A list that starts with a prefix gives back the rest. -/
theorem dropPrefix?_append (pre rest : List Char) :
    dropPrefix? pre (pre ++ rest) = some rest := by
  simp [dropPrefix?]

/-- A list that gives back a rest is the prefix followed by the rest. -/
theorem eq_append_of_dropPrefix? {pre cs rest : List Char}
    (h : dropPrefix? pre cs = some rest) : cs = pre ++ rest := by
  unfold dropPrefix? at h
  split at h
  · rename_i hp
    cases h
    exact (List.prefix_iff_eq_append.mp (List.isPrefixOf_iff_prefix.mp hp)).symm
  · cases h

/-- A list that ends with a suffix gives back the start. -/
theorem dropSuffix?_append (start suf : List Char) :
    dropSuffix? suf (start ++ suf) = some start := by
  simp [dropSuffix?]

/-- A list that gives back a start is the start followed by the suffix. -/
theorem eq_append_of_dropSuffix? {suf cs start : List Char}
    (h : dropSuffix? suf cs = some start) : cs = start ++ suf := by
  unfold dropSuffix? at h
  split at h
  · rename_i hs
    cases h
    exact (List.suffix_iff_eq_append.mp (List.isSuffixOf_iff_suffix.mp hs)).symm
  · cases h

/-! ## The fork digest -/

/-- The hex digit of a value below 16 reads back as that value. -/
theorem hexDigit?_hexDigitChar : ∀ k : Fin 16, hexDigit? (Base.hexDigitChar k) = some k.val := by
  decide

/-- A character that reads as a value is the hex digit of that value, below 16. -/
theorem hexDigit?_eq_some {c : Char} {k : Nat} (h : hexDigit? c = some k) :
    ∃ hk : k < 16, Base.hexDigitChar ⟨k, hk⟩ = c := by
  unfold hexDigit? at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i.isLt, by simpa using List.find?_some hi⟩

/-- The two hex digits of a byte read back as that byte. -/
theorem hexByte?_hexDigitChar (byte : UInt8) :
    hexByte? (Base.hexDigitChar ⟨byte.toNat / 16, by have := byte.toNat_lt; omega⟩)
      (Base.hexDigitChar ⟨byte.toNat % 16, by omega⟩) = some byte := by
  simp only [hexByte?, hexDigit?_hexDigitChar, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Nat.div_add_mod, UInt8.ofNat_toNat]

/-- Two characters that read as a byte are the two hex digits of that byte. -/
theorem byteHexDigits_of_hexByte? {hi lo : Char} {byte : UInt8}
    (h : hexByte? hi lo = some byte) : Base.byteHexDigits byte = [hi, lo] := by
  simp only [hexByte?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨k, hk, l, hl, rfl⟩ := h
  obtain ⟨hk16, rfl⟩ := hexDigit?_eq_some hk
  obtain ⟨hl16, rfl⟩ := hexDigit?_eq_some hl
  have : (UInt8.ofNat (16 * k + l)).toNat = 16 * k + l := by
    rw [UInt8.toNat_ofNat']
    omega
  simp only [Base.byteHexDigits, this]
  congr 4 <;> omega

/-- Two characters read as a byte exactly when they are the two hex digits of that byte. -/
theorem hexByte?_eq_some_iff (hi lo : Char) (byte : UInt8) :
    hexByte? hi lo = some byte ↔ Base.byteHexDigits byte = [hi, lo] := by
  refine ⟨byteHexDigits_of_hexByte?, fun h => ?_⟩
  simp only [Base.byteHexDigits, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  exact hexByte?_hexDigitChar byte

/-- A fork digest is its four bytes. -/
theorem vector_four (v : Vector UInt8 4) : v = #v[v[0], v[1], v[2], v[3]] := by
  apply Vector.ext
  intro i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

/-- A fork digest has eight hex digits. -/
theorem forkDigestChars_length (digest : Vector UInt8 4) :
    (forkDigestChars digest).length = 8 := by
  rw [vector_four digest]
  simp [forkDigestChars, Base.byteHexDigits]

/-- The hex digits of a fork digest read back as that digest. -/
theorem parseForkDigest_forkDigestChars (digest : Vector UInt8 4) :
    parseForkDigest (forkDigestChars digest) = some digest := by
  rw [vector_four digest]
  simp [forkDigestChars, Base.byteHexDigits, parseForkDigest, hexByte?_hexDigitChar]

/-- Characters that read as a fork digest are the hex digits of that digest. -/
theorem forkDigestChars_of_parseForkDigest {cs : List Char} {digest : Vector UInt8 4}
    (h : parseForkDigest cs = some digest) : forkDigestChars digest = cs := by
  unfold parseForkDigest at h
  split at h
  · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨w, hw, x, hx, y, hy, z, hz, rfl⟩ := h
    simp [forkDigestChars, byteHexDigits_of_hexByte? hw, byteHexDigits_of_hexByte? hx,
      byteHexDigits_of_hexByte? hy, byteHexDigits_of_hexByte? hz]
  · cases h

/-- Characters read as a fork digest exactly when they are the hex digits of that digest. -/
theorem parseForkDigest_eq_some_iff (cs : List Char) (digest : Vector UInt8 4) :
    parseForkDigest cs = some digest ↔ forkDigestChars digest = cs :=
  ⟨forkDigestChars_of_parseForkDigest, fun h => h ▸ parseForkDigest_forkDigestChars digest⟩

/-! ## Topic strings -/

/-- The characters of a topic string, part by part. -/
theorem toList_topicString (digest : Vector UInt8 4) (name : String) :
    (topicString digest name).toList = "/eth2/".toList ++
      (forkDigestChars digest ++ (['/'] ++ (name.toList ++ "/ssz_snappy".toList))) := by
  simp [topicString]

/-- A topic string of a name without `/` parses back to its fork digest and its name. -/
theorem parseTopic_topicString (digest : Vector UInt8 4) {name : String}
    (h : '/' ∉ name.toList) : parseTopic (topicString digest name) = .ok (digest, name) := by
  have length := forkDigestChars_length digest
  unfold parseTopic
  rw [toList_topicString, dropPrefix?_append]
  simp only [List.take_left' length, List.drop_left' length, parseForkDigest_forkDigestChars,
    dropPrefix?_append, dropSuffix?_append]
  simp [h]
  rfl

/-- A string that parses is the topic string of its fork digest and its name. -/
theorem topicString_of_parseTopic {topic name : String} {digest : Vector UInt8 4}
    (h : parseTopic topic = .ok (digest, name)) : topicString digest name = topic := by
  unfold parseTopic at h
  split at h
  next rest hrest =>
    split at h
    next d hd =>
      split at h
      next body hbody =>
        split at h
        next chars hchars =>
          split at h
          · cases h
          · cases h
            have hr :
                rest = forkDigestChars digest ++ (['/'] ++ (chars ++ "/ssz_snappy".toList)) := by
              rw [← List.take_append_drop 8 rest, forkDigestChars_of_parseForkDigest hd,
                eq_append_of_dropPrefix? hbody, eq_append_of_dropSuffix? hchars]
            apply String.toList_injective
            rw [toList_topicString, String.toList_ofList, eq_append_of_dropPrefix? hrest, hr]
            simp
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-- The name that a topic string parses to contains no `/`. -/
theorem slash_not_mem_of_parseTopic {topic name : String} {digest : Vector UInt8 4}
    (h : parseTopic topic = .ok (digest, name)) : '/' ∉ name.toList := by
  unfold parseTopic at h
  split at h
  next rest hrest =>
    split at h
    next d hd =>
      split at h
      next body hbody =>
        split at h
        next chars hchars =>
          split at h
          · cases h
          · rename_i hslash
            cases h
            simpa using hslash
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-- A string parses to a fork digest and a name exactly when it is their topic string.

The name must also contain no `/`. -/
theorem parseTopic_eq_ok_iff (topic : String) (digest : Vector UInt8 4) (name : String) :
    parseTopic topic = .ok (digest, name) ↔
      topicString digest name = topic ∧ '/' ∉ name.toList :=
  ⟨fun h => ⟨topicString_of_parseTopic h, slash_not_mem_of_parseTopic h⟩,
    fun ⟨h, hs⟩ => h ▸ parseTopic_topicString digest hs⟩

/-! ## Subnet topics -/

/-- Reading the decimal digits of a number gives the number. -/
theorem foldl_toDigits (n : Nat) :
    (Nat.toDigits 10 n).foldl (fun acc c => 10 * acc + (c.toNat - 48)) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · simp [Nat.toNat_digitChar_sub_48_of_lt_ten ‹_›]
    · rw [List.foldl_append, ih (n / 10) (by omega)]
      simp [Nat.toNat_digitChar_sub_48_of_lt_ten (Nat.mod_lt n (by decide))]
      omega

/-- The decimal digits of a subnet ID read back as that ID. -/
theorem parseSubnetId_toDigits (subnetId : SubnetID) :
    parseSubnetId (Nat.toDigits 10 subnetId.toNat) = some subnetId := by
  simpa [parseSubnetId, foldl_toDigits] using subnetId.toNat_lt

/-- Characters that read as a subnet ID are the decimal digits of that ID. -/
theorem toDigits_of_parseSubnetId {digits : List Char} {subnetId : SubnetID}
    (h : parseSubnetId digits = some subnetId) : Nat.toDigits 10 subnetId.toNat = digits := by
  simp only [parseSubnetId] at h
  split at h
  · rename_i hv
    cases h
    simp only [Char.reduceToNat] at hv
    simp [Nat.mod_eq_of_lt hv.1, hv.2]
  · cases h

/-- The name of a subnet topic parses back to its subnet ID. -/
theorem parseSubnetTopicName_subnetTopicName (base : String) (subnetId : SubnetID) :
    parseSubnetTopicName base (subnetTopicName base subnetId) = some subnetId := by
  have : (subnetTopicName base subnetId).toList =
      (base ++ "_").toList ++ Nat.toDigits 10 subnetId.toNat := by
    simp [subnetTopicName]
  rw [parseSubnetTopicName, this, dropPrefix?_append, Option.bind_some, parseSubnetId_toDigits]

/-- A name that parses is the name of the subnet topic of what it parses to. -/
theorem subnetTopicName_of_parseSubnetTopicName {base name : String} {subnetId : SubnetID}
    (h : parseSubnetTopicName base name = some subnetId) :
    subnetTopicName base subnetId = name := by
  simp only [parseSubnetTopicName, Option.bind_eq_some_iff] at h
  obtain ⟨digits, hd, hs⟩ := h
  apply String.toList_injective
  rw [eq_append_of_dropPrefix? hd, ← toDigits_of_parseSubnetId hs]
  simp [subnetTopicName]

/-- The name of a subnet topic contains `/` only if its base name does. -/
theorem slash_not_mem_subnetTopicName {base : String} (h : '/' ∉ base.toList)
    (subnetId : SubnetID) : '/' ∉ (subnetTopicName base subnetId).toList := by
  simp only [subnetTopicName, String.toList_append, Nat.toList_repr, List.mem_append]
  intro hm
  rcases hm with (hm | hm) | hm
  · exact h hm
  · simp at hm
  · have := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hm
    exact absurd this (by decide)

/-- Characters read as a subnet ID exactly when they are the decimal digits of that ID. -/
theorem parseSubnetId_eq_some_iff (digits : List Char) (subnetId : SubnetID) :
    parseSubnetId digits = some subnetId ↔ Nat.toDigits 10 subnetId.toNat = digits :=
  ⟨toDigits_of_parseSubnetId, fun h => h ▸ parseSubnetId_toDigits subnetId⟩

/-- A name parses to a subnet ID exactly when it is the name of that subnet's topic. -/
theorem parseSubnetTopicName_eq_some_iff (base name : String) (subnetId : SubnetID) :
    parseSubnetTopicName base name = some subnetId ↔ subnetTopicName base subnetId = name :=
  ⟨subnetTopicName_of_parseSubnetTopicName,
    fun h => h ▸ parseSubnetTopicName_subnetTopicName base subnetId⟩

end EthLib.Networking.Proofs.Gossip.Topic
