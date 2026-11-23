module

public import EthLib.Base.Json.Document
public import EthLib.Base.Proofs.Json
public import EthLib.Base.Proofs.Json.Escape
public import EthLib.Base.Proofs.Json.Number
public import Std.Data.TreeMap.Raw.Lemmas
public import Std.Data.TreeMap.Raw.WF

/-!
# Proofs: a printed document reads back

The printer writes a text that the reader reads back, for a document whose objects repeat no name.

The reader rebuilds each object from its members, in increasing order of names.

So the document read back holds the same names and values, though a tree may differ in shape.

A name looked up in a rebuilt object gives the rebuilt value that the object held under it.
-/

@[expose] public section

namespace EthLib.Base.Json

open Lean

/-- No object of a document repeats a name, at any depth. -/
inductive Distinct : Lean.Json → Prop
  | null : Distinct .null
  | bool (b : Bool) : Distinct (.bool b)
  | num (number : JsonNumber) : Distinct (.num number)
  | str (text : String) : Distinct (.str text)
  | arr {items : Array Lean.Json} (each : ∀ item ∈ items, Distinct item) : Distinct (.arr items)
  | obj {members : Std.TreeMap.Raw String Lean.Json} (names : members.keys.Nodup)
      (each : ∀ name item, (name, item) ∈ members.toList → Distinct item) :
      Distinct (.obj members)

mutual

/-- The document that the reader builds from the text of a document whose objects repeat no name.

Each object is rebuilt from its members, in increasing order of names. -/
def canonical (document : Lean.Json) : Lean.Json :=
  match document with
  | .arr ⟨items⟩ => .arr ⟨canonicalItems items⟩
  | .obj ⟨⟨members⟩⟩ => .obj (canonicalMembers members ∅)
  | document => document
termination_by structural document

/-- The rebuilt items of an array. -/
def canonicalItems (items : List Lean.Json) : List Lean.Json :=
  match items with
  | [] => []
  | item :: rest => canonical item :: canonicalItems rest
termination_by structural items

/-- The rebuilt members of an object, inserted in increasing order of names after the others. -/
def canonicalMembers (members : Std.DTreeMap.Internal.Impl String fun _ => Lean.Json)
    (acc : Std.TreeMap.Raw String Lean.Json) : Std.TreeMap.Raw String Lean.Json :=
  match members with
  | .leaf => acc
  | .inner _ name item left right =>
    canonicalMembers right ((canonicalMembers left acc).insert name (canonical item))
termination_by structural members

end

/-! ## The members of an object in order -/

/-- The members of a tree, in order. -/
private def inorder : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) →
    List (String × Lean.Json)
  | .leaf => []
  | .inner _ name item left right => inorder left ++ (name, item) :: inorder right

private theorem inorder_eq (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    inorder t = t.toListModel.map fun e => (e.1, e.2) := by
  induction t with
  | leaf => rfl
  | inner _ k v l r ihl ihr => simp [inorder, ihl, ihr]

private theorem toList_mk (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    (⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json).toList = inorder t := by
  rw [inorder_eq, ← Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map]
  rfl

private theorem keys_mk (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    (⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json).keys = (inorder t).map Prod.fst := by
  rw [← toList_mk, Std.TreeMap.Raw.map_fst_toList_eq_keys]

/-- Induction over documents, with a hypothesis for each item and each member. -/
private theorem induct (P : Lean.Json → Prop) (null : P .null) (bool : ∀ b, P (.bool b))
    (num : ∀ n, P (.num n)) (str : ∀ s, P (.str s))
    (arr : ∀ items : List Lean.Json, (∀ x ∈ items, P x) → P (.arr ⟨items⟩))
    (obj : ∀ t, (∀ p ∈ inorder t, P p.2) → P (.obj ⟨⟨t⟩⟩)) (j : Lean.Json) : P j :=
  go j
where
  go (j : Lean.Json) : P j := match j with
    | .null => null
    | .bool b => bool b
    | .num n => num n
    | .str s => str s
    | .arr ⟨items⟩ => arr items (goItems items)
    | .obj ⟨⟨t⟩⟩ => obj t (goMembers t)
  termination_by structural j
  goItems (items : List Lean.Json) : ∀ x ∈ items, P x := match items with
    | [] => by simp
    | x :: xs => List.forall_mem_cons.2 ⟨go x, goItems xs⟩
  termination_by structural items
  goMembers (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
      ∀ p ∈ inorder t, P p.2 := match t with
    | .leaf => by simp [inorder]
    | .inner _ k v l r => by
      have hl := goMembers l
      have hv := go v
      have hr := goMembers r
      simp only [inorder, List.mem_append, List.mem_cons]
      rintro p (hp | rfl | hp)
      · exact hl p hp
      · exact hv
      · exact hr p hp
  termination_by structural t

/-! ## Inserting members in order -/

/-- The members of a list inserted in order, each value mapped first. -/
private def insertAll (g : Lean.Json → Lean.Json) (l : List (String × Lean.Json))
    (acc : Std.TreeMap.Raw String Lean.Json) : Std.TreeMap.Raw String Lean.Json :=
  l.foldl (fun a p => a.insert p.1 (g p.2)) acc

private theorem insertAll_wf (g : Lean.Json → Lean.Json) :
    ∀ (l : List (String × Lean.Json)) (acc : Std.TreeMap.Raw String Lean.Json), acc.WF →
      (insertAll g l acc).WF
  | [], _, h => h
  | _ :: r, _, h => insertAll_wf g r _ h.insert

private theorem getElem?_insertAll_of_not_mem (g : Lean.Json → Lean.Json) {name : String} :
    ∀ (l : List (String × Lean.Json)) (acc : Std.TreeMap.Raw String Lean.Json), acc.WF →
      name ∉ l.map Prod.fst → (insertAll g l acc)[name]? = acc[name]?
  | [], _, _, _ => rfl
  | (k, v) :: r, acc, h, hn => by
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    simp only [insertAll, List.foldl_cons]
    rw [← insertAll, getElem?_insertAll_of_not_mem g r _ h.insert hn.2,
      Std.TreeMap.Raw.getElem?_insert h]
    have : ¬ compare k name = .eq := fun e => hn.1 (Std.LawfulEqOrd.compare_eq_iff_eq.mp e).symm
    simp [this]

private theorem getElem?_insertAll_of_mem (g : Lean.Json → Lean.Json) {name : String}
    {v : Lean.Json} :
    ∀ (l : List (String × Lean.Json)) (acc : Std.TreeMap.Raw String Lean.Json), acc.WF →
      (l.map Prod.fst).Nodup → (name, v) ∈ l → (insertAll g l acc)[name]? = some (g v)
  | [], _, _, _, hm => by simp at hm
  | (k, w) :: r, acc, h, hd, hm => by
    simp only [List.map_cons, List.nodup_cons] at hd
    simp only [insertAll, List.foldl_cons]
    rw [← insertAll]
    rcases List.mem_cons.mp hm with e | hm
    · cases e
      rw [getElem?_insertAll_of_not_mem g r _ h.insert hd.1,
        Std.TreeMap.Raw.getElem?_insert h]
      simp
    · exact getElem?_insertAll_of_mem g r _ h.insert hd.2 hm

/-- A string is its own rebuilt document. -/
@[simp] theorem canonical_str (text : String) : canonical (.str text) = .str text := by
  simp [canonical]

/-- The rebuilt items are the items rebuilt one by one. -/
private theorem canonicalItems_eq (items : List Lean.Json) :
    canonicalItems items = items.map canonical := by
  induction items with
  | nil => simp [canonicalItems]
  | cons x xs ih => simp [canonicalItems, ih]

/-- The rebuilt array holds the rebuilt items. -/
@[simp] theorem canonical_arr (items : Array Lean.Json) :
    canonical (.arr items) = .arr (items.map canonical) := by
  obtain ⟨items⟩ := items
  simp [canonical, canonicalItems_eq]

/-- The rebuilt members are inserted in order, each with its rebuilt value. -/
private theorem canonicalMembers_eq (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json))
    (acc : Std.TreeMap.Raw String Lean.Json) :
    canonicalMembers t acc = (inorder t).foldl (fun a p => a.insert p.1 (canonical p.2)) acc := by
  induction t generalizing acc with
  | leaf => simp [canonicalMembers, inorder]
  | inner _ k v l r ihl ihr => simp [canonicalMembers, inorder, ihl, ihr]

/-! ## The text of a document -/

/-- The text of one character of a string. -/
private def esc (c : Char) : List Char := (escape "" c).toList

private theorem escape_toList (acc : String) (c : Char) :
    (escape acc c).toList = acc.toList ++ esc c := by
  unfold esc escape
  repeat' split
  all_goals simp_all [String.toList_append, String.toList_push]

private theorem foldl_escape_toList :
    ∀ (cs : List Char) (acc : String), (cs.foldl escape acc).toList = acc.toList ++ cs.flatMap esc
  | [], _ => by simp
  | c :: cs, acc => by simp [foldl_escape_toList cs, escape_toList]

private theorem esc_of_plain {c : Char} (h : plain c = true) : esc c = [c] := by
  simp only [plain, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h4 : c ≠ '\n' := by rintro rfl; exact h3 (by decide)
  have h5 : c ≠ '\r' := by rintro rfl; exact h3 (by decide)
  simp [esc, escape, h1, h2, h3, h4, h5]

/-- Characters that are all plain escape to themselves. -/
private theorem flatMap_esc_of_plain :
    ∀ cs : List Char, cs.dropWhile plain = [] → cs.flatMap esc = cs
  | [], _ => by simp
  | c :: cs, h => by
    by_cases hc : plain c = true
    · rw [List.dropWhile_cons_of_pos hc] at h
      simp [esc_of_plain hc, flatMap_esc_of_plain cs h]
    · simp [List.dropWhile_cons_of_neg hc] at h

private theorem writeString_toList (s acc : String) :
    (writeString s acc).toList = acc.toList ++ '"' :: (s.toList.flatMap esc ++ ['"']) := by
  unfold writeString
  split
  · rename_i all
    -- Every character is plain, so each one escapes to itself.
    have plainAll : s.toList.dropWhile plain = [] := by
      rw [← after_startPos, ← after_plainEnd, all, (after_eq_nil_iff).2 rfl]
    simp [flatMap_esc_of_plain _ plainAll, String.toList_push, String.toList_append]
  · simp [foldl_escape_toList, String.toList_push]

/-- The text of a number. -/
private def numText (n : JsonNumber) : List Char :=
  n.mantissa.repr.toList ++ if n.exponent = 0 then [] else 'e' :: '-' :: n.exponent.repr.toList

private theorem writeNumber_toList (n : JsonNumber) (acc : String) :
    (writeNumber n acc).toList = acc.toList ++ numText n := by
  unfold writeNumber numText
  split <;> simp_all [String.toList_append]

/-- The members of a list as the text writes them, each after a comma but the first. -/
private def wm : List (String × Lean.Json) → String → Bool → String
  | [], acc, _ => acc
  | (k, v) :: r, acc, first =>
    wm r (write v ((writeString k (if first then acc else acc.push ',')).push ':')) false

private theorem wm_append :
    ∀ (l₁ l₂ : List (String × Lean.Json)) (acc : String) (first : Bool),
      wm (l₁ ++ l₂) acc first = wm l₂ (wm l₁ acc first) (first && l₁.isEmpty)
  | [], _, _, _ => by simp [wm]
  | (k, v) :: r, l₂, acc, first => by simp [wm, wm_append r]

private theorem writeMembers_eq (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    ∀ (acc : String) (first : Bool),
      writeMembers t acc first = (wm (inorder t) acc first, first && (inorder t).isEmpty) := by
  induction t with
  | leaf => intro acc first; simp [writeMembers, inorder, wm]
  | inner _ k v l r ihl ihr =>
    intro acc first
    rw [writeMembers, ihl]
    simp only [inorder, ihr, wm_append, wm]
    simp

/-- A document whose text after other text is that text, then its own. -/
private def Appends (j : Lean.Json) : Prop :=
  ∀ acc : String, (write j acc).toList = acc.toList ++ (write j "").toList

private theorem writeItems_toList :
    ∀ (l : List Lean.Json), (∀ x ∈ l, Appends x) → ∀ (acc : String) (first : Bool),
      (writeItems l acc first).toList = acc.toList ++ (writeItems l "" first).toList
  | [], _, _, _ => by simp [writeItems]
  | x :: xs, h, acc, first => by
    have hx := h x (by simp)
    have hxs := writeItems_toList xs (fun y hy => h y (by simp [hy]))
    simp only [writeItems]
    rw [hxs (write x (if first then acc else acc.push ',')),
      hxs (write x (if first then "" else "".push ',')), hx (if first then acc else acc.push ','),
      hx (if first then "" else "".push ',')]
    cases first <;> simp [String.toList_push]

private theorem wm_toList :
    ∀ (l : List (String × Lean.Json)), (∀ p ∈ l, Appends p.2) → ∀ (acc : String) (first : Bool),
      (wm l acc first).toList = acc.toList ++ (wm l "" first).toList
  | [], _, _, _ => by simp [wm]
  | (k, v) :: r, h, acc, first => by
    have hv := h (k, v) (by simp)
    have hr := wm_toList r (fun p hp => h p (by simp [hp]))
    simp only [wm]
    rw [hr, hr (write v _), hv, hv ((writeString k _).push ':')]
    cases first <;> simp [String.toList_push, writeString_toList]

/-- The text of a document after other text is that text, then its own. -/
private theorem write_toList (j : Lean.Json) :
    ∀ acc : String, (write j acc).toList = acc.toList ++ (write j "").toList := by
  refine induct Appends ?_ ?_ ?_ ?_ ?_ ?_ j
  · intro acc; simp [write, String.toList_append]
  · intro b acc; cases b <;> simp [write, String.toList_append]
  · intro n acc; simp [write, writeNumber_toList]
  · intro s acc; simp [write, writeString_toList]
  · intro items h acc
    simp [write, String.toList_push, writeItems_toList items h (acc.push '['),
      writeItems_toList items h "["]
  · intro t h acc
    simp [write, writeMembers_eq, String.toList_push, wm_toList (inorder t) h (acc.push '{'),
      wm_toList (inorder t) h "{"]

/-- The text of a document, as characters. -/
private def text (j : Lean.Json) : List Char := (write j "").toList

private theorem text_arr (items : List Lean.Json) :
    text (.arr ⟨items⟩) = '[' :: ((writeItems items "" true).toList ++ [']']) := by
  simp [text, write, String.toList_push, writeItems_toList items (fun x _ => write_toList x) "["]

private theorem writeItems_cons_true (x : Lean.Json) (xs : List Lean.Json) :
    (writeItems (x :: xs) "" true).toList = text x ++ (writeItems xs "" false).toList := by
  simp [writeItems, text, writeItems_toList xs (fun x _ => write_toList x) (write x "")]

private theorem writeItems_cons_false (x : Lean.Json) (xs : List Lean.Json) :
    (writeItems (x :: xs) "" false).toList =
      ',' :: (text x ++ (writeItems xs "" false).toList) := by
  simp [writeItems, text, writeItems_toList xs (fun x _ => write_toList x) (write x _),
    write_toList x ","]

private theorem text_obj (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    text (.obj ⟨⟨t⟩⟩) = '{' :: ((wm (inorder t) "" true).toList ++ ['}']) := by
  simp [text, write, writeMembers_eq, String.toList_push,
    wm_toList (inorder t) (fun p _ => write_toList p.2) "{"]

private theorem wm_cons (k : String) (v : Lean.Json) (r : List (String × Lean.Json))
    (first : Bool) :
    (wm ((k, v) :: r) "" first).toList = (if first then [] else [',']) ++
      '"' :: (k.toList.flatMap esc ++ '"' :: ':' :: (text v ++ (wm r "" false).toList)) := by
  simp only [wm]
  rw [wm_toList r (fun p _ => write_toList p.2), write_toList v]
  cases first <;> simp [writeString_toList, String.toList_push, text]

/-! ## Reading a string back -/

/-- The characters of a text that a list of characters ends with have a position. -/
private theorem exists_after_of_append {s : String} :
    ∀ (cs : List Char) {Y : List Char} {p : s.Pos}, after p = cs ++ Y →
      ∃ r : s.Pos, after r = Y
  | [], _, p, h => ⟨p, by simpa using h⟩
  | c :: cs, _, _, h => by
    obtain ⟨_, -, h'⟩ := after_eq_cons (by simpa using h)
    exact exists_after_of_append cs h'

private theorem append_of_isEmpty (acc piece : String) :
    (if acc.isEmpty then piece else acc ++ piece) = acc ++ piece := by
  split
  · rename_i h
    rw [String.isEmpty_iff.1 h]
    simp
  · rfl

private theorem esc_of_not_plain {c : Char} (h : plain c = false) : ∃ t, esc c = '\\' :: t := by
  unfold esc escape
  repeat' split
  all_goals simp_all [plain, String.toList_push]

private theorem takeWhile_esc : ∀ (cs X : List Char),
    (cs.flatMap esc ++ '"' :: X).takeWhile plain = cs.takeWhile plain
  | [], X => by simp [plain]
  | c :: cs, X => by
    cases hc : plain c
    · obtain ⟨t, ht⟩ := esc_of_not_plain hc
      simp [ht, plain, List.takeWhile_cons_of_neg (by simp [hc] : ¬ plain c = true)]
    · simp [esc_of_plain hc, hc, takeWhile_esc cs X]

private theorem dropWhile_esc : ∀ (cs X : List Char),
    (cs.flatMap esc ++ '"' :: X).dropWhile plain = (cs.dropWhile plain).flatMap esc ++ '"' :: X
  | [], X => by simp [plain]
  | c :: cs, X => by
    cases hc : plain c
    · obtain ⟨t, ht⟩ := esc_of_not_plain hc
      simp [ht, plain, List.dropWhile_cons_of_neg (by simp [hc] : ¬ plain c = true)]
    · simp [esc_of_plain hc, hc, dropWhile_esc cs X]

/-- An escaped character that needs an escape is read back after the run before it. -/
private theorem string_escape {s : String} (n : Nat) (p : s.Pos) (acc : String) {c : Char}
    {Y : List Char} (hc : plain c = false) (h : after (plainEnd p) = esc c ++ Y) :
    ∃ r : s.Pos, after r = Y ∧
      string (n + 1) p acc = string n r ((acc ++ s.extract p (plainEnd p)).push c) := by
  -- A reverse solidus and a letter other than `u` stand for the character of a short escape.
  have short : ∀ {d : Char}, after (plainEnd p) = '\\' :: d :: Y → d ≠ 'u' →
      shortEscape d = some c →
      ∃ r : s.Pos, after r = Y ∧
        string (n + 1) p acc = string n r ((acc ++ s.extract p (plainEnd p)).push c) := by
    intro d e hu hd
    obtain ⟨hq, g, e'⟩ := after_eq_cons e
    obtain ⟨hq', g', e''⟩ := after_eq_cons e'
    refine ⟨_, e'', ?_⟩
    simp only [string, append_of_isEmpty]
    simp [hq, g, hq', g', hu, hd]
  unfold esc escape at h
  by_cases h1 : c = '"'
  · subst h1
    exact short (by simpa using h) (by decide) rfl
  by_cases h2 : c = '\\'
  · subst h2
    exact short (by simpa using h) (by decide) rfl
  by_cases h3 : c = '\n'
  · subst h3
    exact short (by simpa using h) (by decide) rfl
  by_cases h4 : c = '\r'
  · subst h4
    exact short (by simpa using h) (by decide) rfl
  by_cases h5 : c.toNat < 0x20
  · -- Any other control character is a Unicode escape of `00` and its two hex digits.
    simp only [h1, h2, h3, h4, h5, ite_false, dite_true, String.toList_push,
      String.toList_append] at h
    have ha := hexValue?_hexDigitChar ⟨c.toNat / 16, by omega⟩
    have hb := hexValue?_hexDigitChar ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩
    rw [show "\\u00".toList = ['\\', 'u', '0', '0'] from rfl] at h
    simp only [String.toList_empty, List.nil_append, List.cons_append] at h
    obtain ⟨hq, g, e⟩ := after_eq_cons h
    obtain ⟨hq', g', e'⟩ := after_eq_cons e
    obtain ⟨r, hr⟩ := exists_after_of_append ['0', '0', _, _] (by simpa using e')
    have hx : hex4 (((plainEnd p).next hq).next hq') = some (c.toNat, r) := by
      refine (hex4_eq_some_iff e').2 ⟨hr, 0, 0, _, _, by decide, by decide, ha, hb, ?_⟩
      have : (0 : UInt8).toNat = 0 := rfl
      simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
      omega
    have hu := (unicodeEscape_eq_of_not_surrogate hx (Or.inl (by omega))).1
    rw [Char.ofNat_toNat] at hu
    refine ⟨r, hr, ?_⟩
    simp only [string, append_of_isEmpty]
    simp [hq, g, hq', g', hu]
  · simp [plain, h1, h2, h5] at hc

private theorem string_esc {s : String} : ∀ (fuel : Nat) (cs X : List Char) (p : s.Pos)
    (acc : String), cs.length < fuel → after p = cs.flatMap esc ++ '"' :: X →
    ∃ q, string fuel p acc = some (acc ++ String.ofList cs, q) ∧ after q = X
  | 0, _, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | n + 1, cs, X, p, acc, hl, h => by
    have hd : after (plainEnd p) = (cs.dropWhile plain).flatMap esc ++ '"' :: X := by
      rw [after_plainEnd, h, dropWhile_esc]
    have ht : s.extract p (plainEnd p) = String.ofList (cs.takeWhile plain) := by
      rw [extract_plainEnd, h, takeWhile_esc]
    have split := (List.takeWhile_append_dropWhile (p := plain) (l := cs)).symm
    cases e : cs.dropWhile plain with
    | nil =>
      rw [e] at hd split
      obtain ⟨hq, g, h'⟩ := after_eq_cons (by simpa using hd)
      refine ⟨_, ?_, h'⟩
      simp only [string, hq, g, ht, append_of_isEmpty]
      simp only [List.append_nil] at split
      simp [← split]
    | cons c ds =>
      have hc : plain c = false := by
        have := List.head_dropWhile_not plain (l := cs) (by simp [e])
        simpa [e] using this
      rw [e, List.flatMap_cons, List.append_assoc] at hd
      rw [e] at split
      obtain ⟨r, hr, eq⟩ := string_escape n p acc hc hd
      have hlen : ds.length < n := by
        have := congrArg List.length split
        simp at this
        omega
      obtain ⟨q, hq, hX⟩ := string_esc n ds X r _ hlen hr
      refine ⟨q, ?_, hX⟩
      rw [eq, hq, ht]
      refine congrArg (fun x => some (x, q)) ?_
      rw [← String.toList_inj]
      conv => rhs; rw [split]
      simp

/-! ## Reading a number back -/

/-- What may follow the text of a document inside the text of another. -/
private def Good (rest : List Char) : Prop := ∀ c ∈ rest.head?, c = ',' ∨ c = ']' ∨ c = '}'

private theorem good_digit {rest : List Char} (hr : Good rest) :
    ∀ c ∈ rest.head?, digit c = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  intro c hc
  rcases hr c hc with rfl | rfl | rfl <;> decide

/-- The digits of a number, with or without a minus sign, then an exponent or none. -/
private theorem number_digits {s : String} (neg : Bool) (a : Nat) (hpos : neg = true → 0 < a)
    (X rest : List Char) (expo : Int) (hr : Good rest)
    (hX : (X = rest ∧ expo = 0) ∨
      ∃ b, 0 < b ∧ X = 'e' :: '-' :: (Nat.toDigits 10 b ++ rest) ∧ expo = -(b : Int))
    (p : s.Pos) (hp : after p = (if neg then ['-'] else []) ++ Nat.toDigits 10 a ++ X) :
    ∃ q, number p = some (⟨if neg then -(a : Int) else a, expo⟩, q) ∧ after q = rest := by
  have hg := good_digit hr
  have hXh : ∀ c ∈ X.head?, digit c = false ∧ c ≠ '.' := by
    rcases hX with ⟨rfl, -⟩ | ⟨b, -, rfl, -⟩
    · exact fun c hc => ⟨(hg c hc).1, (hg c hc).2.1⟩
    · intro c hc
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
      subst hc
      decide
  obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 a = d :: ds :=
    List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
  have hdig := digit_of_mem_toDigits (c := d) (n := a) (by simp [hd])
  have hminus : d ≠ '-' := by rintro rfl; revert hdig; decide
  -- The sign is read first, which leaves the digits.
  obtain ⟨p₁, hp₁, hsign⟩ : ∃ p₁ : s.Pos, after p₁ = Nat.toDigits 10 a ++ X ∧
      expect p '-' = (if neg then some p₁ else none) ∧ (neg = false → p₁ = p) := by
    cases neg
    · exact ⟨p, by simpa using hp, expect_eq_none (by simp [hp, hd, hminus]), fun _ => rfl⟩
    · obtain ⟨q, e, hq⟩ := expect_of_after (by simpa using hp)
      exact ⟨q, hq, e, by simp⟩
  -- The digits of the integer part give its value, and a non-digit ends them.
  obtain ⟨p₂, hdigits, hp₂⟩ := digits_eq p₁ 0 0
  rw [hp₁, takeWhile_toDigits a X (fun c hc => (hXh c hc).1), foldl_digitStep_toDigits]
    at hdigits
  rw [hp₁, dropWhile_toDigits a X (fun c hc => (hXh c hc).1)] at hp₂
  -- A leading zero comes only in the number zero.
  have hlead : ((expect p₁ '0').isSome && decide ((Nat.toDigits 10 a).length > 1)) = false := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · rw [expect_eq_none]
      · simp
      · rw [hp₁, hd]
        have := head_toDigits_ne_zero a ha
        rw [hd] at this
        simpa using this
  have hdot : expect p₂ '.' = none := expect_eq_none (by
    intro e
    obtain ⟨c, hc⟩ : ∃ c, X.head? = some c := by
      cases X with
      | nil => simp [hp₂] at e
      | cons c _ => exact ⟨c, rfl⟩
    rw [hp₂, hc] at e
    exact (hXh c hc).2 (Option.some.inj e))
  rw [Nat.zero_add] at hdigits
  have hlen : decide ((Nat.toDigits 10 a).length = 0) = false := by simp [hd]
  cases neg
  all_goals first | obtain rfl := hsign.2 rfl | skip
  all_goals
    simp only [number, hsign.1, Bool.false_eq_true, ite_false, ite_true]
    simp only [hdigits, hlead, hlen, hdot, Bool.or_false, Bool.false_eq_true, ite_false, bind,
      Option.bind]
    rcases hX with ⟨rfl, rfl⟩ | ⟨b, hb, rfl, rfl⟩
    · -- No exponent follows.
      have he : expect p₂ 'e' = none := expect_eq_none fun e => by
        cases X with
        | nil => simp [hp₂] at e
        | cons c _ => exact (hg c (by simp)).2.2.1 (by simpa [hp₂] using e)
      have hE : expect p₂ 'E' = none := expect_eq_none fun e => by
        cases X with
        | nil => simp [hp₂] at e
        | cons c _ => exact (hg c (by simp)).2.2.2 (by simpa [hp₂] using e)
      exact ⟨p₂, by simp [he, hE], hp₂⟩
    · -- An exponent `e-` and its digits follow.
      obtain ⟨p₃, e₃, h₃⟩ := expect_of_after hp₂
      obtain ⟨p₄, e₄, h₄⟩ := expect_of_after h₃
      obtain ⟨p₅, e₅, h₅⟩ := digits_eq p₄ 0 0
      rw [h₄, takeWhile_toDigits b rest (fun c hc => (hg c hc).1), foldl_digitStep_toDigits,
        Nat.zero_add] at e₅
      rw [h₄, dropWhile_toDigits b rest (fun c hc => (hg c hc).1)] at h₅
      have hlb : (Nat.toDigits 10 b).length ≠ 0 := by
        simp [List.length_eq_zero_iff, Nat.toDigits_ne_nil]
      exact ⟨p₅, by simp [e₃, e₄, e₅, hlb], h₅⟩
private theorem number_numText {s : String} (n : JsonNumber) (rest : List Char) (hr : Good rest)
    (p : s.Pos) (hp : after p = numText n ++ rest) :
    ∃ q, number p = some (⟨n.mantissa, -(n.exponent : Int)⟩, q) ∧ after q = rest := by
  obtain ⟨m, e⟩ := n
  have hX : (((if e = 0 then [] else 'e' :: '-' :: Nat.toDigits 10 e) ++ rest) = rest ∧
      -(e : Int) = 0) ∨ ∃ b, 0 < b ∧
        ((if e = 0 then [] else 'e' :: '-' :: Nat.toDigits 10 e) ++ rest) =
          'e' :: '-' :: (Nat.toDigits 10 b ++ rest) ∧ -(e : Int) = -(b : Int) := by
    by_cases he : e = 0
    · left; simp [he]
    · right; exact ⟨e, by omega, by simp [he], rfl⟩
  simp only [numText, List.append_assoc, Nat.toList_repr] at hp
  rw [Int.repr_eq_ite] at hp
  by_cases hm : 0 ≤ m
  · obtain ⟨q, eq, hq⟩ := number_digits false m.toNat (by simp) _ rest _ hr hX p
      (by simpa [hm, Nat.toList_repr] using hp)
    refine ⟨q, ?_, hq⟩
    rw [eq]
    simp [Int.toNat_of_nonneg hm]
  · obtain ⟨q, eq, hq⟩ := number_digits true (-m).toNat (fun _ => by omega) _ rest _ hr hX p
      (by simpa [hm, Nat.toList_repr] using hp)
    refine ⟨q, ?_, hq⟩
    rw [eq]
    simp [Int.toNat_of_nonneg (by omega : 0 ≤ -m)]

/-! ## Reading a document back -/

mutual

/-- The value that the reader builds from the text of a document. -/
private def toValue (j : Lean.Json) : Value :=
  match j with
  | .null => .null
  | .bool b => .bool b
  | .num n => .num ⟨n.mantissa, -(n.exponent : Int)⟩
  | .str s => .str s
  | .arr ⟨items⟩ => .arr (toValueItems items)
  | .obj ⟨⟨t⟩⟩ => .obj (toValueMembers t)
termination_by structural j

/-- The values of the items of an array. -/
private def toValueItems (items : List Lean.Json) : List Value :=
  match items with
  | [] => []
  | x :: xs => toValue x :: toValueItems xs
termination_by structural items

/-- The members of an object as values, in order. -/
private def toValueMembers (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    List (String × Value) :=
  match t with
  | .leaf => []
  | .inner _ k v l r => toValueMembers l ++ (k, toValue v) :: toValueMembers r
termination_by structural t

end

private theorem toValueItems_eq (items : List Lean.Json) :
    toValueItems items = items.map toValue := by
  induction items with
  | nil => simp [toValueItems]
  | cons x xs ih => simp [toValueItems, ih]

private theorem toValueMembers_eq (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    toValueMembers t = (inorder t).map fun p => (p.1, toValue p.2) := by
  induction t with
  | leaf => simp [toValueMembers, inorder]
  | inner _ k v l r ihl ihr => simp [toValueMembers, inorder, ihl, ihr]

private theorem text_head (j : Lean.Json) :
    ∃ c tl, text j = c :: tl ∧ whitespace c = false ∧ c ≠ ']' := by
  match j with
  | .null => exact ⟨'n', _, rfl, by decide, by decide⟩
  | .bool true => exact ⟨'t', _, rfl, by decide, by decide⟩
  | .bool false => exact ⟨'f', _, rfl, by decide, by decide⟩
  | .str s =>
    exact ⟨'"', s.toList.flatMap esc ++ ['"'], by simp [text, write, writeString_toList],
      by decide, by decide⟩
  | .arr ⟨items⟩ => exact ⟨'[', _, text_arr items, by decide, by decide⟩
  | .obj ⟨⟨t⟩⟩ => exact ⟨'{', _, text_obj t, by decide, by decide⟩
  | .num ⟨m, e⟩ =>
    simp only [text, write, writeNumber_toList, numText, String.toList_empty, List.nil_append]
    rw [Int.repr_eq_ite]
    by_cases hm : 0 ≤ m
    · simp only [hm, ite_true, Nat.toList_repr]
      obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 m.toNat = d :: ds :=
        List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
      have hdig := digit_of_mem_toDigits (c := d) (n := m.toNat) (by simp [hd])
      refine ⟨d, _, by rw [hd, List.cons_append], ?_, ?_⟩
      · simp only [digit, Bool.and_eq_true, decide_eq_true_eq] at hdig
        simp only [whitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> rintro rfl <;> revert hdig <;> decide
      · rintro rfl; revert hdig; decide
    · simp only [hm, ite_false, String.toList_append]
      exact ⟨'-', _, rfl, by decide, by decide⟩

/-- Whitespace is skipped up to a character that is not whitespace. -/
private theorem skipWhitespace_of_head {s : String} {p : s.Pos} {c : Char} {t : List Char}
    (h : after p = c :: t) (hc : whitespace c = false) : skipWhitespace p = p :=
  eq_of_after_eq (by rw [after_skipWhitespace, h, List.dropWhile_cons_of_neg (by simp [hc])])

/-- No whitespace starts the text of a document. -/
private theorem skipWhitespace_text {s : String} {p : s.Pos} (j : Lean.Json) {X : List Char}
    (h : after p = text j ++ X) : skipWhitespace p = p := by
  obtain ⟨c, tl, hc, hws, -⟩ := text_head j
  exact skipWhitespace_of_head (by rw [h, hc, List.cons_append]) hws

/-- The reader reads the text of a document followed by what may follow it. -/
private def Reads (s : String) (j : Lean.Json) : Prop :=
  ∀ (p : s.Pos) (f : Nat) (rest : List Char), after p = text j ++ rest →
    2 * (text j).length < f → Good rest →
    ∃ q, value f p = some (toValue j, q) ∧ after q = rest

private theorem array_read {s : String} :
    ∀ (xs : List Lean.Json) (x : Lean.Json) (acc : List Value) (empty : Bool) (f : Nat)
      (rest : List Char) (p : s.Pos), (∀ y ∈ x :: xs, Reads s y) → Good rest →
      2 * (text x ++ (writeItems xs "" false).toList).length + 2 < f →
      after p = text x ++ ((writeItems xs "" false).toList ++ ']' :: rest) →
      ∃ q, array f p acc empty = some (acc.reverse ++ (x :: xs).map toValue, q) ∧
        after q = rest := by
  intro xs
  induction xs with
  | nil =>
    intro x acc empty f rest p h hr hf hp
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    obtain ⟨c, tl, hc, -, hbr⟩ := text_head x
    simp only [writeItems, String.toList_empty, List.nil_append] at hp hf
    have hp' : after p = c :: (tl ++ ']' :: rest) := by rw [hp, hc, List.cons_append]
    obtain ⟨hp₀, g₀, -⟩ := after_eq_cons hp'
    obtain ⟨q, hv, hq⟩ := h x (by simp) p n (']' :: rest) hp (by simp at hf; omega)
      (by simp [Good])
    obtain ⟨hq₀, g₁, hq₁⟩ := after_eq_cons hq
    refine ⟨_, ?_, hq₁⟩
    rw [array]
    simp [hp₀, g₀, hbr, hv, skipWhitespace_of_head hq (by decide), hq₀, g₁]
  | cons y ys ih =>
    intro x acc empty f rest p h hr hf hp
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    obtain ⟨c, tl, hc, -, hbr⟩ := text_head x
    rw [writeItems_cons_false] at hf hp
    simp only [List.length_append, List.length_cons] at hf
    simp only [List.cons_append, List.append_assoc] at hp
    have hp' : after p = c :: (tl ++ ',' :: (text y ++ ((writeItems ys "" false).toList ++
        ']' :: rest))) := by rw [hp, hc, List.cons_append]
    obtain ⟨hp₀, g₀, -⟩ := after_eq_cons hp'
    obtain ⟨q, hv, hq⟩ := h x (by simp) p n _ hp (by omega) (by simp [Good])
    obtain ⟨hq₀, g₁, hq₁⟩ := after_eq_cons hq
    obtain ⟨r, hi, hr'⟩ := ih y (toValue x :: acc) false n rest (q.next hq₀)
      (fun z hz => h z (by simp_all)) hr (by simp only [List.length_append]; omega) hq₁
    refine ⟨r, ?_, hr'⟩
    rw [array]
    simp [hp₀, g₀, hbr, hv, skipWhitespace_of_head hq (by decide), hq₀, g₁,
      skipWhitespace_text y hq₁, hi]

private theorem length_esc (c : Char) : 1 ≤ (esc c).length := by
  unfold esc escape
  repeat' split
  all_goals simp [String.toList_push]

private theorem length_flatMap_esc : ∀ cs : List Char, cs.length ≤ (cs.flatMap esc).length
  | [] => by simp
  | c :: cs => by
    have := length_esc c
    have := length_flatMap_esc cs
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private theorem object_read {s : String} :
    ∀ (r : List (String × Lean.Json)) (k : String) (v : Lean.Json)
      (acc : List (String × Value)) (empty : Bool) (f : Nat) (rest : List Char) (p : s.Pos),
      (∀ p ∈ (k, v) :: r, Reads s p.2) → Good rest →
      2 * (wm ((k, v) :: r) "" true).toList.length + 2 < f →
      after p = (wm ((k, v) :: r) "" true).toList ++ '}' :: rest →
      ∃ q, object f p acc empty =
          some (acc.reverse ++ ((k, v) :: r).map (fun p => (p.1, toValue p.2)), q) ∧
        after q = rest := by
  intro r
  induction r with
  | nil =>
    intro k v acc empty f rest p h hr hf hp
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    have hk := length_flatMap_esc k.toList
    rw [wm_cons] at hf hp
    simp only [wm, String.toList_empty, List.append_nil, ↓reduceIte, List.nil_append,
      List.length_cons, List.length_append, List.cons_append, List.append_assoc] at hf hp
    obtain ⟨hp₀, g₀, hp₁⟩ := after_eq_cons hp
    obtain ⟨q₁, hs, hq₁⟩ := string_esc n k.toList _ _ "" (by omega) hp₁
    obtain ⟨q₂, he, hq₂⟩ := expect_of_after hq₁
    obtain ⟨q₃, hv, hq₃⟩ := h (k, v) (by simp) q₂ n _ hq₂ (by dsimp only; omega)
      (by simp [Good])
    obtain ⟨hq₃', g₃, hq₄⟩ := after_eq_cons hq₃
    refine ⟨_, ?_, hq₄⟩
    rw [object]
    simp [hp₀, g₀, hs, skipWhitespace_of_head hq₁ (by decide), he, hv,
      skipWhitespace_of_head hq₃ (by decide), hq₃', g₃]
  | cons pr r ih =>
    intro k v acc empty f rest p h hr hf hp
    obtain ⟨k', v'⟩ := pr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    have hk := length_flatMap_esc k.toList
    have hM : (wm ((k', v') :: r) "" false).toList =
        ',' :: (wm ((k', v') :: r) "" true).toList := by
      rw [wm_cons, wm_cons]
      simp
    obtain ⟨M, hM'⟩ : ∃ M, (wm ((k', v') :: r) "" true).toList = '"' :: M :=
      ⟨_, wm_cons k' v' r true⟩
    rw [wm_cons k v, hM] at hf hp
    simp only [↓reduceIte, List.nil_append, List.length_cons, List.length_append,
      List.cons_append, List.append_assoc] at hf hp
    obtain ⟨hp₀, g₀, hp₁⟩ := after_eq_cons hp
    obtain ⟨q₁, hs, hq₁⟩ := string_esc n k.toList _ _ "" (by omega) hp₁
    obtain ⟨q₂, he, hq₂⟩ := expect_of_after hq₁
    obtain ⟨q₃, hv, hq₃⟩ := h (k, v) (by simp) q₂ n _ hq₂ (by dsimp only; omega)
      (by simp [Good])
    obtain ⟨hq₃', g₃, hq₄⟩ := after_eq_cons hq₃
    have hq₄' : after (q₃.next hq₃') = '"' :: (M ++ '}' :: rest) := by
      rw [hq₄, hM', List.cons_append]
    obtain ⟨q, ho, hq⟩ := ih k' v' ((k, toValue v) :: acc) false n rest (q₃.next hq₃')
      (fun q hq => h q (by simp_all)) hr (by omega) hq₄
    refine ⟨q, ?_, hq⟩
    rw [object]
    simp [hp₀, g₀, hs, skipWhitespace_of_head hq₁ (by decide), he, hv,
      skipWhitespace_of_head hq₃ (by decide), hq₃', g₃, skipWhitespace_of_head hq₄' (by decide),
      ho]

private theorem numText_head (n : JsonNumber) :
    ∃ c tl, numText n = c :: tl ∧ (c = '-' ∨ digit c = true) := by
  obtain ⟨m, e⟩ := n
  simp only [numText]
  rw [Int.repr_eq_ite]
  by_cases hm : 0 ≤ m
  · simp only [hm, ite_true, Nat.toList_repr]
    obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 m.toNat = d :: ds :=
      List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
    exact ⟨d, _, by rw [hd, List.cons_append],
      Or.inr (digit_of_mem_toDigits (c := d) (n := m.toNat) (by simp [hd]))⟩
  · simp only [hm, ite_false, String.toList_append]
    exact ⟨'-', _, rfl, Or.inl rfl⟩

/-- The reader reads back the text of every document. -/
private theorem reads (s : String) (j : Lean.Json) : Reads s j := by
  refine induct (Reads s) ?_ ?_ ?_ ?_ ?_ ?_ j
  · intro p f rest hp hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    simp only [text, write] at hp
    rw [show ("" ++ "null").toList = ['n', 'u', 'l', 'l'] from rfl] at hp
    simp only [List.cons_append, List.nil_append] at hp
    obtain ⟨hp₀, g₀, h₁⟩ := after_eq_cons hp
    obtain ⟨q₁, e₁, h₂⟩ := expect_of_after h₁
    obtain ⟨q₂, e₂, h₃⟩ := expect_of_after h₂
    obtain ⟨q₃, e₃, h₄⟩ := expect_of_after h₃
    refine ⟨q₃, ?_, h₄⟩
    rw [value]
    simp [skipWhitespace_of_head hp (by decide), hp₀, g₀, e₁, e₂, e₃, toValue, bind,
      Option.bind]
  · intro b p f rest hp hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    cases b
    · simp only [text, write] at hp
      rw [show ("" ++ "false").toList = ['f', 'a', 'l', 's', 'e'] from rfl] at hp
      simp only [List.cons_append, List.nil_append] at hp
      obtain ⟨hp₀, g₀, h₁⟩ := after_eq_cons hp
      obtain ⟨q₁, e₁, h₂⟩ := expect_of_after h₁
      obtain ⟨q₂, e₂, h₃⟩ := expect_of_after h₂
      obtain ⟨q₃, e₃, h₄⟩ := expect_of_after h₃
      obtain ⟨q₄, e₄, h₅⟩ := expect_of_after h₄
      refine ⟨q₄, ?_, h₅⟩
      rw [value]
      simp [skipWhitespace_of_head hp (by decide), hp₀, g₀, e₁, e₂, e₃, e₄, toValue, bind,
        Option.bind]
    · simp only [text, write] at hp
      rw [show ("" ++ "true").toList = ['t', 'r', 'u', 'e'] from rfl] at hp
      simp only [List.cons_append, List.nil_append] at hp
      obtain ⟨hp₀, g₀, h₁⟩ := after_eq_cons hp
      obtain ⟨q₁, e₁, h₂⟩ := expect_of_after h₁
      obtain ⟨q₂, e₂, h₃⟩ := expect_of_after h₂
      obtain ⟨q₃, e₃, h₄⟩ := expect_of_after h₃
      refine ⟨q₃, ?_, h₄⟩
      rw [value]
      simp [skipWhitespace_of_head hp (by decide), hp₀, g₀, e₁, e₂, e₃, toValue, bind,
        Option.bind]
  · intro num p f rest hp hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    have skip := skipWhitespace_text _ hp
    have ht : text (.num num) = numText num := by simp [text, write, writeNumber_toList]
    rw [ht] at hp
    obtain ⟨q, hnum, hq⟩ := number_numText num rest hr p hp
    obtain ⟨c, tl, hc, hcd⟩ := numText_head num
    rw [hc, List.cons_append] at hp
    obtain ⟨hp₀, g₀, -⟩ := after_eq_cons hp
    have hne : c ≠ '"' ∧ c ≠ '{' ∧ c ≠ '[' ∧ c ≠ 't' ∧ c ≠ 'f' ∧ c ≠ 'n' := by
      rcases hcd with rfl | hcd
      · decide
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert hcd <;> decide
    refine ⟨q, ?_, hq⟩
    rw [value]
    simp [skip, hp₀, g₀, hne, hnum, toValue, bind, Option.bind]
  · intro w p f rest hp hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    have hk := length_flatMap_esc w.toList
    simp only [text, write, writeString_toList, String.toList_empty, List.nil_append,
      List.length_cons, List.length_append, List.cons_append, List.append_assoc] at hf hp
    obtain ⟨hp₀, g₀, hp₁⟩ := after_eq_cons hp
    obtain ⟨q, hs, hq⟩ := string_esc n w.toList rest _ "" (by omega) hp₁
    refine ⟨q, ?_, hq⟩
    rw [value]
    simp [skipWhitespace_of_head hp (by decide), hp₀, g₀, hs, toValue, bind, Option.bind]
  · intro items h p f rest hp hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    rw [text_arr] at hf hp
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hp
    obtain ⟨hp₀, g₀, hp₁⟩ := after_eq_cons hp
    cases items with
    | nil =>
      simp only [writeItems, String.toList_empty, List.nil_append] at hp₁ hf
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hf; omega⟩
      obtain ⟨hq₀, g₁, hq₁⟩ := after_eq_cons hp₁
      have ha : array (m + 1) (p.next hp₀) [] true = some ([], (p.next hp₀).next hq₀) := by
        rw [array]
        simp [hq₀, g₁]
      refine ⟨_, ?_, hq₁⟩
      rw [value]
      simp [skipWhitespace_of_head hp (by decide), hp₀, g₀, skipWhitespace_of_head hp₁ (by decide),
        ha, toValue, toValueItems_eq, bind, Option.bind]
    | cons x xs =>
      rw [writeItems_cons_true] at hf hp₁
      simp only [List.length_cons, List.length_append, List.append_assoc] at hf hp₁
      obtain ⟨q, ha, hq⟩ := array_read xs x [] true n rest _ h hr
        (by simp only [List.length_append]; omega) hp₁
      refine ⟨q, ?_, hq⟩
      rw [value]
      simp [skipWhitespace_of_head hp (by decide), hp₀, g₀, skipWhitespace_text x hp₁, ha,
        toValue, toValueItems_eq, bind, Option.bind]
  · intro t h p f rest hp hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    rw [text_obj] at hf hp
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hp
    obtain ⟨hp₀, g₀, hp₁⟩ := after_eq_cons hp
    cases hi : inorder t with
    | nil =>
      rw [hi] at hp₁ hf
      simp only [wm, String.toList_empty, List.nil_append] at hp₁ hf
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hf; omega⟩
      obtain ⟨hq₀, g₁, hq₁⟩ := after_eq_cons hp₁
      have ho : object (m + 1) (p.next hp₀) [] true = some ([], (p.next hp₀).next hq₀) := by
        rw [object]
        simp [hq₀, g₁]
      refine ⟨_, ?_, hq₁⟩
      rw [value]
      simp [skipWhitespace_of_head hp (by decide), hp₀, g₀, skipWhitespace_of_head hp₁ (by decide),
        ho, toValue, toValueMembers_eq, hi, bind, Option.bind]
    | cons pr r =>
      obtain ⟨k, v⟩ := pr
      rw [hi] at h hf hp₁
      obtain ⟨M, hM⟩ : ∃ M, (wm ((k, v) :: r) "" true).toList = '"' :: M :=
        ⟨_, wm_cons k v r true⟩
      obtain ⟨q, ho, hq⟩ := object_read r k v [] true n rest _ h hr
        (by simp only [List.length_cons, List.length_append] at hf; omega) hp₁
      have hp₁' : after (p.next hp₀) = '"' :: (M ++ '}' :: rest) := by
        rw [hp₁, hM, List.cons_append]
      refine ⟨q, ?_, hq⟩
      rw [value]
      simp [skipWhitespace_of_head hp (by decide), hp₀, g₀, skipWhitespace_of_head hp₁' (by decide),
        ho, toValue, toValueMembers_eq, hi, bind, Option.bind]

/-! ## The document of the value read back -/

/-- A document whose value read back gives its rebuilt document, when it repeats no name. -/
private def Builds (j : Lean.Json) : Prop :=
  Distinct j → (toValue j).toJson = .ok (canonical j)

private theorem itemsToJson_map :
    ∀ (l : List Lean.Json) (acc : Array Lean.Json),
      (∀ x ∈ l, (toValue x).toJson = .ok (canonical x)) →
      itemsToJson (l.map toValue) acc = .ok (acc ++ (l.map canonical).toArray)
  | [], acc, _ => by simp [itemsToJson]
  | x :: xs, acc, h => by
    have hx := h x (by simp)
    simp only [List.map_cons, itemsToJson, hx]
    show itemsToJson (xs.map toValue) (acc.push (canonical x)) = _
    rw [itemsToJson_map xs _ (fun y hy => h y (by simp [hy]))]
    simp

private theorem membersToJson_map :
    ∀ (l : List (String × Lean.Json)) (acc : Std.TreeMap.Raw String Lean.Json), acc.WF →
      (l.map Prod.fst).Nodup → (∀ p ∈ l, acc.contains p.1 = false) →
      (∀ p ∈ l, (toValue p.2).toJson = .ok (canonical p.2)) →
      membersToJson (l.map fun p => (p.1, toValue p.2)) acc = .ok (insertAll canonical l acc)
  | [], acc, _, _, _, _ => by simp [membersToJson, insertAll]
  | (k, v) :: r, acc, wf, hd, hc, h => by
    simp only [List.map_cons, List.nodup_cons] at hd
    have hv := h (k, v) (by simp)
    have hk := hc (k, v) (by simp)
    simp only at hv hk
    simp only [List.map_cons, membersToJson, hk, hv, Bool.false_eq_true, ite_false]
    show membersToJson (r.map fun p => (p.1, toValue p.2)) (acc.insert k (canonical v)) = _
    rw [membersToJson_map r _ wf.insert hd.2 ?_ (fun p hp => h p (by simp [hp]))]
    · rfl
    · intro p hp
      rw [Std.TreeMap.Raw.contains_insert wf, hc p (by simp [hp])]
      have : ¬ compare k p.1 = .eq := fun e =>
        hd.1 ((Std.LawfulEqOrd.compare_eq_iff_eq.mp e) ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      simp [this]

private theorem builds (j : Lean.Json) : Builds j := by
  refine induct Builds ?_ ?_ ?_ ?_ ?_ ?_ j
  · intro _; simp [toValue, Value.toJson, canonical]
  · intro b _; simp [toValue, Value.toJson, canonical]
  · intro n _
    obtain ⟨m, e⟩ := n
    cases e with
    | zero => simp [toValue, Value.toJson, canonical, Number.toJsonNumber, maxExponent]
    | succ k =>
      have : -((k + 1 : Nat) : Int) = Int.negSucc k := rfl
      simp only [toValue, Value.toJson, canonical, Number.toJsonNumber, this]
  · intro s _; simp [toValue, Value.toJson, canonical]
  · intro items h hd
    cases hd with
    | arr each =>
      simp only [toValue, toValueItems_eq, Value.toJson]
      rw [itemsToJson_map items #[] (fun x hx => h x hx (each x (by simpa using hx))),
        canonical_arr]
      simp
      rfl
  · intro t h hd
    cases hd with
    | obj names each =>
      rw [keys_mk] at names
      simp only [toValue, toValueMembers_eq, Value.toJson]
      rw [membersToJson_map (inorder t) ∅ Std.TreeMap.Raw.WF.emptyc names
        (fun p _ => Std.TreeMap.Raw.contains_emptyc)
        (fun p hp => h p hp (each p.1 p.2 (by rw [toList_mk]; exact hp)))]
      simp only [canonical, canonicalMembers_eq, insertAll]
      rfl

/-- A printed document whose objects repeat no name reads back as its rebuilt document. -/
theorem ofText_toText {document : Lean.Json} (distinct : Distinct document) :
    ofText (toText document) = .ok (canonical document) := by
  obtain ⟨q, hv, hq⟩ := reads (toText document) document (toText document).startPos
    (2 * (text document).length + 1) [] (by rw [after_startPos, List.append_nil]; rfl)
    (by omega) (by simp [Good])
  have hr : read (toText document) = some (toValue document) := by
    have hlen : (toText document).length = (text document).length := by
      simp [text, toText, String.length_toList]
    rw [(after_eq_nil_iff).1 hq] at hv
    simp only [read, hlen, hv, bind, Option.bind]
    simp [skipWhitespace]
  simp only [ofText, hr]
  exact builds document distinct

/-- An object built from pairs of distinct names, each value without a repeated name. -/
theorem distinct_mkObj {pairs : List (String × Lean.Json)}
    (names : pairs.Pairwise fun a b => a.1 ≠ b.1) (each : ∀ pair ∈ pairs, Distinct pair.2) :
    Distinct (Json.mkObj pairs) := by
  rw [Toolchain.Json.mkObj_eq]
  have wf : (Std.TreeMap.Raw.ofList pairs compare).WF := Std.TreeMap.Raw.WF.ofList
  have keys : pairs.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
    names.imp fun different equal => different (Std.LawfulEqOrd.compare_eq_iff_eq.mp equal)
  refine .obj (Std.TreeMap.Raw.nodup_keys wf) fun name item mem => ?_
  rw [Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some wf] at mem
  by_cases h : name ∈ pairs.map Prod.fst
  · obtain ⟨⟨k, v⟩, hp, rfl⟩ := List.mem_map.mp h
    rw [Std.TreeMap.Raw.getElem?_ofList_of_mem Std.ReflCmp.compare_self keys hp] at mem
    cases mem
    exact each _ hp
  · rw [Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false (by simpa using h)] at mem
    cases mem

/-- A name in a rebuilt well-formed object gives the rebuilt value that the object holds under it.

A name that the object does not hold gives none. -/
theorem getObjVal?_canonical {members : Std.TreeMap.Raw String Lean.Json} (wf : members.WF)
    (name : String) :
    (canonical (.obj members)).getObjVal? name =
      ((Json.obj members).getObjVal? name).map canonical := by
  obtain ⟨⟨t⟩⟩ := members
  have hc : canonical (.obj ⟨⟨t⟩⟩) = .obj (insertAll canonical (inorder t) ∅) := by
    simp [canonical, canonicalMembers_eq, insertAll]
  have hd : ((inorder t).map Prod.fst).Nodup := by
    rw [← keys_mk]
    exact Std.TreeMap.Raw.nodup_keys wf
  have key : (insertAll canonical (inorder t) ∅)[name]? =
      ((⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json)[name]?).map canonical := by
    by_cases h : name ∈ (inorder t).map Prod.fst
    · obtain ⟨⟨k, v⟩, hp, rfl⟩ := List.mem_map.mp h
      have hm := hp
      rw [← toList_mk, Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some wf] at hm
      rw [hm, getElem?_insertAll_of_mem canonical _ _ Std.TreeMap.Raw.WF.emptyc hd hp]
      rfl
    · rw [getElem?_insertAll_of_not_mem canonical _ _ Std.TreeMap.Raw.WF.emptyc h,
        Std.TreeMap.Raw.getElem?_emptyc]
      cases hg : (⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json)[name]? with
      | none => rfl
      | some v =>
        rw [← Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some wf, toList_mk] at hg
        exact absurd (List.mem_map.mpr ⟨_, hg, rfl⟩) h
  rw [hc, Toolchain.Json.getObjVal?_eq, Toolchain.Json.getObjVal?_eq]
  simp only [Std.TreeMap.Raw.get?_eq_getElem?, key]
  cases (⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json)[name]? <;> rfl

end EthLib.Base.Json
