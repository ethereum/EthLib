module

public import EthLib.Base.Unicode.Data
public import Init.Data.Array.BinSearch

/-!
# Unicode 16.0.0 NFKD normalization

NFKD fully decomposes compatibility mappings, then orders non-starters by combining class.

The algorithm follows [Unicode 16.0.0, §§3.11 and 3.12][unicode].

[UAX #15, rev. 56, §1.3][uax15] describes the same process.

The tables come from the pinned Unicode Character Database, not the host's Unicode library.

[unicode]: https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/
[uax15]: https://www.unicode.org/reports/tr15/tr15-56.html
-/

@[expose] public section

namespace EthLib.Base.Unicode

/-- The value of a code point in a table sorted by its first component. -/
def lookup {α : Type} [Inhabited α] (table : Array (Nat × α)) (code : Nat) : Option α :=
  (table.binSearch (code, default) (fun a b => a.1 < b.1)).map Prod.snd

/-- The canonical combining class; an unlisted code point has class zero (§3.11.4). -/
def combiningClass (c : Char) : Nat :=
  (lookup Data.combiningClasses c.toNat).getD 0

/-- Full compatibility decomposition, including algorithmic Hangul decomposition (§3.12.2). -/
def decompose (c : Char) : List Char :=
  let code := c.toNat
  let parts := if 0xAC00 ≤ code ∧ code < 0xAC00 + 11172 then
      let index := code - 0xAC00
      let leading := 0x1100 + index / 588
      let vowel := 0x1161 + index % 588 / 28
      let trailing := index % 28
      if trailing = 0 then [leading, vowel] else [leading, vowel, 0x11A7 + trailing]
    else (lookup Data.decompositions code).getD [code]
  parts.map Char.ofNat

/-- Insert a non-starter after those of equal class, preserving their original order (§3.11.5). -/
def insertMark (c : Char) (rank : Nat) : List (Char × Nat) → List (Char × Nat)
  | [] => [(c, rank)]
  | (d, other) :: rest =>
    if rank < other then (c, rank) :: (d, other) :: rest
    else (d, other) :: insertMark c rank rest

/-- Order each run of non-starters without moving a character across a starter (§3.11.5). -/
def canonicalOrder (chars : List Char) : List Char :=
  let (out, marks) := chars.foldl (fun (out, marks) c =>
    let rank := combiningClass c
    if rank = 0 then (out ++ marks.map Prod.fst |>.push c, [])
    else (out, insertMark c rank marks)) ((#[] : Array Char), [])
  (out ++ marks.map Prod.fst).toList

/-- Normalization Form KD (NFKD), Unicode 16.0.0 §3.11.7, definition D119. -/
def nfkd (text : String) : String :=
  String.ofList (canonicalOrder (text.toList.flatMap decompose))

end EthLib.Base.Unicode
