module

public import EthLib.Cryptography.Unicode.Data
public import Init.Data.Array.BinSearch

/-!
# Unicode 16.0.0 NFKD normalization

The algorithm follows [Unicode 16.0.0, §§3.11 and 3.12][unicode].

[UAX #15, rev. 56, §1.3][uax15] describes the same process.

The tables come from the pinned Unicode Character Database, not the host's Unicode library.

[unicode]: https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/
[uax15]: https://www.unicode.org/reports/tr15/tr15-56.html
-/

@[expose] public section

namespace EthLib.Cryptography.Unicode

/-- The value of a code point in a table sorted by its first component. -/
def lookup {α : Type} [Inhabited α] (table : Array (Nat × α)) (code : Nat) : Option α :=
  (table.binSearch (code, default) (fun a b => a.1 < b.1)).map Prod.snd

/-- The canonical combining class; an unlisted code point has class zero (§3.11.4). -/
def combiningClass (c : Char) : Nat :=
  (lookup Data.combiningClasses c.toNat).getD 0

/-- Full compatibility decomposition, including algorithmic Hangul decomposition (§3.12.2). -/
def decompose (c : Char) : List Char :=
  let code := c.toNat
  -- The 11172 precomposed Hangul syllables start at `SBase = 0xAC00`.
  let parts := if 0xAC00 ≤ code ∧ code < 0xAC00 + 11172 then
      let index := code - 0xAC00
      -- Each leading consonant covers `NCount = 21 * 28 = 588` syllables, from `LBase = 0x1100`.
      let leading := 0x1100 + index / 588
      -- Each vowel covers `TCount = 28` syllables, from `VBase = 0x1161`.
      let vowel := 0x1161 + index % 588 / 28
      -- Trailing index 0 means no trailing consonant, and the others start after `TBase = 0x11A7`.
      let trailing := index % 28
      if trailing = 0 then [leading, vowel] else [leading, vowel, 0x11A7 + trailing]
    -- Any other code point decomposes by the table, or stays as it is.
    else (lookup Data.decompositions code).getD [code]
  parts.map Char.ofNat

/-- Insert a non-starter after those of equal class, preserving their original order (§3.11.5). -/
def insertMark (c : Char) (rank : Nat) : List (Char × Nat) → List (Char × Nat)
  | [] => [(c, rank)]
  | (d, other) :: rest =>
    -- Stop before the first mark of a higher class, so equal classes keep their order.
    if rank < other then (c, rank) :: (d, other) :: rest
    else (d, other) :: insertMark c rank rest

/-- Order each run of non-starters without moving a character across a starter (§3.11.5). -/
def canonicalOrder (chars : List Char) : List Char :=
  -- The output so far, and the sorted run of non-starters since the last starter.
  let (out, marks) := chars.foldl (fun (out, marks) c =>
    let rank := combiningClass c
    -- A starter flushes the run, then joins the output.
    if rank = 0 then (out ++ marks.map Prod.fst |>.push c, [])
    -- A non-starter joins the run at its place by class.
    else (out, insertMark c rank marks)) ((#[] : Array Char), [])
  -- Flush the run after the last starter.
  (out ++ marks.map Prod.fst).toList

/-- Normalization Form KD (NFKD), Unicode 16.0.0 §3.11.7, definition D119.

It fully decomposes compatibility mappings, then orders non-starters by combining class. -/
def nfkd (text : String) : String :=
  String.ofList (canonicalOrder (text.toList.flatMap decompose))

end EthLib.Cryptography.Unicode
