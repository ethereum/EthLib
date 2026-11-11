module

import EthLib.Consensus.Shuffle
import EthLib.Cryptography.Hash.Sha256

/-!
Run pinned test vectors through the specification, with no export and no binding in between.

The Python suite reaches the specification through the C exports and the Python extension.

This program calls the same definitions that the theorems are about, compiled, on the same files.

So a disagreement lies in the specification, in the compiler or in how this program reads files.

The exports and the bindings play no part.

Each family reads its vectors from `tests/`, at the pins of `tests/sources.toml`.

It prints one line per family, then fails when any case disagrees.

```text
    lake exe known-answers [repository root]
```
-/

open EthLib

namespace KnownAnswers

/-- The text split at each occurrence of `sep`, as lists of characters. -/
def splitChars (sep : Char) (text : List Char) : List (List Char) :=
  text.foldr (fun c acc => if c = sep then [] :: acc else
    match acc with
    | first :: rest => (c :: first) :: rest
    | [] => [[c]]) [[]]

/-- The bytes of a hex string, with or without `0x`, or none for a malformed string. -/
def hexBytes (text : String) : Option ByteArray := do
  let chars := text.toList
  let digits := if chars.take 2 == ['0', 'x'] then chars.drop 2 else chars
  -- Two hex digits per byte, so an odd count is malformed.
  if digits.length % 2 ≠ 0 then none
  let nibble (c : Char) : Option UInt8 :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
    else none
  let rec go : List Char → ByteArray → Option ByteArray
    | hi :: lo :: rest, acc => do go rest (acc.push ((← nibble hi) * 16 + (← nibble lo)))
    | _, acc => some acc
  go digits .empty

/-- The value of `key` in a flat YAML file, without quotes and spaces, or none if it is absent. -/
def field (yaml : String) (key : String) : Option String :=
  let label := key.toList ++ [':']
  (splitChars '\n' yaml.toList).findSome? fun line =>
    let line := line.dropWhile (· = ' ')
    if line.take label.length == label then
      some (String.ofList ((line.drop label.length).filter fun c => c ≠ '\'' ∧ c ≠ ' '))
    else none

/-- The numbers of the first YAML flow list in the text, such as `[6, 9, 2]`.

A malformed list gives none.

A long list wraps onto several lines, so the line breaks and spaces between items are dropped. -/
def numbers (text : String) : Option (List Nat) :=
  let inner := (text.toList.dropWhile (· ≠ '[')).drop 1 |>.takeWhile (· ≠ ']')
  if inner.isEmpty then some [] else
  (splitChars ',' inner).mapM fun item =>
    (String.ofList (item.filter fun c => c ≠ ' ' ∧ c ≠ '\n')).toNat?

/-- The subdirectories of a directory, in name order. -/
def caseDirs (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← dir.readDir
  let dirs ← entries.filterM fun e => e.path.isDir
  return (dirs.map (·.path)).qsort (·.toString < ·.toString)

/-- The counts of one family: cases run, cases that disagree, and the names of the first few. -/
structure Tally where
  run : Nat := 0
  failed : Nat := 0
  names : Array String := #[]

/-- Count one case, and keep its name when it fails. -/
def Tally.add (t : Tally) (name : String) (ok : Bool) : Tally :=
  { run := t.run + 1, failed := t.failed + (if ok then 0 else 1),
    names := if ok || t.names.size ≥ 5 then t.names else t.names.push name }

/-! ## Families -/

/-- The shuffling vectors of consensus-specs: each case gives a seed, a count and a list.

The list holds the shuffled index of every index below the count.

`tests/formats/shuffling/README.md` of consensus-specs describes the format. -/
def shuffling (root : System.FilePath) : IO Tally := do
  let mut tally : Tally := {}
  for (presetName, preset) in [("minimal", Consensus.Preset.minimal),
      ("mainnet", Consensus.Preset.mainnet)] do
    let dir := root / "tests/consensus/shuffling" / presetName / "phase0/shuffling/core/shuffle"
    for case in ← caseDirs dir do
      let yaml ← IO.FS.readFile (case / "mapping.yaml")
      let ok := Id.run do
        let some seedHex := field yaml "seed" | return false
        let some count := (field yaml "count").bind (·.toNat?) | return false
        let some seed := hexBytes seedHex | return false
        -- A seed of another length is a malformed vector, not a disagreement of the shuffle.
        if h : seed.size = 32 then
          -- The list is the only one in the file, and it can span several lines.
          let some expected := numbers yaml | return false
          let seed : Base.Bytes32 := ⟨seed.data, h⟩
          -- A count that the shuffle refuses is a disagreement, since every vector has an answer.
          match Consensus.computeShuffledPermutation preset count.toUInt64 seed with
          | .ok permutation => return permutation.toList == expected.map UInt64.ofNat
          | .error _ => return false
        else return false
      tally := tally.add case.toString ok
  return tally

/-- The SHA-256 vectors: NIST CAVP short and long messages, and the FIPS 180-2 examples. -/
def sha256 (root : System.FilePath) : IO Tally := do
  let mut tally : Tally := {}
  for case in ← caseDirs (root / "tests/cryptography/sha256/hash") do
    -- Each case is a directory with a `data.yaml`; `format.md` beside them is not a case.
    let yaml ← IO.FS.readFile (case / "data.yaml")
    let ok := match (field yaml "message").bind hexBytes, (field yaml "output").bind hexBytes with
      | some message, some expected => Cryptography.Hash.Sha256.hash message == expected
      | _, _ => false
    tally := tally.add case.toString ok
  return tally

/-- Run one family, print its counts and its time, and say whether every case agreed. -/
def report (name : String) (family : IO Tally) : IO Bool := do
  let start ← IO.monoNanosNow
  let tally ← family
  let stop ← IO.monoNanosNow
  let millis := (stop - start).toFloat / 1000000
  IO.println s!"{name}: {tally.run} cases, {tally.failed} disagree, {millis} ms"
  for n in tally.names do IO.println s!"  disagrees: {n}"
  return tally.failed == 0 && tally.run > 0

end KnownAnswers

public def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD "."
  let a ← KnownAnswers.report "shuffling" (KnownAnswers.shuffling root)
  let b ← KnownAnswers.report "sha256" (KnownAnswers.sha256 root)
  return if a && b then 0 else 1
