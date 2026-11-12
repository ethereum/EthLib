module

import EthLib.Base.Hex
import EthLib.Consensus.Shuffle
import EthLib.Cryptography.Hash.Sha256

/-!
# Known answers through the compiled specification

Run pinned test vectors through the specification, with no export and no binding in between.

The Python suite reaches the specification through the C exports and the Python extension.

This program calls the definitions that the theorems are about, compiled.

So a disagreement lies in the specification, in the compiler or in how this program reads files.

Both families also run in the Python suite: here they check the specification without the bindings.

Each family reads its vectors from `tests/`, whose pinned origins `tests/sources.toml` records.

It prints one line per family, and the paths of up to five cases that disagree.

It fails when any case disagrees, or when a family finds no case.

Run it as `lake exe known-answers`, optionally followed by the repository root.
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
def hexBytes (text : String) : Option ByteArray :=
  let chars := text.toList
  Base.hexBytes? (if chars.take 2 == ['0', 'x'] then chars.drop 2 else chars)

/-- The value of the first line that starts with `key` and a colon, after leading spaces.

Single quotes and spaces are dropped, and a key that no line starts with gives none. -/
def field (yaml : String) (key : String) : Option String :=
  let label := key.toList ++ [':']
  (splitChars '\n' yaml.toList).findSome? fun line =>
    let line := line.dropWhile (· = ' ')
    if line.take label.length == label then
      some (String.ofList ((line.drop label.length).filter fun c => c ≠ '\'' ∧ c ≠ ' '))
    else none

/-- The numbers of the first YAML flow list in the text, such as `[6, 9, 2]`.

A malformed list gives none, and text with no list gives the empty list.

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

/-- The counts of one family: cases run, cases that disagree, and the paths of the first five. -/
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

It runs the vectors of the minimal and the mainnet presets.

The [format of consensus-specs][format] describes the files.

[format]: https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/tests/formats/shuffling/README.md
-/
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
        -- A seed of another length cannot reach the shuffle, so the case fails.
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

/-- Run one family, print its counts and its time, and say whether it ran a case and all agreed. -/
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
