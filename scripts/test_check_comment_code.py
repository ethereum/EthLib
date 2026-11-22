"""Tests of `check_comment_code.py` on small repositories in a temporary directory."""

import contextlib
import importlib.util
import io
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_comment_code", HERE / "check_comment_code.py")
assert spec and spec.loader
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)

FORMAL = """\
/-- The base fee of a block, from its parent.

The bound holds for indices in this range: the slot is kept.

[EIP-1559](https://eips.ethereum.org/EIPS/eip-1559#specification) defines it. -/
def baseFee (used target fee : Nat) : Nat :=
  -- The rise is `max(floor(floor(f * (u - t) / t) / 8), 1)` when `u > t`.
  --
  -- Step d: `K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1))`.
  --
  -- Each deposit log of the block, in order, gives one request.
  --
  -- A link to another list, `enrtree://<key>@<domain>`, or `file:///x`.
  if used > target then fee + 1 else fee

/-- **A bold title of a theorem stays in a doc comment.** -/
theorem budget_sync_le : True := trivial

-- `budget_sync_le` names a Lean theorem, not a source.
def text : String := "-- `a == b` in a string is no comment"
def quote : Char := '"'
def prime (x x' : Nat) : Nat := x' + 1
"""

# Each line plants exactly one finding, with the rule it breaks.
PLANTED = [
    ("C1", "-- `pubkey_size == 48`."),
    ("C1", "-- `a != b`."),
    ("C2", "-- For each receipt: for log in receipt.logs: the log is read."),
    ("C3", "-- `if blob_count > 6:`"),
    ("C3", "-- `elif blob_count > 6:`"),
    ("C3", "-- `else:`"),
    ("C4", "-- `assert verify(proof)`."),
    ("C5", "-- `return output`."),
    ("C6", "-- The step def check(x): reads the word."),
    ("C7", "-- The count is the size of the list, not len(list)."),
    ("C7", "-- The list grows by items.append(x)."),
    ("C8", "-- The output is `BASE**EXPONENT`."),
    ("C8", "-- The output is 2 ** w."),
    ("C9", "-- `numerator // denominator`."),
    ("C10", "-- `x < 3 and y`."),
    ("C11", "-- process_slashings: the slashings of the epoch."),
    ("C12", "-- The rule follows ethereum/consensus-specs at a pinned commit."),
    ("C12", "-- The rule follows execution-specs at a pinned commit."),
    ("C12", "-- The rule follows execution_specs at a pinned commit."),
    ("C13", "-- The `storage_changes` of an account."),
    ("C14", "-- Record **post-transaction nonces**."),
    ("C15", "-- `current_target = tx.to`."),
]


class CheckCommentCode(unittest.TestCase):
    def run_check(self, files: dict[str, str], allowlist: str = "") -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, text in files.items():
                path = root / "EthLib" / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            (root / "scripts").mkdir()
            (root / check.ALLOWLIST).write_text(allowlist, encoding="utf-8")
            return check.check(root)

    def test_formal_comments_pass(self):
        self.assertEqual(self.run_check({"A.lean": FORMAL}), [])

    def test_each_rule_finds_its_planted_line(self):
        for code, line in PLANTED:
            with self.subTest(code=code, line=line):
                problems = self.run_check({"A.lean": FORMAL + line + "\n"})
                self.assertEqual(len(problems), 1, problems)
                self.assertIn(f": {code} ", problems[0])

    def test_finding_names_its_line(self):
        problems = self.run_check({"A.lean": "def x := 1\n\n-- `return x`.\n"})
        self.assertEqual(problems, ["EthLib/A.lean:3: C5 say what the step gives: return x"])

    def test_doc_comment_is_read(self):
        text = "/-- One line.\n\nThe `a == b` case. -/\ndef x := 1\n"
        problems = self.run_check({"A.lean": text})
        self.assertEqual(len(problems), 1)
        self.assertIn("EthLib/A.lean:3: C1 ", problems[0])

    def test_doc_comment_keeps_emphasis_and_snake_names(self):
        text = "/-- **Title**, see `storage_changes`. -/\ndef x := 1\n"
        self.assertEqual(self.run_check({"A.lean": text}), [])

    def test_proof_comment_names_a_lemma(self):
        text = "theorem t : True := by\n  -- `mul_comm` and `rw [pow_succ]` close it.\n  trivial\n"
        self.assertEqual(self.run_check({"Proofs/A.lean": text}), [])
        self.assertEqual(len(self.run_check({"A.lean": text})), 2)

    def test_nested_block_comment_is_read(self):
        text = "/- outer /- inner -/ `return x` -/\ndef x := 1\n"
        problems = self.run_check({"A.lean": text})
        self.assertEqual(len(problems), 1)
        self.assertIn(": C5 ", problems[0])

    def test_literals_hide_no_comment(self):
        # Each literal holds a would-be comment that breaks a rule, so an early end fails.
        cases = {
            "escaped quote": 'def s := "a \\" -- `return t`"\n',
            "quote character": "def s := '\"' -- `return s`\n",
            "escaped character": "def s := '\\\"' -- `return s`\n",
            "raw string": 'def s := r#"a " -- `return t`"#\n',
        }
        for name, text in cases.items():
            with self.subTest(name=name):
                problems = self.run_check({"A.lean": text})
                expected = (
                    []
                    if "return t" in text
                    else ["EthLib/A.lean:1: C5 say what the step gives: return s"]
                )
                self.assertEqual(problems, expected)

    def test_raw_string_keeps_line_numbers(self):
        problems = self.run_check({"A.lean": 'def s := r#"a\n"b"#\n-- `return s`\n'})
        self.assertEqual(problems, ["EthLib/A.lean:3: C5 say what the step gives: return s"])

    def test_comments_after_literals_are_read(self):
        cases = {
            "escaped quote": 'def s := "a \\" -- b"\n',
            "quote character": "def s := '\"'\n",
            "escaped character": "def s := '\\''\n",
            "raw string": 'def s := r#"a " -- b"#\n',
        }
        for name, text in cases.items():
            with self.subTest(name=name):
                problems = self.run_check({"A.lean": text + "-- `return s`\n"})
                self.assertEqual(
                    problems, ["EthLib/A.lean:2: C5 say what the step gives: return s"]
                )

    def test_strings_keep_line_numbers(self):
        cases = {
            "multi-line string": 'def s := "a\nb"\n',
            "string gap": 'def s := "a\\\n  b"\n',
        }
        for name, text in cases.items():
            with self.subTest(name=name):
                problems = self.run_check({"A.lean": text + "-- `return s`\n"})
                self.assertEqual(
                    problems, ["EthLib/A.lean:3: C5 say what the step gives: return s"]
                )

    def test_allowlisted_finding_passes(self):
        text = "-- `v[a] := (v[a] + v[b] + x) mod 2**w`.\n"
        allowlist = (
            "EthLib/A.lean | C8 | RFC 7693 writes it | `v[a] := (v[a] + v[b] + x) mod 2**w`.\n"
        )
        self.assertEqual(self.run_check({"A.lean": text}, allowlist), [])

    def test_allowlisted_finding_hides_no_other_rule(self):
        text = "-- `a ** b`, then `return c`.\n"
        allowlist = "EthLib/A.lean | C8 | a source writes it | `a ** b`, then `return c`.\n"
        problems = self.run_check({"A.lean": text}, allowlist)
        self.assertEqual(problems, ["EthLib/A.lean:1: C5 say what the step gives: return c"])

    def test_entry_for_one_rule_hides_no_other_rule_on_its_text(self):
        text = "-- `return a == b`.\n"
        allowlist = "EthLib/A.lean | C1 | a source writes the equality | return a == b\n"
        problems = self.run_check({"A.lean": text}, allowlist)
        self.assertEqual(problems, ["EthLib/A.lean:1: C5 say what the step gives: return a == b"])

    def test_entry_without_reason_fails(self):
        problems = self.run_check({"A.lean": FORMAL}, "EthLib/A.lean | C8 | x\n")
        self.assertEqual(len(problems), 1)
        self.assertIn("path | rule | reason | text", problems[0])

    def test_repeated_entry_fails(self):
        entry = "EthLib/A.lean | C8 | RFC 7693 writes it | 2**w.\n"
        problems = self.run_check({"A.lean": "-- 2**w.\n"}, entry + entry)
        self.assertEqual(len(problems), 1)
        self.assertIn("repeats an earlier one", problems[0])

    def test_stale_entry_fails(self):
        allowlist = "EthLib/A.lean | C8 | no longer written | 2**w\n"
        problems = self.run_check({"A.lean": FORMAL}, allowlist)
        self.assertEqual(len(problems), 1)
        self.assertIn("matches nothing", problems[0])

    def test_spec_mention_is_found_everywhere(self):
        cases = {
            "A.lean": "/-- From execution-specs. -/\ndef x := 1\n",
            "Proofs/A.lean": "-- From consensus specs.\n",
            "B.lean": "-- See `ethereum/Consensus-Specs`.\n",
        }
        for name, text in cases.items():
            with self.subTest(name=name):
                problems = self.run_check({name: text})
                self.assertEqual(len(problems), 1, problems)
                self.assertIn(": C12 ", problems[0])

    def test_module_doc_is_a_doc_comment(self):
        self.assertEqual(self.run_check({"A.lean": "/-!\nprocess_slashings: x\n-/\n"}), [])
        problems = self.run_check({"A.lean": "/-! The `a == b` case. -/\n"})
        self.assertEqual(problems, ["EthLib/A.lean:1: C1 write `=` or `≠` in words: a == b"])

    def test_block_comment_counts_its_lines(self):
        problems = self.run_check({"A.lean": "/- one\ntwo\nthe `return x` -/\n"})
        self.assertEqual(problems, ["EthLib/A.lean:3: C5 say what the step gives: return x"])

    def test_hypothesis_name_is_no_function(self):
        self.assertEqual(self.run_check({"A.lean": "-- h_le: the bound holds.\n"}), [])

    def test_main_returns_the_exit_code(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "EthLib").mkdir()
            (root / "scripts").mkdir()
            (root / "EthLib" / "A.lean").write_text("-- `return x`.\n", encoding="utf-8")
            with mock.patch.object(check, "ROOT", root):
                errors = io.StringIO()
                with contextlib.redirect_stderr(errors):
                    self.assertEqual(check.main(), 1)
                self.assertEqual(
                    errors.getvalue(), "EthLib/A.lean:1: C5 say what the step gives: return x\n"
                )
                (root / "EthLib" / "A.lean").write_text("-- Formal.\n", encoding="utf-8")
                self.assertEqual(check.main(), 0)

    def test_repository_passes(self):
        self.assertEqual(check.check(HERE.parent), [])


if __name__ == "__main__":
    unittest.main()
