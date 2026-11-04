#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Tests for EthLib's optional writing suggestions."""

from __future__ import annotations

import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


WRITING = load("check_writing", "check_writing.py")




def findings(text: str, path: str = "doc.md") -> list[str]:
    blocks = WRITING.file_blocks(path, text)
    return sorted({item.rule for item in WRITING.check_blocks(blocks)})


class WritingRuleTests(unittest.TestCase):

    def test_vocabulary_is_parsed(self) -> None:
        general, history = WRITING.avoid_words()
        self.assertIn("utilize", general)
        self.assertIn("e.g.", general)
        self.assertIn("no longer", history)
        self.assertNotIn("now", history)
        self.assertNotIn("new", history)

    def test_sentence_length(self) -> None:
        long_sentence = " ".join(["word"] * 26) + "."
        self.assertEqual(findings(long_sentence), ["S1"])
        self.assertEqual(findings(" ".join(["word"] * 25) + "."), [])
        self.assertEqual(findings("1. " + " ".join(["word"] * 21) + "."), [])
        self.assertEqual(findings("- " + " ".join(["word"] * 21) + "."), [])
        self.assertEqual(findings("- " + " ".join(["word"] * 21) + ".", 'AGENTS.md'), ['S1'])
        self.assertEqual(findings(" ".join(["word"] * 21) + ".", 'docs/skills/task.md'), ['S1'])
        self.assertEqual(findings("- [ ] " + " ".join(["word"] * 21) + "."), ['S1'])
        self.assertNotIn('S1', findings('/-!\n1. ' + ' '.join(['word'] * 21) + '.\n-/', 'M.lean'))

    def test_text_in_parentheses_is_a_separate_sentence(self) -> None:
        inner = " ".join(["word"] * 40)
        self.assertEqual(findings(f"The bound holds ({inner})."), ["S1"])
        self.assertEqual(findings(f"The bound holds (see ({inner}))."), ["S1"])
        self.assertEqual(findings("The bound holds (for each code)."), [])

    def test_one_word_elements(self) -> None:
        sentence = ("The bound `Code.dist_le_of_mem (h : x ∈ C)` and $\\delta \\le 1 - \\sqrt{\\rho}$ "
                    "from [BCIKS20, Theorem 1.2] and [the page](https://example.org/a.b) hold "
                    "(for every code that this page lists) here.")
        self.assertEqual(findings(sentence), [])
        counted = WRITING.mask(sentence, collapse_parentheses=True)
        self.assertEqual(WRITING.word_count(counted), 13)

    def test_sentence_can_start_with_a_lowercase_filename(self) -> None:
        text = " ".join(["word"] * 20) + ". pr-scope.py " + " ".join(["word"] * 20) + "."
        self.assertEqual(findings(text), [])
        self.assertEqual(len(WRITING.sentences(text)), 2)

    def test_license_text_is_exempt_but_later_prose_is_checked(self) -> None:
        legal = "## Licensing\n\nEnsure these terms; do not change them.\n"
        self.assertEqual(findings(legal, "CONTRIBUTING.md"), [])
        nested = legal + "\n### Conditions\n\nWe utilize these terms.\n"
        self.assertEqual(findings(nested, "CONTRIBUTING.md"), [])
        resumed = nested + "\n## Next steps\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(resumed, "CONTRIBUTING.md"), ["W1"])
        self.assertEqual(findings("Ensure these terms; do not change them.", "LICENSE.md"), [])
        fenced = "```md\n## License\n```\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(fenced), ["W1"])

    def test_mathematical_terms_are_not_blanket_vocabulary_bans(self) -> None:
        for text in ["The following are equivalent.", "Every valid transcript has a witness.",
                     "The space is simply connected.", "This functor is essentially surjective.",
                     "Complete the pull request template."]:
            self.assertNotIn("W1", findings(text), text)


    def test_definition_description_is_still_checked(self) -> None:
        self.assertEqual(findings("- `δ` — We utilize the lemma."), ["W1"])

    def test_grammar_and_structure_are_left_to_review(self) -> None:
        for text in ["The verifier is rejecting the message.", "The lemma has changed.",
                     "Leading coefficients aside, the lemma holds.", "Constructing a proof, the budget changes.",
                     "The bound holds. This is the main result.", "The code is linear; it is cyclic.",
                     "The code is linear — it is cyclic.", "Before making a change, run the tests.",
                     " ".join(["One sentence."] * 7)]:
            with self.subTest(text=text):
                self.assertEqual(findings(text), [])

    def test_word_suggestions_are_optional(self) -> None:
        for options, expected in [([], 0), (["--strict"], 1)]:
            with mock.patch("sys.stdin", io.StringIO("We utilize this lemma.")):
                with mock.patch("sys.stdout", io.StringIO()) as output:
                    self.assertEqual(WRITING.main(["check_writing.py", "--stdin", "body", *options]), expected)
            self.assertIn("1 writing suggestion(s)", output.getvalue())
            self.assertIn("leave clear, correct text alone", output.getvalue())

    def test_words(self) -> None:
        self.assertEqual(findings("Use a ring, e.g. the integers."), ["W7"])
        self.assertEqual(findings("We utilize the lemma."), ["W1"])
        self.assertEqual(findings("Set up the build."), ["W6"])
        self.assertEqual(findings("The word ends in a vowel."), [])
        self.assertEqual(findings("Don't run the build."), ["S5"])
        self.assertEqual(findings("The prover's message is short."), [])


    def test_history_words_apply_to_library_text_only(self) -> None:
        self.assertEqual(findings("The lemma is no longer needed.", "EthLib/example.md"), ["C3"])
        self.assertEqual(findings("The lemma is no longer needed.", "body.md"), [])
        self.assertEqual(findings("The new code is now linear.", "EthLib/example.md"), [])

    def test_exempt_text(self) -> None:
        text = ("Avoid \"e.g.; it's robust\" in prose.\n\n# Heading; with e.g. a dash — here\n\n"
                "```\nlet x := 1; e.g.\n```\n\n<!-- e.g.; utilize -->\n")
        self.assertEqual(findings(text), [])

    def test_table_cells_and_header(self) -> None:
        text = "| Utilize this header | Use |\n|---|---|\n| We utilize this cell. | Fine. |\n"
        self.assertEqual(findings(text), ["W1"])


class LeanExtractionTests(unittest.TestCase):
    def test_doc_comments_and_line_numbers(self) -> None:
        source = ('/-! # Title\n\nWe utilize this module. -/\n'
                  'def f : Nat := 1 -- We utilize this value.\n'
                  'def s : String := "-- utilize is not a comment"\n'
                  '/-- The definition utilizes `x; y`. -/\n'
                  'theorem t : True := trivial\n')
        blocks = WRITING.lean_blocks("A.lean", source)
        lines = {block.line: block.text for block in blocks}
        self.assertIn(3, lines)
        self.assertIn(4, lines)
        self.assertIn(6, lines)
        self.assertNotIn(5, lines)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(3, "W1"), (4, "W1"), (6, "W1")})

    def test_character_literals_do_not_start_strings(self) -> None:
        source = ("def quote : Char := '\"'\n"
                  "def escaped : Char := '\\''\n"
                  "def x' : Nat := 1\n"
                  "/-- The definition utilizes a quote. -/\n"
                  "def y : Nat := 2\n")
        blocks = WRITING.lean_blocks("A.lean", source)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(4, "W1")})


class ChangedLineTests(unittest.TestCase):
    def test_only_changed_blocks_are_checked(self) -> None:
        environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        with tempfile.TemporaryDirectory() as directory, \
                mock.patch.dict(os.environ, environment, clear=True):
            root = Path(directory)

            def run(*args: str) -> None:
                subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)

            run("init", "-q", "-b", "master", "--template=")
            run("config", "user.email", "test@example.org")
            run("config", "user.name", "Test")
            run("config", "commit.gpgsign", "false")
            run("config", "core.hooksPath", os.devnull)
            (root / "page.md").write_text("Old text; with a semicolon.\n\nA clean line.\n")
            run("add", "page.md")
            run("commit", "-q", "-m", "base")
            run("checkout", "-q", "-b", "topic")
            (root / "page.md").write_text(
                "Old text; with a semicolon.\n\nA clean line.\n\nNew text; also bad.\n")
            (root / "untracked.md").write_text("Untracked; ignored.\n")
            with mock.patch.object(WRITING, "ROOT", root):
                blocks = WRITING.changed_blocks("master")
            self.assertEqual([block.line for block in blocks], [5])


class WritingRegressionTests(unittest.TestCase):
    def test_findings_point_to_the_source_line(self) -> None:
        text = ('The [reference](https://example.org/a(b)) and `x` agree.\n'
                'The quoted "a; b" is code here.\n'
                'We utilize the last line.\n')
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        item = next(f for f in found if f.rule == 'W1')
        self.assertEqual(item.line, 3)
        self.assertEqual(item.excerpt, 'utilize')
        self.assertNotIn('Code', item.excerpt)

    def test_line_numbers_in_lists_and_lean_comments(self) -> None:
        cases = [('- First line.\n  We utilize the second line.\n', 'page.md', 2),
                 ('/-! First line.\nWe utilize the second line.\n-/', 'A.lean', 2),
                 ('-- First line.\n-- We utilize the second line.\n', 'A.lean', 2)]
        for text, path, line in cases:
            with self.subTest(path=path, text=text):
                found = WRITING.check_blocks(WRITING.file_blocks(path, text))
                self.assertEqual([f.line for f in found if f.rule == 'W1'], [line])

    def test_word_findings_keep_source_spelling_and_line(self) -> None:
        text = 'A clean line with `code`.\nWe utilize the lemma.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([(f.line, f.excerpt) for f in found if f.rule == 'W1'], [(2, 'utilize')])

    def test_parenthetical_length_finding_points_inside_the_parenthesis(self) -> None:
        text = 'A short sentence (\n' + ' '.join(['word'] * 30) + ').'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'S1'], [2])


    def test_latin_abbreviations_have_one_finding(self) -> None:
        for word in ['e.g.', 'i.e.', 'etc.', 'cf.', 'resp.']:
            pattern = WRITING.word_pattern([word])
            blocks = WRITING.file_blocks('page.md', f'Use {word} here.')
            found = [f for b in blocks for f in WRITING.check_block(b, pattern, None)]
            self.assertEqual([f.rule for f in found], ['W7'])

    def test_final_e_verbs_keep_ing_inflections(self) -> None:
        pattern = WRITING.word_pattern(['ensure', 'utilize', 'leverage'])
        for word in ['ensure', 'ensures', 'ensured', 'ensuring', 'utilizing', 'leveraging']:
            self.assertIsNotNone(pattern.fullmatch(word), word)
        self.assertIsNone(pattern.fullmatch('reassuring'))

    def test_fences_use_their_opening_character_and_length(self) -> None:
        for opening, inner in [('~~~~', '```'), ('````', '```'), ('~~~', '```')]:
            text = f'{opening}\n{inner}\nUtilize ignored code.\n{opening}\n\nWe utilize prose.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(6, 'W1')])

    def test_visible_prose_after_comments_and_thematic_breaks(self) -> None:
        for text in ['<!-- comment --> We utilize prose.',
                     '---\nWe utilize prose.\n---', '#1431 utilizes prose.']:
            self.assertIn('W1', findings(text), text)
        self.assertEqual(findings('    Utilize example code.\n'), [])
        self.assertEqual(findings('---\nstatus: utilize metadata\n---\nClean prose.'), [])

    def test_literal_comment_markers_do_not_hide_prose(self) -> None:
        for text in ['The token `<!--` opens a comment.\nWe utilize prose.\n',
                     '```\n<!--\n```\nWe utilize prose.\n',
                     'The token `<!--` is code, as is `-->`.\nWe utilize prose.\n',
                     'The token `some\n<!--\ntext` is literal.\nWe utilize prose.\n',
                     'The text \\<!-- is literal.\nWe utilize prose.\n',
                     'The text \\<!-- utilizes a literal; --> stays visible.']:
            with self.subTest(text=text):
                self.assertIn('W1', findings(text))
        text = 'A clean line.\n    We utilize this paragraph continuation.\n'
        self.assertIn('W1', findings(text))

    def test_indented_list_continuations_remain_prose(self) -> None:
        for text in ['- Outer item.\n\n    - We utilize prose.\n',
                     '1. Outer item.\n\n    1. We utilize prose.\n',
                     '- Outer item.\n\n    We utilize prose.\n']:
            with self.subTest(text=text):
                self.assertIn('W1', findings(text))

    def test_raw_lean_strings_do_not_create_comments(self) -> None:
        for value in ['r#"a " -- utilize fake comment"#', 'r"a\\"']:
            text = f'def s := {value}\n-- We utilize prose.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(2, 'W1')])

    def test_escaped_newlines_in_lean_strings_keep_comment_locations(self) -> None:
        text = 'def s := "a\\\nb"\n-- We utilize prose.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
        self.assertEqual([(f.line, f.rule) for f in found], [(3, 'W1')])


    def test_wrapped_phrasal_and_history_terms_remain_visible(self) -> None:
        self.assertIn('W6', findings('Carry\nout the test.'))
        self.assertIn('C3', findings('The lemma is no\nlonger needed.', 'EthLib/example.md'))

    def test_wrapped_straight_quotes_are_one_exempt_element(self) -> None:
        text = ('"essentially\nsurjective". Review their meaning. Do not delete them as '
                'isolated words. "Negligible" retains its technical meaning.')
        self.assertEqual(findings(text), [])
        text = 'The text "utilize quoted\nwords; ignored" is literal.\nWe utilize prose.'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'W1'], [3])

    def test_annotation_properties_are_escaped(self) -> None:
        item = WRITING.Finding('a%,line=9::b.md', 2, 'W1', 'message', 'excerpt')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            WRITING.report([item], True, True)
        self.assertIn('file=a%25%2Cline=9%3A%3Ab.md,line=2,', output.getvalue())


class ChangedFileRegressionTests(unittest.TestCase):
    def setUp(self) -> None:
        super().setUp()
        environment = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
        environment.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                           GIT_CONFIG_SYSTEM=os.devnull)
        patcher = mock.patch.dict(os.environ, environment, clear=True)
        patcher.start(); self.addCleanup(patcher.stop)
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        patcher = mock.patch.object(WRITING, 'ROOT', self.root)
        patcher.start(); self.addCleanup(patcher.stop)
        self.git('init', '-q', '-b', 'master', '--template=')
        self.git('config', 'user.email', 'test@example.org')
        self.git('config', 'user.name', 'Test')
        self.git('config', 'commit.gpgsign', 'false')
        self.git('config', 'core.hooksPath', os.devnull)
        self.git('commit', '-q', '--allow-empty', '-m', 'base')
        self.git('checkout', '-q', '-b', 'topic')

    def git(self, *args: str) -> None:
        subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True)

    def test_git_settings_and_quoted_paths_do_not_hide_changes(self) -> None:
        names = ['page.md', 'space name.md', 'café.md', 'quote"name.md', 'back\\slash.md',
                 'line\nbreak.md', ':(glob)nothing.md', ':(literal)foo.md', 'a[1].md', 'a*.md']
        for name in names:
            (self.root / name).write_text('Good line.\nWe utilize the second line.\n')
        self.git('add', '.')
        for option in ['diff.noprefix', 'diff.mnemonicPrefix', 'core.quotePath']:
            for value in ['true', 'false']:
                with self.subTest(option=option, value=value):
                    self.git('config', option, value)
                    found = WRITING.check_blocks(WRITING.changed_blocks('master'))
                    self.assertEqual({f.path for f in found if f.rule == 'W1'}, set(names))
                    self.assertEqual({f.line for f in found if f.rule == 'W1'}, {2})

    def test_renames_check_only_edited_prose(self) -> None:
        old, new = 'old café.md', 'new name.md'
        text = 'We utilize unchanged prose.\n\nA clean line.\n'
        (self.root/old).write_text(text)
        self.git('add', '.')
        self.git('commit', '-q', '-m', 'base prose')
        self.git('branch', '-f', 'master', 'HEAD')
        self.git('mv', old, new)
        (self.root/new).write_text(text + '\nWe utilize changed prose.\n')
        self.git('add', '.')
        found = WRITING.check_blocks(WRITING.changed_blocks('master'))
        self.assertEqual([(f.path, f.line) for f in found if f.rule == 'W1'], [(new, 5)])

    def test_interhunk_context_does_not_add_unchanged_paragraphs(self) -> None:
        path = self.root / 'page.md'
        path.write_text('First paragraph.\n\nWe utilize unchanged prose.\n\nLast paragraph.\n')
        self.git('add', '.')
        self.git('commit', '-q', '-m', 'base prose')
        self.git('branch', '-f', 'master', 'HEAD')
        path.write_text('Changed first paragraph.\n\nWe utilize unchanged prose.\n\nChanged last paragraph.\n')
        self.git('config', 'diff.interHunkContext', '100')
        found = WRITING.check_blocks(WRITING.changed_blocks('master'))
        self.assertFalse([item for item in found if item.rule == 'W1'])

    def test_directory_and_loop_symlinks_are_advisory(self) -> None:
        (self.root / 'directory').mkdir()
        (self.root / 'directory.md').symlink_to('directory', target_is_directory=True)
        (self.root / 'loop.md').symlink_to('loop.md')
        self.git('add', '.')
        diagnostics = []
        self.assertEqual(WRITING.changed_blocks('master', diagnostics), [])
        self.assertEqual({item.path for item in diagnostics}, {'directory.md', 'loop.md'})
        self.assertEqual({item.rule for item in diagnostics}, {'Input'})
        with mock.patch('sys.stdout', io.StringIO()):
            self.assertEqual(WRITING.main(['check_writing.py', '--base', 'master']), 0)

    def test_symlink_diff_lines_do_not_describe_target_prose(self) -> None:
        with tempfile.TemporaryDirectory() as outside:
            target = Path(outside) / 'target.md'
            target.write_text('First line.\n\nWe utilize later prose.\n')
            (self.root / 'link.md').symlink_to(target)
            self.git('add', '.')
            diagnostics = []
            self.assertEqual(WRITING.changed_blocks('master', diagnostics), [])
            self.assertEqual([(item.path, item.rule) for item in diagnostics], [('link.md', 'Input')])
            self.assertNotIn('utilize', diagnostics[0].excerpt)

    def test_non_utf8_and_dangling_symlinks_are_advisory(self) -> None:
        (self.root / 'invalid.md').write_bytes(b'Caf\xe9; text.\n')
        (self.root / 'dangling.md').symlink_to('missing-target')
        (self.root / 'good.md').write_text('We utilize prose.\n')
        self.git('add', '.')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check_writing.py', '--base', 'master']), 0)
        self.assertIn('not UTF-8', output.getvalue())
        self.assertIn('symlink', output.getvalue())
        self.assertIn('W1', output.getvalue())
        self.assertNotIn('No writing suggestions', output.getvalue())
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check_writing.py', str(self.root/'invalid.md')]), 0)
        self.assertIn('not UTF-8', output.getvalue())

    def test_invalid_byte_stdin_has_an_input_diagnostic(self) -> None:
        environment = dict(os.environ, PYTHONIOENCODING='utf-8:surrogateescape')
        result = subprocess.run([sys.executable, WRITING.__file__, '--stdin', 'body'],
                                input=b'\xff\n', capture_output=True, env=environment)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b'not UTF-8', result.stdout)
        self.assertNotIn(b'No writing suggestions', result.stdout)

    def test_missing_base_and_broken_configuration_are_errors(self) -> None:
        with mock.patch('sys.stderr', io.StringIO()) as error:
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['check_writing.py', '--base', 'missing-base'])
        self.assertEqual(result.exception.code, 2)
        self.assertIn('git failed', error.getvalue())
        with mock.patch('sys.stderr', io.StringIO()), mock.patch('sys.stdin', io.StringIO('')):
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['check_writing.py', '--stdin', 'body', '--vocabulary',
                              str(self.root/'missing-vocabulary')])
        self.assertEqual(result.exception.code, 2)


class EthLibTests(unittest.TestCase):
    def test_words_to_avoid_stop_at_the_next_heading(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            guide = Path(directory) / "WRITING.md"
            guide.write_text('### Words to avoid\n\n| Avoid | Use |\n| --- | --- |\n'
                             '| "utilize" | use |\n| "previously" | reference history (rule C3) |\n\n'
                             '## Examples\n\n| Before | After |\n| --- | --- |\n'
                             '| "Matching a client" | Keep as written |\n')
            general, history = WRITING.avoid_words(guide)
        self.assertEqual(general, ["utilize"])
        self.assertEqual(history, ["previously"])

    def test_all_three_contribution_legal_sections_are_exempt(self) -> None:
        for heading in ["Licence", "Copyright notices", "Material from other projects"]:
            text = (f"## {heading}\n\nWe utilize this licence, e.g. its terms. Don't rewrite it.\n"
                    "\n### Conditions\n\nWe utilize these terms.\n"
                    "\n## Editing advice\n\nWe utilize the result.\n")
            with self.subTest(heading=heading):
                found = WRITING.check_blocks(WRITING.file_blocks("CONTRIBUTING.md", text))
                self.assertEqual([(f.line, f.rule) for f in found], [(11, "W1")])

    def test_third_party_discussion_elsewhere_is_not_a_legal_exemption(self) -> None:
        text = "## Material from other projects\n\nWe utilize the result.\n"
        self.assertIn("W1", findings(text, "README.md"))

    def test_copyright_notices_elsewhere_keep_their_existing_exemption(self) -> None:
        text = "## Copyright notice\n\nWe utilize this licence. Don't rewrite it.\n"
        self.assertEqual(findings(text, "NOTICE.md"), [])

    def test_citation_estimates_preserve_source_offsets(self) -> None:
        counted = WRITING.mask("It follows SEC 1 v2 §4.1.6 here.", collapse_parentheses=True)
        self.assertEqual(WRITING.word_count(counted), 4)
        text = "It follows RFC 9380\n§5.3.1 here.\nWe utilize the last line."
        found = WRITING.check_blocks(WRITING.file_blocks("page.md", text))
        self.assertEqual([(f.line, f.excerpt) for f in found if f.rule == "W1"], [(3, "utilize")])

    def test_generated_soundness_facts_are_skipped(self) -> None:
        text = ("<!-- generated: native -->\nWe utilize generated facts.\n"
                "<!-- end generated -->\n\nWe utilize authored prose.\n")
        found = WRITING.check_blocks(WRITING.file_blocks("SOUNDNESS.md", text))
        self.assertEqual([(f.line, f.rule) for f in found], [(5, "W1")])

    def test_generated_marker_inside_a_fence_does_not_hide_prose(self) -> None:
        text = "```md\n<!-- generated: native -->\n```\n\nWe utilize authored prose.\n"
        found = WRITING.check_blocks(WRITING.file_blocks("SOUNDNESS.md", text))
        self.assertEqual([(f.line, f.rule) for f in found], [(5, "W1")])

    def test_generated_contents_cannot_hide_prose_after_the_end_marker(self) -> None:
        text = ("<!-- generated: native -->\n```text\nWe utilize generated facts.\n"
                "<!-- end generated -->\n\nWe utilize authored prose.\n")
        found = WRITING.check_blocks(WRITING.file_blocks("SOUNDNESS.md", text))
        self.assertEqual([(f.line, f.rule) for f in found], [(6, "W1")])

    def test_history_scope_keeps_contribution_bodies_and_commit_messages(self) -> None:
        for path in ["README.md", "SOUNDNESS.md", "EthLib/Example/README.md"]:
            with self.subTest(path=path):
                self.assertEqual(findings("The lemma is no longer needed.", path), ["C3"])
        self.assertEqual(findings("/-- The lemma is no longer needed. -/\ndef x := 1\n",
                                  "EthLib/X.lean"), ["C3"])
        for path in ["description", "commits", "CONTRIBUTING.md"]:
            with self.subTest(path=path):
                self.assertEqual(findings("The lemma is no longer needed.", path), [])

    def test_legacy_guide_option_selects_an_explicit_vocabulary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            guide = Path(directory) / "guide.md"
            guide.write_text('### Words to avoid\n\n| Avoid | Use |\n| --- | --- |\n'
                             '| "utilize" | use |\n')
            with mock.patch("sys.stdin", io.StringIO("We utilize the result.")), \
                    mock.patch("sys.stdout", io.StringIO()) as output:
                status = WRITING.main(["check_writing.py", "--stdin", "body", "--guide", str(guide)])
        self.assertEqual(status, 0)
        self.assertIn("[W1]", output.getvalue())

    def test_only_the_six_optional_suggestion_types_are_emitted(self) -> None:
        for text in ["The scheme is hiding.", "The function is increasing.",
                     "The polynomials have correlated agreement.",
                     "Nothing, in this case, changes.", "Bring the proof, then run the check.",
                     "Morning, afternoon and evening are labels."]:
            with self.subTest(text=text):
                self.assertEqual(findings(text), [])


class RecoveryRegressionTests(unittest.TestCase):
    def test_indented_lean_prose_is_checked_but_markdown_code_is_not(self) -> None:
        examples = [('/-!\n    We utilize indented prose.\n-/', 2),
                    ('/-- First line.\n\n        We utilize the second paragraph.\n-/', 3)]
        for text, line in examples:
            with self.subTest(text=text):
                found = WRITING.check_blocks(WRITING.file_blocks('Module.lean', text))
                self.assertEqual([item.line for item in found if item.rule == 'W1'], [line])
        self.assertNotIn('W1', findings('    Utilize exempt code.', 'page.md'))
        self.assertNotIn('W1', findings('/-!\n```lean\nutilize exempt code\n```\n-/', 'Module.lean'))

    def test_github_summary_contains_all_findings_as_escaped_text(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            summary = Path(directory) / 'summary.md'
            items = [WRITING.Finding('<tag>.md', index, 'W1', 'Review <text>.', 'utilize')
                     for index in range(1, 13)]
            with mock.patch.dict(os.environ, GITHUB_STEP_SUMMARY=str(summary)):
                with mock.patch('sys.stdout', io.StringIO()):
                    WRITING.report(items, True, True)
            text = summary.read_text()
            self.assertIn('12 writing suggestion(s)', text)
            self.assertIn('&lt;tag&gt;.md:12:', text)
            self.assertNotIn('<tag>', text)


if __name__ == "__main__":
    unittest.main()
