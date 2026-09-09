#!/usr/bin/env python3
"""Negative controls for the KR comparator, isolated from all production files."""
from pathlib import Path
import copy
import contextlib
import io
import importlib.util
import json
import re
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('kr_comparator', ROOT/'scripts/check-comparator.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class ComparatorGateTests(unittest.TestCase):
    def test_complete_standard_axioms(self):
        output = '\n'.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                           for name in checker.NAMES)
        checker.verify_axioms(output)

    def test_missing_duplicate_and_unapproved_audit_results(self):
        good = [f"'{name}' depends on axioms: [propext]" for name in checker.NAMES]
        for output in ('\n'.join(good[:-1]), '\n'.join(good + good[:1]),
                       '\n'.join(good).replace('[propext]', '[sorryAx]', 1),
                       '\n'.join(good).replace('[propext]', '[inventedCharacterFormula]', 1)):
            with self.subTest(output=output), self.assertRaises(ValueError):
                checker.verify_axioms(output)

    def test_cannot_remove_kr_target_or_permit_an_axiom(self):
        original = json.loads((ROOT/'comparator.json').read_text(encoding='utf-8-sig'))
        checker.validate_config(original)
        config = copy.deepcopy(original)
        config['theorem_names'].remove('Challenge.kr₁')
        with self.assertRaises(ValueError):
            checker.validate_config(config)
        config = copy.deepcopy(original)
        config['permitted_axioms'].append('sorryAx')
        with self.assertRaises(ValueError):
            checker.validate_config(config)

    def test_cannot_remove_explicit_coefficient_targets(self):
        original = json.loads((ROOT/'comparator.json').read_text(encoding='utf-8-sig'))
        for digit in ('₁', '₂', '₃'):
            with self.subTest(product=digit):
                config = copy.deepcopy(original)
                config['theorem_names'].remove(f'Challenge.product{digit}_initial_coefficients')
                with self.assertRaises(ValueError):
                    checker.validate_config(config)

    def test_changed_explicit_coefficient_statement_is_rejected(self):
        problem = (ROOT/'Comparator/Problem.lean').read_text(encoding='utf-8-sig')
        challenge = (ROOT/'Challenge.lean').read_text(encoding='utf-8-sig')
        for digit, value in (('₁', 1), ('₂', 1), ('₃', 0)):
            with self.subTest(product=digit):
                original = f'PowerSeries.coeff 2 product{digit} = {value}'
                self.assertIn(original, problem)
                changed = problem.replace(original, f'PowerSeries.coeff 2 product{digit} = {1-value}', 1)
                with self.assertRaises(ValueError):
                    checker.validate_problem_copy(challenge, changed)

    def test_definitions_in_comments_do_not_hide_changed_formula(self):
        problem = (ROOT/'Comparator/Problem.lean').read_text(encoding='utf-8-sig')
        challenge = (ROOT/'Challenge.lean').read_text(encoding='utf-8-sig')
        checker.validate_problem_copy(challenge, problem)
        changed = problem.replace(':= PowerSeries.X', ':= 0', 1) + '\n/-\n' + problem + '\n-/\n'
        with self.assertRaises(ValueError):
            checker.validate_problem_copy(challenge, changed)

    def test_nested_comments_and_string_literals(self):
        self.assertEqual(checker.canonical('def x := 1 /- outer /- inner -/ end -/ -- tail\n'), 'def x := 1')
        self.assertEqual(checker.canonical('def s := "/- not a comment -/"'), 'def s := "/- not a comment -/"')

    def test_skip_full_build_still_refreshes_comparator(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'Solution.lean').write_text((ROOT/'Solution.lean').read_text(encoding='utf-8-sig'), encoding='utf-8')
            output = '\n'.join(f"'{name}' depends on axioms: [propext]" for name in checker.NAMES)
            with patch.object(checker, 'ROOT', root), patch.object(checker, 'validate_sources'), \
                 patch.object(checker, 'run_checked', return_value=output) as run, \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(checker.main(['--no-build']), 0)
            self.assertEqual(run.call_args_list[0].args[0], ['lake', 'build', 'Comparator'])
            self.assertEqual(run.call_args_list[1].args[0][:3], ['lake', 'env', 'lean'])
    def test_conditional_target_is_rejected(self):
        challenge = (ROOT/'Challenge.lean').read_text(encoding='utf-8-sig')
        changed = challenge.replace('theorem kr₁ :', 'theorem kr₁ (h : False) :', 1)
        with self.assertRaises(ValueError):
            checker.target_headers(changed)


class LeanNegativeControls(unittest.TestCase):
    """Each case compiles a disposable module, never modifying the actual proof."""
    @classmethod
    def setUpClass(cls):
        (ROOT/'build').mkdir(exist_ok=True)
        cls.scratch = tempfile.TemporaryDirectory(prefix='comparator-negative-', dir=ROOT/'build')

    @classmethod
    def tearDownClass(cls):
        cls.scratch.cleanup()

    def compile(self, body):
        path = Path(self.scratch.name)/(self._testMethodName + '.lean')
        path.write_text('import Comparator.Submission\n\n' + body, encoding='utf-8')
        return subprocess.run(['lake', 'env', 'lean', str(path.relative_to(ROOT))], cwd=ROOT,
                              capture_output=True, encoding='utf-8', errors='replace')

    def test_wrong_kr_identity_is_rejected(self):
        result = self.compile('example : KRChallenge.KR₁ := KRChallenge.Submitted.kr₂\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Type mismatch', result.stdout)

    def test_zero_constant_coefficient_is_rejected(self):
        result = self.compile('example : PowerSeries.coeff 0 (0 : PowerSeries ℤ) ≠ 0 := by\n'
                              '  have h := KRChallenge.Submitted.product₁_initial_coefficients\n'
                              '  have hn : PowerSeries.coeff 0 KRChallenge.product₁ ≠ 0 := by\n'
                              '    rw [h.1]; norm_num\n'
                              '  exact hn\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Type mismatch', result.stdout)

    def test_hidden_section_assumption_is_rejected(self):
        solution = (ROOT/'Solution.lean').read_text(encoding='utf-8-sig')
        changed = solution.replace('namespace Challenge', 'namespace Challenge\nvariable (h : False)\ninclude h', 1)
        checker.target_headers(changed)  # Surface headers alone cannot detect the extra parameter.
        result = self.compile(checker.audit_source(changed))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Type mismatch', result.stdout)
    def test_sorry_compiles_but_axiom_gate_rejects_it(self):
        result = self.compile('theorem Challenge.kr₁ : KRChallenge.KR₁ := by sorry\n'
                              '#print axioms Challenge.kr₁\n')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with self.assertRaisesRegex(ValueError, 'sorryAx'):
            checker.verify_axioms(result.stdout, ('Challenge.kr₁',))

    def test_custom_axiom_compiles_but_gate_rejects_it(self):
        result = self.compile('axiom inventedCharacterFormula : KRChallenge.KR₁\n'
                              'theorem Challenge.kr₁ : KRChallenge.KR₁ := inventedCharacterFormula\n'
                              '#print axioms Challenge.kr₁\n')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with self.assertRaisesRegex(ValueError, 'inventedCharacterFormula'):
            checker.verify_axioms(result.stdout, ('Challenge.kr₁',))


class LakeModuleRebuildTests(unittest.TestCase):
    """Imported comparator bridges must remain owned incremental-build inputs."""

    def test_imported_bridges_rebuild_after_source_changes(self):
        lakefile = (ROOT/'lakefile.toml').read_text(encoding='utf-8-sig')
        stanzas = re.findall(r'^\[\[lean_lib\]\][^\n]*\n.*?(?=^\[|\Z)',
                             lakefile, re.M | re.S)
        comparator = [stanza for stanza in stanzas
                      if re.search(r'^name\s*=\s*"Comparator"\s*$', stanza, re.M)]
        self.assertEqual(len(comparator), 1, 'Expected one actual Comparator library stanza')
        build = ROOT/'build'
        build.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='comparator-rebuild-', dir=build) as scratch:
            project = Path(scratch).resolve()
            self.assertEqual(project.parent, build.resolve())
            (project/'lakefile.toml').write_text(
                'name = "KRComparatorRebuildTest"\n\n' + comparator[0], encoding='utf-8')
            (project/'lean-toolchain').write_text(
                (ROOT/'lean-toolchain').read_text(encoding='utf-8-sig'), encoding='utf-8')
            (project/'Comparator').mkdir()
            problem = project/'Comparator/Problem.lean'
            submission = project/'Comparator/Submission.lean'
            problem.write_text('theorem KRRebuildProbe.problemBase : True := True.intro\n',
                               encoding='utf-8')
            submission.write_text('import Comparator.Problem\n'
                                  'theorem KRRebuildProbe.submissionBase : True := True.intro\n',
                                  encoding='utf-8')
            (project/'Challenge.lean').write_text(
                'theorem KRRebuildProbe.challengeBase : True := True.intro\n', encoding='utf-8')
            (project/'Solution.lean').write_text('import Comparator.Submission\n', encoding='utf-8')

            def run(*args):
                result = subprocess.run(args, cwd=project, capture_output=True,
                                        encoding='utf-8', errors='replace', timeout=120)
                self.assertEqual(result.returncode, 0,
                                 ' '.join(args) + '\n' + result.stdout + result.stderr)

            run('lake', 'build', 'Comparator')
            with problem.open('a', encoding='utf-8') as stream:
                stream.write('theorem KRRebuildProbe.problemFresh : True := True.intro\n')
            with submission.open('a', encoding='utf-8') as stream:
                stream.write('theorem KRRebuildProbe.submissionFresh : True := True.intro\n')
            # Neither endpoint changes: only dependency ownership can refresh these imports.
            run('lake', 'build', 'Comparator')
            (project/'Probe.lean').write_text(
                'import Solution\n'
                'example : True := KRRebuildProbe.problemFresh\n'
                'example : True := KRRebuildProbe.submissionFresh\n', encoding='utf-8')
            run('lake', 'env', 'lean', 'Probe.lean')


if __name__ == '__main__':
    unittest.main(verbosity=2)
