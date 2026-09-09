#!/usr/bin/env python3
"""Negative controls for the KR comparator, isolated from all production files."""
from pathlib import Path
import copy
import contextlib
import io
import importlib.util
import json
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

    def test_cannot_remove_nontriviality_or_permit_an_axiom(self):
        original = json.loads((ROOT/'comparator.json').read_text(encoding='utf-8-sig'))
        checker.validate_config(original)
        config = copy.deepcopy(original)
        config['theorem_names'].pop()
        with self.assertRaises(ValueError):
            checker.validate_config(config)
        config = copy.deepcopy(original)
        config['permitted_axioms'].append('sorryAx')
        with self.assertRaises(ValueError):
            checker.validate_config(config)

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
                              '  have h := KRChallenge.Submitted.constantCoefficientNontriviality\n'
                              '  exact h.1\n')
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


if __name__ == '__main__':
    unittest.main(verbosity=2)
