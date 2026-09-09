#!/usr/bin/env python3
"""Compile the KR-only challenge submission and check its transitive axioms.

The Linux CI additionally runs the independent leanprover/comparator exporter.
This local gate never counts a listed theorem as proved without checking Lean.
"""
from pathlib import Path
import argparse
import json
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    'kr₁': 'KRChallenge.KR₁',
    'kr₂': 'KRChallenge.KR₂',
    'kr₃': 'KRChallenge.KR₃',
    'constantCoefficientNontriviality': 'KRChallenge.ConstantCoefficientNontriviality',
}
NAMES = tuple('Challenge.' + name for name in TARGETS)
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def without_comments(text):
    """Remove nested Lean comments without interpreting comment markers in strings."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                if text[i] == '\n':
                    out.append('\n')
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                i += 1
                out.append(text[i])
            elif text[i] == '"':
                quoted = False
            i += 1
        elif text.startswith('/-', i):
            out.append(' ')
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            quoted = text[i] == '"'
            out.append(text[i])
            i += 1
    if depth or quoted:
        raise ValueError('Unterminated Lean comment or string')
    return ''.join(out)


def canonical(text):
    return ' '.join(without_comments(text).split())


def validate_config(config):
    expected = {
        'challenge_module': 'Challenge',
        'solution_module': 'Solution',
        'theorem_names': list(NAMES),
        'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
        'enable_nanoda': False,
    }
    if config != expected:
        raise ValueError('comparator.json must select exactly the three KR statements and constant-coefficient nontriviality, with only the standard axioms')


def target_headers(source):
    code = without_comments(source)
    parts = re.split(r'^namespace Challenge\s*$', code, flags=re.M)
    if len(parts) != 2:
        raise ValueError('Expected exactly one namespace Challenge')
    headers = re.findall(r'^theorem (\S+)\s*:\s*(.*?)\s*:=', parts[1], re.M | re.S)
    if len(headers) != len(TARGETS) or dict(headers) != TARGETS:
        raise ValueError('Expected exactly four closed challenge statements; no conditional or auxiliary targets')
    return parts[0]


def validate_problem_copy(challenge, problem):
    prefix = target_headers(challenge)
    if canonical(prefix) != canonical(problem):
        raise ValueError('Submission definitions differ from the independently stated Challenge.lean')
    imports = re.findall(r'^import (\S+)\s*$', without_comments(challenge), re.M)
    if imports != ['Mathlib', 'RogersRamanujan']:
        raise ValueError('The challenge must import only Mathlib and RogersRamanujan')


def validate_sources(root):
    read = lambda path: (root / path).read_text(encoding='utf-8-sig')
    validate_config(json.loads(read('comparator.json')))
    challenge = read('Challenge.lean')
    validate_problem_copy(challenge, read('Comparator/Problem.lean'))
    if len(re.findall(r'\bsorry\b', without_comments(challenge))) != 4:
        raise ValueError('The challenge must contain exactly its four proof placeholders')
    target_headers(read('Solution.lean'))
    proofs = [root/'Solution.lean', root/'Comparator/Problem.lean',
              root/'Comparator/Submission.lean', root/'KanadeRussell.lean']
    proofs += sorted((root/'KanadeRussell').rglob('*.lean'))
    for path in proofs:
        code = without_comments(path.read_text(encoding='utf-8-sig'))
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', code):
            raise ValueError('Proof escape in ' + str(path.relative_to(root)))
        for imports in re.findall(r'^import\s+([^\n]+)', code, re.M):
            for module in imports.split():
                if module in ('Challenge', 'Comparator.KanadeRussell'):
                    raise ValueError('Submission imports a challenge with proof placeholders: ' + str(path.relative_to(root)))
                if path == root/'KanadeRussell.lean' or root/'KanadeRussell' in path.parents:
                    if module == 'Solution' or module.startswith('Comparator.'):
                        raise ValueError('Production imports the comparator: ' + str(path.relative_to(root)))


def verify_axioms(output, expected=NAMES):
    found = {}
    records = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output)
    records += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    for name, axioms in records:
        if name in found:
            raise ValueError('Duplicate axiom result: ' + name)
        found[name] = {a.strip() for a in axioms.split(',') if a.strip()}
    if set(found) != set(expected):
        raise ValueError('Incomplete or unexpected axiom coverage: expected ' + ', '.join(expected))
    for name, axioms in found.items():
        if extra := axioms - ALLOWED_AXIOMS:
            raise ValueError('Unapproved axioms for ' + name + ': ' + ', '.join(sorted(extra)))


def run_checked(args, log, root=ROOT):
    with log.open('w', encoding='utf-8') as stream:
        result = subprocess.run(args, cwd=root, stdout=stream, stderr=subprocess.STDOUT)
    output = log.read_text(encoding='utf-8', errors='replace')
    if result.returncode:
        raise ValueError('Command failed: ' + ' '.join(args) + '\n' + output[-12000:])
    return output


def audit_source(solution):
    checks = []
    for name, statement in TARGETS.items():
        # @ prevents implicit section parameters from being silently instantiated.
        checks.append(f'example : {statement} := @Challenge.{name}')
        checks.append(f'#print axioms Challenge.{name}')
    return solution.rstrip() + '\n\n' + '\n'.join(checks) + '\n'

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-build', action='store_true',
                        help='Skip the full production target after a CI build; still rebuild Comparator and its dependencies')
    args = parser.parse_args(argv)
    validate_sources(ROOT)
    base = ROOT/'build/comparator-check'
    base.mkdir(parents=True, exist_ok=True)
    out = Path(tempfile.mkdtemp(prefix='run-', dir=base))
    if not args.no_build:
        run_checked(['lake', 'build', 'KanadeRussell', 'Comparator'], out/'build.log')
    else:
        run_checked(['lake', 'build', 'Comparator'], out/'build.log')
    audit = out/'Audit.lean'
    # Compile the solution source itself, rather than trusting a cached Solution.olean.
    audit.write_text(audit_source((ROOT/'Solution.lean').read_text(encoding='utf-8-sig')), encoding='utf-8')
    output = run_checked(['lake', 'env', 'lean', str(audit.relative_to(ROOT))], out/'solution.log')
    verify_axioms(output)
    print('Verified KR challenge: 3 original HasSum identities and nonzero constant coefficients for all 6 sides.')
    print('All 4 targets compiled; transitive axioms: propext, Classical.choice, Quot.sound only.')
    print('Verification logs: ' + str(out.relative_to(ROOT)))
    print('Independent exporter comparison: lake env comparator comparator.json (Linux CI).')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError) as error:
        print('Comparator FAILED: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
