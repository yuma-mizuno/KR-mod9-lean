"""Fail if completed production theorems depend on any undeclared axiom."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    result = subprocess.run(['lake', 'env', 'lean', 'KanadeRussell/AxiomAudit.lean'],
                            cwd=ROOT, capture_output=True, encoding='utf-8')
    sys.stdout.buffer.write(result.stdout.encode('utf-8'))
    sys.stderr.buffer.write(result.stderr.encode('utf-8'))
    if result.returncode:
        return result.returncode
    checks = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout)
    no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)
    expected = len(re.findall(r'^#print axioms ',
                   (ROOT / 'KanadeRussell/AxiomAudit.lean').read_text(encoding='utf-8-sig'), re.M))
    if len(checks) + len(no_axioms) != expected:
        raise SystemExit('Incomplete axiom output; refusing to treat the audit as successful.')
    for name, axioms in checks:
        extra = {a.strip() for a in axioms.split(',') if a.strip()} - ALLOWED
        if extra:
            raise SystemExit(f'Unapproved axioms for {name}: {sorted(extra)}')
    print(f'Axiom audit: {expected} declarations; only propext, Classical.choice, Quot.sound.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
