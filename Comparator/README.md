# KR statement and constant-coefficient challenge

The active independent challenge is the root [`Challenge.lean`](../Challenge.lean).
Its complete target set is:

1. The first original modulo-nine KR identity, as a convergent `HasSum`.
2. The second original modulo-nine KR identity, as a convergent `HasSum`.
3. The third original modulo-nine KR identity, as a convergent `HasSum`.
4. Nonzero constant coefficients for all three source sums and all three
   reciprocal products.

The formulas use integer formal power series with `q = PowerSeries.X`,
explicit finite products in the summand denominators, and one infinite
product for each of the residue sets `(1,3,6,8)`, `(2,3,6,7)`, `(3,4,5,6)`
modulo nine. The source linear terms are respectively `0`, `m+3n`, `2m+3n`.
There are no character, lower-bound, norm, or other auxiliary challenge
hypotheses. `HasSum` includes convergence; the fourth target rules out zero
constant terms on either side.

`Challenge.lean` imports only Mathlib and RogersRamanujan and contains exactly
four intentional proof placeholders. The root [`Solution.lean`](../Solution.lean)
proves the same four names without importing the challenge. Its independent
formula definitions are in `Problem.lean`; `Submission.lean` proves exact
bridges from the explicit finite/infinite products to the completed library
theorems. The checker requires the formula definitions to match the trusted
challenge, ignoring comments and whitespace.

## Local checks

```powershell
python scripts/check-comparator.py
python scripts/test_check_comparator.py
```

The first command builds the library and both Comparator entry points,
recompiles the solution source, checks that all four constants inhabit their
closed challenge types, and audits their transitive axioms. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. It fails on missing targets,
definition mismatch, compilation failure, hidden theorem parameters, or
incomplete/unapproved axiom output. It never uses a hard-coded proved count.
Logs are isolated per run under `build/comparator-check/`.

`--no-build` skips only the full production-library target after a preceding
CI build. It still runs `lake build Comparator`, refreshing every transitive
dependency before checking the solution. The negative tests use temporary
files and exercise wrong KR statements, zero constant terms, hidden section
assumptions, proof placeholders, custom axioms, and incomplete audit output.

## Independent GitHub Actions verifier

[`comparator.json`](../comparator.json) selects exactly these four targets.
The workflow compiles the proof, caches the project artifacts and pinned
verifier binaries separately, then runs the isolated
`leanprover/comparator` export comparison:

```sh
lake env comparator comparator.json
```

The pinned Comparator and lean4export revisions match Lean 4.31.0. The
workflow includes a `systemd-run` wrapper and address-family
restriction for landrun. The local Python gate and its tests supplement this
independent comparison; they do not replace it.

## Historical checks

`Comparator/KanadeRussell.lean` and `Comparator/Solution.lean` retain the old
sixteen-statement checkpoint, including conditional reductions and auxiliary
lemmas. They are not the active challenge or the CI acceptance target.
`check_statements.py` remains a separate truncated-coefficient consistency
check. A finite numerical match is not an infinite-series proof.
