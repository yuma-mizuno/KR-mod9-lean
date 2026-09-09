# Kanade–Russell identity challenge

The main challenge in [`Challenge.lean`](../Challenge.lean) is to prove the
three original Kanade–Russell identities modulo nine:

1. `Challenge.kr₁`: the first full double-sum/product identity.
2. `Challenge.kr₂`: the second full double-sum/product identity.
3. `Challenge.kr₃`: the third full double-sum/product identity.

Each is stated as `HasSum`, so it includes convergence and equality of the
entire formal power series. These are the main mathematical results checked
by the Comparator.

Three auxiliary targets, `Challenge.product₁_initial_coefficients`,
`Challenge.product₂_initial_coefficients`, and
`Challenge.product₃_initial_coefficients`, check the product definitions in
degrees 0, 1, 2, giving the initial expansions below.

The formulas use integer formal power series with `q = PowerSeries.X`,
explicit finite products in the summand denominators, and one infinite
product for each of the residue sets `(1,3,6,8)`, `(2,3,6,7)`, `(3,4,5,6)`
modulo nine. The source linear terms are respectively `0`, `m+3n`, `2m+3n`.
The challenge consists of six closed propositions. The three coefficient targets fix
the product constant coefficients to 1; the `HasSum` equalities then give
constant coefficient 1 on the source sides as well.

`Challenge.lean` imports only Mathlib and contains six intentional proof
placeholders. The root [`Solution.lean`](../Solution.lean) proves the same six
statements, using `RogersRamanujan` as a pinned proof dependency. Its independent
formula definitions are in [`Problem.lean`](Problem.lean);
[`Submission.lean`](Submission.lean) identifies them with the library definitions.
The checker requires these definitions to match the challenge, ignoring
comments and whitespace.

## Local checks

```powershell
python scripts/check-comparator.py
python scripts/test_check_comparator.py
```

The first command builds the production library and all four Comparator
modules (`Challenge`, `Solution`, `Comparator.Problem`, `Comparator.Submission`),
recompiles the solution source, checks that all six constants inhabit their
closed challenge types, and audits their transitive axioms. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. It fails on missing targets,
definition mismatch, compilation failure, hidden theorem parameters, or
incomplete/unapproved axiom output.
Logs are isolated per run under `build/comparator-check/`.

`--no-build` skips only the full production-library target after a preceding
CI build. It runs `lake build Comparator`, refreshing every transitive
dependency before checking the solution. The negative tests use temporary
files and exercise wrong KR statements, zero constant terms, hidden section
assumptions, proof placeholders, custom axioms, and incomplete audit output.
A separate isolated Lake project checks that edits to both imported bridge
modules are rebuilt even when the top-level solution is unchanged. The
Comparator library explicitly owns `Problem` and `Submission` for this reason.

## Auxiliary checks: initial product expansions

The product-side theorems in
[`KanadeRussell/Product/InitialCoefficients.lean`](../KanadeRussell/Product/InitialCoefficients.lean)
give the following expansions directly:

$$
\begin{aligned}
K_1 &= 1 + q + q^2 + O(q^3), \\
K_2 &= 1 + q^2 + O(q^3), \\
K_3 &= 1 + O(q^3).
\end{aligned}
$$

`Challenge.product₁_initial_coefficients`,
`Challenge.product₂_initial_coefficients`, and
`Challenge.product₃_initial_coefficients` are the three auxiliary coefficient
targets. Their propositions are stated independently in `Challenge.lean` and
`Problem.lean`; `Solution.lean` proves them through the product bridges in
`Submission.lean`. Both the local checker and the independent export
comparison include these targets.

## Independent GitHub Actions verifier

[`comparator.json`](../comparator.json) selects the three main identity targets
and the three auxiliary coefficient targets.
The [Linux workflow](../.github/workflows/ci.yml) builds the library, runs the
local checker and its tests, and is configured to run the isolated
`leanprover/comparator` export comparison:

```sh
lake env comparator comparator.json
```

The pinned Comparator and lean4export revisions match Lean 4.31.0. The
workflow caches library artifacts and verifier binaries separately and runs
the verifier through `systemd-run` with an address-family restriction for
landrun. The local checker and the export comparison are separate checks;
the workflow run records the result of the export comparison.

## Historical and numerical checks

The superseded sixteen-statement specification and solution were removed
from the working tree. Their last versions are available in Git at
`4acc752:Comparator/KanadeRussell.lean` and
`4acc752:Comparator/Solution.lean`. The current Comparator directory contains
only the independent definitions, proof bridges, this guide, and the numerical
consistency checker.

`check_statements.py` checks numerical consistency of the coefficients through
a finite cutoff.
