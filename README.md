# KR-mod9-lean

Lean 4 formalization of the three original Kanade–Russell identities modulo
nine over integer formal power series, including convergence of the double
sums.

The mathematical reference is Y. Mizuno, *The three Kanade–Russell identities
modulo nine* (2026), Theorem `thm:KR-evaluations`.

## Proved statements

[`KanadeRussell/Theorems.lean`](KanadeRussell/Theorems.lean) proves:

| Declaration in `KanadeRussell` | Statement |
| --- | --- |
| `kanade_russell₁`, `kanade_russell₂`, `kanade_russell₃` | `A = K₁`, `B = K₂`, `C = K₃` |
| `kanade_russell_hasSum₁`, `kanade_russell_hasSum₂`, `kanade_russell_hasSum₃` | The three double sums converge to their respective products |
| `kanade_russell` | The conjunction of the three equalities |

The proof combines Tsuchioka's concrete spanning bounds with proved character
formulas for the three constructed modules. These give coefficient lower
bounds; the independently proved source and product norms, together with
positive-coefficient rigidity, yield the identities. The character formulas
are evaluated using the proved G2 denominator identity.

The final KR theorems have no character-formula or lower-bound hypothesis.
The broader universal character theorem for arbitrary highest-weight modules
is retained as an explicit hypothesis in
[`FromPrincipalCharacterTheorem.lean`](KanadeRussell/FromPrincipalCharacterTheorem.lean);
the completed proof does not depend on that conditional entry point.

## Main KR challenge and auxiliary checks

[`Challenge.lean`](Challenge.lean) states the main challenge as the three full
KR identities: `Challenge.kr₁`, `Challenge.kr₂`, and `Challenge.kr₃`, each in
`HasSum` form. It also includes three auxiliary checks of the initial product
coefficients below. [`Solution.lean`](Solution.lean) proves the main identities
and the auxiliary checks using definitions and proof bridges in `Comparator/`.
The challenge imports only Mathlib; Rogers–Ramanujan is used by the production
proof. The challenge definitions are independent of that proof. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted axioms.

[`Product/InitialCoefficients.lean`](KanadeRussell/Product/InitialCoefficients.lean)
also proves the following coefficients directly from the products:

| Product | Degree 0 | Degree 1 | Degree 2 |
| --- | --- | --- | --- |
| `K₁` | 1 | 1 | 1 |
| `K₂` | 1 | 0 | 1 |
| `K₃` | 1 | 0 | 0 |

These are named Lean theorems and auxiliary Comparator targets verifying
the product definitions in low degrees. See the [Comparator guide](Comparator/README.md) for
statements, checks, and the Linux export verifier.

## Build and verify

The versions are pinned in [`lakefile.toml`](lakefile.toml) and
[`lean-toolchain`](lean-toolchain): Lean and mathlib `v4.31.0`, and AxiomMath's
`RogersRamanujan` at `f391e2763f47243d4c252604aad65bbb2a22751a`.
With Lean's `lake` command and Python available:

```sh
git clone https://github.com/yuma-mizuno/KR-mod9-lean.git
cd KR-mod9-lean
lake exe cache get
python scripts/check-comparator.py
python scripts/test_check_comparator.py
python scripts/audit-axioms.py
```

The comparator checker builds the production library, challenge, definitions,
bridges, and solution, then checks the six closed types and their transitive
axioms. The test suite includes isolated Lean failure cases and a regression
for rebuilding imported bridge modules. The public theorem axiom audit also
includes the three explicit coefficient theorems.

[GitHub Actions](.github/workflows/ci.yml) is configured to build the library,
run the comparator checker and its tests, and run the independent
`leanprover/comparator` export comparison with pinned verifier binaries.

The optional command `python Comparator/check_statements.py` checks finite
truncations numerically. Its output is a separate consistency check, not an
infinite-series proof.

## Code and documentation

- [`KanadeRussell.lean`](KanadeRussell.lean): library entry point for the final
  theorems, initial coefficients, Tsuchioka components, and conditional interface.
- [`KanadeRussell/Theorems.lean`](KanadeRussell/Theorems.lean): the three full
  identities and their convergence statements.
- [`KanadeRussell/Product/InitialCoefficients.lean`](KanadeRussell/Product/InitialCoefficients.lean):
  direct proofs of the initial product coefficients.
- [`Comparator/README.md`](Comparator/README.md): independent specification,
  verification commands, and the numerical consistency checker.
- `scripts/`: reproducible verification tools.
