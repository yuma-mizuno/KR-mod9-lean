# KR-mod9-lean

Lean 4 formalization of the three Kanade–Russell identities modulo nine,
following Y. Mizuno, *The three Kanade–Russell identities modulo nine* (2026).

## Main results

The final entry point is [KanadeRussell/Theorems.lean](KanadeRussell/Theorems.lean).
It proves the three formal power series identities over the integers:

- `KanadeRussell.kanade_russell₁`: `A = K₁`.
- `KanadeRussell.kanade_russell₂`: `B = K₂`.
- `KanadeRussell.kanade_russell₃`: `C = K₃`.

The declarations `kanade_russell_hasSum₁`, `kanade_russell_hasSum₂`, and
`kanade_russell_hasSum₃` prove convergence of the original double sums to
the corresponding products in the coefficientwise topology on formal power
series. The conjunction of the three identities is `KanadeRussell.kanade_russell`.
The source sums and products are defined in
[KanadeRussell/Source/Defs.lean](KanadeRussell/Source/Defs.lean).

The proof combines concrete three-sector vertex-operator spanning bounds,
Heisenberg character factorizations, character evaluation through a proved
G2 denominator identity, independent source and product cubic norms, and
positive-coefficient rigidity. The three character formulas and coefficient
lower bounds are proved in the library; they are not additional assumptions
of the final identities.

## Build

Install [Lean via elan](https://github.com/leanprover/elan), Git, and Python 3,
then run:

```sh
git clone https://github.com/yuma-mizuno/KR-mod9-lean.git
cd KR-mod9-lean
lake exe cache get
lake build KanadeRussell
```

The toolchain and dependency revisions are pinned in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`:

- Lean `v4.31.0`.
- mathlib `v4.31.0`.
- [AxiomMath/RogersRamanujan](https://github.com/AxiomMath/RogersRamanujan),
  revision `f391e2763f47243d4c252604aad65bbb2a22751a`.

The first build also compiles the RogersRamanujan dependency from source.

## Verification

```sh
python scripts/check-comparator.py
python scripts/test_check_comparator.py
python scripts/audit-axioms.py
python Comparator/check_statements.py
```

The independent challenge in [Challenge.lean](Challenge.lean) has four closed
targets: the three original identities as convergent `HasSum` statements and
nonzero constant coefficients for all six sides. [Solution.lean](Solution.lean)
proves these targets without importing the challenge's proof placeholders.
The checker builds the proof, checks the exact closed types, and audits their
transitive axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The negative tests check that invalid statements, hidden assumptions, and
incomplete axiom output are rejected.

[GitHub Actions](.github/workflows/ci.yml) also runs the independent
`leanprover/comparator` export comparison using [comparator.json](comparator.json).
The earlier sixteen-statement checkpoint is retained under `Comparator/`.
The numerical comparator checks finite truncations as an additional check of
the statements; it is not a proof. See [Comparator/README.md](Comparator/README.md)
for the verification protocol.

## Layout

- `KanadeRussell/`: proof library and axiom audit.
- `Challenge.lean`, `Solution.lean`, `comparator.json`: independent four-target
  challenge, solution, and verifier configuration.
- `Comparator/`: independent formula definitions, proof bridges, historical
  specification checks, and numerical statement checks.
- `.github/workflows/ci.yml`: build and independent verification on GitHub Actions.
- `scripts/`: reproducible verification tools.

The `KanadeRussell/Pending/` modules define propositions used by conditional
entry points. They contain no custom axioms. The final theorems discharge
the required inputs; the broader universal character proposition is not
assumed by them.
