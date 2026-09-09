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
lake env lean Comparator/Solution.lean
python scripts/audit-axioms.py
python Comparator/check_statements.py
```

The independent specification has 16 targets, all matched by the production
proof. The axiom audit allows only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. The numerical comparator checks finite
truncations as an additional check of the statements; it is not a proof.
See [Comparator/README.md](Comparator/README.md) for the specification protocol.

## Layout

- `KanadeRussell/`: proof library and axiom audit.
- `Comparator/`: independent specification, exact-type submission, and
  numerical statement checks.
- `scripts/`: reproducible verification tools.

The `KanadeRussell/Pending/` modules define propositions used by conditional
entry points. They contain no custom axioms. The final theorems discharge
the required inputs; the broader universal character proposition is not
assumed by them.
