# KR-mod9-lean

Lean 4 proofs of the three Kanade–Russell identities modulo nine:

$$
\begin{aligned}
\sum_{m,n\geq 0}\frac{q^{m^2+3mn+3n^2}}{(q;q)_m(q^3;q^3)_n}
&=\frac{1}{(q,q^3,q^6,q^8;q^9)_\infty},\\
\sum_{m,n\geq 0}\frac{q^{m^2+3mn+3n^2+m+3n}}{(q;q)_m(q^3;q^3)_n}
&=\frac{1}{(q^2,q^3,q^6,q^7;q^9)_\infty},\\
\sum_{m,n\geq 0}\frac{q^{m^2+3mn+3n^2+2m+3n}}{(q;q)_m(q^3;q^3)_n}
&=\frac{1}{(q^3,q^4,q^5,q^6;q^9)_\infty}.
\end{aligned}
$$

Here $(a;q)_m=\prod_{j=0}^{m-1}(1-aq^j)$ and
$(a_1,\ldots,a_r;q)_\infty=\prod_{i=1}^r\prod_{j\geq0}(1-a_iq^j)$.
The identities are formalized over `PowerSeries ℤ`. The
[`kanade_russell_hasSum₁`, `kanade_russell_hasSum₂`, and `kanade_russell_hasSum₃`](KanadeRussell/Theorems.lean)
theorems include convergence of the double sums in the coefficientwise topology.

The formalization follows Y. Mizuno, *The three Kanade–Russell identities
modulo nine* (2026).

## Proof

The $G_2$ denominator identity evaluates the three principally specialized
characters. Heisenberg factorization identifies their vacuum characters with
the three products above. Tsuchioka's spanning bounds then bound the product
coefficients by the corresponding sum coefficients. Equality of the cubic
norms, together with these bounds and constant terms equal to one, gives the
three identities by coefficient rigidity.

The proof is assembled in [`Theorems.lean`](KanadeRussell/Theorems.lean).
The [Tsuchioka modules](KanadeRussell/Tsuchioka) formalize the
representation-theoretic construction.

## Build and verify

Install Lean's `elan` toolchain manager, Git, and Python, then run:

```sh
git clone https://github.com/yuma-mizuno/KR-mod9-lean.git
cd KR-mod9-lean
lake exe cache get
python scripts/check-comparator.py
python scripts/test_check_comparator.py
python scripts/audit-axioms.py
```

The checker builds the library, verifies the solutions to
[`Challenge.lean`](Challenge.lean), and audits their axioms. The last two
commands test the checker and audit the library's public theorems. The allowed
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

[GitHub Actions](.github/workflows/ci.yml) also runs `leanprover/comparator`.
See the [Comparator guide](Comparator/README.md) for the verification setup.
Lean, mathlib, and the `RogersRamanujan` dependency are pinned in
[`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml).
