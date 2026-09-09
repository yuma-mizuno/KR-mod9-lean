import Mathlib
import RogersRamanujan
set_option backward.isDefEq.respectTransparency false

/-!
# Comparator: trusted specification of the three Kanade–Russell identities modulo 9

This file is the *trusted specification* (the "problem" side of the comparator).
It contains only definitions written directly from the paper

  Y. Mizuno, *The three Kanade–Russell identities modulo nine* (2026),

and the statements to be proved, each with a single `sorry`.  The production proof lives in
the library `KanadeRussell` and is submitted through `Comparator/Solution.lean`, which must
close every `sorry` below *with these exact statements* and no additional axioms.

Everything is an identity in `ℤ⟦X⟧` with the product topology (`PowerSeries.WithPiTopology`),
where `X` plays the role of `q`.  Infinite sums are `tsum`/`HasSum` over `ℕ × ℕ`; infinite
products are the conditional products `qPochhammerInf` of the `RogersRamanujan` library
(`(a; q)_∞`).  The `HasSum` forms of the main statements and the anchoring lemmas at the end
guard against the statements being vacuously true through junk values of `tsum`, `tprod`
or `bInv`.

Paper labels: `eq:source-definition`, `eq:K-products`, `thm:KR-evaluations`.
-/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

namespace KanadeRussell

/-- The formal variable, written `q` as in the paper. -/
noncomputable abbrev q : PowerSeries ℤ := PowerSeries.X

/-- The summand of the Nahm sums (paper `eq:source-definition`):
`q^{m² + 3mn + 3n² + a m + b n} / ((q; q)_m (q³; q³)_n)`.  The reciprocal factorials are
written with the both-sided inverse `bInv` of the `RogersRamanujan` library; both
`(q; q)_m` and `(q³; q³)_n` are units of `ℤ⟦X⟧`, see `isUnit_qPochhammer_q` below. -/
noncomputable def sourceTerm (a b : ℕ) : ℕ × ℕ → PowerSeries ℤ
  | (m, n) => q ^ (m ^ 2 + 3 * m * n + 3 * n ^ 2 + a * m + b * n)
      * bInv (q; q)_m * bInv (q ^ 3; q ^ 3)_n

/-- `𝖠 = 𝖥(1, 1)`, the first Kanade–Russell sum. -/
noncomputable def A : PowerSeries ℤ := ∑' mn, sourceTerm 0 0 mn

/-- `𝖡 = 𝖥(q, q³)`, the second Kanade–Russell sum. -/
noncomputable def B : PowerSeries ℤ := ∑' mn, sourceTerm 1 3 mn

/-- `𝖢 = 𝖥(q², q³)`, the third Kanade–Russell sum. -/
noncomputable def C : PowerSeries ℤ := ∑' mn, sourceTerm 2 3 mn

/-- `(q^r; q^9)_∞`. -/
noncomputable def P9 (r : ℕ) : PowerSeries ℤ := (q ^ r; q ^ 9)_∞

/-- `𝖪𝖱₁ = 1 / (q, q³, q⁶, q⁸; q⁹)_∞` (paper `eq:K-products`). -/
noncomputable def K₁ : PowerSeries ℤ := bInv (P9 1 * P9 3 * P9 6 * P9 8)

/-- `𝖪𝖱₂ = 1 / (q², q³, q⁶, q⁷; q⁹)_∞`. -/
noncomputable def K₂ : PowerSeries ℤ := bInv (P9 2 * P9 3 * P9 6 * P9 7)

/-- `𝖪𝖱₃ = 1 / (q³, q⁴, q⁵, q⁶; q⁹)_∞`. -/
noncomputable def K₃ : PowerSeries ℤ := bInv (P9 3 * P9 4 * P9 5 * P9 6)

/-! ## Main statements (paper `thm:KR-evaluations`)

The `HasSum` forms are the primary targets: they assert convergence of the double sums to
the products, so they cannot hold for junk reasons.  The equalities `A = K₁` etc. are the
forms used in the paper. -/

/-- **First Kanade–Russell identity modulo 9**, `HasSum` form. -/
theorem kanade_russell_hasSum₁ : HasSum (sourceTerm 0 0) K₁ := by
  sorry

/-- **Second Kanade–Russell identity modulo 9**, `HasSum` form. -/
theorem kanade_russell_hasSum₂ : HasSum (sourceTerm 1 3) K₂ := by
  sorry

/-- **Third Kanade–Russell identity modulo 9**, `HasSum` form. -/
theorem kanade_russell_hasSum₃ : HasSum (sourceTerm 2 3) K₃ := by
  sorry

/-- **First Kanade–Russell identity modulo 9**: `𝖠 = 𝖪𝖱₁`. -/
theorem kanade_russell₁ : A = K₁ := by
  sorry

/-- **Second Kanade–Russell identity modulo 9**: `𝖡 = 𝖪𝖱₂`. -/
theorem kanade_russell₂ : B = K₂ := by
  sorry

/-- **Third Kanade–Russell identity modulo 9**: `𝖢 = 𝖪𝖱₃`. -/
theorem kanade_russell₃ : C = K₃ := by
  sorry

/-! ## Conditional targets

The two propositions below describe inputs to intermediate conditional theorems.
The production library proves the required inputs and uses them to obtain the
unconditional identities. -/

/-- `(q^d; q^d)_∞`, written `E_d` in the paper. -/
noncomputable def E (d : ℕ) : PowerSeries ℤ := (q ^ d; q ^ d)_∞

/-- The `A₂` theta series `𝔞(q) = ∑_{r,s ∈ ℤ} q^{r² + rs + s²}` (paper §`sec:positive-completion`).
The exponent is a nonnegative integer; `Int.toNat` is exact. -/
noncomputable def a : PowerSeries ℤ := ∑' rs : ℤ × ℤ, q ^ (rs.1 ^ 2 + rs.1 * rs.2 + rs.2 ^ 2).toNat

/-- The cubic norm `𝒩(X, Y, Z) = X³ + q Y³ − q² Z³ + 3 q X Y Z`. -/
noncomputable def cubicNorm (X Y Z : PowerSeries ℤ) : PowerSeries ℤ :=
  X ^ 3 + q * Y ^ 3 - q ^ 2 * Z ^ 3 + 3 * q * X * Y * Z

/-- Paper `lem:KR-lower-bounds` (Kurşungöz's generating functions and Tsuchioka's spanning
theorem, Corollary 1.4): `𝖠 − 𝖪𝖱₁`, `𝖡 − 𝖪𝖱₂`, `𝖢 − 𝖪𝖱₃` have nonnegative coefficients.
Pending assumption `P1` of the plan. -/
def LowerBounds : Prop :=
  (∀ n, coeff n K₁ ≤ coeff n A) ∧ (∀ n, coeff n K₂ ≤ coeff n B) ∧ (∀ n, coeff n K₃ ≤ coeff n C)

/-- The product half of paper `lem:equal-norms`: `E₁ E₃ 𝒩(𝖪𝖱₁, 𝖪𝖱₂, 𝖪𝖱₃) = 𝔞(q)`.  In the paper
this follows from five modular-function certificates (`lem:product-comparison`).  It is the
fallback Pending assumption `P2` of the plan, used only if phase P6 does not produce an
elementary proof. -/
def ProductNorm : Prop := E 1 * E 3 * cubicNorm K₁ K₂ K₃ = a

/-- **Deliverable level A**: the Kanade–Russell identities follow from the lower bounds. -/
theorem kanade_russell_of_lowerBounds (h : LowerBounds) : A = K₁ ∧ B = K₂ ∧ C = K₃ := by
  sorry

/-- **Deliverable level A′** (fallback): the identities follow from the lower bounds and the
product norm. -/
theorem kanade_russell_of_lowerBounds_of_productNorm (h : LowerBounds) (h' : ProductNorm) :
    A = K₁ ∧ B = K₂ ∧ C = K₃ := by
  sorry

/-- The source half of paper `lem:equal-norms`, an unconditional target of phase P5:
`E₁ E₃ 𝒩(𝖠, 𝖡, 𝖢) = 𝔞(q)`. -/
theorem sourceNorm : E 1 * E 3 * cubicNorm A B C = a := by
  sorry

/-! ## Anchoring statements

These pin down the meaning of the definitions above in elementary terms.  They are part of
the trusted specification and must also be proved by the solution. -/

/-- The finite Pochhammer symbols in the denominators are units, so `bInv` is a genuine
inverse in `sourceTerm`. -/
theorem isUnit_qPochhammer_q (d m : ℕ) : IsUnit (q ^ (d + 1); q ^ (d + 1))_m := by
  sorry

/-- The Nahm sums converge (so `A`, `B`, `C` are their honest sums). -/
theorem summable_sourceTerm (a b : ℕ) : Summable (sourceTerm a b) := by
  sorry

/-- Each factor `(q^r; q^9)_∞` with `r ≥ 1` is the convergent product `∏ (1 - q^r q^{9i})`. -/
theorem hasProd_P9 (r : ℕ) :
    HasProd (fun i : ℕ ↦ 1 - q ^ (r + 1) * (q ^ 9) ^ i) (P9 (r + 1)) := by
  sorry

/-- The product sides are genuine reciprocals of their defining products. -/
theorem K₁_mul : K₁ * (P9 1 * P9 3 * P9 6 * P9 8) = 1 := by
  sorry

theorem K₂_mul : K₂ * (P9 2 * P9 3 * P9 6 * P9 7) = 1 := by
  sorry

theorem K₃_mul : K₃ * (P9 3 * P9 4 * P9 5 * P9 6) = 1 := by
  sorry

/-- Normalization check: every series in the theorem has constant coefficient `1`. -/
theorem constantCoeff_eq_one :
    constantCoeff A = 1 ∧ constantCoeff B = 1 ∧ constantCoeff C = 1 ∧
    constantCoeff K₁ = 1 ∧ constantCoeff K₂ = 1 ∧ constantCoeff K₃ = 1 := by
  sorry

end KanadeRussell
