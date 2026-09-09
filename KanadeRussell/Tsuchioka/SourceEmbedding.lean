import KanadeRussell.Tsuchioka.SourceSeries

/-! Embedding the ordinary source variable as the ratio in the Fock calculation. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Substitution of the ratio of the two field variables.
Each coefficient is a single Laurent monomial, so the map is defined on all series. -/
noncomputable def ratioEmbedding :
    PowerSeries K →+* PowerSeries (LaurentSeries (Space K)) :=
  (rescale (HahnSeries.single (-1 : ℤ) (1 : Space K))).comp
    (PowerSeries.map (HahnSeries.C.comp MvPolynomial.C))

theorem coeff_ratioEmbedding (f : PowerSeries K) (n : ℕ) :
    coeff n (ratioEmbedding f) =
      HahnSeries.single (-(n : ℤ)) (MvPolynomial.C (coeff n f)) := by
  simp only [ratioEmbedding, RingHom.comp_apply, coeff_rescale, coeff_map,
    HahnSeries.single_pow, one_pow, HahnSeries.C_apply, HahnSeries.single_mul_single,
    one_mul, add_zero]
  congr 1
  simp

theorem ratioEmbedding_binomialFactor (r : ℚ) (c : K) :
    ratioEmbedding (binomialFactor r c) =
      binomialFactor r (HahnSeries.single (-1 : ℤ) (MvPolynomial.C c)) := by
  unfold ratioEmbedding
  rw [RingHom.comp_apply, map_binomialFactor, rescale_binomialFactor]
  simp [HahnSeries.C_apply, HahnSeries.single_mul_single]

/-- The ordinary source H-series is exactly the one used in the Wick calculation. -/
theorem ratioEmbedding_H (w : K) (a : Fin 6 → ℤ) :
    ratioEmbedding (Scalar.H w a) = sourceH w a := by
  simp only [Scalar.H, sourceH, map_prod, map_mul, ratioEmbedding_binomialFactor,
    ratioMonomial, map_neg, HahnSeries.single_neg, neg_div]

theorem ratioEmbedding_G1 (w : K) :
    ratioEmbedding (Scalar.G w 0) = sourceG1 w := by
  rw [Scalar.G, ratioEmbedding_H]
  rfl

/-- The full univariate source G1 maps to the scalar of the actual Fock operators. -/
theorem ratioEmbedding_G1_eq_rootFactor (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    ratioEmbedding (Scalar.G w 0) = rootFactor w := by
  rw [ratioEmbedding_G1, rootFactor_eq_sourceG1 w hw]

/-- Coefficients of the concrete Fock scalar are the source coefficients times
the required inner Laurent monomial. -/
theorem coeff_rootFactor_source (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) (n : ℕ) :
    coeff n (rootFactor w) =
      HahnSeries.single (-(n : ℤ)) (MvPolynomial.C (coeff n (Scalar.G w 0))) := by
  rw [← ratioEmbedding_G1_eq_rootFactor w hw, coeff_ratioEmbedding]

end KanadeRussell.Tsuchioka.Fock
