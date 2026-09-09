import KanadeRussell.Tsuchioka.RatioContraction

/-!
Weighted sequential operators reduce to the source's same- and distinct-position
Fourier kernels. This connects the scalar Fourier identities to actual fields.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

theorem ratio_inverse_G1 (w : K) :
    (ratioEmbedding (Scalar.H w (-Scalar.exponents 0)) :
        LaurentSeries (LaurentSeries (Space K))) *
      (sourceG1 w : LaurentSeries (LaurentSeries (Space K))) = 1 := by
  have h := congrArg (ratioEmbedding (K := K)) (Scalar.H_neg_mul w (Scalar.exponents 0))
  change ratioEmbedding (Scalar.H w (-Scalar.exponents 0) * Scalar.G w 0) = ratioEmbedding 1 at h
  rw [map_mul, map_one, ratioEmbedding_G1] at h
  have hc := congrArg
    (HahnSeries.ofPowerSeries ℤ (LaurentSeries (Space K))) h
  simpa only [map_mul, map_one] using hc

theorem twoSummands_distinct_source_expansion (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (s t : Fin 3) (hst : s ≠ t) (f : Space K) :
    twoSummands w s t f = normalProduct w s t f *
      (ratioEmbedding (Scalar.H w (-Scalar.exponents 0)) :
        LaurentSeries (LaurentSeries (Space K))) := by
  calc
    twoSummands w s t f =
        (twoSummands w s t f * (sourceG1 w : LaurentSeries (LaurentSeries (Space K)))) *
          (ratioEmbedding (Scalar.H w (-Scalar.exponents 0)) :
            LaurentSeries (LaurentSeries (Space K))) := by
      rw [mul_assoc, mul_comm (sourceG1 w : LaurentSeries (LaurentSeries (Space K))),
        ratio_inverse_G1, mul_one]
    _ = _ := by rw [twoSummands_distinct_source w hw s t hst]

theorem weighted_twoSummands_same (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (h : PowerSeries K) (s : Fin 3) (f : Space K) :
    (ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) * twoSummands w s s f =
      (ratioEmbedding (Scalar.G w 0 ^ 2 * h) :
        LaurentSeries (LaurentSeries (Space K))) * normalProduct w s s f := by
  rw [twoSummands_same_source w hw, map_mul, map_pow (ratioEmbedding (K := K)), ratioEmbedding_G1,
    PowerSeries.coe_mul, PowerSeries.coe_pow]
  ring

theorem weighted_twoSummands_distinct (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (h : PowerSeries K) (s t : Fin 3) (hst : s ≠ t) (f : Space K) :
    (ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) * twoSummands w s t f =
      (ratioEmbedding (Scalar.H w (-Scalar.exponents 0) * h) :
        LaurentSeries (LaurentSeries (Space K))) * normalProduct w s t f := by
  rw [twoSummands_distinct_source_expansion w hw s t hst, map_mul, PowerSeries.coe_mul]
  ring

theorem weighted_same_symmetric (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (h : PowerSeries K) (s : Fin 3) (f : Space K) (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoSummands w s s f).coeff b).coeff a +
      (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoSummands w s s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C (Scalar.symmetricFourier (Scalar.G w 0 ^ 2 * h) n))
        (normalProduct w s s f) a b := by
  rw [weighted_twoSummands_same w hw]
  exact normalProduct_symmetric_expansions w s s f (Scalar.G w 0 ^ 2 * h) a b

theorem weighted_same_antisymmetric (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (h : PowerSeries K) (s : Fin 3) (f : Space K) (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoSummands w s s f).coeff b).coeff a -
      (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoSummands w s s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C (Scalar.antisymmetricFourier (Scalar.G w 0 ^ 2 * h) n))
        (normalProduct w s s f) a b := by
  rw [weighted_twoSummands_same w hw]
  exact normalProduct_antisymmetric_expansions w s s f (Scalar.G w 0 ^ 2 * h) a b

theorem weighted_distinct_symmetric (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (h : PowerSeries K) (s t : Fin 3) (hst : s ≠ t) (f : Space K) (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoSummands w s t f).coeff b).coeff a +
      (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoSummands w t s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C
        (Scalar.symmetricFourier (Scalar.H w (-Scalar.exponents 0) * h) n))
        (normalProduct w s t f) a b := by
  rw [weighted_twoSummands_distinct w hw h s t hst,
    weighted_twoSummands_distinct w hw h t s hst.symm]
  exact normalProduct_symmetric_expansions w s t f
    (Scalar.H w (-Scalar.exponents 0) * h) a b

theorem weighted_distinct_antisymmetric (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (h : PowerSeries K) (s t : Fin 3) (hst : s ≠ t) (f : Space K) (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoSummands w s t f).coeff b).coeff a -
      (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoSummands w t s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C
        (Scalar.antisymmetricFourier (Scalar.H w (-Scalar.exponents 0) * h) n))
        (normalProduct w s t f) a b := by
  rw [weighted_twoSummands_distinct w hw h s t hst,
    weighted_twoSummands_distinct w hw h t s hst.symm]
  exact normalProduct_antisymmetric_expansions w s t f
    (Scalar.H w (-Scalar.exponents 0) * h) a b

/-- Exact coefficients of the weighted full fields are the quadratic mode
convolution; the scalar sequence vanishes at negative indices. -/
theorem weighted_twoFields_coeff (w : K) (h : PowerSeries K) (f : Space K) (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoFields w f).coeff (-b)).coeff (-a) =
      ∑ᶠ n : ℤ, MvPolynomial.C (positive h n) *
        mode w (a - n) (mode w (b + n) f) := by
  rw [ratio_product_coeff]
  unfold contract
  apply finsum_congr
  intro n
  rw [show -b - n = -(b + n) by ring, show -a + n = -(a - n) by ring,
    twoFields_coeff]


/-- The quadratic mode convolution above is an actual finite sum on every
polynomial input, not merely the default value of a formal finsum. -/
theorem weighted_twoFields_mode_convolution_finite (w : K) (h : PowerSeries K)
    (f : Space K) (a b : ℤ) :
    (Function.support (fun n : ℤ => MvPolynomial.C (positive h n) *
      mode w (a - n) (mode w (b + n) f))).Finite := by
  have hf := ratio_contraction_finite h (twoFields w f) (-a) (-b)
  have he : (fun n : ℤ => MvPolynomial.C (positive h n) *
      ((twoFields w f).coeff (-b - n)).coeff (-a + n)) =
      (fun n : ℤ => MvPolynomial.C (positive h n) *
        mode w (a - n) (mode w (b + n) f)) := by
    funext n
    rw [show -b - n = -(b + n) by ring, show -a + n = -(a - n) by ring,
      twoFields_coeff]
  rw [he] at hf
  exact hf

end KanadeRussell.Tsuchioka.Fock
