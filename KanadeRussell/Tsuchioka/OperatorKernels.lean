import KanadeRussell.Tsuchioka.ResidueMaps

/-! Decomposition of the full weighted-field relation into its two residue maps. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries

variable {K : Type*} [Field K] [CharZero K]

/-- The quadratic mode convolution associated with the source coefficients. -/
noncomputable def quadraticConvolution (w : K) (h : PowerSeries K)
    (f : Space K) (a b : ℤ) : Space K :=
  ∑ᶠ n : ℤ, positive h n • mode w (a - n) (mode w (b + n) f)

theorem quadraticConvolution_finite (w : K) (h : PowerSeries K)
    (f : Space K) (a b : ℤ) :
    (Function.support (fun n : ℤ =>
      positive h n • mode w (a - n) (mode w (b + n) f))).Finite := by
  simpa only [Algebra.smul_def, MvPolynomial.algebraMap_eq] using
    weighted_twoFields_mode_convolution_finite w h f a b

theorem quadraticConvolution_eq_coeff (w : K) (h : PowerSeries K)
    (f : Space K) (a b : ℤ) :
    quadraticConvolution w h f a b =
      (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        twoFields w f).coeff (-b)).coeff (-a) := by
  rw [weighted_twoFields_coeff]
  simp only [quadraticConvolution, Algebra.smul_def, MvPolynomial.algebraMap_eq]

noncomputable def weightedTensorCoefficient (w : K) (h : PowerSeries K)
    (s t : Fin 3) (f : Space K) (a b : ℤ) : Space K :=
  (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
    twoSummands w s t f).coeff (-b)).coeff (-a)

theorem quadraticConvolution_tensor_sum (w : K) (h : PowerSeries K)
    (f : Space K) (a b : ℤ) :
    quadraticConvolution w h f a b =
      (1 / 144 : K) • ∑ s : Fin 3, ∑ t : Fin 3,
        weightedTensorCoefficient w h s t f a b := by
  have hsmul (c : K) (F : LaurentSeries (LaurentSeries (Space K))) :
      c • F = HahnSeries.C (HahnSeries.C (MvPolynomial.C c)) * F := by
    apply HahnSeries.ext
    funext j
    apply HahnSeries.ext
    funext i
    simp only [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
      HahnSeries.coeff_smul, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [quadraticConvolution_eq_coeff, twoFields_eq_sum, hsmul]
  rw [← mul_assoc, mul_comm (ratioEmbedding h : LaurentSeries (LaurentSeries (Space K)))
      (HahnSeries.C (HahnSeries.C (MvPolynomial.C (1 / 144 : K)))),
    mul_assoc]
  simp only [Finset.mul_sum, HahnSeries.coeff_sum, weightedTensorCoefficient,
    HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    Algebra.smul_def, MvPolynomial.algebraMap_eq]

/-- The full symmetric mode relation, reduced to the source's two
Fourier kernels. No mode relation is assumed. -/
theorem quadraticConvolution_symmetric_kernel (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (h : PowerSeries K) (f : Space K) (a b : ℤ) :
    quadraticConvolution w h f a b + quadraticConvolution w h f b a =
      sameResidue w f a b (Scalar.symmetricFourier (Scalar.G w 0 ^ 2 * h)) +
        mixedResidue w f a b
          (Scalar.symmetricFourier (Scalar.H w (-Scalar.exponents 0) * h)) := by
  let cs := Scalar.symmetricFourier (Scalar.G w 0 ^ 2 * h)
  let cd := Scalar.symmetricFourier (Scalar.H w (-Scalar.exponents 0) * h)
  have hp (s t : Fin 3) :
      weightedTensorCoefficient w h s t f a b + weightedTensorCoefficient w h t s f b a =
        (if s = t then normalResidue w s s f a b cs else 0) +
          (if s = t then 0 else normalResidue w s t f a b cd) := by
    by_cases hst : s = t
    · subst t
      simp only [ite_true, add_zero]
      exact weighted_same_symmetric w hw h s f (-a) (-b)
    · simp only [if_neg hst, zero_add]
      exact weighted_distinct_symmetric w hw h s t hst f (-a) (-b)
  have hs :
      (∑ s : Fin 3, ∑ t : Fin 3, weightedTensorCoefficient w h s t f b a) =
      (∑ s : Fin 3, ∑ t : Fin 3, weightedTensorCoefficient w h t s f b a) :=
    Finset.sum_comm
  rw [quadraticConvolution_tensor_sum, quadraticConvolution_tensor_sum, hs, ← smul_add]
  simp only [← Finset.sum_add_distrib]
  simp_rw [hp]
  simp [sameResidue_apply, mixedResidue_apply, Finset.sum_add_distrib, smul_add, cs, cd]

/-- The full skew relation uses the same residue maps with antisymmetric kernels. -/
theorem quadraticConvolution_antisymmetric_kernel (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (h : PowerSeries K) (f : Space K) (a b : ℤ) :
    quadraticConvolution w h f a b - quadraticConvolution w h f b a =
      sameResidue w f a b (Scalar.antisymmetricFourier (Scalar.G w 0 ^ 2 * h)) +
        mixedResidue w f a b
          (Scalar.antisymmetricFourier (Scalar.H w (-Scalar.exponents 0) * h)) := by
  let cs := Scalar.antisymmetricFourier (Scalar.G w 0 ^ 2 * h)
  let cd := Scalar.antisymmetricFourier (Scalar.H w (-Scalar.exponents 0) * h)
  have hp (s t : Fin 3) :
      weightedTensorCoefficient w h s t f a b - weightedTensorCoefficient w h t s f b a =
        (if s = t then normalResidue w s s f a b cs else 0) +
          (if s = t then 0 else normalResidue w s t f a b cd) := by
    by_cases hst : s = t
    · subst t
      simp only [ite_true, add_zero]
      exact weighted_same_antisymmetric w hw h s f (-a) (-b)
    · simp only [if_neg hst, zero_add]
      exact weighted_distinct_antisymmetric w hw h s t hst f (-a) (-b)
  have hs :
      (∑ s : Fin 3, ∑ t : Fin 3, weightedTensorCoefficient w h s t f b a) =
      (∑ s : Fin 3, ∑ t : Fin 3, weightedTensorCoefficient w h t s f b a) :=
    Finset.sum_comm
  rw [quadraticConvolution_tensor_sum, quadraticConvolution_tensor_sum, hs, ← smul_sub]
  simp only [← Finset.sum_sub_distrib]
  simp_rw [hp]
  simp [sameResidue_apply, mixedResidue_apply, Finset.sum_add_distrib, smul_add, cs, cd]

end KanadeRussell.Tsuchioka.Fock
