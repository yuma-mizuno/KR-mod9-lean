import KanadeRussell.Tsuchioka.TensorJointAnnihilation
import KanadeRussell.Tsuchioka.RatioContraction
import KanadeRussell.Tsuchioka.CommutatorScalar

/-! The actual tensor first-root commutator as a finite Fourier contraction.
TensorFirstRootCommutator evaluates its delta and Euler residues as root,
Heisenberg, and central terms; affine-module identification remains separate. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (Lattice simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorNormalProduct_contract_swapped (w : K) (β γ : Lattice)
    (s t : Fin 3) (f : Space K) (c : ℤ → Space K) (a b : ℤ) :
    contract c (tensorNormalProduct w γ β t s f) b a =
      contract (reflect c) (tensorNormalProduct w β γ s t f) a b := by
  unfold contract
  apply finsum_eq_of_bijective (fun n : ℤ => -n)
    (Function.Involutive.bijective (fun n : ℤ => neg_neg n))
  intro n
  rw [tensorNormalProduct_swapped]
  simp only [reflect, neg_neg, sub_eq_add_neg]

theorem tensorNormalProduct_antisymmetric_expansions (w : K) (β γ : Lattice)
    (s t : Fin 3) (f : Space K) (h : PowerSeries K) (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        tensorNormalProduct w β γ s t f).coeff b).coeff a -
      (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        tensorNormalProduct w γ β t s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C (Scalar.antisymmetricFourier h n))
        (tensorNormalProduct w β γ s t f) a b := by
  obtain ⟨l, r, hb⟩ := tensorNormalProduct_bounded w β γ s t f
  rw [ratio_product_coeff, ratio_product_coeff,
    tensorNormalProduct_contract_swapped w β γ s t f (fun n => MvPolynomial.C (positive h n)) a b]
  have hc : (fun n => (MvPolynomial.C (Scalar.antisymmetricFourier h n) : Space K)) =
      (fun n => MvPolynomial.C (positive h n)) -
        reflect (fun n => MvPolynomial.C (positive h n)) := by
    funext n
    simp [Scalar.antisymmetricFourier, reflect]
  rw [hc, contract_sub hb]

theorem tensorTwoSummands_first_same_kernel (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s : Fin 3) (f : Space K) (a b : ℤ) :
    ((tensorTwoSummands w (simpleRoot 0) (simpleRoot 0) s s f).coeff b).coeff a -
      ((tensorTwoSummands w (simpleRoot 0) (simpleRoot 0) s s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C (Scalar.antisymmetricFourier (Scalar.G w 0 ^ 3) n))
        (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) s s f) a b := by
  have h := tensorNormalProduct_antisymmetric_expansions w (simpleRoot 0) (simpleRoot 0)
    s s f (Scalar.G w 0 ^ 3) a b
  rw [tensorTwoSummands_first_same_source w hw]
  simp only [map_pow (ratioEmbedding (K := K)), ratioEmbedding_G1] at h
  rw [mul_comm (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) s s f)]
  exact h

/-- Distinct tensor positions cancel. The remaining three terms use the
full, untruncated G1-cubed Fourier kernel. -/
theorem tensorRootMode_first_commutator_kernel (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootMode w (simpleRoot 0) a (tensorRootMode w (simpleRoot 0) b f) -
        tensorRootMode w (simpleRoot 0) b (tensorRootMode w (simpleRoot 0) a f) =
      (1 / 144 : K) • ∑ s : Fin 3,
        contract (fun n => MvPolynomial.C (Scalar.antisymmetricFourier (Scalar.G w 0 ^ 3) n))
          (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) s s f) (-a) (-b) := by
  let P (s t : Fin 3) (a b : ℤ) : Space K :=
    ((tensorTwoSummands w (simpleRoot 0) (simpleRoot 0) s t f).coeff (-b)).coeff (-a)
  have hfield (i j : ℤ) :
      tensorRootMode w (simpleRoot 0) i (tensorRootMode w (simpleRoot 0) j f) =
        (1 / 144 : K) • ∑ s : Fin 3, ∑ t : Fin 3, P s t i j := by
    have h := congrArg (fun F : LaurentSeries (LaurentSeries (Space K)) =>
      (F.coeff (-j)).coeff (-i)) (tensorTwoFields_eq_sum w (simpleRoot 0) (simpleRoot 0) f)
    simpa only [tensorTwoFields_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_sum, P] using h
  have hp (s t : Fin 3) : P s t a b - P t s b a =
      if s = t then contract
        (fun n => MvPolynomial.C (Scalar.antisymmetricFourier (Scalar.G w 0 ^ 3) n))
          (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) s s f) (-a) (-b) else 0 := by
    by_cases hst : s = t
    · subst t
      simp only [if_true]
      exact tensorTwoSummands_first_same_kernel w hw s f (-a) (-b)
    · simp only [if_neg hst]
      apply sub_eq_zero.mpr
      exact tensorRootSummand_modes_commute_distinct w (simpleRoot 0) (simpleRoot 0) s t hst a b f
  have hs : (∑ s : Fin 3, ∑ t : Fin 3, P s t b a) =
      ∑ s : Fin 3, ∑ t : Fin 3, P t s b a := Finset.sum_comm
  rw [hfield a b, hfield b a, hs, ← smul_sub]
  simp only [← Finset.sum_sub_distrib]
  simp_rw [hp]
  simp

/-- The concrete commutator has the source's four noncentral poles and
central Euler-delta kernel. Every contraction is finite by the normal-product bounds. -/
theorem tensorRootMode_first_commutator_fourier (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    tensorRootMode w (simpleRoot 0) a (tensorRootMode w (simpleRoot 0) b f) -
        tensorRootMode w (simpleRoot 0) b (tensorRootMode w (simpleRoot 0) a f) =
      (1 / 144 : K) • ∑ s : Fin 3, contract (fun n => MvPolynomial.C
        (Coefficients.pCoeff w * (Scalar.delta (w ^ (-4 : ℤ)) n - Scalar.delta (w ^ 4) n) +
          Scalar.rootSecondResidue w * (Scalar.delta (w ^ (-5 : ℤ)) n - Scalar.delta (w ^ 5) n) +
          (2 * Scalar.cPrime w) * Scalar.eulerDelta (-1) n))
        (tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) s s f) (-a) (-b) := by
  rw [tensorRootMode_first_commutator_kernel w hw, Scalar.G1_cube_fourier w hw]

end KanadeRussell.Tsuchioka.Fock
