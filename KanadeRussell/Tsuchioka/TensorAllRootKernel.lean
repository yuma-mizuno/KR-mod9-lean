import KanadeRussell.Tsuchioka.TensorRootScalars
import KanadeRussell.Tsuchioka.TensorCommutatorKernel

/-! Every tensor root commutator is a finite contraction of the forward
and reverse rational scalar expansions. All lattice pairs are covered;
the non-first-root residues are not assumed to be affine brackets. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Scalar

open FormalSeries RootData

variable {K : Type*} [Field K] [CharZero K]

noncomputable def rootCommutatorKernel (w : K) (beta gamma : Lattice) (n : ℤ) : K :=
  positive (rootScalar w beta gamma) n - positive (rootScalar w gamma beta) (-n)

end KanadeRussell.Tsuchioka.Scalar

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (Lattice)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorNormalProduct_mixed_expansions (w : K) (beta gamma : Lattice)
    (s t : Fin 3) (f : Space K) (h g : PowerSeries K) (a b : ℤ) :
    (((ratioEmbedding h : LaurentSeries (LaurentSeries (Space K))) *
        tensorNormalProduct w beta gamma s t f).coeff b).coeff a -
      (((ratioEmbedding g : LaurentSeries (LaurentSeries (Space K))) *
        tensorNormalProduct w gamma beta t s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C (positive h n - positive g (-n)))
        (tensorNormalProduct w beta gamma s t f) a b := by
  obtain ⟨l, r, hb⟩ := tensorNormalProduct_bounded w beta gamma s t f
  rw [ratio_product_coeff, ratio_product_coeff,
    tensorNormalProduct_contract_swapped w beta gamma s t f
      (fun n => MvPolynomial.C (positive g n)) a b]
  have hc : (fun n => (MvPolynomial.C (positive h n - positive g (-n)) : Space K)) =
      (fun n => MvPolynomial.C (positive h n)) -
        reflect (fun n => MvPolynomial.C (positive g n)) := by
    funext n
    simp [reflect]
  rw [hc, contract_sub hb]

theorem tensorTwoSummands_same_commutator_kernel (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta gamma : Lattice)
    (s : Fin 3) (f : Space K) (a b : ℤ) :
    ((tensorTwoSummands w beta gamma s s f).coeff b).coeff a -
      ((tensorTwoSummands w gamma beta s s f).coeff a).coeff b =
      contract (fun n => MvPolynomial.C (Scalar.rootCommutatorKernel w beta gamma n))
        (tensorNormalProduct w beta gamma s s f) a b := by
  rw [tensorTwoSummands_same_rootScalar w hw, tensorTwoSummands_same_rootScalar w hw]
  rw [mul_comm (tensorNormalProduct w beta gamma s s f),
    mul_comm (tensorNormalProduct w gamma beta s s f)]
  exact tensorNormalProduct_mixed_expansions w beta gamma s s f
    (Scalar.rootScalar w beta gamma) (Scalar.rootScalar w gamma beta) a b

/-- The full mode commutator for arbitrary lattice pairs reduces to three
same-position terms; every contraction has separately bounded support. -/
theorem tensorRootMode_commutator_kernel (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta gamma : Lattice)
    (f : Space K) (a b : ℤ) :
    tensorRootMode w beta a (tensorRootMode w gamma b f) -
        tensorRootMode w gamma b (tensorRootMode w beta a f) =
      (1 / 144 : K) • ∑ s : Fin 3,
        contract (fun n => MvPolynomial.C (Scalar.rootCommutatorKernel w beta gamma n))
          (tensorNormalProduct w beta gamma s s f) (-a) (-b) := by
  let P (beta gamma : Lattice) (s t : Fin 3) (a b : ℤ) : Space K :=
    ((tensorTwoSummands w beta gamma s t f).coeff (-b)).coeff (-a)
  have hfield (beta gamma : Lattice) (i j : ℤ) :
      tensorRootMode w beta i (tensorRootMode w gamma j f) =
        (1 / 144 : K) • ∑ s : Fin 3, ∑ t : Fin 3, P beta gamma s t i j := by
    have h := congrArg (fun F : LaurentSeries (LaurentSeries (Space K)) =>
      (F.coeff (-j)).coeff (-i)) (tensorTwoFields_eq_sum w beta gamma f)
    simpa only [tensorTwoFields_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_sum, P] using h
  have hp (s t : Fin 3) : P beta gamma s t a b - P gamma beta t s b a =
      if s = t then contract
        (fun n => MvPolynomial.C (Scalar.rootCommutatorKernel w beta gamma n))
          (tensorNormalProduct w beta gamma s s f) (-a) (-b) else 0 := by
    by_cases hst : s = t
    · subst t
      simp only [if_true]
      exact tensorTwoSummands_same_commutator_kernel w hw beta gamma s f (-a) (-b)
    · simp only [if_neg hst]
      apply sub_eq_zero.mpr
      exact tensorRootSummand_modes_commute_distinct w beta gamma s t hst a b f
  have hs : (∑ s : Fin 3, ∑ t : Fin 3, P gamma beta s t b a) =
      ∑ s : Fin 3, ∑ t : Fin 3, P gamma beta t s b a := Finset.sum_comm
  rw [hfield beta gamma a b, hfield gamma beta b a, hs, ← smul_sub]
  simp only [← Finset.sum_sub_distrib]
  simp_rw [hp]
  simp

end KanadeRussell.Tsuchioka.Fock
