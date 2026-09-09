import KanadeRussell.Tsuchioka.TensorModeResidues
import KanadeRussell.Tsuchioka.ScalarContraction

/-! Finite linear residue maps and pole-fusion coefficients for arbitrary
tensor root pairs. Every fusion conclusion uses a proved lattice equality. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (Lattice simpleRoot coxeter)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorRootPair_delta_fusion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta gamma : Lattice) (p q : ℕ) (β : Lattice)
    (hfusion : (coxeter^[p]) beta + gamma = (coxeter^[q]) β)
    (j : Fin 3) (f : Space K) (a b : ℤ) :
    contract (fun n : ℤ => MvPolynomial.C (w ^ (-(p : ℤ) * n)))
        (tensorNormalProduct w beta gamma j j f) (-a) (-b) =
      w ^ (((q : ℤ) - p) * a + q * b) •
        (tensorRootSummand w β j f).coeff (-(a + b)) := by
  have hc : (fun n : ℤ => MvPolynomial.C (w ^ (-(p : ℤ) * n))) =
      (fun n => ((phaseUnit w hw p ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    exact (phaseUnit_zpow w hw p n).symm
  rw [hc, tensorNormalProduct_delta_contraction_same, hfusion,
    tensorRootSummand_iterate w hw, coeff_laurentRescale, phaseUnit_zpow]
  rw [show -a + -b = -(a + b) by ring]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [← mul_assoc, ← map_mul, ← zpow_add₀ (Coefficients.root_ne_zero w hw)]
  congr 2
  ring

/-- Summing all tensor positions and restoring the field normalization gives
the coefficient 1/12 multiplying the fused root mode. -/
theorem tensorRootPair_delta_sum_fusion (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (beta gamma : Lattice) (p q : ℕ) (β : Lattice)
    (hfusion : (coxeter^[p]) beta + gamma = (coxeter^[q]) β)
    (f : Space K) (a b : ℤ) :
    (1 / 144 : K) • ∑ j : Fin 3,
      contract (fun n : ℤ => MvPolynomial.C (w ^ (-(p : ℤ) * n)))
        (tensorNormalProduct w beta gamma j j f) (-a) (-b) =
      (w ^ (((q : ℤ) - p) * a + q * b) / 12) • tensorRootMode w β (a + b) f := by
  simp_rw [tensorRootPair_delta_fusion w hw beta gamma p q β hfusion]
  rw [← Finset.smul_sum, sum_tensorRootSummand_coeff, smul_smul, smul_smul]
  congr 1
  ring

/-- Finite contraction against one normal product, as a linear map in the kernel. -/
noncomputable def tensorPairNormalResidue (w : K) (beta gamma : Lattice) (s t : Fin 3) (f : Space K) (a b : ℤ) :
    (ℤ → K) →ₗ[K] Space K where
  toFun c := scalarContract c (tensorNormalProduct w beta gamma s t f) (-a) (-b)
  map_add' c d := by
    obtain ⟨l, r, h⟩ := tensorNormalProduct_bounded w beta gamma s t f
    exact scalarContract_add h c d (-a) (-b)
  map_smul' z c := by
    obtain ⟨l, r, h⟩ := tensorNormalProduct_bounded w beta gamma s t f
    change scalarContract (fun n => z * c n) (tensorNormalProduct w beta gamma s t f) (-a) (-b) =
      z • scalarContract c (tensorNormalProduct w beta gamma s t f) (-a) (-b)
    exact scalarContract_mul h c z (-a) (-b)

@[simp] theorem tensorPairNormalResidue_apply (w : K) (beta gamma : Lattice) (s t : Fin 3) (f : Space K) (a b : ℤ)
    (c : ℤ → K) :
    tensorPairNormalResidue w beta gamma s t f a b c =
      scalarContract c (tensorNormalProduct w beta gamma s t f) (-a) (-b) := rfl

noncomputable def tensorRootPairResidue (w : K) (beta gamma : Lattice) (f : Space K) (a b : ℤ) :
    (ℤ → K) →ₗ[K] Space K :=
  (1 / 144 : K) • ∑ j : Fin 3, tensorPairNormalResidue w beta gamma j j f a b

theorem tensorRootPairResidue_apply (w : K) (beta gamma : Lattice) (f : Space K) (a b : ℤ) (c : ℤ → K) :
    tensorRootPairResidue w beta gamma f a b c =
      (1 / 144 : K) • ∑ j : Fin 3, tensorPairNormalResidue w beta gamma j j f a b c := by
  simp only [tensorRootPairResidue, LinearMap.smul_apply, LinearMap.sum_apply]

theorem tensorRootPairResidue_phase_fusion (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (beta gamma eta : Lattice)
    (p : Fin 12) (q : ℕ)
    (hfusion : (coxeter^[p.val]) beta + gamma = (coxeter^[q]) eta)
    (f : Space K) (a b : ℤ) :
    tensorRootPairResidue w beta gamma f a b
      (fun n => (Scalar.phasePolynomial w p) ^ n) =
      (w ^ (((q : ℤ) - p.val) * a + q * b) / 12) •
        tensorRootMode w eta (a + b) f := by
  simp only [tensorRootPairResidue_apply, tensorPairNormalResidue_apply,
    ← Scalar.negative_phase w hw]
  change (1 / 144 : K) • ∑ j : Fin 3,
    scalarContract (Scalar.delta (w ^ (-(p.val : ℤ))))
      (tensorNormalProduct w beta gamma j j f) (-a) (-b) = _
  simp_rw [scalarContract_delta_phase]
  exact tensorRootPair_delta_sum_fusion w hw beta gamma p.val q eta hfusion f a b

end KanadeRussell.Tsuchioka.Fock
