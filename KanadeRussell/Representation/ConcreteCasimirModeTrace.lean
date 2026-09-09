import KanadeRussell.Representation.NegativePrincipalModes
import KanadeRussell.Representation.ConcreteCasimirCutoff
import KanadeRussell.Representation.ConcreteCasimirTrace
import KanadeRussell.Representation.RootModeTraceRecurrence

/-! The actual root-grade Casimir is a finite sum of ordered eigenmode
products. Taking trace gives its concrete finite mode-trace expression. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def tensorPrincipalModule_rootModeProduct
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (n : ℕ) (r : Fin 3) (beta : RootCoefficients) : Module.End K (M.rootGrade beta) :=
  (M.rootModeUpBack (negativeCyclicPrincipalMode w seed n r) (positiveModeOccupation n r)
    (tensorPrincipalModule_negativeMode_mem_rootGrade w hw seed M haction d hD n r) beta).comp
  (M.rootModeDown (positiveCyclicPrincipalMode w seed n r) (positiveModeOccupation n r)
    (tensorPrincipalModule_positiveMode_mem_rootGrade w hw seed M haction d hD n r) beta)

@[simp] theorem tensorPrincipalModule_rootModeProduct_val
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (n : ℕ) (r : Fin 3) (beta : RootCoefficients) (v : M.rootGrade beta) :
    (tensorPrincipalModule_rootModeProduct w hw seed M haction d hD n r beta v).val.val =
      negativePrincipalMode w n r (positivePrincipalMode w n r v.val.val) := rfl

theorem tensorPrincipalModule_rootGradeCasimir_eq_modeSum
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (beta : RootCoefficients) :
    tensorPrincipalModule_rootGradeCasimir w hw seed M haction beta =
      (2:K) • ∑ n ∈ Finset.range (totalDegree beta).toNat,
        ∑ r : Fin 3, tensorPrincipalModule_rootModeProduct w hw seed M haction d hD n r beta := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply Subtype.ext
  simp only [tensorPrincipalModule_rootGradeCasimir_val, LinearMap.smul_apply,
    LinearMap.sum_apply, Submodule.coe_smul, Submodule.coe_sum,
    tensorPrincipalModule_rootModeProduct_val]
  rw [tensorPrincipalModule_casimir_apply_eq_relative_sum w hw seed M haction d hD beta v.val v.property]
  simp only [normalOrderedMode_eq_negative_positive w hw, LinearMap.sum_apply, Module.End.mul_apply]

theorem tensorPrincipalModule_casimir_trace_eq_modeSum
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (beta : RootCoefficients) :
    LinearMap.trace K (M.rootGrade beta)
      (tensorPrincipalModule_rootGradeCasimir w hw seed M haction beta) =
      2 * ∑ n ∈ Finset.range (totalDegree beta).toNat, ∑ r : Fin 3,
        M.rootModeTrace (positiveCyclicPrincipalMode w seed n r) (negativeCyclicPrincipalMode w seed n r)
          (positiveModeOccupation n r)
          (tensorPrincipalModule_positiveMode_mem_rootGrade w hw seed M haction d hD n r)
          (tensorPrincipalModule_negativeMode_mem_rootGrade w hw seed M haction d hD n r) beta := by
  rw [tensorPrincipalModule_rootGradeCasimir_eq_modeSum w hw seed M haction d hD beta]
  simp only [map_smul, map_sum, smul_eq_mul, tensorPrincipalModule_rootModeProduct,
    PrincipalHighestWeightModule.rootModeTrace]

/-- The scalar Casimir recurrence has the negative of the ordered mode-trace sum. -/
theorem tensorPrincipalModule_casimir_mul_finrank_eq_neg_modeSum
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (beta : RootCoefficients) :
    (casimir (fun i => M.highestWeightLabels i+1) beta : K) *
      (Module.finrank K (M.rootGrade beta) : K) =
      -(∑ n ∈ Finset.range (totalDegree beta).toNat, ∑ r : Fin 3,
        M.rootModeTrace (positiveCyclicPrincipalMode w seed n r) (negativeCyclicPrincipalMode w seed n r)
          (positiveModeOccupation n r)
          (tensorPrincipalModule_positiveMode_mem_rootGrade w hw seed M haction d hD n r)
          (tensorPrincipalModule_negativeMode_mem_rootGrade w hw seed M haction d hD n r) beta) := by
  have h := (tensorPrincipalModule_casimir_trace w hw seed M haction beta).symm.trans
    (tensorPrincipalModule_casimir_trace_eq_modeSum w hw seed M haction d hD beta)
  push_cast at h
  linear_combination (-1/2 : K) * h

end KanadeRussell.Representation
