import KanadeRussell.Representation.TensorPrimitiveUniqueness
import KanadeRussell.Representation.RootGradeTrace

/-! Scalar action and trace of the actual locally finite tensor-mode Casimir
on root grades. Its operator equations are proved, not supplied as assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice Sectors
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem tensorPrincipalModule_casimir_rootGrade
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed)
    (beta : RootCoefficients) (v : tensorCyclicSpan w seed) (hv : v ∈ M.rootGrade beta) :
    tensorCyclicModeCasimir w seed v =
      ((-2 * casimir (fun i => M.highestWeightLabels i + 1) beta : ℤ) : K) • v := by
  have hhighest : tensorCyclicModeCasimir w seed M.highestVector = 0 := by
    apply Subtype.ext
    change tensorModeCasimir w M.highestVector.val = 0
    apply tensorModeCasimir_kills_primitive w hw
    intro i
    have h := congrArg Subtype.val (M.E_highestVector i)
    simpa only [haction, tensorCyclicChevalleyAction_E_val, ZeroMemClass.coe_zero] using h
  have hcomm : ∀ i, ⁅tensorCyclicModeCasimir w seed, M.action.F i⁆ =
      (2 * (symmetrizer i : K)) • (M.action.F i * M.action.H i) := by
    intro i
    rw [haction]
    exact tensorCyclicModeCasimir_lie_of_operator_equation w hw seed i (tensorModeCasimir_lie w hw i)
  exact M.casimir_rootGrade _ hhighest hcomm beta v hv

theorem tensorPrincipalModule_casimir_preserves_rootGrade
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed)
    (beta : RootCoefficients) (v : tensorCyclicSpan w seed) (hv : v ∈ M.rootGrade beta) :
    tensorCyclicModeCasimir w seed v ∈ M.rootGrade beta := by
  rw [tensorPrincipalModule_casimir_rootGrade w hw seed M haction beta v hv]
  exact (M.rootGrade beta).smul_mem _ hv

noncomputable def tensorPrincipalModule_rootGradeCasimir
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed)
    (beta : RootCoefficients) : Module.End K (M.rootGrade beta) :=
  M.rootGradeRestriction beta beta (tensorCyclicModeCasimir w seed)
    (tensorPrincipalModule_casimir_preserves_rootGrade w hw seed M haction beta)

@[simp] theorem tensorPrincipalModule_rootGradeCasimir_val
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed)
    (beta : RootCoefficients) (v : M.rootGrade beta) :
    (tensorPrincipalModule_rootGradeCasimir w hw seed M haction beta v).val.val =
      tensorModeCasimir w v.val.val := rfl

theorem tensorPrincipalModule_casimir_trace
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed)
    (beta : RootCoefficients) :
    LinearMap.trace K (M.rootGrade beta)
      (tensorPrincipalModule_rootGradeCasimir w hw seed M haction beta) =
      (Module.finrank K (M.rootGrade beta) : K) *
        ((-2 * casimir (fun i => M.highestWeightLabels i + 1) beta : ℤ) : K) :=
  M.rootGradeRestriction_trace_of_scalar beta _ _ _
    (tensorPrincipalModule_casimir_rootGrade w hw seed M haction beta)

theorem skewPrincipalModule_casimir_rootGrade
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients)
    (v : tensorCyclicSpan w (skewSeed : Space K))
    (hv : v ∈ (skewPrincipalModule w hw).rootGrade beta) :
    tensorCyclicModeCasimir w skewSeed v =
      ((-2 * casimir (fun i => (skewPrincipalModule w hw).highestWeightLabels i + 1) beta : ℤ) : K) • v :=
  tensorPrincipalModule_casimir_rootGrade w hw skewSeed (skewPrincipalModule w hw) rfl beta v hv

theorem skewPrincipalModule_casimir_trace
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients) :
    LinearMap.trace K ((skewPrincipalModule w hw).rootGrade beta)
      (tensorPrincipalModule_rootGradeCasimir w hw skewSeed (skewPrincipalModule w hw) rfl beta) =
      (Module.finrank K ((skewPrincipalModule w hw).rootGrade beta) : K) *
        ((-2 * casimir (fun i => (skewPrincipalModule w hw).highestWeightLabels i + 1) beta : ℤ) : K) :=
  tensorPrincipalModule_casimir_trace w hw skewSeed (skewPrincipalModule w hw) rfl beta

theorem vacuumPrincipalModule_casimir_rootGrade
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients)
    (v : tensorCyclicSpan w (1 : Space K))
    (hv : v ∈ (vacuumPrincipalModule w hw).rootGrade beta) :
    tensorCyclicModeCasimir w 1 v =
      ((-2 * casimir (fun i => (vacuumPrincipalModule w hw).highestWeightLabels i + 1) beta : ℤ) : K) • v :=
  tensorPrincipalModule_casimir_rootGrade w hw 1 (vacuumPrincipalModule w hw) rfl beta v hv

theorem vacuumPrincipalModule_casimir_trace
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients) :
    LinearMap.trace K ((vacuumPrincipalModule w hw).rootGrade beta)
      (tensorPrincipalModule_rootGradeCasimir w hw 1 (vacuumPrincipalModule w hw) rfl beta) =
      (Module.finrank K ((vacuumPrincipalModule w hw).rootGrade beta) : K) *
        ((-2 * casimir (fun i => (vacuumPrincipalModule w hw).highestWeightLabels i + 1) beta : ℤ) : K) :=
  tensorPrincipalModule_casimir_trace w hw 1 (vacuumPrincipalModule w hw) rfl beta

theorem alternatingPrincipalModule_casimir_rootGrade
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients)
    (v : tensorCyclicSpan w (alternatingSeed : Space K))
    (hv : v ∈ (alternatingPrincipalModule w hw).rootGrade beta) :
    tensorCyclicModeCasimir w alternatingSeed v =
      ((-2 * casimir (fun i => (alternatingPrincipalModule w hw).highestWeightLabels i + 1) beta : ℤ) : K) • v :=
  tensorPrincipalModule_casimir_rootGrade w hw alternatingSeed (alternatingPrincipalModule w hw) rfl beta v hv

theorem alternatingPrincipalModule_casimir_trace
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients) :
    LinearMap.trace K ((alternatingPrincipalModule w hw).rootGrade beta)
      (tensorPrincipalModule_rootGradeCasimir w hw alternatingSeed (alternatingPrincipalModule w hw) rfl beta) =
      (Module.finrank K ((alternatingPrincipalModule w hw).rootGrade beta) : K) *
        ((-2 * casimir (fun i => (alternatingPrincipalModule w hw).highestWeightLabels i + 1) beta : ℤ) : K) :=
  tensorPrincipalModule_casimir_trace w hw alternatingSeed (alternatingPrincipalModule w hw) rfl beta
end KanadeRussell.Representation
