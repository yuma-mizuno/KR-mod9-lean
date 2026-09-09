import KanadeRussell.Representation.TensorPrimitiveUniqueness

/-! Primitive vectors in root grades of the actual three tensor cyclic modules
belong to their highest lines. No character theorem is assumed. -/
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice Sectors
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem tensorPrincipalModule_primitive_mem_highestLine
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed)
    (beta : RootCoefficients) (v : tensorCyclicSpan w seed)
    (hgrade : v ∈ M.rootGrade beta) (hE : ∀ i, M.action.E i v=0) :
    v ∈ Submodule.span K {M.highestVector} := by
  by_cases hv : v=0
  · rw [hv]; exact Submodule.zero_mem _
  exact tensorPrincipalModule_primitive_mem_highestLine_of_operator_equations
    w hw seed M haction (tensorModeCasimir_lie w hw) beta v hv hgrade hE

theorem skewPrincipalModule_primitive_mem_highestLine
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients)
    (v : tensorCyclicSpan w (skewSeed : Space K))
    (hgrade : v ∈ (skewPrincipalModule w hw).rootGrade beta)
    (hE : ∀ i, (skewPrincipalModule w hw).action.E i v=0) :
    v ∈ Submodule.span K {(skewPrincipalModule w hw).highestVector} :=
  tensorPrincipalModule_primitive_mem_highestLine w hw skewSeed
    (skewPrincipalModule w hw) rfl beta v hgrade hE

theorem vacuumPrincipalModule_primitive_mem_highestLine
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients)
    (v : tensorCyclicSpan w (1 : Space K))
    (hgrade : v ∈ (vacuumPrincipalModule w hw).rootGrade beta)
    (hE : ∀ i, (vacuumPrincipalModule w hw).action.E i v=0) :
    v ∈ Submodule.span K {(vacuumPrincipalModule w hw).highestVector} :=
  tensorPrincipalModule_primitive_mem_highestLine w hw 1
    (vacuumPrincipalModule w hw) rfl beta v hgrade hE

theorem alternatingPrincipalModule_primitive_mem_highestLine
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients)
    (v : tensorCyclicSpan w (alternatingSeed : Space K))
    (hgrade : v ∈ (alternatingPrincipalModule w hw).rootGrade beta)
    (hE : ∀ i, (alternatingPrincipalModule w hw).action.E i v=0) :
    v ∈ Submodule.span K {(alternatingPrincipalModule w hw).highestVector} :=
  tensorPrincipalModule_primitive_mem_highestLine w hw alternatingSeed
    (alternatingPrincipalModule w hw) rfl beta v hgrade hE

end KanadeRussell.Representation
