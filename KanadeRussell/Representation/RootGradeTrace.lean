import KanadeRussell.Representation.RootOccupationGrading
import Mathlib.LinearAlgebra.Trace

/-! Restrictions to actual finite root grades and algebraic trace identities.
No character formula or recurrence is assumed. -/
set_option autoImplicit false
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

/-- An ambient operator with a specified root-grade shift, restricted to its
actual source and target root subspaces. -/
def rootGradeRestriction (beta gamma : RootCoefficients) (f : Module.End K V)
    (hf : ∀ v, v ∈ M.rootGrade beta → f v ∈ M.rootGrade gamma) :
    M.rootGrade beta →ₗ[K] M.rootGrade gamma where
  toFun v := ⟨f v.val, hf v.val v.property⟩
  map_add' x y := by apply Subtype.ext; exact f.map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact f.map_smul c x.val

@[simp] theorem rootGradeRestriction_val (beta gamma : RootCoefficients) (f : Module.End K V)
    (hf : ∀ v, v ∈ M.rootGrade beta → f v ∈ M.rootGrade gamma) (v : M.rootGrade beta) :
    (M.rootGradeRestriction beta gamma f hf v).val = f v.val := rfl

/-- Cyclicity of trace holds even when the two finite root grades have different dimensions. -/
theorem rootGrade_trace_comp_comm (beta gamma : RootCoefficients)
    (f : M.rootGrade beta →ₗ[K] M.rootGrade gamma)
    (g : M.rootGrade gamma →ₗ[K] M.rootGrade beta) :
    LinearMap.trace K (M.rootGrade beta) (g.comp f) =
      LinearMap.trace K (M.rootGrade gamma) (f.comp g) := by
  letI := M.rootGrade_finite beta
  letI := M.rootGrade_finite gamma
  exact LinearMap.trace_comp_comm' f g

/-- The down/up traces agree for restrictions of the original ambient operators. -/
theorem rootGradeRestriction_trace_comp_comm (beta gamma : RootCoefficients)
    (f g : Module.End K V)
    (hf : ∀ v, v ∈ M.rootGrade beta → f v ∈ M.rootGrade gamma)
    (hg : ∀ v, v ∈ M.rootGrade gamma → g v ∈ M.rootGrade beta) :
    LinearMap.trace K (M.rootGrade beta)
      ((M.rootGradeRestriction gamma beta g hg).comp (M.rootGradeRestriction beta gamma f hf)) =
    LinearMap.trace K (M.rootGrade gamma)
      ((M.rootGradeRestriction beta gamma f hf).comp (M.rootGradeRestriction gamma beta g hg)) :=
  M.rootGrade_trace_comp_comm beta gamma _ _

theorem rootGrade_trace_scalar (beta : RootCoefficients) (c : K) :
    LinearMap.trace K (M.rootGrade beta) (c • (1 : Module.End K (M.rootGrade beta))) =
      (Module.finrank K (M.rootGrade beta) : K) * c := by
  letI := M.rootGrade_finite beta
  simp [mul_comm]

/-- A scalar ambient action on a root grade has the expected trace after restriction. -/
theorem rootGradeRestriction_trace_of_scalar (beta : RootCoefficients) (f : Module.End K V)
    (hf : ∀ v, v ∈ M.rootGrade beta → f v ∈ M.rootGrade beta)
    (c : K) (hscalar : ∀ v, v ∈ M.rootGrade beta → f v = c • v) :
    LinearMap.trace K (M.rootGrade beta) (M.rootGradeRestriction beta beta f hf) =
      (Module.finrank K (M.rootGrade beta) : K) * c := by
  have heq : M.rootGradeRestriction beta beta f hf = c • (1 : Module.End K (M.rootGrade beta)) := by
    ext v
    exact hscalar v.val v.property
  rw [heq, M.rootGrade_trace_scalar]

end KanadeRussell.Representation.PrincipalHighestWeightModule
