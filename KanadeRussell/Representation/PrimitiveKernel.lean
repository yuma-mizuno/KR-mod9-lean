import KanadeRussell.Representation.RootGradeShifts

/-! The common kernel of the raising operators decomposes into its actual root
components, without any hypothesis on a submodule being graded. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped DirectSum
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

noncomputable def rootGradingEquiv : (⨁ beta : RootCoefficients, M.rootGrade beta) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap M.rootGrade) M.rootGrade_isInternal

@[simp] theorem rootGradingEquiv_lof (beta : RootCoefficients) (v : M.rootGrade beta) :
    M.rootGradingEquiv (DirectSum.lof K RootCoefficients (fun b => M.rootGrade b) beta v)=v :=
  DirectSum.coeLinearMap_lof M.rootGrade beta v

theorem rootGradingEquiv_symm_of_mem (beta : RootCoefficients) (v : V)
    (hv : v∈M.rootGrade beta) :
    M.rootGradingEquiv.symm v = DirectSum.lof K RootCoefficients
      (fun b => M.rootGrade b) beta ⟨v,hv⟩ := by
  apply M.rootGradingEquiv.injective
  rw [LinearEquiv.apply_symm_apply, M.rootGradingEquiv_lof]

noncomputable def rootGradeProjection (beta : RootCoefficients) : Module.End K V :=
  (M.rootGrade beta).subtype.comp ((DirectSum.component K RootCoefficients
    (fun b => M.rootGrade b) beta).comp M.rootGradingEquiv.symm.toLinearMap)

theorem rootGradeProjection_mem (beta : RootCoefficients) (v : V) :
    M.rootGradeProjection beta v∈M.rootGrade beta := Subtype.coe_prop _

theorem rootGradeProjection_of_mem (beta : RootCoefficients) (v : V)
    (hv : v∈M.rootGrade beta) : M.rootGradeProjection beta v=v := by
  simp only [rootGradeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    M.rootGradingEquiv_symm_of_mem beta v hv, DirectSum.component.lof_self]
  rfl

theorem rootGradeProjection_of_mem_ne (beta gamma : RootCoefficients) (v : V)
    (hv : v∈M.rootGrade gamma) (hne : beta≠gamma) : M.rootGradeProjection beta v=0 := by
  simp only [rootGradeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    M.rootGradingEquiv_symm_of_mem gamma v hv, DirectSum.component.of, Ne.symm hne, ↓reduceDIte]
  simp

theorem E_rootGradeProjection (i : Fin 3) (beta : RootCoefficients) (v : V) :
    M.action.E i (M.rootGradeProjection beta v) =
      M.rootGradeProjection (beta-Pi.single i 1) (M.action.E i v) := by
  have hhom (gamma : RootCoefficients) (x : V) (hx : x ∈ M.rootGrade gamma) :
      M.action.E i (M.rootGradeProjection beta x) =
        M.rootGradeProjection (beta-Pi.single i 1) (M.action.E i x) := by
    by_cases h : beta=gamma
    · subst gamma
      rw [M.rootGradeProjection_of_mem beta x hx]
      exact (M.rootGradeProjection_of_mem _ _ (M.E_mem_rootGrade i beta x hx)).symm
    · have hne : beta-Pi.single i 1 ≠ gamma-Pi.single i 1 := fun heq => h (sub_left_injective heq)
      rw [M.rootGradeProjection_of_mem_ne beta gamma x hx h, map_zero]
      exact (M.rootGradeProjection_of_mem_ne (beta-Pi.single i 1) (gamma-Pi.single i 1)
        (M.action.E i x) (M.E_mem_rootGrade i gamma x hx) hne).symm
  have hv : v ∈ M.negativeWordSpan := by rw [M.negativeWordSpan_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,rfl⟩ := hx
    exact hhom _ _ (M.negativeWordValue_mem_rootGrade u)
  | zero => simp only [map_zero]
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul c x hx ih => simp only [map_smul, ih]
theorem rootGradeProjection_primitive (beta : RootCoefficients) (v : V)
    (hv : ∀ i, M.action.E i v=0) : ∀ i, M.action.E i (M.rootGradeProjection beta v)=0 := by
  intro i
  rw [M.E_rootGradeProjection, hv i, map_zero]

theorem primitive_mem_highestLine_of_rootGrades
    (hprimitive : ∀ beta v, v∈M.rootGrade beta → (∀ i, M.action.E i v=0) →
      v∈Submodule.span K {M.highestVector})
    (v : V) (hE : ∀ i, M.action.E i v=0) : v∈Submodule.span K {M.highestVector} := by
  classical
  let P := Submodule.span K {M.highestVector}
  have hcomponent (beta) : M.rootGradeProjection beta v∈P :=
    hprimitive beta _ (M.rootGradeProjection_mem beta v) (M.rootGradeProjection_primitive beta v hE)
  have hdecomp : ∀ x : ⨁ beta : RootCoefficients, M.rootGrade beta,
      (∀ beta, ((DirectSum.component K RootCoefficients (fun b => M.rootGrade b) beta) x).val∈P) →
      M.rootGradingEquiv x∈P := by
    intro x hx
    have hsum : M.rootGradingEquiv x =
        ∑ beta ∈ x.support, ((DirectSum.component K RootCoefficients (fun b => M.rootGrade b) beta) x).val := by
      change DirectSum.coeLinearMap M.rootGrade x = _
      simp [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum, DirectSum.component]
      rfl
    rw [hsum]
    exact P.sum_mem (fun beta _ => hx beta)
  have h := hdecomp (M.rootGradingEquiv.symm v) hcomponent
  simpa using h

end KanadeRussell.Representation.PrincipalHighestWeightModule
