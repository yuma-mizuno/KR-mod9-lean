import KanadeRussell.Representation.PrincipalDerivation

/-! Homogeneous projections and homogeneous spanning sets for the actual internal grading. -/
set_option backward.isDefEq.respectTransparency false
open scoped DirectSum
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

/-- Projection to one actual homogeneous subspace, followed by its inclusion. -/
noncomputable def gradeProjection (n : ℤ) : Module.End K V :=
  (M.grade n).subtype.comp ((DirectSum.component K ℤ (fun n => M.grade n) n).comp
    M.gradingEquiv.symm.toLinearMap)

theorem gradeProjection_mem (n : ℤ) (v : V) : M.gradeProjection n v ∈ M.grade n :=
  Subtype.coe_prop _

theorem gradeProjection_of_mem (n : ℤ) (v : V) (hv : v ∈ M.grade n) :
    M.gradeProjection n v = v := by
  simp only [gradeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    M.gradingEquiv_symm_of_mem n v hv, DirectSum.component.lof_self]
  rfl

theorem gradeProjection_of_mem_ne (n m : ℤ) (v : V) (hv : v ∈ M.grade m)
    (hnm : n ≠ m) : M.gradeProjection n v = 0 := by
  simp only [gradeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    M.gradingEquiv_symm_of_mem m v hv, DirectSum.component.of, Ne.symm hnm, ↓reduceDIte]
  simp

/-- A homogeneous spanning family spans each degree using exactly the vectors of that degree. -/
theorem grade_eq_span_homogeneous {ι : Type*} (v : ι → V) (degree : ι → ℤ)
    (hv : ∀ i, v i ∈ M.grade (degree i))
    (hspan : Submodule.span K (Set.range v) = ⊤) (n : ℤ) :
    M.grade n = Submodule.span K (v '' {i | degree i = n}) := by
  classical
  apply le_antisymm
  · intro x hx
    have hproj : ∀ y ∈ Submodule.span K (Set.range v),
        M.gradeProjection n y ∈ Submodule.span K (v '' {i | degree i = n}) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        by_cases hi : degree i = n
        · rw [M.gradeProjection_of_mem n (v i) (hi ▸ hv i)]
          exact Submodule.subset_span ⟨i, hi, rfl⟩
        · rw [M.gradeProjection_of_mem_ne n (degree i) (v i) (hv i) (Ne.symm hi)]
          exact Submodule.zero_mem _
      | zero => simpa using (Submodule.zero_mem
          (Submodule.span K (v '' {i | degree i = n})))
      | add y z hy hz ihy ihz => simpa only [map_add] using Submodule.add_mem _ ihy ihz
      | smul c y hy ih => simpa only [map_smul] using Submodule.smul_mem _ c ih
    have hxspan : x ∈ Submodule.span K (Set.range v) := by rw [hspan]; trivial
    simpa only [M.gradeProjection_of_mem n x hx] using hproj x hxspan
  · apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    exact hi ▸ hv i

end KanadeRussell.Representation.PrincipalHighestWeightModule
