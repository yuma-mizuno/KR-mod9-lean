import KanadeRussell.Representation.HighestWeightSupport

/-! The full Cartan weight spaces are finite-dimensional. The principal
derivation distinguishes the grades even along the affine null-root direction. -/
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

theorem grade_eq_principalDerivation_eigenspace (n : ℤ) :
    M.grade n = M.principalDerivation.eigenspace (-(n : K)) := by
  have hi : iSupIndep (fun m : ℤ => M.principalDerivation.eigenspace (-(m : K))) :=
    M.principalDerivation.eigenspaces_iSupIndep.comp (by
      intro a b hab
      exact Int.cast_injective (neg_injective hab))
  have heq : M.grade = fun m : ℤ => M.principalDerivation.eigenspace (-(m : K)) :=
    (hi.le_iff_eq_of_iSup_eq_top M.grading_internal.submodule_iSup_eq_top).mp (by
      intro m v hv
      exact Module.End.mem_eigenspace_iff.mpr (M.principalDerivation_of_mem m v hv))
  exact congrFun heq n

theorem extendedWeightSpace_le_grade (mu : Fin 4 → K) (n : ℤ)
    (hmu : mu 0 = -(n : K)) : M.extendedWeightSpace mu ≤ M.grade n := by
  intro v hv
  rw [M.grade_eq_principalDerivation_eigenspace, Module.End.mem_eigenspace_iff]
  have h := (M.mem_extendedWeightSpace mu v).mp hv 0
  simpa only [extendedCartan, Fin.cases_zero, hmu] using h

theorem extendedWeightSpace_finite (mu : Fin 4 → K) :
    Module.Finite K (M.extendedWeightSpace mu) := by
  classical
  by_cases hbot : M.extendedWeightSpace mu = ⊥
  · rw [hbot]
    infer_instance
  · obtain ⟨u, hu⟩ := M.extendedWeightSpace_support mu hbot
    have hmu : mu 0 = -((u.length : ℤ) : K) := by
      simpa only [negativeWordWeight, Fin.cases_zero, Int.cast_natCast] using (congrFun hu 0).symm
    have hle := M.extendedWeightSpace_le_grade mu (u.length : ℤ) hmu
    letI := M.grade_finite (u.length : ℤ)
    exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end KanadeRussell.Representation.PrincipalHighestWeightModule
