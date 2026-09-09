import KanadeRussell.Representation.PrincipalHighestWeight

/-! The principal derivation is supplied by the actual internal grading.
Its brackets follow from the degree shifts of the Chevalley generators. -/
set_option backward.isDefEq.respectTransparency false
open scoped DirectSum
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

/-- The sum of the homogeneous inclusions is a linear equivalence. -/
noncomputable def gradingEquiv : (⨁ n : ℤ, M.grade n) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap M.grade) M.grading_internal

@[simp] theorem gradingEquiv_lof (n : ℤ) (v : M.grade n) :
    M.gradingEquiv (DirectSum.lof K ℤ (fun n => M.grade n) n v) = v := by
  exact DirectSum.coeLinearMap_lof M.grade n v

theorem gradingEquiv_symm_of_mem (n : ℤ) (v : V) (hv : v ∈ M.grade n) :
    M.gradingEquiv.symm v = DirectSum.lof K ℤ (fun n => M.grade n) n ⟨v, hv⟩ := by
  apply M.gradingEquiv.injective
  rw [LinearEquiv.apply_symm_apply, M.gradingEquiv_lof]

/-- The normalized principal derivation acts by minus the homogeneous degree. -/
noncomputable def principalDerivation : Module.End K V :=
  (DirectSum.toModule K ℤ V (fun n => -(n : K) • (M.grade n).subtype)).comp
    M.gradingEquiv.symm.toLinearMap

theorem principalDerivation_of_mem (n : ℤ) (v : V) (hv : v ∈ M.grade n) :
    M.principalDerivation v = -(n : K) • v := by
  change DirectSum.toModule K ℤ V (fun n => -(n : K) • (M.grade n).subtype)
    (M.gradingEquiv.symm v) = _
  rw [M.gradingEquiv_symm_of_mem n v hv, DirectSum.toModule_lof]
  rfl

theorem principalDerivation_mem_grade (n : ℤ) (v : V) (hv : v ∈ M.grade n) :
    M.principalDerivation v ∈ M.grade n := by
  rw [M.principalDerivation_of_mem n v hv]
  exact (M.grade n).smul_mem _ hv

/-- Linear maps are determined on the actual homogeneous subspaces. -/
theorem linearMap_ext_on_grade {W : Type*} [AddCommGroup W] [Module K W]
    (f g : V →ₗ[K] W)
    (h : ∀ n v, v ∈ M.grade n → f v = g v) : f = g := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ ⨆ n : ℤ, M.grade n := by
    rw [M.grading_internal.submodule_iSup_eq_top]
    trivial
  exact Submodule.iSup_induction M.grade (motive := fun x => f x = g x) hv h (by simp) (fun x y hx hy => by
    simp only [map_add, hx, hy])

/-- A homogeneous operator of degree `k` has principal bracket `-k` times itself. -/
theorem principalDerivation_lie_of_grade_shift (a : Module.End K V) (k : ℤ)
    (ha : ∀ n v, v ∈ M.grade n → a v ∈ M.grade (n+k)) :
    ⁅M.principalDerivation, a⁆ = -(k : K) • a := by
  apply M.linearMap_ext_on_grade
  intro n v hv
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]
  rw [M.principalDerivation_of_mem (n+k) (a v) (ha n v hv),
    M.principalDerivation_of_mem n v hv, map_smul, ← sub_smul]
  congr 1
  push_cast
  ring

theorem principalDerivation_E (i : Fin 3) :
    ⁅M.principalDerivation, M.action.E i⁆ = M.action.E i := by
  have h := M.principalDerivation_lie_of_grade_shift (M.action.E i) (-1)
    (fun n v hv => by simpa only [sub_eq_add_neg] using M.E_grade i n v hv)
  simpa using h

theorem principalDerivation_F (i : Fin 3) :
    ⁅M.principalDerivation, M.action.F i⁆ = -M.action.F i := by
  have h := M.principalDerivation_lie_of_grade_shift (M.action.F i) 1
    (M.F_grade i)
  simpa using h

theorem principalDerivation_H (i : Fin 3) :
    ⁅M.principalDerivation, M.action.H i⁆ = 0 := by
  have h := M.principalDerivation_lie_of_grade_shift (M.action.H i) 0
    (fun n v hv => by simpa only [add_zero] using M.H_grade i n v hv)
  simpa using h

@[simp] theorem principalDerivation_highestVector :
    M.principalDerivation M.highestVector = 0 := by
  rw [M.principalDerivation_of_mem 0 M.highestVector M.highestVector_grade]
  simp

end KanadeRussell.Representation.PrincipalHighestWeightModule
