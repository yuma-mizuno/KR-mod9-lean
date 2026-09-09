import KanadeRussell.Representation.RootGradeTrace

/-! Trace recurrence for a pair of operators with opposite root-grade shifts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)
variable (X Y : Module.End K V) (gamma : RootCoefficients)
variable (hX : ∀ beta v, v ∈ M.rootGrade beta → X v ∈ M.rootGrade (beta-gamma))
variable (hY : ∀ beta v, v ∈ M.rootGrade beta → Y v ∈ M.rootGrade (beta+gamma))

noncomputable def rootModeDown (beta : RootCoefficients) :
    M.rootGrade beta →ₗ[K] M.rootGrade (beta-gamma) :=
  M.rootGradeRestriction beta (beta-gamma) X (hX beta)

noncomputable def rootModeUpBack (beta : RootCoefficients) :
    M.rootGrade (beta-gamma) →ₗ[K] M.rootGrade beta :=
  M.rootGradeRestriction (beta-gamma) beta Y (by
    intro v hv
    simpa only [sub_add_cancel] using hY (beta-gamma) v hv)

noncomputable def rootModeTrace (beta : RootCoefficients) : K :=
  LinearMap.trace K (M.rootGrade beta)
    ((M.rootModeUpBack Y gamma hY beta).comp (M.rootModeDown X gamma hX beta))

theorem rootModeTrace_recurrence (c : RootCoefficients → K)
    (hcomm : ∀ alpha v, v ∈ M.rootGrade alpha → (X*Y-Y*X) v = c alpha • v)
    (beta : RootCoefficients) :
    M.rootModeTrace X Y gamma hX hY beta =
      M.rootModeTrace X Y gamma hX hY (beta-gamma) +
        c (beta-gamma) * (Module.finrank K (M.rootGrade (beta-gamma)) : K) := by
  have heq :
      (M.rootModeDown X gamma hX beta).comp (M.rootModeUpBack Y gamma hY beta) =
      (M.rootModeUpBack Y gamma hY (beta-gamma)).comp (M.rootModeDown X gamma hX (beta-gamma)) +
        c (beta-gamma) • (1 : Module.End K (M.rootGrade (beta-gamma))) := by
    ext v
    have h := hcomm (beta-gamma) v.val v.property
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    change X (Y v.val) = Y (X v.val) + c (beta-gamma) • v.val
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)
  rw [rootModeTrace, M.rootGrade_trace_comp_comm beta (beta-gamma), heq, map_add]
  rw [M.rootGrade_trace_scalar]
  change M.rootModeTrace X Y gamma hX hY (beta-gamma) + _ = _
  rw [mul_comm]

theorem rootModeTrace_eq_zero_of_rootGrade_eq_bot (beta : RootCoefficients)
    (hb : M.rootGrade beta = ⊥) : M.rootModeTrace X Y gamma hX hY beta = 0 := by
  letI : Subsingleton (M.rootGrade beta) := by rw [hb]; infer_instance
  have hz : (M.rootModeUpBack Y gamma hY beta).comp (M.rootModeDown X gamma hX beta) = 0 :=
    Subsingleton.elim _ _
  rw [rootModeTrace, hz, map_zero]

theorem rootModeTrace_eq_zero_of_totalDegree_neg (beta : RootCoefficients)
    (hb : totalDegree beta < 0) : M.rootModeTrace X Y gamma hX hY beta = 0 := by
  apply M.rootModeTrace_eq_zero_of_rootGrade_eq_bot X Y gamma hX hY beta
  apply le_antisymm _ bot_le
  exact (M.rootGrade_le_grade beta).trans (by rw [M.grade_negative _ hb])

theorem rootModeTrace_telescope (c : RootCoefficients → K)
    (hcomm : ∀ alpha v, v ∈ M.rootGrade alpha → (X*Y-Y*X) v = c alpha • v)
    (beta : RootCoefficients) (N : ℕ) :
    M.rootModeTrace X Y gamma hX hY beta =
      M.rootModeTrace X Y gamma hX hY (beta-(N:ℤ) • gamma) +
        ∑ k ∈ Finset.range N, c (beta-((k+1:ℕ):ℤ) • gamma) *
          (Module.finrank K (M.rootGrade (beta-((k+1:ℕ):ℤ) • gamma)) : K) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h := M.rootModeTrace_recurrence X Y gamma hX hY c hcomm (beta-(N:ℤ) • gamma)
    have hshift : beta-(N:ℤ) • gamma-gamma = beta-((N+1:ℕ):ℤ) • gamma := by
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, sub_sub]
    rw [hshift] at h
    rw [ih, h, Finset.sum_range_succ]
    ring

theorem rootModeTrace_eq_sum_of_terminal_degree_neg (c : RootCoefficients → K)
    (hcomm : ∀ alpha v, v ∈ M.rootGrade alpha → (X*Y-Y*X) v = c alpha • v)
    (beta : RootCoefficients) (N : ℕ) (hN : totalDegree (beta-(N:ℤ) • gamma) < 0) :
    M.rootModeTrace X Y gamma hX hY beta =
      ∑ k ∈ Finset.range N, c (beta-((k+1:ℕ):ℤ) • gamma) *
        (Module.finrank K (M.rootGrade (beta-((k+1:ℕ):ℤ) • gamma)) : K) := by
  rw [M.rootModeTrace_telescope X Y gamma hX hY c hcomm beta N,
    M.rootModeTrace_eq_zero_of_totalDegree_neg X Y gamma hX hY _ hN, zero_add]

end KanadeRussell.Representation.PrincipalHighestWeightModule
