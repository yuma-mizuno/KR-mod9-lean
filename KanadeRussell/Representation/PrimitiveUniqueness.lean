import KanadeRussell.Representation.PrimitiveWeights
import KanadeRussell.Representation.RootOccupationGrading
import KanadeRussell.Representation.DominantCasimirRigidity

/-! Primitive-vector uniqueness conditional on one explicit lattice equation.
The Casimir operator and the representation-theoretic origin of that equation
are not assumed to have been constructed. -/
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

omit [CharZero K] in
theorem rootGrade_H (beta : RootCoefficients) (v : V)
    (hgrade : v ∈ M.rootGrade beta) (i : Fin 3) :
    M.action.H i v = (weightLabels M.highestWeightLabels beta i : K) • v := by
  have hweight := (M.mem_extendedWeightSpace _ v).mp hgrade i.succ
  exact hweight

theorem rootGrade_nonneg_of_mem (beta : RootCoefficients) (v : V)
    (hv : v ≠ 0) (hgrade : v ∈ M.rootGrade beta) : ∀ i, 0 ≤ beta i := by
  apply M.rootGrade_support beta
  intro hbot
  rw [hbot, Submodule.mem_bot] at hgrade
  exact hv hgrade

/-- Primitive dominance, stated in the actual integer occupation labels. -/
theorem primitive_rootGrade_labels_nonneg (beta : RootCoefficients) (v : V)
    (hv : v ≠ 0) (hgrade : v ∈ M.rootGrade beta)
    (hE : ∀ i, M.action.E i v = 0) :
    ∀ i, 0 ≤ weightLabels M.highestWeightLabels beta i := by
  obtain ⟨mu, hmu⟩ := M.primitive_weight_dominant
    (fun i => (weightLabels M.highestWeightLabels beta i : K)) v hv
    (M.rootGrade_H beta v hgrade) hE
  intro i
  have hi : weightLabels M.highestWeightLabels beta i = (mu i : ℤ) :=
    Int.cast_injective (by simpa using hmu i :
      (weightLabels M.highestWeightLabels beta i : K) = ((mu i : ℤ) : K))
  rw [hi]
  exact Int.natCast_nonneg _

theorem primitive_rootGrade_dominant (beta : RootCoefficients) (v : V)
    (hv : v ≠ 0) (hgrade : v ∈ M.rootGrade beta)
    (hE : ∀ i, M.action.E i v = 0) :
    (∀ i, 0 ≤ beta i) ∧ (∀ i, 0 ≤ weightLabels M.highestWeightLabels beta i) :=
  ⟨M.rootGrade_nonneg_of_mem beta v hv hgrade,
    M.primitive_rootGrade_labels_nonneg beta v hv hgrade hE⟩

/-- The additional premise is exactly the missing Casimir scalar equality. -/
theorem primitive_rootGrade_eq_zero_of_casimir (beta : RootCoefficients) (v : V)
    (hv : v ≠ 0) (hgrade : v ∈ M.rootGrade beta)
    (hE : ∀ i, M.action.E i v = 0)
    (hcasimir : casimir (fun i => M.highestWeightLabels i + 1) beta = 0) : beta = 0 := by
  obtain ⟨hbeta, hdominant⟩ := M.primitive_rootGrade_dominant beta v hv hgrade hE
  exact eq_zero_of_casimir_rho_eq_zero_of_dominant M.highestWeightLabels beta
    (fun i => Int.natCast_nonneg (M.highestWeight i)) hbeta hdominant hcasimir

theorem primitive_mem_highestLine_of_casimir (beta : RootCoefficients) (v : V)
    (hv : v ≠ 0) (hgrade : v ∈ M.rootGrade beta)
    (hE : ∀ i, M.action.E i v = 0)
    (hcasimir : casimir (fun i => M.highestWeightLabels i + 1) beta = 0) :
    v ∈ Submodule.span K {M.highestVector} := by
  have hbeta := M.primitive_rootGrade_eq_zero_of_casimir beta v hv hgrade hE hcasimir
  have hprincipal := M.rootGrade_le_grade beta hgrade
  simpa [hbeta, totalDegree, M.grade_zero_eq_highestLine] using hprincipal

theorem primitive_eq_smul_highest_of_casimir (beta : RootCoefficients) (v : V)
    (hv : v ≠ 0) (hgrade : v ∈ M.rootGrade beta)
    (hE : ∀ i, M.action.E i v = 0)
    (hcasimir : casimir (fun i => M.highestWeightLabels i + 1) beta = 0) :
    ∃ c : K, c • M.highestVector = v :=
  Submodule.mem_span_singleton.mp
    (M.primitive_mem_highestLine_of_casimir beta v hv hgrade hE hcasimir)

end KanadeRussell.Representation.PrincipalHighestWeightModule
