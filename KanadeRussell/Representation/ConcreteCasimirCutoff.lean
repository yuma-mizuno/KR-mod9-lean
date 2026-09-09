import KanadeRussell.Representation.PositivePrincipalModes
import KanadeRussell.Representation.TensorModeCasimir

/-! A uniform relative-degree cutoff for the actual normal-ordered Casimir
on each root grade, independent of the polynomial degree of its seed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock AffineWeightLattice Sectors
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem tensorPrincipalModule_positiveMode_eq_zero_of_degree_lt
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (beta : RootCoefficients) (p : tensorCyclicSpan w seed) (hp : p ∈ M.rootGrade beta)
    (n : ℕ) (hn : totalDegree beta < (n:ℤ)+1) (r : Fin 3) :
    positiveCyclicPrincipalMode w seed n r p=0 := by
  have h := tensorPrincipalModule_positiveMode_mem_rootGrade w hw seed M haction d hD n r beta p hp
  have hdeg : totalDegree (beta-positiveModeOccupation n r) < 0 := by
    have he : totalDegree (beta-positiveModeOccupation n r) =
        totalDegree beta - totalDegree (positiveModeOccupation n r) := by
      simp [totalDegree, Pi.sub_apply, Finset.sum_sub_distrib]
    rw [he, positiveModeOccupation_degree]
    omega
  have hg := M.rootGrade_le_grade (beta-positiveModeOccupation n r) h
  rw [M.grade_negative _ hdeg, Submodule.mem_bot] at hg
  exact hg

theorem tensorPrincipalModule_principalMode_eq_zero_of_degree_lt
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (beta : RootCoefficients) (p : tensorCyclicSpan w seed) (hp : p ∈ M.rootGrade beta)
    (n : ℕ) (hn : totalDegree beta < (n:ℤ)+1) (r : Fin 3) :
    principalMode w ((n:ℤ)+1) r p.val=0 := by
  have hz (s : Fin 3) : positivePrincipalMode w n s p.val=0 := by
    have h := congrArg Subtype.val
      (tensorPrincipalModule_positiveMode_eq_zero_of_degree_lt w hw seed M haction d hD beta p hp n hn s)
    exact h
  have h := congrArg (fun f : Module.End K (Space K) => f p.val)
    (principalModeCombination_eq_sum_positivePrincipalMode w hw n (Pi.single r 1))
  simpa [principalModeCombination_apply, LinearMap.sum_apply, LinearMap.smul_apply, hz] using h

theorem tensorPrincipalModule_casimir_apply_eq_relative_sum
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K)
    (M : PrincipalHighestWeightModule K (tensorCyclicSpan w seed))
    (haction : M.action = tensorCyclicChevalleyAction w hw seed) (d : K)
    (hD : ∀ p, (M.principalDerivation p).val = Fock.principalDerivation p.val + d • p.val)
    (beta : RootCoefficients) (p : tensorCyclicSpan w seed) (hp : p ∈ M.rootGrade beta) :
    tensorModeCasimir w p.val = (2:K) •
      ∑ n ∈ Finset.range (totalDegree beta).toNat, normalOrderedMode w ((n:ℤ)+1) p.val := by
  apply tensorModeCasimir_apply_eq_sum
  intro n hn
  apply normalOrderedMode_eq_zero
  exact tensorPrincipalModule_principalMode_eq_zero_of_degree_lt w hw seed M haction d hD beta p hp n
    (by omega)



theorem skewPrincipalModule_casimir_apply_eq_relative_sum
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients)
    (p : tensorCyclicSpan w (skewSeed : Space K))
    (hp : p ∈ (skewPrincipalModule w hw).rootGrade beta) :
    tensorModeCasimir w p.val = (2:K) •
      ∑ n ∈ Finset.range (totalDegree beta).toNat, normalOrderedMode w ((n:ℤ)+1) p.val := by
  apply tensorPrincipalModule_casimir_apply_eq_relative_sum w hw skewSeed
    (skewPrincipalModule w hw) rfl 1 ?_ beta p hp
  intro q
  simpa only [one_smul, zero_smul, add_zero] using skewPrincipalModule_principalDerivation_val w hw q
theorem vacuumPrincipalModule_casimir_apply_eq_relative_sum
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients)
    (p : tensorCyclicSpan w (1 : Space K))
    (hp : p ∈ (vacuumPrincipalModule w hw).rootGrade beta) :
    tensorModeCasimir w p.val = (2:K) •
      ∑ n ∈ Finset.range (totalDegree beta).toNat, normalOrderedMode w ((n:ℤ)+1) p.val := by
  apply tensorPrincipalModule_casimir_apply_eq_relative_sum w hw 1
    (vacuumPrincipalModule w hw) rfl 0 ?_ beta p hp
  intro q
  simpa only [one_smul, zero_smul, add_zero] using vacuumPrincipalModule_principalDerivation_val w hw q
theorem alternatingPrincipalModule_casimir_apply_eq_relative_sum
    (w : K) (hw : w^4-w^2+1=0) (beta : RootCoefficients)
    (p : tensorCyclicSpan w (alternatingSeed : Space K))
    (hp : p ∈ (alternatingPrincipalModule w hw).rootGrade beta) :
    tensorModeCasimir w p.val = (2:K) •
      ∑ n ∈ Finset.range (totalDegree beta).toNat, normalOrderedMode w ((n:ℤ)+1) p.val := by
  apply tensorPrincipalModule_casimir_apply_eq_relative_sum w hw alternatingSeed
    (alternatingPrincipalModule w hw) rfl 3 ?_ beta p hp
  intro q
  simpa only [one_smul, zero_smul, add_zero] using alternatingPrincipalModule_principalDerivation_val w hw q

end KanadeRussell.Representation
