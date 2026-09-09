import KanadeRussell.Representation.RootOccupationGrading
import KanadeRussell.Representation.FiniteRootOrbit

namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

theorem occupationWeight_sub_simple (lambda beta : RootCoefficients) (i : Fin 3) (j : Fin 4) :
    occupationWeight (K := K) lambda (beta-Pi.single i 1) j =
      occupationWeight lambda beta j + (rootCartanCoefficient i j : K) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [occupationWeight, totalDegree, rootCartanCoefficient, Pi.sub_apply,
      Finset.sum_sub_distrib, Pi.single_apply, Int.cast_sub]
    ring
  · simp only [occupationWeight, rootCartanCoefficient, Fin.cases_succ, weightLabels,
      Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    simp [Pi.single_apply, apply_ite, Int.cast_sub, Int.cast_add]
    ring

theorem E_mem_rootGrade (i : Fin 3) (beta : RootCoefficients) (v : V)
    (hv : v ∈ M.rootGrade beta) :
    M.action.E i v ∈ M.rootGrade (beta-Pi.single i 1) := by
  apply (M.mem_extendedWeightSpace _ _).mpr
  intro j
  have hvj := (M.mem_extendedWeightSpace _ _).mp hv j
  have h := congrArg (fun a : Module.End K V => a v) (M.extendedCartan_E i j)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, hvj, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, occupationWeight_sub_simple (K := K)]
  module

end KanadeRussell.Representation.PrincipalHighestWeightModule
