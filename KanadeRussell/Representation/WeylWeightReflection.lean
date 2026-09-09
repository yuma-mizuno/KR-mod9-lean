import KanadeRussell.Representation.FiniteRootOrbit
import KanadeRussell.Representation.RootOccupationWeights

/-! Reflection of full Cartan weights agrees with reflection of integer root
occupations, including the principal derivation coordinate. -/
namespace KanadeRussell.Representation.AffineWeightLattice
open Tsuchioka.Fock

theorem totalDegree_simpleReflection (lambda beta : RootCoefficients) (i : Fin 3) :
    totalDegree (simpleReflection lambda i beta) = totalDegree beta + weightLabels lambda beta i := by
  simp [totalDegree, simpleReflection, Finset.sum_add_distrib, Pi.single_apply]

end KanadeRussell.Representation.AffineWeightLattice

namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice Tsuchioka.Fock
variable {K : Type*} [Field K]

theorem rootCartanCoefficient_self (i : Fin 3) : rootCartanCoefficient i i.succ = 2 := by
  change affineCartanMatrix i i = 2
  fin_cases i <;> rfl

def reflectFullWeight (i : Fin 3) (mu : Fin 4 → K) : Fin 4 → K :=
  fun j => mu j - (rootCartanCoefficient i j : K) * mu i.succ

@[simp] theorem reflectFullWeight_self (i : Fin 3) (mu : Fin 4 → K) :
    reflectFullWeight i mu i.succ = -mu i.succ := by
  simp only [reflectFullWeight, rootCartanCoefficient_self, Int.cast_ofNat]
  ring

theorem reflectFullWeight_involutive (i : Fin 3) :
    Function.Involutive (reflectFullWeight (K := K) i) := by
  intro mu
  funext j
  simp only [reflectFullWeight, rootCartanCoefficient_self, Int.cast_ofNat]
  ring

theorem occupationWeight_simpleReflection (lambda beta : RootCoefficients) (i : Fin 3) :
    occupationWeight (K := K) lambda (simpleReflection lambda i beta) =
      reflectFullWeight i (occupationWeight lambda beta) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [occupationWeight, reflectFullWeight, rootCartanCoefficient,
      Fin.cases_zero, Fin.cases_succ, totalDegree_simpleReflection, Int.cast_add, Int.cast_one]
    ring
  · simp only [occupationWeight, reflectFullWeight, rootCartanCoefficient,
      Fin.cases_succ, weightLabels_simpleReflection, Int.cast_sub, Int.cast_mul]

end KanadeRussell.Representation.PrincipalHighestWeightModule
