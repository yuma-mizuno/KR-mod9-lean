import KanadeRussell.Representation.ConcreteIrreducibility
import KanadeRussell.Representation.HighestWeightComparison

/-! Comparisons of the three actual tensor cyclic modules with arbitrary
irreducible highest-weight modules of the same labels. -/
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock Sectors
attribute [local instance] LieRing.ofAssociativeRing
variable {K W : Type*} [Field K] [CharZero K] [AddCommGroup W] [Module K W]

theorem skewPrincipalModule_highestWeight (w : K) (hw : w^4-w^2+1=0) :
    (skewPrincipalModule w hw).highestWeight = ![1,1,0] := by
  funext i
  fin_cases i <;> rfl

noncomputable def skewHighestWeightEquiv (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![1,1,0])
    (hN : N.action.IsIrreducible) : tensorCyclicSpan w (skewSeed : Space K) ≃ₗ[K] W :=
  highestWeightEquiv (skewPrincipalModule w hw) N
    ((skewPrincipalModule_highestWeight w hw).trans hweight.symm)
    (skewPrincipalModule_isIrreducible w hw) hN

theorem skewHighestWeightEquiv_highest (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![1,1,0])
    (hN : N.action.IsIrreducible) :
    skewHighestWeightEquiv w hw N hweight hN (skewPrincipalModule w hw).highestVector=N.highestVector :=
  highestWeightEquiv_highest _ _ _ _ _

theorem skewHighestWeightEquiv_map_grade (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![1,1,0])
    (hN : N.action.IsIrreducible) (n : ℤ) :
    ((skewPrincipalModule w hw).grade n).map (skewHighestWeightEquiv w hw N hweight hN).toLinearMap =
      N.grade n := highestWeightEquiv_map_grade _ _ _ _ _ n

theorem skewHighestWeight_character_eq (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![1,1,0])
    (hN : N.action.IsIrreducible) : (skewPrincipalModule w hw).character=N.character :=
  highestWeight_character_eq _ _ ((skewPrincipalModule_highestWeight w hw).trans hweight.symm)
    (skewPrincipalModule_isIrreducible w hw) hN

theorem vacuumPrincipalModule_highestWeight (w : K) (hw : w^4-w^2+1=0) :
    (vacuumPrincipalModule w hw).highestWeight = ![3,0,0] := by
  funext i
  fin_cases i <;> rfl

noncomputable def vacuumHighestWeightEquiv (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![3,0,0])
    (hN : N.action.IsIrreducible) : tensorCyclicSpan w (1 : Space K) ≃ₗ[K] W :=
  highestWeightEquiv (vacuumPrincipalModule w hw) N
    ((vacuumPrincipalModule_highestWeight w hw).trans hweight.symm)
    (vacuumPrincipalModule_isIrreducible w hw) hN

theorem vacuumHighestWeightEquiv_highest (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![3,0,0])
    (hN : N.action.IsIrreducible) :
    vacuumHighestWeightEquiv w hw N hweight hN (vacuumPrincipalModule w hw).highestVector=N.highestVector :=
  highestWeightEquiv_highest _ _ _ _ _

theorem vacuumHighestWeightEquiv_map_grade (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![3,0,0])
    (hN : N.action.IsIrreducible) (n : ℤ) :
    ((vacuumPrincipalModule w hw).grade n).map (vacuumHighestWeightEquiv w hw N hweight hN).toLinearMap =
      N.grade n := highestWeightEquiv_map_grade _ _ _ _ _ n

theorem vacuumHighestWeight_character_eq (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![3,0,0])
    (hN : N.action.IsIrreducible) : (vacuumPrincipalModule w hw).character=N.character :=
  highestWeight_character_eq _ _ ((vacuumPrincipalModule_highestWeight w hw).trans hweight.symm)
    (vacuumPrincipalModule_isIrreducible w hw) hN

theorem alternatingPrincipalModule_highestWeight (w : K) (hw : w^4-w^2+1=0) :
    (alternatingPrincipalModule w hw).highestWeight = ![0,0,1] := by
  funext i
  fin_cases i <;> rfl

noncomputable def alternatingHighestWeightEquiv (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![0,0,1])
    (hN : N.action.IsIrreducible) : tensorCyclicSpan w (alternatingSeed : Space K) ≃ₗ[K] W :=
  highestWeightEquiv (alternatingPrincipalModule w hw) N
    ((alternatingPrincipalModule_highestWeight w hw).trans hweight.symm)
    (alternatingPrincipalModule_isIrreducible w hw) hN

theorem alternatingHighestWeightEquiv_highest (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![0,0,1])
    (hN : N.action.IsIrreducible) :
    alternatingHighestWeightEquiv w hw N hweight hN (alternatingPrincipalModule w hw).highestVector=N.highestVector :=
  highestWeightEquiv_highest _ _ _ _ _

theorem alternatingHighestWeightEquiv_map_grade (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![0,0,1])
    (hN : N.action.IsIrreducible) (n : ℤ) :
    ((alternatingPrincipalModule w hw).grade n).map (alternatingHighestWeightEquiv w hw N hweight hN).toLinearMap =
      N.grade n := highestWeightEquiv_map_grade _ _ _ _ _ n

theorem alternatingHighestWeight_character_eq (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![0,0,1])
    (hN : N.action.IsIrreducible) : (alternatingPrincipalModule w hw).character=N.character :=
  highestWeight_character_eq _ _ ((alternatingPrincipalModule_highestWeight w hw).trans hweight.symm)
    (alternatingPrincipalModule_isIrreducible w hw) hN


theorem skewHighestWeightEquiv_E (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![1,1,0])
    (hN : N.action.IsIrreducible) (i : Fin 3) (v : tensorCyclicSpan w (skewSeed : Space K)) :
    skewHighestWeightEquiv w hw N hweight hN ((skewPrincipalModule w hw).action.E i v) =
      N.action.E i (skewHighestWeightEquiv w hw N hweight hN v) :=
  highestWeightEquiv_E _ _ _ _ _ i v
theorem skewHighestWeightEquiv_F (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![1,1,0])
    (hN : N.action.IsIrreducible) (i : Fin 3) (v : tensorCyclicSpan w (skewSeed : Space K)) :
    skewHighestWeightEquiv w hw N hweight hN ((skewPrincipalModule w hw).action.F i v) =
      N.action.F i (skewHighestWeightEquiv w hw N hweight hN v) :=
  highestWeightEquiv_F _ _ _ _ _ i v
theorem skewHighestWeightEquiv_H (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![1,1,0])
    (hN : N.action.IsIrreducible) (i : Fin 3) (v : tensorCyclicSpan w (skewSeed : Space K)) :
    skewHighestWeightEquiv w hw N hweight hN ((skewPrincipalModule w hw).action.H i v) =
      N.action.H i (skewHighestWeightEquiv w hw N hweight hN v) :=
  highestWeightEquiv_H _ _ _ _ _ i v
theorem vacuumHighestWeightEquiv_E (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![3,0,0])
    (hN : N.action.IsIrreducible) (i : Fin 3) (v : tensorCyclicSpan w (1 : Space K)) :
    vacuumHighestWeightEquiv w hw N hweight hN ((vacuumPrincipalModule w hw).action.E i v) =
      N.action.E i (vacuumHighestWeightEquiv w hw N hweight hN v) :=
  highestWeightEquiv_E _ _ _ _ _ i v
theorem vacuumHighestWeightEquiv_F (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![3,0,0])
    (hN : N.action.IsIrreducible) (i : Fin 3) (v : tensorCyclicSpan w (1 : Space K)) :
    vacuumHighestWeightEquiv w hw N hweight hN ((vacuumPrincipalModule w hw).action.F i v) =
      N.action.F i (vacuumHighestWeightEquiv w hw N hweight hN v) :=
  highestWeightEquiv_F _ _ _ _ _ i v
theorem vacuumHighestWeightEquiv_H (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![3,0,0])
    (hN : N.action.IsIrreducible) (i : Fin 3) (v : tensorCyclicSpan w (1 : Space K)) :
    vacuumHighestWeightEquiv w hw N hweight hN ((vacuumPrincipalModule w hw).action.H i v) =
      N.action.H i (vacuumHighestWeightEquiv w hw N hweight hN v) :=
  highestWeightEquiv_H _ _ _ _ _ i v
theorem alternatingHighestWeightEquiv_E (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![0,0,1])
    (hN : N.action.IsIrreducible) (i : Fin 3) (v : tensorCyclicSpan w (alternatingSeed : Space K)) :
    alternatingHighestWeightEquiv w hw N hweight hN ((alternatingPrincipalModule w hw).action.E i v) =
      N.action.E i (alternatingHighestWeightEquiv w hw N hweight hN v) :=
  highestWeightEquiv_E _ _ _ _ _ i v
theorem alternatingHighestWeightEquiv_F (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![0,0,1])
    (hN : N.action.IsIrreducible) (i : Fin 3) (v : tensorCyclicSpan w (alternatingSeed : Space K)) :
    alternatingHighestWeightEquiv w hw N hweight hN ((alternatingPrincipalModule w hw).action.F i v) =
      N.action.F i (alternatingHighestWeightEquiv w hw N hweight hN v) :=
  highestWeightEquiv_F _ _ _ _ _ i v
theorem alternatingHighestWeightEquiv_H (w : K) (hw : w^4-w^2+1=0)
    (N : PrincipalHighestWeightModule K W) (hweight : N.highestWeight=![0,0,1])
    (hN : N.action.IsIrreducible) (i : Fin 3) (v : tensorCyclicSpan w (alternatingSeed : Space K)) :
    alternatingHighestWeightEquiv w hw N hweight hN ((alternatingPrincipalModule w hw).action.H i v) =
      N.action.H i (alternatingHighestWeightEquiv w hw N hweight hN v) :=
  highestWeightEquiv_H _ _ _ _ _ i v

end KanadeRussell.Representation
