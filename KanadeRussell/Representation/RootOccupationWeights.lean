import KanadeRussell.Representation.AffineWeightLattice
import KanadeRussell.Representation.HighestWeightSupport

/-! Root occupations record exactly the full Cartan weight of a lowering word.
The principal degree distinguishes weights that differ by a null-root multiple. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation.AffineWeightLattice
open Tsuchioka.Fock

def wordOccupation : List (Fin 3) → RootCoefficients
  | [] => 0
  | i :: u => Pi.single i 1 + wordOccupation u

@[simp] theorem wordOccupation_nil : wordOccupation [] = 0 := rfl

@[simp] theorem wordOccupation_cons (i : Fin 3) (u : List (Fin 3)) :
    wordOccupation (i :: u) = Pi.single i 1 + wordOccupation u := rfl

theorem wordOccupation_nonneg (u : List (Fin 3)) (i : Fin 3) :
    0 ≤ wordOccupation u i := by
  induction u with
  | nil => simp
  | cons j u ih =>
    have hj : (0 : ℤ) ≤ (Pi.single j 1 : RootCoefficients) i := by
      by_cases h : i = j <;> simp [h]
    exact add_nonneg hj ih

theorem sum_mul_wordOccupation {R : Type*} [Ring R]
    (f : Fin 3 → R) (u : List (Fin 3)) :
    (∑ i : Fin 3, f i * (wordOccupation u i : R)) = (u.map f).sum := by
  induction u with
  | nil => simp
  | cons j u ih =>
    simp only [wordOccupation_cons, Pi.add_apply, Int.cast_add, mul_add,
      Finset.sum_add_distrib, List.map_cons, List.sum_cons, ih]
    congr 1
    simp [Pi.single_apply, apply_ite]

@[simp] theorem totalDegree_wordOccupation (u : List (Fin 3)) :
    totalDegree (wordOccupation u) = (u.length : ℤ) := by
  simpa [totalDegree] using sum_mul_wordOccupation (fun _ => (1 : ℤ)) u

/-- Full weight, with the principal derivation in the first coordinate. -/
def occupationWeight {K : Type*} [Ring K] (lambda beta : RootCoefficients) : Fin 4 → K :=
  Fin.cases (-(totalDegree beta : K)) (fun i => (weightLabels lambda beta i : K))

theorem occupationWeight_injective {K : Type*} [Ring K] [CharZero K]
    (lambda : RootCoefficients) :
    Function.Injective (occupationWeight (K := K) lambda) := by
  intro beta gamma h
  apply eq_of_totalDegree_eq_of_weightLabels_eq lambda beta gamma
  · have hd := congrFun h 0
    simp only [occupationWeight, Fin.cases_zero, neg_inj] at hd
    exact Int.cast_injective hd
  · funext i
    have hw := congrFun h i.succ
    simp only [occupationWeight, Fin.cases_succ] at hw
    exact Int.cast_injective hw

end KanadeRussell.Representation.AffineWeightLattice

namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice Tsuchioka.Fock
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

def highestWeightLabels : RootCoefficients := fun i => (M.highestWeight i : ℤ)

theorem negativeWordWeight_eq_occupationWeight (u : List (Fin 3)) :
    M.negativeWordWeight u =
      occupationWeight M.highestWeightLabels (wordOccupation u) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [negativeWordWeight, occupationWeight]
  · simp only [negativeWordWeight, occupationWeight, Fin.cases_succ,
      weightLabels, highestWeightLabels, Int.cast_sub, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast]
    rw [sum_mul_wordOccupation]

theorem negativeWordWeight_eq_iff_occupation_eq [CharZero K] (u v : List (Fin 3)) :
    M.negativeWordWeight u = M.negativeWordWeight v ↔ wordOccupation u = wordOccupation v := by
  rw [M.negativeWordWeight_eq_occupationWeight, M.negativeWordWeight_eq_occupationWeight]
  exact (occupationWeight_injective M.highestWeightLabels).eq_iff

theorem negativeWordValue_mem_occupationWeightSpace (u : List (Fin 3)) :
    M.negativeWordValue u ∈
      M.extendedWeightSpace (occupationWeight M.highestWeightLabels (wordOccupation u)) := by
  rw [← M.negativeWordWeight_eq_occupationWeight]
  exact M.negativeWordValue_mem_extendedWeightSpace u

theorem extendedWeightSpace_occupation_support (mu : Fin 4 → K)
    (hmu : M.extendedWeightSpace mu ≠ ⊥) :
    ∃ beta : RootCoefficients, (∀ i, 0 ≤ beta i) ∧
      occupationWeight M.highestWeightLabels beta = mu := by
  obtain ⟨u, hu⟩ := M.extendedWeightSpace_support mu hmu
  refine ⟨wordOccupation u, wordOccupation_nonneg u, ?_⟩
  rw [← M.negativeWordWeight_eq_occupationWeight]
  exact hu

end KanadeRussell.Representation.PrincipalHighestWeightModule
