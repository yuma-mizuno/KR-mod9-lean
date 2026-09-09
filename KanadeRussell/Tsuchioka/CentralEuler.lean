import KanadeRussell.Tsuchioka.CentralCreationEuler
import KanadeRussell.Tsuchioka.CentralAnnihilationEuler
import KanadeRussell.Tsuchioka.ResidueMaps

/-! The summed central Euler derivative and its normalized mode residue. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

theorem normalProduct_central_euler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) (d : ℤ) :
    diagonalEulerCoefficient (phaseUnit w hw 6) (normalProduct w j j f) d =
      (laurentRescale (phaseUnit w hw 6)
          (laurentEuler (creation (K := K) j : LaurentSeries (Space K))) *
        (creation (K := K) j : LaurentSeries (Space K)) * HahnSeries.C f).coeff d -
      (centralAnnihilationEuler w hw j f).coeff d := by
  rw [normalProduct_eq_normalWithPolynomial, normalWithPolynomial_euler,
    polynomial_central_evaluation w hw, creation_central_fusion w hw, one_mul]
  rfl

/-- The inner derivative cancels after summing the three normal products.
No cancellation of an individual tensor summand is assumed. -/
theorem sum_normalProduct_central_euler (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (d : ℤ) :
    ∑ j : Fin 3,
      diagonalEulerCoefficient (phaseUnit w hw 6) (normalProduct w j j f) d = 0 := by
  simp only [normalProduct_central_euler w hw, Finset.sum_sub_distrib,
    ← HahnSeries.coeff_sum, ← Finset.sum_mul, sum_creation_central_euler w hw,
    sum_centralAnnihilationEuler w hw, zero_mul, HahnSeries.coeff_zero, sub_self]

/-- The individual Euler residue retains the derivative of the normal product. -/
theorem normalResidue_euler_central (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (j : Fin 3) (f : Space K) (a b : ℤ) :
    normalResidue w j j f a b (Scalar.eulerDelta (-1 : K)) =
      MvPolynomial.C ((-1 : K) ^ a) *
        diagonalEulerCoefficient (phaseUnit w hw 6) (normalProduct w j j f) (-a + -b) +
      (a : K) • normalResidue w j j f a b (Scalar.delta (-1 : K)) := by
  obtain ⟨l, r, h⟩ := normalProduct_bounded w j j f
  have hc : (fun n : ℤ => (MvPolynomial.C (Scalar.delta (-1 : K) n) : Space K)) =
      (fun n => ((phaseUnit w hw 6 ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    simp only [Scalar.delta, phaseUnit_zpow, root_six_neg_phase w hw]
  have he : (fun n : ℤ => (MvPolynomial.C (Scalar.eulerDelta (-1 : K) n) : Space K)) =
      (fun n : ℤ => (n : Space K) * ((phaseUnit w hw 6 ^ n : (Space K)ˣ) : Space K)) := by
    funext n
    simp only [Scalar.eulerDelta, map_mul, map_intCast, phaseUnit_zpow,
      root_six_neg_phase w hw]
  simp only [normalResidue_apply, scalarContract]
  rw [he, hc, contract_eulerDelta h, contract_delta h, phaseUnit_zpow]
  simp only [neg_neg, root_six_neg_phase w hw, Int.cast_neg, Algebra.smul_def,
    MvPolynomial.algebraMap_eq, map_intCast]
  ring

theorem sameResidue_euler_eq_delta (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.eulerDelta (-1 : K)) =
      (a : K) • sameResidue w f a b (Scalar.delta (-1 : K)) := by
  simp only [sameResidue_apply, normalResidue_euler_central w hw,
    Finset.sum_add_distrib, ← Finset.mul_sum, sum_normalProduct_central_euler w hw,
    mul_zero, zero_add, ← Finset.smul_sum, smul_smul]
  congr 1
  ring

/-- The central Euler-delta term has the source factor A*(-1)^A/48. -/
theorem sameResidue_euler_central (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : Space K) (a b : ℤ) :
    sameResidue w f a b (Scalar.eulerDelta (-1 : K)) =
      if a + b = 0 then ((a : K) * (-1 : K) ^ a / 48) • f else 0 := by
  rw [sameResidue_euler_eq_delta w hw, sameResidue_delta_central w hw]
  by_cases hab : a + b = 0
  · simp only [if_pos hab, smul_smul]
    congr 1
    ring
  · simp [hab]

end KanadeRussell.Tsuchioka.Fock
