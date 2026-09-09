import KanadeRussell.Representation.RootEulerProduct
import KanadeRussell.Representation.RootCoefficientFunction

/-! Finite Euler products expanded over subsets, retaining repeated root slots. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
variable {K : Type*} [Field K]

/-- Subsets are subsets of slots, so distinct slots with equal exponents stay distinct. -/
theorem rootEulerProduct_eq_sum_subsets {ι : Type*} (S : Finset ι)
    (gamma : ι → Fin 3 →₀ ℕ) :
    (∏ p ∈ S, (1-MvPowerSeries.monomial (gamma p) (1 : K))) =
      ∑ T ∈ S.powerset, MvPowerSeries.monomial (∑ p ∈ T, gamma p) ((-1 : K)^T.card) := by
  classical
  simp only [sub_eq_add_neg, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [← map_neg, MvPowerSeries.prod_monomial, Finset.prod_const]

theorem coeff_rootEulerProduct_eq_sum_subsets {ι : Type*} (S : Finset ι)
    (gamma : ι → Fin 3 →₀ ℕ) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (∏ p ∈ S, (1-MvPowerSeries.monomial (gamma p) (1 : K))) =
      ∑ T ∈ S.powerset, if (∑ p ∈ T, gamma p) = e then (-1 : K)^T.card else 0 := by
  classical
  rw [rootEulerProduct_eq_sum_subsets, map_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp [MvPowerSeries.coeff_monomial, eq_comm]

@[simp] theorem rootCoefficientsOfExponent_sum {ι : Type*} (S : Finset ι)
    (gamma : ι → Fin 3 →₀ ℕ) :
    rootCoefficientsOfExponent (∑ p ∈ S, gamma p) = ∑ p ∈ S, rootCoefficientsOfExponent (gamma p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih => simp [Finset.sum_insert hp, rootCoefficientsOfExponent_add, ih]

/-- Finite root coefficients are signed counts of subsets of slots. -/
theorem rootCoefficient_eulerProduct_eq_sum_subsets {ι : Type*} (S : Finset ι)
    (gamma : ι → Fin 3 →₀ ℕ) (beta : AffineWeightLattice.RootCoefficients) :
    rootCoefficient (∏ p ∈ S, (1-MvPowerSeries.monomial (gamma p) (1 : K))) beta =
      ∑ T ∈ S.powerset,
        if (∑ p ∈ T, rootCoefficientsOfExponent (gamma p)) = beta then (-1 : K)^T.card else 0 := by
  classical
  rw [rootEulerProduct_eq_sum_subsets]
  change rootCoefficientLinear beta (∑ T ∈ S.powerset,
    MvPowerSeries.monomial (∑ p ∈ T, gamma p) ((-1 : K)^T.card)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [rootCoefficientLinear_apply, rootCoefficient_monomial, rootCoefficientsOfExponent_sum]
  simp only [eq_comm]

/-- A root-lattice automorphism transports finite Euler coefficients whenever
it transports each exponent in the selected family. -/
theorem rootCoefficient_eulerProduct_transport {ι : Type*} (S : Finset ι)
    (f g : ι → Fin 3 →₀ ℕ)
    (L : AffineWeightLattice.RootCoefficients ≃+ AffineWeightLattice.RootCoefficients)
    (h : ∀ p ∈ S, rootCoefficientsOfExponent (g p) = L (rootCoefficientsOfExponent (f p)))
    (beta : AffineWeightLattice.RootCoefficients) :
    rootCoefficient (∏ p ∈ S, (1-MvPowerSeries.monomial (g p) (1 : K))) (L beta) =
      rootCoefficient (∏ p ∈ S, (1-MvPowerSeries.monomial (f p) (1 : K))) beta := by
  classical
  rw [rootCoefficient_eulerProduct_eq_sum_subsets, rootCoefficient_eulerProduct_eq_sum_subsets]
  apply Finset.sum_congr rfl
  intro T hT
  have hTS := Finset.mem_powerset.mp hT
  have hsum : (∑ p ∈ T, rootCoefficientsOfExponent (g p)) =
      L (∑ p ∈ T, rootCoefficientsOfExponent (f p)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun p hp => h p (hTS hp))
  simp only [hsum, L.injective.eq_iff]

/-- Factors outside the coefficient box may be added to a finite Euler product. -/
theorem rootCoeffAgree_eulerProduct_of_subset {ι : Type*} (S T : Finset ι)
    (gamma : ι → Fin 3 →₀ ℕ) (e : Fin 3 →₀ ℕ) (hST : S ⊆ T)
    (hout : ∀ p ∈ T, p ∉ S → ¬ gamma p ≤ e) :
    RootCoeffAgree e (∏ p ∈ T, (1-MvPowerSeries.monomial (gamma p) (1 : K)))
      (∏ p ∈ S, (1-MvPowerSeries.monomial (gamma p) (1 : K))) := by
  classical
  let F : ι → MvPowerSeries (Fin 3) K := fun p => 1-MvPowerSeries.monomial (gamma p) 1
  let G : ι → MvPowerSeries (Fin 3) K := fun p => if p ∈ S then F p else 1
  have hagree : ∀ p ∈ T, RootCoeffAgree e (F p) (G p) := by
    intro p hp
    by_cases hs : p ∈ S
    · simp only [G, if_pos hs]
      exact RootCoeffAgree.refl _
    · have hz := rootCoeffAgree_monomial_zero (K := K) e (gamma p) (hout p hp hs) 1
      intro d hd
      simp only [F, G, if_neg hs, map_sub, hz d hd, map_zero, sub_zero]
  have hprod : (∏ p ∈ S, F p) = ∏ p ∈ T, G p :=
    Finset.prod_subset_one_on_sdiff hST
      (fun p hp => if_neg (Finset.mem_sdiff.mp hp).2)
      (fun p hp => (if_pos hp).symm)
  change RootCoeffAgree e (∏ p ∈ T, F p) (∏ p ∈ S, F p)
  rw [hprod]
  exact RootCoeffAgree.prod T hagree

end KanadeRussell.Representation
