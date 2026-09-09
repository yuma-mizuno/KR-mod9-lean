import KanadeRussell.Representation.PrincipalEulerDegreeProduct
import KanadeRussell.Representation.PrincipalRootEulerProduct
import KanadeRussell.Representation.RootPrincipalSpecialization

/-! Principal specialization and convergence of the stabilized root Euler product. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped MvPowerSeries.WithPiTopology

namespace KanadeRussell.Representation
variable {K : Type*} [Field K]

theorem rootExponentDegree_eq_finsupp_degree (e : Fin 3 →₀ ℕ) :
    rootExponentDegree e = e.degree := rfl

theorem principalRootEulerPartial_tendsto [TopologicalSpace K] :
    Filter.Tendsto (principalRootEulerPartial (K := K)) Filter.atTop
      (nhds principalRootEulerDenominator) := by
  rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro e
  exact tendsto_atTop_of_eventually_const fun B (hB : rootExponentDegree e ≤ B) =>
    (coeff_principalRootEulerDenominator e B hB).symm

theorem coeff_rootPrincipalSpecialization_denominator (n B : ℕ) (hB : n ≤ B) :
    PowerSeries.coeff n (rootPrincipalSpecialization (principalRootEulerDenominator (K := K))) =
      PowerSeries.coeff n (rootPrincipalSpecialization (principalRootEulerPartial B)) := by
  rw [coeff_rootPrincipalSpecialization, coeff_rootPrincipalSpecialization]
  apply Finset.sum_congr rfl
  intro b hb
  apply coeff_principalRootEulerDenominator
  rw [rootExponentDegree_eq_finsupp_degree, b.exponent_degree]
  exact hB

/-- Finite root Euler products specialize to the same principal degree cutoff. -/
theorem rootPrincipalSpecialization_partial (B : ℕ) :
    rootPrincipalSpecialization (principalRootEulerPartial (K := K) B) =
      PowerSeries.map (Int.castRingHom K) (principalEulerDegreePartial B) := by
  classical
  simp only [principalRootEulerPartial, principalEulerDegreePartial, map_prod]
  apply Finset.prod_congr rfl
  intro n hn
  apply Finset.prod_congr rfl
  intro r hr
  by_cases ha : principalWeightSlotActive (positiveModeResidue n) r
  · simp [principalRootEulerFactor, ha, rootPrincipalSpecialization_monomial,
      ← rootExponentDegree_eq_finsupp_degree, PowerSeries.monomial_eq_C_mul_X_pow, q]
  · simp [principalRootEulerFactor, ha]

open scoped DiscreteUniformity in
/-- The exact infinite root denominator has the prescribed principal specialization. -/
theorem rootPrincipalSpecialization_denominator :
    rootPrincipalSpecialization (principalRootEulerDenominator (K := K)) =
      PowerSeries.map (Int.castRingHom K) (Product.dualAffineDenominator 1 1 1) := by
  letI : UniformSpace K := ⊥
  ext n
  have hleft : Filter.Tendsto (fun N : ℕ => PowerSeries.coeff n
      (rootPrincipalSpecialization (principalRootEulerPartial (K := K) (12*N))))
      Filter.atTop (nhds (PowerSeries.coeff n
        (rootPrincipalSpecialization (principalRootEulerDenominator (K := K))))) := by
    exact tendsto_atTop_of_eventually_const fun N (hN : n ≤ N) =>
      (coeff_rootPrincipalSpecialization_denominator n (12*N) (by omega)).symm
  have hcoeff := (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℤ _ _ _).mp
    principalEulerDegreePartial_twelve_tendsto n
  have hcast : Continuous (fun z : ℤ => (z : K)) := continuous_of_discreteTopology
  have hright := (hcast.tendsto _).comp hcoeff
  apply tendsto_nhds_unique hleft
  simpa only [rootPrincipalSpecialization_partial, PowerSeries.coeff_map,
    Int.coe_castRingHom, Function.comp_def] using hright
namespace PrincipalHighestWeightModule
variable {V : Type*} [CharZero K] [AddCommGroup V] [Module K V]

/-- The actual root numerator specializes to the cleared original character. -/
theorem rootPrincipalSpecialization_rootNumerator (M : PrincipalHighestWeightModule K V) :
    rootPrincipalSpecialization (M.rootCharacter * principalRootEulerDenominator) =
      PowerSeries.map (Int.castRingHom K)
        (M.character * Product.dualAffineDenominator 1 1 1) := by
  rw [map_mul, M.rootPrincipalSpecialization_rootCharacter,
    rootPrincipalSpecialization_denominator, map_mul]

end PrincipalHighestWeightModule
end KanadeRussell.Representation
