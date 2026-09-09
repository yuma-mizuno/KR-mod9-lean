import KanadeRussell.Representation.RootEulerCasimirReduction
import KanadeRussell.Representation.RootPrincipalSpecialization

/-! Exact principal specialization of the root Lambert series and its Euler
derivatives. All coefficients are finite sums over the actual active slots.
The resulting one-variable residual is not asserted to vanish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

noncomputable def principalLambertDegreePartial (i : Fin 3) (B : ℕ) : PowerSeries K :=
  ∑ n ∈ Finset.range B, ∑ r : Fin 3,
    if principalWeightSlotActive (positiveModeResidue n) r then
      (positiveModeOccupation n r i : K) •
        ∑ k ∈ Finset.range (B+1), PowerSeries.monomial ((k+1)*(n+1)) (1 : K)
    else 0

noncomputable def principalLambertDerivativeDegreePartial (i j : Fin 3) (B : ℕ) : PowerSeries K :=
  ∑ n ∈ Finset.range B, ∑ r : Fin 3,
    if principalWeightSlotActive (positiveModeResidue n) r then
      ∑ k ∈ Finset.range (B+1),
        (((k+1 : ℕ) : K) * (positiveModeOccupation n r i : K) *
          (positiveModeOccupation n r j : K)) • PowerSeries.monomial ((k+1)*(n+1)) (1 : K)
    else 0

noncomputable def principalLambertDegree (i : Fin 3) : PowerSeries K :=
  PowerSeries.mk (fun n => PowerSeries.coeff n (principalLambertDegreePartial (K := K) i n))

noncomputable def principalLambertDerivativeDegree (i j : Fin 3) : PowerSeries K :=
  PowerSeries.mk (fun n => PowerSeries.coeff n (principalLambertDerivativeDegreePartial (K := K) i j n))

theorem rootPrincipalSpecialization_lambertPartial (i : Fin 3) (B : ℕ) :
    rootPrincipalSpecialization (principalRootEulerLambertPartial (K := K) i B) =
      principalLambertDegreePartial i B := by
  classical
  unfold principalRootEulerLambertPartial principalLambertDegreePartial
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  unfold principalRootEulerLambertFactor
  split_ifs
  · simp only [map_smul, map_sum, MvPowerSeries.monomial_pow, one_pow,
      rootPrincipalSpecialization_monomial, positiveModeExponent_cast]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hd : ((k+1) • positiveModeExponent n r).degree = (k+1)*(n+1) :=
      (rootExponentDegree_nsmul _ _).trans (congrArg (fun m => (k+1)*m) (positiveModeExponent_degree n r))
    rw [hd]
  · simp

theorem rootPrincipalSpecialization_lambertDerivativePartial (i j : Fin 3) (B : ℕ) :
    rootPrincipalSpecialization (rootEulerOperator i (principalRootEulerLambertPartial (K := K) j B)) =
      principalLambertDerivativeDegreePartial i j B := by
  classical
  unfold principalRootEulerLambertPartial principalLambertDerivativeDegreePartial
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  unfold principalRootEulerLambertFactor
  split_ifs
  · simp only [map_smul, map_sum, MvPowerSeries.monomial_pow, one_pow,
      rootEulerOperator_monomial, Finset.smul_sum, rootPrincipalSpecialization_monomial]
    apply Finset.sum_congr rfl
    intro k hk
    have hd : ((k+1) • positiveModeExponent n r).degree = (k+1)*(n+1) :=
      (rootExponentDegree_nsmul _ _).trans (congrArg (fun m => (k+1)*m) (positiveModeExponent_degree n r))
    rw [hd]
    simp only [Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul, positiveModeExponent_cast,
      smul_smul]
    congr 1
    ring
  · simp

theorem coeff_rootPrincipalSpecialization_lambert (i : Fin 3) (n B : ℕ) (hB : n ≤ B) :
    PowerSeries.coeff n (rootPrincipalSpecialization (principalRootLambert (K := K) i)) =
      PowerSeries.coeff n (principalLambertDegreePartial i B) := by
  rw [← rootPrincipalSpecialization_lambertPartial,
    coeff_rootPrincipalSpecialization, coeff_rootPrincipalSpecialization]
  apply Finset.sum_congr rfl
  intro b hb
  apply principalRootLambert_agree_partial i b.exponent B _ b.exponent le_rfl
  change b.exponent.degree ≤ B
  rw [b.exponent_degree]
  exact hB

theorem coeff_rootPrincipalSpecialization_lambertDerivative (i j : Fin 3) (n B : ℕ)
    (hB : n ≤ B) :
    PowerSeries.coeff n (rootPrincipalSpecialization (rootEulerOperator i (principalRootLambert (K := K) j))) =
      PowerSeries.coeff n (principalLambertDerivativeDegreePartial i j B) := by
  rw [← rootPrincipalSpecialization_lambertDerivativePartial,
    coeff_rootPrincipalSpecialization, coeff_rootPrincipalSpecialization]
  apply Finset.sum_congr rfl
  intro b hb
  have hdeg : rootExponentDegree b.exponent ≤ B := by
    change b.exponent.degree ≤ B
    rw [b.exponent_degree]
    exact hB
  exact (principalRootLambert_agree_partial j b.exponent B hdeg).euler i b.exponent le_rfl

theorem rootPrincipalSpecialization_lambert (i : Fin 3) :
    rootPrincipalSpecialization (principalRootLambert (K := K) i) = principalLambertDegree i := by
  ext n
  rw [principalLambertDegree, PowerSeries.coeff_mk]
  exact coeff_rootPrincipalSpecialization_lambert (K := K) i n n le_rfl

theorem rootPrincipalSpecialization_lambertDerivative (i j : Fin 3) :
    rootPrincipalSpecialization (rootEulerOperator i (principalRootLambert (K := K) j)) =
      principalLambertDerivativeDegree i j := by
  ext n
  rw [principalLambertDerivativeDegree, PowerSeries.coeff_mk]
  exact coeff_rootPrincipalSpecialization_lambertDerivative (K := K) i j n n le_rfl

/-- A finite formula for every coefficient of the first root moment. -/
theorem coeff_principalLambertDegree (i : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (principalLambertDegree (K := K) i) =
      ∑ h ∈ Finset.range n, ∑ r : Fin 3,
        if principalWeightSlotActive (positiveModeResidue h) r then
          ∑ k ∈ Finset.range (n+1),
            if (k+1)*(h+1) = n then (positiveModeOccupation h r i : K) else 0
        else 0 := by
  classical
  rw [principalLambertDegree, PowerSeries.coeff_mk]
  unfold principalLambertDegreePartial
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs
  · simp only [map_smul, map_sum, PowerSeries.coeff_monomial, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases he : (k+1)*(h+1) = n
    · simp [he]
    · simp [he, Ne.symm he]
  · simp

/-- Euler differentiation weights a repeated root by its repetition number. -/
theorem coeff_principalLambertDerivativeDegree (i j : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (principalLambertDerivativeDegree (K := K) i j) =
      ∑ h ∈ Finset.range n, ∑ r : Fin 3,
        if principalWeightSlotActive (positiveModeResidue h) r then
          ∑ k ∈ Finset.range (n+1),
            if (k+1)*(h+1) = n then
              ((k+1 : ℕ) : K)*(positiveModeOccupation h r i : K)*(positiveModeOccupation h r j : K)
            else 0
        else 0 := by
  classical
  rw [principalLambertDerivativeDegree, PowerSeries.coeff_mk]
  unfold principalLambertDerivativeDegreePartial
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs
  · simp [PowerSeries.coeff_monomial, eq_comm]
  · simp

/-- The exact one-variable equation still required for denominator harmonicity. -/
theorem rootPrincipalSpecialization_lambertResidual :
    rootPrincipalSpecialization (principalRootLambertResidual (K := K)) =
      (principalLambertDegree 0)^2 + (principalLambertDegree 1)^2 +
      3 • (principalLambertDegree 2)^2 - principalLambertDegree 0 * principalLambertDegree 1 -
      3 • (principalLambertDegree 1 * principalLambertDegree 2) -
      principalLambertDerivativeDegree 0 0 - principalLambertDerivativeDegree 1 1 -
      3 • principalLambertDerivativeDegree 2 2 + principalLambertDerivativeDegree 0 1 +
      3 • principalLambertDerivativeDegree 1 2 + principalLambertDegree 0 +
      principalLambertDegree 1 + 3 • principalLambertDegree 2 := by
  simp only [principalRootLambertResidual, map_add, map_sub, map_nsmul, map_mul, map_pow,
    rootPrincipalSpecialization_lambert, rootPrincipalSpecialization_lambertDerivative]

end KanadeRussell.Representation
