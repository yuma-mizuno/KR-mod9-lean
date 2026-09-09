import KanadeRussell.Representation.RootEulerProduct
import KanadeRussell.Representation.PrincipalRootSeriesData

/-! The root Euler denominator is the coefficientwise stabilized product of
all active principal-mode factors. Its logarithmic derivative is proved by
finite geometric sums; no infinite-product identity is assumed. -/
set_option autoImplicit false
namespace KanadeRussell.Representation
variable {K : Type*} [Field K]

noncomputable def principalRootEulerFactor (n : ℕ) (r : Fin 3) : MvPowerSeries (Fin 3) K :=
  if principalWeightSlotActive (positiveModeResidue n) r then
    1-MvPowerSeries.monomial (positiveModeExponent n r) 1 else 1

noncomputable def principalRootEulerPartial (B : ℕ) : MvPowerSeries (Fin 3) K :=
  ∏ n ∈ Finset.range B, ∏ r : Fin 3, principalRootEulerFactor n r

theorem principalRootEulerFactor_agree_one (e : Fin 3 →₀ ℕ) (n : ℕ) (r : Fin 3)
    (hn : rootExponentDegree e ≤ n) :
    RootCoeffAgree e (principalRootEulerFactor (K := K) n r) 1 := by
  classical
  unfold principalRootEulerFactor
  split_ifs
  · have hz := rootCoeffAgree_monomial_zero (K := K) e (positiveModeExponent n r)
      (fun h => (Nat.not_lt_of_ge hn) (positiveModeExponent_le_degree e n r h)) 1
    intro d hd
    simp only [map_sub, hz d hd, map_zero, sub_zero]
  · exact RootCoeffAgree.refl _

theorem principalRootEulerPartial_agree (e : Fin 3 →₀ ℕ) (A B : ℕ)
    (hA : rootExponentDegree e ≤ A) (hAB : A ≤ B) :
    RootCoeffAgree e (principalRootEulerPartial (K := K) B) (principalRootEulerPartial A) := by
  induction B, hAB using Nat.le_induction with
  | base => exact RootCoeffAgree.refl _
  | @succ B hAB ih =>
    unfold principalRootEulerPartial at *
    rw [Finset.prod_range_succ]
    have hblock : RootCoeffAgree e (∏ r : Fin 3, principalRootEulerFactor (K := K) B r) 1 := by
      simpa using RootCoeffAgree.prod (Finset.univ : Finset (Fin 3))
        (fun r _ => principalRootEulerFactor_agree_one e B r (hA.trans hAB))
    simpa using ih.mul hblock

/-- Each coefficient uses precisely the factors whose degree can contribute. -/
noncomputable def principalRootEulerDenominator : MvPowerSeries (Fin 3) K :=
  fun e => MvPowerSeries.coeff e (principalRootEulerPartial (K := K) (rootExponentDegree e))

theorem coeff_principalRootEulerDenominator (e : Fin 3 →₀ ℕ) (B : ℕ)
    (hB : rootExponentDegree e ≤ B) :
    MvPowerSeries.coeff e (principalRootEulerDenominator (K := K)) =
      MvPowerSeries.coeff e (principalRootEulerPartial B) :=
  (principalRootEulerPartial_agree e (rootExponentDegree e) B le_rfl hB e le_rfl).symm

theorem principalRootEulerDenominator_agree (e : Fin 3 →₀ ℕ) (B : ℕ)
    (hB : rootExponentDegree e ≤ B) :
    RootCoeffAgree e (principalRootEulerDenominator (K := K)) (principalRootEulerPartial B) :=
  fun d hd => coeff_principalRootEulerDenominator d B ((rootExponentDegree_mono hd).trans hB)

@[simp] theorem constantCoeff_principalRootEulerDenominator :
    MvPowerSeries.constantCoeff (principalRootEulerDenominator (K := K)) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_principalRootEulerDenominator 0 0 (by simp)]
  simp [principalRootEulerPartial]

noncomputable def principalRootEulerLambertFactor (i : Fin 3) (B n : ℕ) (r : Fin 3) :
    MvPowerSeries (Fin 3) K :=
  if principalWeightSlotActive (positiveModeResidue n) r then
    (positiveModeExponent n r i : K) •
      ∑ k ∈ Finset.range (B+1), MvPowerSeries.monomial (positiveModeExponent n r) (1 : K)^(k+1)
  else 0

noncomputable def principalRootEulerLambertPartial (i : Fin 3) (B : ℕ) :
    MvPowerSeries (Fin 3) K :=
  ∑ n ∈ Finset.range B, ∑ r : Fin 3, principalRootEulerLambertFactor i B n r

theorem principalRootEulerFactor_derivative_local (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (B n : ℕ) (r : Fin 3) (hB : rootExponentDegree e ≤ B) :
    RootCoeffAgree e (rootEulerOperator i (principalRootEulerFactor (K := K) n r))
      (-(principalRootEulerFactor n r * principalRootEulerLambertFactor i B n r)) := by
  classical
  unfold principalRootEulerFactor principalRootEulerLambertFactor
  split_ifs
  · apply rootEulerOperator_factor_local
    intro h
    have hd := rootExponentDegree_mono h
    rw [rootExponentDegree_nsmul, positiveModeExponent_degree] at hd
    nlinarith
  · simp [RootCoeffAgree]

theorem principalRootEulerPartial_derivative_local (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (B : ℕ) (hB : rootExponentDegree e ≤ B) :
    RootCoeffAgree e (rootEulerOperator i (principalRootEulerPartial (K := K) B))
      (-(principalRootEulerPartial B) * principalRootEulerLambertPartial i B) := by
  classical
  unfold principalRootEulerPartial principalRootEulerLambertPartial
  apply rootEulerOperator_prod_local
  intro n hn
  simpa only [neg_mul] using rootEulerOperator_prod_local i e (Finset.univ : Finset (Fin 3))
    (principalRootEulerFactor (K := K) n) (principalRootEulerLambertFactor i B n)
    (fun r _ => principalRootEulerFactor_derivative_local i e B n r hB)

theorem positiveModeExponent_cast (n : ℕ) (r i : Fin 3) :
    (positiveModeExponent n r i : K) = (positiveModeOccupation n r i : K) := by
  have h := congrFun (rootCoefficientsOfExponent_positiveModeExponent n r) i
  change (positiveModeExponent n r i : ℤ) = positiveModeOccupation n r i at h
  simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : K)) h

theorem coeff_principalRootEulerLambertPartial (i : Fin 3) (e : Fin 3 →₀ ℕ) (B : ℕ) :
    MvPowerSeries.coeff e (principalRootEulerLambertPartial (K := K) i B) =
      ∑ n ∈ Finset.range B, ∑ r : Fin 3, ∑ k ∈ Finset.range (B+1),
        principalRootLambertTerm i e n r k := by
  classical
  unfold principalRootEulerLambertPartial
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  unfold principalRootEulerLambertFactor principalRootLambertTerm
  split_ifs with ha
  · simp only [map_smul, map_sum, Finset.smul_sum, MvPowerSeries.monomial_pow,
      one_pow, MvPowerSeries.coeff_monomial, positiveModeExponent_cast]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases he : e = (k+1) • positiveModeExponent n r
    · simp [he, smul_eq_mul]
    · simp [he, Ne.symm he, smul_eq_mul]
  · simp

theorem principalRootLambert_agree_partial (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (B : ℕ) (hB : rootExponentDegree e ≤ B) :
    RootCoeffAgree e (principalRootLambert (K := K) i) (principalRootEulerLambertPartial i B) := by
  intro d hd
  rw [coeff_principalRootEulerLambertPartial]
  exact coeff_principalRootLambert_cutoff i d B ((rootExponentDegree_mono hd).trans hB)

/-- The genuine infinite root Euler product has the coefficientwise Lambert logarithmic derivative. -/
theorem rootEulerOperator_principalRootEulerDenominator (i : Fin 3) :
    rootEulerOperator i (principalRootEulerDenominator (K := K)) =
      -principalRootEulerDenominator * principalRootLambert i := by
  ext e
  let B := rootExponentDegree e
  have hD := principalRootEulerDenominator_agree (K := K) e B le_rfl
  have hL := principalRootLambert_agree_partial (K := K) i e B le_rfl
  exact ((hD.euler i).trans
    ((principalRootEulerPartial_derivative_local i e B le_rfl).trans
      ((hD.neg.mul hL).symm))) e le_rfl

end KanadeRussell.Representation
