import KanadeRussell.Tsuchioka.CoefficientDerivations

/-! Differentiation of formal exponentials in their coefficient algebra.
The proof uses finite coefficient products and formal differential uniqueness. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open PowerSeries

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

noncomputable def powerSeriesDerivation (D : Derivation K A A) :
    PowerSeries A →ₗ[K] PowerSeries A where
  toFun f := PowerSeries.mk fun n => D (coeff n f)
  map_add' f g := by ext n; simp only [coeff_mk, map_add]
  map_smul' c f := by ext n; simp only [PowerSeries.coeff_smul, coeff_mk, D.map_smul, RingHom.id_apply]

@[simp] theorem coeff_powerSeriesDerivation (D : Derivation K A A)
    (f : PowerSeries A) (n : ℕ) :
    coeff n (powerSeriesDerivation D f) = D (coeff n f) := by simp only [powerSeriesDerivation, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk]

theorem powerSeriesDerivation_mul (D : Derivation K A A) (f g : PowerSeries A) :
    powerSeriesDerivation D (f * g) =
      powerSeriesDerivation D f * g + f * powerSeriesDerivation D g := by
  ext n
  simp only [coeff_powerSeriesDerivation, coeff_mul, map_sum, map_add,
    D.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro ij hij <;> ring

theorem powerSeriesDerivation_derivative (D : Derivation K A A) (f : PowerSeries A) :
    powerSeriesDerivation D (derivative A f) = derivative A (powerSeriesDerivation D f) := by
  ext n
  simp only [coeff_powerSeriesDerivation, coeff_derivative, D.leibniz,
    D.map_natCast, map_add, D.map_one_eq_zero, add_zero, smul_eq_mul, mul_zero,
    zero_add]
  ring

/-- Differentiating the coefficients of an exponential obeys the chain rule. -/
theorem powerSeriesDerivation_exponential [Algebra ℚ K] [Algebra ℚ A]
    [IsScalarTower ℚ K A] (D : Derivation K A A) (f : PowerSeries A)
    (hf : constantCoeff f = 0) :
    powerSeriesDerivation D (exponential f) =
      exponential f * powerSeriesDerivation D f := by
  letI : IsAddTorsionFree A := .of_module_rat A
  let g := powerSeriesDerivation D (exponential f) -
    exponential f * powerSeriesDerivation D f
  have hg : derivative A g = derivative A f * g := by
    dsimp only [g]
    rw [map_sub, ← powerSeriesDerivation_derivative, derivative_exponential hf,
      powerSeriesDerivation_mul, (derivative A).leibniz,
      derivative_exponential hf, ← powerSeriesDerivation_derivative]
    simp only [smul_eq_mul]
    ring
  have hc : constantCoeff g = constantCoeff (0 : PowerSeries A) := by
    dsimp only [g]
    rw [map_sub, map_mul, constantCoeff_exponential hf,
      ← coeff_zero_eq_constantCoeff, coeff_powerSeriesDerivation,
      coeff_zero_eq_constantCoeff, constantCoeff_exponential hf,
      D.map_one_eq_zero, ← coeff_zero_eq_constantCoeff,
      coeff_powerSeriesDerivation, coeff_zero_eq_constantCoeff, hf, map_zero]
    simp
  have hz : g = 0 := differential_unique (derivative A f) hg (by simp) hc
  exact sub_eq_zero.mp hz

theorem coe_powerSeriesDerivation (D : Derivation K A A) (f : PowerSeries A) :
    (powerSeriesDerivation D f : LaurentSeries A) =
      laurentDerivation D (f : LaurentSeries A) := by
  apply HahnSeries.ext
  funext i
  cases i with
  | ofNat n => simp only [Int.ofNat_eq_natCast, LaurentSeries.coeff_coe_powerSeries,
      coeff_laurentDerivation, coeff_powerSeriesDerivation]
  | negSucc n => simp only [PowerSeries.coeff_coe, Int.negSucc_lt_zero, if_true,
      coeff_laurentDerivation, map_zero]

theorem laurentDerivation_exponential [Algebra ℚ K] [Algebra ℚ A]
    [IsScalarTower ℚ K A] (D : Derivation K A A) (f : PowerSeries A)
    (hf : constantCoeff f = 0) :
    laurentDerivation D (exponential f : LaurentSeries A) =
      (exponential f : LaurentSeries A) * laurentDerivation D (f : LaurentSeries A) := by
  rw [← coe_powerSeriesDerivation, powerSeriesDerivation_exponential D f hf,
    PowerSeries.coe_mul, coe_powerSeriesDerivation]

end KanadeRussell.Tsuchioka.FormalSeries
