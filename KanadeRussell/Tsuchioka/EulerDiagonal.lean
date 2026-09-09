import KanadeRussell.Tsuchioka.DiagonalEvaluation

/-! Euler differentiation of Laurent coefficients and its diagonal evaluation. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open scoped BigOperators

variable {A : Type*} [CommRing A]

/-- The Euler operator t*d/dt, with support contained in the original Laurent support. -/
noncomputable def laurentEulerSeries (f : LaurentSeries A) : LaurentSeries A where
  coeff n := (n : A) * f.coeff n
  isPWO_support' := f.isPWO_support.mono (by
    intro n hn
    change (n : A) * f.coeff n ≠ 0 at hn
    change f.coeff n ≠ 0
    exact fun h => hn (by rw [h, mul_zero]))

noncomputable def laurentEuler : LaurentSeries A →+ LaurentSeries A where
  toFun := laurentEulerSeries
  map_zero' := by
    apply HahnSeries.ext
    funext n
    simp [laurentEulerSeries]
  map_add' f g := by
    apply HahnSeries.ext
    funext n
    simp [laurentEulerSeries, mul_add]

@[simp] theorem coeff_laurentEuler (f : LaurentSeries A) (n : ℤ) :
    (laurentEuler f).coeff n = (n : A) * f.coeff n := rfl

theorem laurentEuler_powerSeries (f : PowerSeries A) :
    laurentEuler (f : LaurentSeries A) =
      ((PowerSeries.X * PowerSeries.derivative A f : PowerSeries A) : LaurentSeries A) := by
  apply HahnSeries.ext
  funext n
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, coeff_laurentEuler, LaurentSeries.coeff_coe_powerSeries,
      coeff_X_derivative, Int.cast_natCast]
    ring
  | negSucc n =>
    simp only [coeff_laurentEuler, PowerSeries.coeff_coe,
      Int.negSucc_lt_zero, if_true, mul_zero]

theorem diagonalEulerCoefficient_separated (u : Aˣ) (f g : LaurentSeries A) (d : ℤ) :
    diagonalEulerCoefficient u (separated f g) d =
      (laurentRescale u (laurentEuler f) * g).coeff d := by
  rw [diagonalEulerCoefficient, laurent_coeff_mul_finsum]
  apply finsum_congr
  intro i
  rw [separated_coeff, coeff_laurentRescale, coeff_laurentEuler]
  ring

theorem diagonalEulerCoefficient_add {f g : LaurentSeries (LaurentSeries A)}
    {l r l' r' : ℤ} (hf : RectangularBound f l r) (hg : RectangularBound g l' r')
    (u : Aˣ) (d : ℤ) :
    diagonalEulerCoefficient u (f + g) d =
      diagonalEulerCoefficient u f d + diagonalEulerCoefficient u g d := by
  simp only [diagonalEulerCoefficient, HahnSeries.coeff_add, mul_add]
  exact finsum_add_distrib (diagonalEulerCoefficient_finite hf u d)
    (diagonalEulerCoefficient_finite hg u d)

/-- A monomial shift contributes its inner exponent to the Euler weight. -/
theorem diagonalEulerCoefficient_single_mul {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (u : Aˣ) (a b : ℤ) (c : A) (d : ℤ) :
    diagonalEulerCoefficient u (HahnSeries.single b (HahnSeries.single a c) * f) d =
      ((u ^ a : Aˣ) * c) *
        (diagonalEulerCoefficient u f (d - a - b) +
          (a : A) * diagonalCoefficient u f (d - a - b)) := by
  have hfin := diagonalCoefficient_finite hf u (d - a - b)
  have hefin := diagonalEulerCoefficient_finite hf u (d - a - b)
  have hafin : (Function.support (fun i : ℤ =>
      (a : A) * ((u ^ i : Aˣ) * (f.coeff (d - a - b - i)).coeff i))).Finite :=
    hfin.subset (by
      intro i hi
      change (u ^ i : Aˣ) * (f.coeff (d - a - b - i)).coeff i ≠ 0
      intro hz
      exact hi (by simp [hz]))
  have hsumfin : (Function.support (fun i : ℤ =>
      (i : A) * (u ^ i : Aˣ) * (f.coeff (d - a - b - i)).coeff i +
        (a : A) * ((u ^ i : Aˣ) * (f.coeff (d - a - b - i)).coeff i))).Finite :=
    Function.HasFiniteSupport.add hefin hafin
  unfold diagonalEulerCoefficient diagonalCoefficient
  rw [mul_finsum' _ _ hfin, ← finsum_add_distrib hefin hafin, mul_finsum' _ _ hsumfin]
  apply finsum_eq_of_bijective (fun i : ℤ => i - a) (Equiv.subRight a).bijective
  intro i
  rw [HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul]
  have hb : d - a - b - (i - a) = d - i - b := by omega
  rw [hb, Int.cast_sub]
  have hu : ((u ^ a : Aˣ) : A) * (u ^ (i - a) : Aˣ) = (u ^ i : Aˣ) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 2
    omega
  linear_combination -((i : A) * c * (f.coeff (d - i - b)).coeff (i - a)) * hu

end KanadeRussell.Tsuchioka.FormalSeries
