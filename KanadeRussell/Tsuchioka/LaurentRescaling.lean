import KanadeRussell.Tsuchioka.RootCovariance

/-! Variable rescaling of Laurent series by a unit, with all integer coefficients. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open scoped BigOperators

variable {A : Type*} [CommRing A]

/-- Substitute t by u*t. The Laurent support is unchanged. -/
noncomputable def laurentRescaleSeries (u : Aˣ) (f : LaurentSeries A) : LaurentSeries A where
  coeff n := (u ^ n : Aˣ) * f.coeff n
  isPWO_support' := f.isPWO_support.mono (by
    intro n hn
    change ((u ^ n : Aˣ) : A) * f.coeff n ≠ 0 at hn
    change f.coeff n ≠ 0
    exact fun h => hn (by rw [h, mul_zero]))

@[simp] theorem coeff_laurentRescaleSeries (u : Aˣ) (f : LaurentSeries A) (n : ℤ) :
    (laurentRescaleSeries u f).coeff n = (u ^ n : Aˣ) * f.coeff n := rfl

@[simp] theorem support_laurentRescaleSeries (u : Aˣ) (f : LaurentSeries A) :
    (laurentRescaleSeries u f).support = f.support := by
  ext n
  simp only [HahnSeries.mem_support, coeff_laurentRescaleSeries, ne_eq,
    Units.mul_right_eq_zero]

theorem laurentRescaleSeries_mul (u : Aˣ) (f g : LaurentSeries A) :
    laurentRescaleSeries u (f * g) =
      laurentRescaleSeries u f * laurentRescaleSeries u g := by
  apply HahnSeries.ext
  funext n
  have hd :
      Finset.addAntidiagonal (laurentRescaleSeries u f).isPWO_support
        (laurentRescaleSeries u g).isPWO_support n =
      Finset.addAntidiagonal f.isPWO_support g.isPWO_support n := by
    ext ij
    simp only [Finset.mem_addAntidiagonal, support_laurentRescaleSeries]
  simp only [coeff_laurentRescaleSeries, HahnSeries.coeff_mul, hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := (Finset.mem_addAntidiagonal.mp hij).2.2
  rw [← he, zpow_add, Units.val_mul]
  ring

/-- Laurent rescaling is a ring homomorphism, including on negative powers. -/
noncomputable def laurentRescale (u : Aˣ) : LaurentSeries A →+* LaurentSeries A where
  toFun := laurentRescaleSeries u
  map_one' := by
    apply HahnSeries.ext
    funext n
    simp only [coeff_laurentRescaleSeries, HahnSeries.coeff_one]
    split_ifs with hn
    · simp [hn]
    · simp
  map_mul' := laurentRescaleSeries_mul u
  map_zero' := by
    apply HahnSeries.ext
    funext n
    simp
  map_add' f g := by
    apply HahnSeries.ext
    funext n
    simp [HahnSeries.coeff_add, mul_add]

@[simp] theorem coeff_laurentRescale (u : Aˣ) (f : LaurentSeries A) (n : ℤ) :
    (laurentRescale u f).coeff n = (u ^ n : Aˣ) * f.coeff n := rfl

theorem laurentRescale_single (u : Aˣ) (n : ℤ) (a : A) :
    laurentRescale u (HahnSeries.single n a) =
      HahnSeries.single n ((u ^ n : Aˣ) * a) := by
  apply HahnSeries.ext
  funext k
  simp only [coeff_laurentRescale, HahnSeries.coeff_single]
  split_ifs with h
  · simp [h]
  · simp

@[simp] theorem laurentRescale_C (u : Aˣ) (a : A) :
    laurentRescale u (HahnSeries.C a) = HahnSeries.C a := by
  rw [HahnSeries.C_apply, laurentRescale_single]
  simp

theorem laurentRescale_powerSeries (u : Aˣ) (f : PowerSeries A) :
    laurentRescale u (f : LaurentSeries A) =
      (PowerSeries.rescale (u : A) f : PowerSeries A) := by
  apply HahnSeries.ext
  funext n
  simp only [coeff_laurentRescale, PowerSeries.coeff_coe, PowerSeries.coeff_rescale]
  split_ifs with hn
  · simp
  · have hn' : 0 ≤ n := by omega
    lift n to ℕ using hn'
    simp only [Int.natAbs_natCast, zpow_natCast, Units.val_pow_eq_pow_val]

end KanadeRussell.Tsuchioka.FormalSeries
