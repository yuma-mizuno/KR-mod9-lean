import KanadeRussell.Tsuchioka.DeltaContraction

/-! Diagonal evaluation of separated Laurent factors and finite monomial shifts. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

open scoped BigOperators

variable {A : Type*} [CommRing A]

/-- Laurent multiplication as a finite sum over the first exponent. -/
theorem laurent_coeff_mul_finsum (f g : LaurentSeries A) (d : ℤ) :
    (f * g).coeff d = ∑ᶠ i : ℤ, f.coeff i * g.coeff (d - i) := by
  classical
  let h := Finset.addAntidiagonal f.isPWO_support g.isPWO_support d
  have hs : Function.support (fun i => f.coeff i * g.coeff (d - i)) ⊆
      (h.image Prod.fst : Set ℤ) := by
    intro i hi
    have hf : f.coeff i ≠ 0 := by
      intro hz
      exact hi (by simp [hz])
    have hg : g.coeff (d - i) ≠ 0 := by
      intro hz
      exact hi (by simp [hz])
    apply Finset.mem_image.mpr
    refine ⟨(i, d - i), ?_, rfl⟩
    exact Finset.mem_addAntidiagonal.mpr ⟨hf, hg, by omega⟩
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_image]
  · rw [HahnSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have he := (Finset.mem_addAntidiagonal.mp hij).2.2
    congr 2
    omega
  · intro ij hij kl hkl he
    have hi := (Finset.mem_addAntidiagonal.mp hij).2.2
    have hk := (Finset.mem_addAntidiagonal.mp hkl).2.2
    exact Prod.ext he (by omega)

/-- One Laurent factor in each variable. -/
noncomputable def separated (f g : LaurentSeries A) :
    LaurentSeries (LaurentSeries A) :=
  HahnSeries.C f * mapLaurent HahnSeries.C g

theorem separated_coeff (f g : LaurentSeries A) (a b : ℤ) :
    ((separated f g).coeff b).coeff a = f.coeff a * g.coeff b := by
  rw [separated, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    coeff_mapLaurent, HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]

theorem rectangular_innerLaurent (f : LaurentSeries A) :
    RectangularBound (HahnSeries.C f) f.order 0 := by
  intro a b hab
  by_cases hb : b = 0
  · subst b
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]
    exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  · simp [HahnSeries.C_apply, HahnSeries.coeff_single, hb]

theorem rectangular_outerLaurent (g : LaurentSeries A) :
    RectangularBound (mapLaurent HahnSeries.C g) 0 g.order := by
  intro a b hab
  rw [coeff_mapLaurent, HahnSeries.C_apply]
  by_cases ha : a = 0
  · subst a
    rw [HahnSeries.coeff_single_same]
    exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  · simp [HahnSeries.coeff_single, ha]

theorem separated_bounded (f g : LaurentSeries A) :
    RectangularBound (separated f g) f.order g.order := by
  simpa only [separated, add_zero, zero_add] using
    rectangular_mul (rectangular_innerLaurent f) (rectangular_outerLaurent g)

/-- Diagonal evaluation of separated factors is their rescaled Laurent product. -/
theorem diagonalCoefficient_separated (u : Aˣ) (f g : LaurentSeries A) (d : ℤ) :
    diagonalCoefficient u (separated f g) d =
      (laurentRescale u f * g).coeff d := by
  rw [diagonalCoefficient, laurent_coeff_mul_finsum]
  apply finsum_congr
  intro i
  rw [separated_coeff, coeff_laurentRescale]
  ring

theorem diagonalCoefficient_add {f g : LaurentSeries (LaurentSeries A)}
    {l r l' r' : ℤ} (hf : RectangularBound f l r) (hg : RectangularBound g l' r')
    (u : Aˣ) (d : ℤ) :
    diagonalCoefficient u (f + g) d =
      diagonalCoefficient u f d + diagonalCoefficient u g d := by
  simp only [diagonalCoefficient, HahnSeries.coeff_add, mul_add]
  exact finsum_add_distrib (diagonalCoefficient_finite hf u d)
    (diagonalCoefficient_finite hg u d)

/-- A monomial shift contributes its specialized phase and total exponent. -/
theorem diagonalCoefficient_single_mul {f : LaurentSeries (LaurentSeries A)} {l r : ℤ}
    (hf : RectangularBound f l r) (u : Aˣ) (a b : ℤ) (c : A) (d : ℤ) :
    diagonalCoefficient u (HahnSeries.single b (HahnSeries.single a c) * f) d =
      ((u ^ a : Aˣ) * c) * diagonalCoefficient u f (d - a - b) := by
  unfold diagonalCoefficient
  rw [mul_finsum' _ _ (diagonalCoefficient_finite hf u (d - a - b))]
  apply finsum_eq_of_bijective (fun i : ℤ => i - a)
    (Equiv.subRight a).bijective
  intro i
  rw [HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul]
  have hb : d - a - b - (i - a) = d - i - b := by omega
  rw [hb]
  have hu : ((u ^ a : Aˣ) : A) * (u ^ (i - a) : Aˣ) = (u ^ i : Aˣ) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 2
    omega
  linear_combination -(c * (f.coeff (d - i - b)).coeff (i - a)) * hu

end KanadeRussell.Tsuchioka.FormalSeries
