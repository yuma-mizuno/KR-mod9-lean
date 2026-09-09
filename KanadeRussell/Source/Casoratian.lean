import KanadeRussell.Infra.QDifference
set_option backward.isDefEq.respectTransparency false

/-! Denominator-free exterior transport, paper `app:casoratian`. -/

open PowerSeries

namespace KanadeRussell.Source

open Infra
variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
private theorem rescale_constant (q a : R) : rescale q (C a) = C a := by
  ext n
  simp only [coeff_rescale, coeff_C]
  split_ifs with h
  · subst n; simp
  · simp

noncomputable def casoratian (q : R) (f g : PowerSeries R) : PowerSeries R :=
  f * rescale q g - g * rescale q f

omit [IsDomain R] in
/-- Elimination of the two exterior transports, without dividing by `q` or `x`. -/
theorem casoratian_transport (q : R) (f g : PowerSeries R)
    (hf : scalarEquation q f = 0) (hg : scalarEquation q g = 0) :
    C q * casoratian q f g - (1 - C (q ^ 2) * X) * rescale q (casoratian q f g) -
      C q * X * (C (1 + q) + C (q ^ 4) * X ^ 2) * rescale (q ^ 2) (casoratian q f g) -
      C (q ^ 4) * X ^ 2 * rescale (q ^ 3) (casoratian q f g) = 0 := by
  have hf1 := congrArg (rescale q) hf
  have hg1 := congrArg (rescale q) hg
  simp only [scalarEquation, map_sub, map_add, map_mul, map_pow, rescale_X,
    rescale_rescale, map_zero, rescale_constant, map_one] at hf1 hg1
  simp only [casoratian, map_sub, map_mul, rescale_rescale]
  simp only [scalarEquation] at hf hg
  simp only [← pow_succ, ← pow_succ', ← pow_two, map_add, map_pow, map_one] at *
  linear_combination rescale q g * hf - rescale q f * hg +
    C q * X * rescale (q ^ 3) g * hf1 - C q * X * rescale (q ^ 3) f * hg1

/-- Dividing the Casoratian by its zero constant term yields the exterior equation. -/
theorem casoratian_exterior (q : R) (hq : q ≠ 0) (f g H : PowerSeries R)
    (hf : scalarEquation q f = 0) (hg : scalarEquation q g = 0)
    (hW : casoratian q f g = X * H) : exteriorEquation q H = 0 := by
  have ht := casoratian_transport q f g hf hg
  rw [hW] at ht
  have he : C q * X * exteriorEquation q H = 0 := by
    convert ht using 1
    simp only [exteriorEquation, map_mul, rescale_X]
    simp only [map_add, map_pow, map_one]
    ring
  have hqC : (C q : PowerSeries R) ≠ 0 := by
    intro h
    have hh := congrArg constantCoeff h
    exact hq (by simpa using hh)
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hqC X_ne_zero)

end KanadeRussell.Source
