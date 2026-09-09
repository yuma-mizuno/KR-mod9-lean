import KanadeRussell.Product.Defs
import KanadeRussell.Pending.ProductNorm

/-! Field-free reduction of the product norm to a level-nine theta identity. -/
namespace KanadeRussell.Product

noncomputable def P : PowerSeries ℤ := J 1 * J 2 * J 4

theorem isUnit_P : IsUnit P :=
  ((isUnit_J 1 (by decide) (by decide)).mul
    (isUnit_J 2 (by decide) (by decide))).mul (isUnit_J 4 (by decide) (by decide))

theorem K_product_J : K₁ * K₂ * K₃ * (E 3) ^ 3 * P = (E 9) ^ 6 := by
  calc
    _ = (K₁ * E 3 * J 1) * (K₂ * E 3 * J 2) * (K₃ * E 3 * J 4) := by
      dsimp [P]; ring
    _ = _ := by rw [K_one_J, K_two_J, K_three_J]; ring

theorem norm_numerator :
    (E 3) ^ 3 * P ^ 3 * cubicNorm K₁ K₂ K₃ = (E 9) ^ 6 * thetaNumerator := by
  have h1 := congrArg (fun z : PowerSeries ℤ => z ^ 3) K_one_J
  have h2 := congrArg (fun z : PowerSeries ℤ => z ^ 3) K_two_J
  have h3 := congrArg (fun z : PowerSeries ℤ => z ^ 3) K_three_J
  have h123 := K_product_J
  dsimp [cubicNorm, thetaNumerator, P] at *
  linear_combination (J 2 * J 4) ^ 3 * h1 + q * (J 1 * J 4) ^ 3 * h2 -
    q ^ 2 * (J 1 * J 2) ^ 3 * h3 + 3 * q * (J 1 * J 2 * J 4) ^ 2 * h123

/-- An exact equivalence; neither side is assumed or asserted unconditionally. -/
theorem productNorm_iff_theta :
    ProductNorm ↔ E 3 * thetaNumerator = a * (E 1) ^ 2 * (E 9) ^ 3 := by
  have hsplit := congrArg (fun z : PowerSeries ℤ => z ^ 3) J_product
  have hres : (E 3) ^ 3 * P ^ 3 * (E 1 * E 3 * cubicNorm K₁ K₂ K₃ - a) =
      E 1 * (E 9) ^ 6 * (E 3 * thetaNumerator - a * (E 1) ^ 2 * (E 9) ^ 3) := by
    have hn := norm_numerator
    dsimp [P] at *
    linear_combination E 1 * E 3 * hn - a * hsplit
  have hl : (E 3) ^ 3 * P ^ 3 ≠ 0 :=
    ((isUnit_E 3 (by decide)).pow 3 |>.mul (isUnit_P.pow 3)).ne_zero
  have hr : E 1 * (E 9) ^ 6 ≠ 0 :=
    ((isUnit_E 1 (by decide)).mul ((isUnit_E 9 (by decide)).pow 6)).ne_zero
  change E 1 * E 3 * cubicNorm K₁ K₂ K₃ = a ↔ _
  constructor
  · intro h
    rw [h, sub_self, mul_zero] at hres
    exact sub_eq_zero.mp ((mul_eq_zero.mp hres.symm).resolve_left hr)
  · intro h
    rw [h, sub_self, mul_zero] at hres
    exact sub_eq_zero.mp ((mul_eq_zero.mp hres).resolve_left hl)

/-- Given the separate cubic theta identity, the remaining product norm is
exactly the cleared level-nine trace relation. -/
theorem productNorm_iff_trace
    (hc : a * E 3 = (E 1) ^ 3 + 9 * q * (E 9) ^ 3) :
    ProductNorm ↔ (E 9) ^ 3 * (thetaNumerator - 9 * q * P ^ 2) = (E 1) ^ 3 * P ^ 2 := by
  rw [productNorm_iff_theta]
  have hsplit := congrArg (fun z : PowerSeries ℤ => z ^ 2) J_product
  have hres : (E 3) ^ 2 *
      ((E 9) ^ 3 * (thetaNumerator - 9 * q * P ^ 2) - (E 1) ^ 3 * P ^ 2) =
      E 3 * (E 9) ^ 3 * (E 3 * thetaNumerator - a * (E 1) ^ 2 * (E 9) ^ 3) := by
    dsimp [P] at *
    linear_combination (E 1) ^ 2 * (E 9) ^ 6 * hc -
      ((E 1) ^ 3 + 9 * q * (E 9) ^ 3) * hsplit
  have hl : (E 3) ^ 2 ≠ 0 := ((isUnit_E 3 (by decide)).pow 2).ne_zero
  have hr : E 3 * (E 9) ^ 3 ≠ 0 :=
    ((isUnit_E 3 (by decide)).mul ((isUnit_E 9 (by decide)).pow 3)).ne_zero
  constructor
  · intro h
    rw [h, sub_self, mul_zero] at hres
    exact sub_eq_zero.mp ((mul_eq_zero.mp hres).resolve_left hl)
  · intro h
    rw [h, sub_self, mul_zero] at hres
    exact sub_eq_zero.mp ((mul_eq_zero.mp hres.symm).resolve_left hr)

end KanadeRussell.Product
