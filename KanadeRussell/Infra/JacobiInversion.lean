import KanadeRussell.Infra.JacobiFiniteOrderArguments
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
namespace KanadeRussell.Infra.JacobiInversion
open JacobiJets JacobiFirstJet
variable {R : Type*} [CommRing R]

/-- Inverting a unit argument preserves invertibility of its initial denominator. -/
theorem denominator_inv_isUnit (u : Rˣ) (hu : IsUnit (1-(u : R))) :
    IsUnit (1-((u⁻¹ : Rˣ) : R)) := by
  have he : 1-((u⁻¹ : Rˣ) : R) = -((u⁻¹ : Rˣ) : R)*(1-(u : R)) := by
    have hh := Units.inv_mul u
    linear_combination -hh
  rw [he]
  exact (u⁻¹).isUnit.neg.mul hu

theorem denominator_inv_bInv (u : Rˣ) (hu : IsUnit (1-(u : R))) :
    bInv (1-((u⁻¹ : Rˣ) : R)) = -(u : R)*bInv (1-(u : R)) := by
  apply (denominator_inv_isUnit u hu).mul_left_cancel
  rw [(denominator_inv_isUnit u hu).mul_bInv_cancel]
  have hh := Units.inv_mul u
  linear_combination -hu.mul_bInv_cancel - bInv (1-(u : R))*hh

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
/-- The centered first logarithmic Jacobi jet is odd. No tail interchange is used. -/
theorem logarithmic_inv (p u : Rˣ) (hu : IsUnit (1-(u : R))) :
    jacobiLogarithmicLambert p u⁻¹ = 1-jacobiLogarithmicLambert p u := by
  simp only [jacobiLogarithmicLambert, denominator_inv_bInv u hu,
    div_eq_mul_inv, Units.val_mul, Units.val_pow_eq_pow_val, inv_inv]
  rw [mul_comm ((u⁻¹ : Rˣ) : R) ((p : R)^2), mul_comm (u : R) ((p : R)^2)]
  have hh := Units.inv_mul u
  linear_combination hu.mul_bInv_cancel + bInv (1-(u : R))*hh

/-- The actual elliptic Lambert function is even under argument inversion. -/
theorem elliptic_inv (p u : Rˣ) (hp : IsTopologicallyNilpotent (p : R))
    (hu : IsTopologicallyNilpotent ((u : R)*(p : R)^2))
    (hv : IsTopologicallyNilpotent (((u⁻¹ : Rˣ) : R)*(p : R)^2))
    (hu0 : IsUnit (1-(u : R))) : ellipticLambert p u⁻¹ = ellipticLambert p u := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  simp only [ellipticLambert, div_eq_mul_inv, Units.val_mul, Units.val_pow_eq_pow_val, inv_inv]
  rw [JacobiParameter.lambertTail_split _ _ hp2 hv,
    JacobiParameter.lambertTail_split (u : R) _ hp2 hu, denominator_inv_bInv u hu0]
  rw [mul_comm ((u⁻¹ : Rˣ) : R) ((p : R)^2), mul_comm (u : R) ((p : R)^2)]
  have hh := Units.inv_mul u
  linear_combination (u : R)*bInv (1-(u : R))^2*hh

/-- Finite-order arguments automatically supply both convergent tails. -/
theorem elliptic_inv_finite_order (p u : Rˣ) {m : ℕ} (hm : m ≠ 0) (ho : u^m=1)
    (hp : IsTopologicallyNilpotent (p : R)) (hu0 : IsUnit (1-(u : R))) :
    ellipticLambert p u⁻¹ = ellipticLambert p u := by
  obtain ⟨hu,hv⟩ := JacobiFiniteOrderArguments.shifted_tails_nilpotent p u hm ho hp
  apply elliptic_inv p u hp hu _ hu0
  simpa only [div_eq_mul_inv, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm] using hv

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
/-- A division-free version of the order-two first-jet normalization. -/
theorem logarithmic_neg_one_twice (p : Rˣ) (h2 : IsUnit (2 : R)) :
    2*jacobiLogarithmicLambert p (-1) = 1 := by
  have hd : IsUnit (1-((-1 : Rˣ) : R)) := by simpa only [Units.val_neg, Units.val_one, sub_neg_eq_add, one_add_one_eq_two] using h2
  have h := logarithmic_inv p (-1) hd
  simp only [inv_neg, inv_one] at h
  linear_combination h

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
/-- The first logarithmic jet at minus one equals the inverse of two. -/
theorem logarithmic_neg_one (p : Rˣ) (h2 : IsUnit (2 : R)) :
    jacobiLogarithmicLambert p (-1) = bInv (2 : R) := by
  calc
    _ = bInv (2 : R)*(2*jacobiLogarithmicLambert p (-1)) := by
      rw [← mul_assoc, h2.bInv_mul_cancel, one_mul]
    _ = _ := by rw [logarithmic_neg_one_twice p h2, mul_one]

end KanadeRussell.Infra.JacobiInversion
