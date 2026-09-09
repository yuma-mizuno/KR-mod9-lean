import KanadeRussell.Representation.NilpotentWeyl
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.RestrictScalars

namespace KanadeRussell.Representation
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

local instance : Algebra ℚ (Module.End K V) := Algebra.restrictScalars ℚ K (Module.End K V)

noncomputable def nilpotentWeylEquiv (E F : Module.End K V)
    (hE : IsNilpotent E) (hF : IsNilpotent F) : V ≃ₗ[K] V where
  toLinearMap := nilpotentWeyl E F
  invFun := fun v => (nilpotentWeylInv E F : Module.End K V) v
  left_inv v := by
    change (nilpotentWeylInv E F * nilpotentWeyl E F) v = v
    rw [nilpotentWeyl_inv_mul hE hF]; rfl
  right_inv v := by
    change (nilpotentWeyl E F * nilpotentWeylInv E F) v = v
    rw [nilpotentWeyl_mul_inv hE hF]; rfl

@[simp] theorem nilpotentWeylEquiv_apply (E F : Module.End K V)
    (hE : IsNilpotent E) (hF : IsNilpotent F) (v : V) :
    nilpotentWeylEquiv E F hE hF v = nilpotentWeyl E F v := rfl

theorem nilpotentWeyl_weight {E F H B : Module.End K V}
    (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEF : E*F-F*E=H) (hHE : H*E-E*H=(2:ℚ) • E)
    (hHF : H*F-F*H=(-2:ℚ) • F) (c : ℚ)
    (hBE : B*E-E*B=c • E) (hBF : B*F-F*B=(-c) • F)
    (v : V) (mu nu : K) (hvH : H v=mu • v) (hvB : B v=nu • v) :
    B (nilpotentWeylEquiv E F hE hF v) =
      (nu-(c:K)*mu) • nilpotentWeylEquiv E F hE hF v := by
  have he := nilpotentWeyl_conjugate_cartan hE.neg hF.neg
    (H := H) (B := B) (by simpa using hEF)
    (by simpa [mul_neg, neg_mul, sub_eq_add_neg, add_comm] using congrArg Neg.neg hHE)
    (by simpa [mul_neg, neg_mul, sub_eq_add_neg, add_comm] using congrArg Neg.neg hHF) c
    (by simpa [mul_neg, neg_mul, sub_eq_add_neg, add_comm] using congrArg Neg.neg hBE)
    (by simpa [mul_neg, neg_mul, sub_eq_add_neg, add_comm] using congrArg Neg.neg hBF)
  have he' : nilpotentWeylInv E F * B * nilpotentWeyl E F = B-c • H := by
    simpa [nilpotentWeyl, nilpotentWeylInv] using he
  have hb : B * nilpotentWeyl E F = nilpotentWeyl E F * (B-c • H) := by
    rw [← he']
    simp only [← mul_assoc, nilpotentWeyl_mul_inv hE hF, one_mul]
  change (B * nilpotentWeyl E F) v = _
  rw [hb]
  simp only [Module.End.mul_apply, LinearMap.sub_apply, hvB,
    map_sub, map_smul, nilpotentWeylEquiv_apply]
  rw [← Rat.cast_smul_eq_qsmul K c]
  simp [LinearMap.smul_apply, hvH, map_smul, smul_smul, sub_smul]

theorem nilpotentWeylInv_weight {E F H B : Module.End K V}
    (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEF : E*F-F*E=H) (hHE : H*E-E*H=(2:ℚ) • E)
    (hHF : H*F-F*H=(-2:ℚ) • F) (c : ℚ)
    (hBE : B*E-E*B=c • E) (hBF : B*F-F*B=(-c) • F)
    (v : V) (mu nu : K) (hvH : H v=mu • v) (hvB : B v=nu • v) :
    B (nilpotentWeylInv E F v) = (nu-(c:K)*mu) • nilpotentWeylInv E F v := by
  have h := nilpotentWeyl_weight hE.neg hF.neg
    (H := H) (B := B) (by simpa using hEF)
    (by simpa [mul_neg, neg_mul, sub_eq_add_neg, add_comm] using congrArg Neg.neg hHE)
    (by simpa [mul_neg, neg_mul, sub_eq_add_neg, add_comm] using congrArg Neg.neg hHF) c
    (by simpa [mul_neg, neg_mul, sub_eq_add_neg, add_comm] using congrArg Neg.neg hBE)
    (by simpa [mul_neg, neg_mul, sub_eq_add_neg, add_comm] using congrArg Neg.neg hBF)
    v mu nu hvH hvB
  simpa [nilpotentWeylEquiv_apply, nilpotentWeyl, nilpotentWeylInv] using h

end KanadeRussell.Representation
