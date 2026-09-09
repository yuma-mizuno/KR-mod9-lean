import KanadeRussell.Representation.NilpotentConjugation
import Mathlib.Tactic.NoncommRing

namespace KanadeRussell.Representation
variable {A : Type*} [Ring A] [Algebra ℚ A]

noncomputable def nilpotentWeyl (E F : A) : A :=
  IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E
noncomputable def nilpotentWeylInv (E F : A) : A :=
  IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E)

theorem nilpotentWeyl_mul_inv {E F : A} (hE : IsNilpotent E) (hF : IsNilpotent F) :
    nilpotentWeyl E F * nilpotentWeylInv E F = 1 := by
  simp only [nilpotentWeyl, nilpotentWeylInv, mul_assoc]
  simp only [← mul_assoc (IsNilpotent.exp E) (IsNilpotent.exp (-E)),
    IsNilpotent.exp_mul_exp_neg_self hE, one_mul]
  simp only [← mul_assoc (IsNilpotent.exp (-F)) (IsNilpotent.exp F),
    IsNilpotent.exp_neg_mul_exp_self hF, one_mul, IsNilpotent.exp_mul_exp_neg_self hE]

theorem nilpotentWeyl_inv_mul {E F : A} (hE : IsNilpotent E) (hF : IsNilpotent F) :
    nilpotentWeylInv E F * nilpotentWeyl E F = 1 := by
  simpa [nilpotentWeyl, nilpotentWeylInv] using
    nilpotentWeyl_mul_inv hE.neg hF.neg

private theorem conj_linear {a b : A} (ha : IsNilpotent a) (t : ℚ)
    (hab : associativeAd a b = t • a) :
    IsNilpotent.exp a * b * IsNilpotent.exp (-a) = b + t • a := by
  have hz : associativeAd a (associativeAd a b) = 0 := by
    rw [hab, map_smul]
    simp
  have hc : (associativeAd a ^ 3) b = 0 := by
    change associativeAd a (associativeAd a (associativeAd a b)) = 0
    rw [hz, map_zero]
  rw [exp_conjugation_of_ad_cube_zero ha b hc, hz, smul_zero, add_zero, hab]

theorem nilpotentWeyl_conjugate_cartan {E F H B : A}
    (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEF : E*F-F*E=H) (hHE : H*E-E*H=(2:ℚ) • E)
    (hHF : H*F-F*H=(-2:ℚ) • F) (c : ℚ)
    (hBE : B*E-E*B=c • E) (hBF : B*F-F*B=(-c) • F) :
    nilpotentWeyl E F * B * nilpotentWeylInv E F = B-c • H := by
  have heB : associativeAd E B = (-c) • E := by
    simp only [associativeAd_apply]; rw [neg_smul, ← hBE]; abel
  have hfB : associativeAd (-F) B = (-c) • F := by
    simp only [associativeAd_apply, neg_mul, mul_neg]; rw [← hBF]; abel
  have hfE : associativeAd (-F) E = H := by
    simp only [associativeAd_apply, neg_mul, mul_neg]; rw [← hEF]; abel
  have hfH : associativeAd (-F) H = (-2:ℚ) • F := by
    simp only [associativeAd_apply, neg_mul, mul_neg]; rw [← hHF]; abel
  have heH : associativeAd E H = (-2:ℚ) • E := by
    simp only [associativeAd_apply]; rw [neg_smul, ← hHE]; abel
  have eB := conj_linear hE (-c) heB
  have eH := conj_linear hE (-2) heH
  have eE := conj_linear hE 0 (b := E) (by simp)
  have fB : IsNilpotent.exp (-F)*B*IsNilpotent.exp F = B + (-c) • F := by
    simpa using conj_linear hF.neg c (b := B) (by simpa using hfB)
  have fE : IsNilpotent.exp (-F)*E*IsNilpotent.exp F = E+H-F := by
    have hc : (associativeAd (-F)^3) E=0 := by
      change associativeAd (-F) (associativeAd (-F) (associativeAd (-F) E))=0
      rw [hfE, hfH, map_smul]
      simp [associativeAd_apply]
    have h := exp_conjugation_of_ad_cube_zero hF.neg E hc
    rw [hfE, hfH] at h
    simpa [smul_smul, sub_eq_add_neg] using h
  have hnest : nilpotentWeyl E F * B * nilpotentWeylInv E F =
      IsNilpotent.exp E * (IsNilpotent.exp (-F) *
        (IsNilpotent.exp E * B * IsNilpotent.exp (-E)) * IsNilpotent.exp F) *
        IsNilpotent.exp (-E) := by
    simp only [nilpotentWeyl, nilpotentWeylInv, mul_assoc]
  rw [hnest, eB]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [fB, fE]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  rw [eB, eE, eH]
  module

theorem nilpotentWeyl_conjugate_H {E F H : A}
    (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEF : E*F-F*E=H) (hHE : H*E-E*H=(2:ℚ) • E)
    (hHF : H*F-F*H=(-2:ℚ) • F) :
    nilpotentWeyl E F * H * nilpotentWeylInv E F = -H := by
  rw [nilpotentWeyl_conjugate_cartan hE hF hEF hHE hHF 2 hHE hHF]
  module

end KanadeRussell.Representation
