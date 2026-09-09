import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Lie.AdjointAction.Basic

namespace KanadeRussell.Representation
variable {A : Type*} [Ring A] [Algebra ℚ A]

noncomputable def associativeAd (a : A) : Module.End ℚ A :=
  LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a

@[simp] theorem associativeAd_apply (a b : A) : associativeAd a b = a*b-b*a := rfl

theorem nilpotent_mulLeft {a : A} (ha : IsNilpotent a) :
    IsNilpotent (LinearMap.mulLeft ℚ a) := by
  obtain ⟨n,hn⟩ := ha
  exact ⟨n, by simp [LinearMap.pow_mulLeft, hn]⟩

theorem nilpotent_mulRight {a : A} (ha : IsNilpotent a) :
    IsNilpotent (LinearMap.mulRight ℚ a) := by
  obtain ⟨n,hn⟩ := ha
  exact ⟨n, by simp [LinearMap.pow_mulRight, hn]⟩

theorem exp_mulLeft_apply {a : A} (ha : IsNilpotent a) (b : A) :
    IsNilpotent.exp (LinearMap.mulLeft ℚ a) b = IsNilpotent.exp a * b := by
  obtain ⟨n,hn⟩ := ha
  rw [IsNilpotent.exp_eq_sum (show (LinearMap.mulLeft ℚ a)^n=0 by simp [hn]),
    IsNilpotent.exp_eq_sum hn]
  simp [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_mul]

theorem exp_mulRight_apply {a : A} (ha : IsNilpotent a) (b : A) :
    IsNilpotent.exp (LinearMap.mulRight ℚ a) b = b * IsNilpotent.exp a := by
  obtain ⟨n,hn⟩ := ha
  rw [IsNilpotent.exp_eq_sum (show (LinearMap.mulRight ℚ a)^n=0 by simp [hn]),
    IsNilpotent.exp_eq_sum hn]
  simp [LinearMap.sum_apply, LinearMap.smul_apply, Finset.mul_sum]

theorem associativeAd_nilpotent {a : A} (ha : IsNilpotent a) :
    IsNilpotent (associativeAd a) := by
  exact (LinearMap.commute_mulLeft_right a a).isNilpotent_sub
    (nilpotent_mulLeft ha) (nilpotent_mulRight ha)

theorem exp_associativeAd_apply {a : A} (ha : IsNilpotent a) (b : A) :
    IsNilpotent.exp (associativeAd a) b =
      IsNilpotent.exp a * b * IsNilpotent.exp (-a) := by
  have heq : associativeAd a = LinearMap.mulLeft ℚ a + LinearMap.mulRight ℚ (-a) := by
    ext x
    simp [associativeAd, mul_neg, sub_eq_add_neg]
  rw [heq, IsNilpotent.exp_add_of_commute (LinearMap.commute_mulLeft_right a (-a))
    (nilpotent_mulLeft ha) (nilpotent_mulRight ha.neg)]
  change IsNilpotent.exp (LinearMap.mulLeft ℚ a)
    (IsNilpotent.exp (LinearMap.mulRight ℚ (-a)) b) = _
  rw [exp_mulLeft_apply ha, exp_mulRight_apply ha.neg, mul_assoc]

theorem exp_conjugation_of_ad_cube_zero {a : A} (ha : IsNilpotent a) (b : A)
    (hb : (associativeAd a ^ 3) b = 0) :
    IsNilpotent.exp a * b * IsNilpotent.exp (-a) =
      b + associativeAd a b + (1/2 : ℚ) • (associativeAd a (associativeAd a b)) := by
  rw [← exp_associativeAd_apply ha b]
  have h := IsNilpotent.exp_smul_eq_sum (m := b) (k := 3) hb
    (associativeAd_nilpotent ha)
  change IsNilpotent.exp (associativeAd a) b = _ at h
  rw [h]
  norm_num [Finset.sum_range_succ, Module.End.smul_def, pow_succ,
    Module.End.mul_apply]

end KanadeRussell.Representation
