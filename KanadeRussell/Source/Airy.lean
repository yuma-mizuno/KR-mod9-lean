import KanadeRussell.Infra.Nonarch
import KanadeRussell.Infra.QDifference
set_option backward.isDefEq.respectTransparency false

/-! The formal q-Airy function and its Wronskian, paper `app:casoratian`. -/

open PowerSeries
open scoped QTheory

namespace KanadeRussell.Source

section Airy
variable {R : Type*} [CommRing R] [IsDomain R]

noncomputable def airy (p : R) : PowerSeries R :=
  mk fun n => p ^ n.choose 2 * bInv (p ^ 2; p ^ 2)_n

omit [IsDomain R] in
@[simp] theorem constantCoeff_rescale (r : R) (f : PowerSeries R) :
    constantCoeff (rescale r f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff]
  simp only [coeff_rescale, pow_zero, one_mul]

omit [IsDomain R] in
@[simp] theorem airy_constantCoeff (p : R) : constantCoeff (airy p) = 1 := by
  simp [airy]

omit [IsDomain R] in
/-- Paper `eq:app-Ai-contiguity`. -/
theorem airy_contiguity (p : R) (hu : ∀ n, IsUnit (p ^ 2; p ^ 2)_n) :
    airy p - rescale (p ^ 2) (airy p) = X * rescale p (airy p) := by
  ext n
  cases n with
  | zero => simp [airy]
  | succ n =>
    simp only [map_sub, coeff_succ_X_mul, coeff_rescale, airy, coeff_mk]
    have hc := Infra.bInv_qFactorial_step (p ^ 2) n (hu n) (hu (n + 1))
    rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    linear_combination p ^ n * p ^ n.choose 2 * hc

/-- A shift-invariant formal series is constant if no positive power of the shift is one. -/
theorem eq_constant_of_rescale_eq (p : R) (hp : ∀ n : ℕ, 0 < n → p ^ n ≠ 1)
    (f : PowerSeries R) (hf : rescale p f = f) : f = C (constantCoeff f) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [coeff_C, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    have h := congrArg (coeff (n + 1)) hf
    rw [coeff_rescale] at h
    have hzero : (p ^ (n + 1) - 1) * coeff (n + 1) f = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (hp _ (by omega)))

/-- Paper `eq:app-Ai-Wronskian`, as an identity of formal series in the Airy argument. -/
theorem airy_wronskian (p : R) (hu : ∀ n, IsUnit (p ^ 2; p ^ 2)_n)
    (hp : ∀ n : ℕ, 0 < n → p ^ n ≠ 1) :
    airy p * rescale (-p) (airy p) + rescale (-1) (airy p) * rescale p (airy p) = 2 := by
  let f := airy p
  let g := rescale (-1) f
  have hf := airy_contiguity p hu
  have hg := congrArg (rescale (-1 : R)) hf
  simp only [map_sub, map_mul, rescale_neg_one_X, rescale_rescale,
    mul_neg_one] at hg
  have hs : rescale p (f * rescale p g + g * rescale p f) =
      f * rescale p g + g * rescale p f := by
    simp only [map_add, map_mul, rescale_rescale]
    dsimp [g, f]
    simp only [rescale_rescale, neg_one_mul]
    rw [← pow_two]
    linear_combination -(rescale (-p) (airy p)) * hf - (rescale p (airy p)) * hg
  have h := eq_constant_of_rescale_eq p hp _ hs
  simpa [f, g, rescale_rescale, map_ofNat, one_add_one_eq_two] using h

end Airy
end KanadeRussell.Source
