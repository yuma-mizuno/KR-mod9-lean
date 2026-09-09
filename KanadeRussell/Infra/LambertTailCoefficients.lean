import KanadeRussell.Infra.JacobiFirstJet
import KanadeRussell.Representation.RootLambertDivisorBridge

/-! Actual Lambert tails as finite-coefficient scalar transforms. The index
exchange is a bijection of the positive divisor pairs of each coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Infra.LambertTailCoefficients
open JacobiJets JacobiFirstJet KanadeRussell.Representation
variable {K : Type*} [Field K]
local instance : UniformSpace K := ⊥

private theorem scalar_monomial_nilpotent (u : K) (h : ℕ) (hh : 0 < h) :
    IsTopologicallyNilpotent (PowerSeries.C u * (X : PowerSeries K)^h) := by
  simp [hh.ne']

private theorem hasSum_log_term (u : K) (h : ℕ) (hh : 0 < h) :
    HasSum (fun k : ℕ => PowerSeries.C (u^(k+1))*(X : PowerSeries K)^((k+1)*h))
      (PowerSeries.C u*X^h*bInv (1-PowerSeries.C u*X^h)) := by
  have hx := scalar_monomial_nilpotent u h hh
  have hg : HasSum (fun k : ℕ => (PowerSeries.C u*(X : PowerSeries K)^h)^k)
      (bInv (1-PowerSeries.C u*X^h)) := by
    rw [hx.bInv_one_sub_eq]
    exact hx.summable_pow.hasSum
  apply (hg.mul_left (PowerSeries.C u*X^h)).congr_fun
  intro k
  rw [← pow_succ', mul_pow, ← map_pow, ← pow_mul, Nat.mul_comm h]

private theorem hasSum_even_term (u : K) (h : ℕ) (hh : 0 < h) :
    HasSum (fun k : ℕ => PowerSeries.C (((k+1 : ℕ) : K)*u^(k+1))*(X : PowerSeries K)^((k+1)*h))
      (PowerSeries.C u*X^h*bInv (1-PowerSeries.C u*X^h)^2) := by
  have hx := scalar_monomial_nilpotent u h hh
  have hg : HasSum (fun k : ℕ => (PowerSeries.C u*(X : PowerSeries K)^h)^k)
      (bInv (1-PowerSeries.C u*X^h)) := by
    rw [hx.bInv_one_sub_eq]
    exact hx.summable_pow.hasSum
  have hc := (hg.mul_antidiagonal hg).mul_left (PowerSeries.C u*X^h)
  have he (k : ℕ) : (∑ p ∈ Finset.antidiagonal k,
      (PowerSeries.C u*(X : PowerSeries K)^h)^p.1*(PowerSeries.C u*X^h)^p.2) =
      (k+1) • (PowerSeries.C u*(X : PowerSeries K)^h)^k := by
    calc
      _ = ∑ _p ∈ Finset.antidiagonal k, (PowerSeries.C u*(X : PowerSeries K)^h)^k :=
        Finset.sum_congr rfl (fun p hp => by rw [← pow_add, Finset.mem_antidiagonal.mp hp])
      _ = _ := by simp
  rw [pow_two]
  apply hc.congr_fun
  intro k
  have hp : PowerSeries.C (u^(k+1))*(X : PowerSeries K)^((k+1)*h) =
      (PowerSeries.C u*X^h)*(PowerSeries.C u*X^h)^k := by
    rw [← pow_succ', mul_pow, ← map_pow, ← pow_mul, Nat.mul_comm h]
  rw [he]
  calc
    _ = (k+1) • (PowerSeries.C (u^(k+1))*(X : PowerSeries K)^((k+1)*h)) := by
      simp only [nsmul_eq_mul, map_mul, map_natCast]
      ring
    _ = _ := by rw [hp]; simp only [nsmul_eq_mul]; ring

private theorem coeff_log_term (u : K) (h n : ℕ) (hh : 0 < h) :
    coeff n (PowerSeries.C u*X^h*bInv (1-PowerSeries.C u*X^h)) =
      ∑ k ∈ Finset.range (n+1), if (k+1)*h=n then u^(k+1) else 0 := by
  classical
  have hc := (hasSum_log_term u h hh).map (coeff n) (continuous_coeff K n)
  rw [← hc.tsum_eq, tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Function.comp_apply, coeff_C_mul, coeff_X_pow]
    by_cases he : (k+1)*h=n
    · simp [he]
    · simp [he, Ne.symm he]
  · intro k hk
    have hne : n ≠ (k+1)*h := by
      have hk' : n+1 ≤ k := Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))
      nlinarith
    simp only [Function.comp_apply, coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero]

private theorem coeff_even_term (u : K) (h n : ℕ) (hh : 0 < h) :
    coeff n (PowerSeries.C u*X^h*bInv (1-PowerSeries.C u*X^h)^2) =
      ∑ k ∈ Finset.range (n+1), if (k+1)*h=n then ((k+1 : ℕ) : K)*u^(k+1) else 0 := by
  classical
  have hc := (hasSum_even_term u h hh).map (coeff n) (continuous_coeff K n)
  rw [← hc.tsum_eq, tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Function.comp_apply, coeff_C_mul, coeff_X_pow]
    by_cases he : (k+1)*h=n
    · simp [he]
    · simp [he, Ne.symm he]
  · intro k hk
    have hne : n ≠ (k+1)*h := by
      have hk' : n+1 ≤ k := Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))
      nlinarith
    simp only [Function.comp_apply, coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero]

theorem scalarLambertTransform_swap (f : ℕ → ℕ → K) :
    scalarLambertTransform (fun h k => f k h) = scalarLambertTransform f := by
  classical
  ext n
  rw [coeff_scalarLambertTransform_divisors, coeff_scalarLambertTransform_divisors]
  apply Finset.sum_bij (fun p _ => p.swap)
  · intro p hp
    simpa using hp
  · intro a ha b hb hab
    exact Prod.swap_injective hab
  · intro p hp
    exact ⟨p.swap, by simpa using hp, Prod.swap_swap p⟩
  · intro p hp
    rfl

/-- The positive logarithmic tail is the actual height-Fourier scalar transform. -/
theorem logLambertTail_eq_scalarLambertTransform (u : K) :
    logLambertTail (PowerSeries.C u*X) X =
      scalarLambertTransform (fun h _ => u^(h+1)) := by
  classical
  rw [← scalarLambertTransform_swap (fun h _ => u^(h+1))]
  ext n
  rw [coeff_scalarLambertTransform]
  have hx : IsTopologicallyNilpotent (X : PowerSeries K) := by simp
  have ha := scalar_monomial_nilpotent u 1 (by decide)
  simp only [pow_one] at ha
  have hc := (summable_logLambertTail (PowerSeries.C u*X) X ha hx).hasSum.map
    (coeff n) (continuous_coeff K n)
  change coeff n (logLambertTail (PowerSeries.C u*X) X) = _
  rw [logLambertTail, ← hc.tsum_eq, tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro h hh
    have hp : PowerSeries.C u*(X : PowerSeries K)*X^h=PowerSeries.C u*X^(h+1) := by
      rw [pow_succ']; ring
    simp only [Function.comp_apply, hp]
    exact coeff_log_term u (h+1) n (by omega)
  · intro h hh
    have hhn : ¬ h+1 ≤ n := by
      have hge : n ≤ h := Nat.le_of_not_gt (fun h => hh (Finset.mem_range.mpr h))
      omega
    have hp : PowerSeries.C u*(X : PowerSeries K)*X^h=PowerSeries.C u*X^(h+1) := by
      rw [pow_succ']; ring
    simp only [Function.comp_apply]
    rw [hp]
    simp only [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg hhn, mul_zero]

/-- The squared-denominator tail carries the height multiplier after divisor exchange. -/
theorem lambertTail_eq_scalarLambertTransform (u : K) :
    lambertTail (PowerSeries.C u*X) X =
      scalarLambertTransform (fun h _ => ((h+1 : ℕ) : K)*u^(h+1)) := by
  classical
  rw [← scalarLambertTransform_swap (fun h _ => ((h+1 : ℕ) : K)*u^(h+1))]
  ext n
  rw [coeff_scalarLambertTransform]
  have hx : IsTopologicallyNilpotent (X : PowerSeries K) := by simp
  have ha := scalar_monomial_nilpotent u 1 (by decide)
  simp only [pow_one] at ha
  have hc := (summable_lambertTail (PowerSeries.C u*X) X ha hx).hasSum.map
    (coeff n) (continuous_coeff K n)
  change coeff n (lambertTail (PowerSeries.C u*X) X) = _
  rw [lambertTail, ← hc.tsum_eq, tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro h hh
    have hp : PowerSeries.C u*(X : PowerSeries K)*X^h=PowerSeries.C u*X^(h+1) := by
      rw [pow_succ']; ring
    simp only [Function.comp_apply, hp]
    exact coeff_even_term u (h+1) n (by omega)
  · intro h hh
    have hhn : ¬ h+1 ≤ n := by
      have hge : n ≤ h := Nat.le_of_not_gt (fun h => hh (Finset.mem_range.mpr h))
      omega
    have hp : PowerSeries.C u*(X : PowerSeries K)*X^h=PowerSeries.C u*X^(h+1) := by
      rw [pow_succ']; ring
    simp only [Function.comp_apply]
    rw [hp]
    simp only [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg hhn, mul_zero]

section ContinuousEvaluation
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

/-- Continuous evaluation transports the proved finite transform to the actual logarithmic tail. -/
theorem map_logLambertTail_transform (f : PowerSeries K →+* R) (hf : Continuous f) (u : K) :
    f (scalarLambertTransform (fun h _ => u^(h+1))) =
      logLambertTail (f (PowerSeries.C u)*f X) (f X) := by
  rw [← logLambertTail_eq_scalarLambertTransform u]
  have hx : IsTopologicallyNilpotent (X : PowerSeries K) := by simp
  have ha := scalar_monomial_nilpotent u 1 (by decide)
  simp only [pow_one] at ha
  have hs := (summable_logLambertTail (PowerSeries.C u*X) X ha hx).hasSum.map f hf
  have ham : IsTopologicallyNilpotent (f (PowerSeries.C u)*f X) := by
    simpa only [map_mul] using ha.map hf
  apply hs.unique
  apply (summable_logLambertTail _ _ ham (hx.map hf)).hasSum.congr_fun
  intro n
  have hu := (ha.mul_pow hx (n := n)).isUnit_one_sub
  simp only [Function.comp_apply, map_mul, map_pow, hu.map_bInv f, map_sub, map_one]

/-- Continuous evaluation transports the height-weighted transform to the actual elliptic tail. -/
theorem map_lambertTail_transform (f : PowerSeries K →+* R) (hf : Continuous f) (u : K) :
    f (scalarLambertTransform (fun h _ => ((h+1 : ℕ) : K)*u^(h+1))) =
      lambertTail (f (PowerSeries.C u)*f X) (f X) := by
  rw [← lambertTail_eq_scalarLambertTransform u]
  have hx : IsTopologicallyNilpotent (X : PowerSeries K) := by simp
  have ha := scalar_monomial_nilpotent u 1 (by decide)
  simp only [pow_one] at ha
  have hs := (summable_lambertTail (PowerSeries.C u*X) X ha hx).hasSum.map f hf
  have ham : IsTopologicallyNilpotent (f (PowerSeries.C u)*f X) := by
    simpa only [map_mul] using ha.map hf
  apply hs.unique
  apply (summable_lambertTail _ _ ham (hx.map hf)).hasSum.congr_fun
  intro n
  have hu := (ha.mul_pow hx (n := n)).isUnit_one_sub
  simp only [Function.comp_apply, map_mul, map_pow, hu.map_bInv f, map_sub, map_one]

end ContinuousEvaluation

end KanadeRussell.Infra.LambertTailCoefficients
