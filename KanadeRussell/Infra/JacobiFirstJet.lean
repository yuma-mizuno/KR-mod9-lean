import KanadeRussell.Infra.FirstCoefficient
import KanadeRussell.Infra.LambertUnitArgument
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology Filter Topology
open scoped QTheory
namespace KanadeRussell.Infra.JacobiFirstJet
open JacobiJets
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def logLambertTail (a Q : R) : R :=
  ∑' n : ℕ, a * Q^n * bInv (1-a*Q^n)

theorem summable_logLambertTail (a Q : R) (ha : IsTopologicallyNilpotent a)
    (hQ : IsTopologicallyNilpotent Q) :
    Summable (fun n : ℕ => a*Q^n*bInv (1-a*Q^n)) := by
  have hz : Tendsto (fun n : ℕ => a*Q^n) atTop (𝓝 0) := by simpa using hQ.const_mul a
  have hi := tendsto_bInv_one_of_tendsto_zero_of_isTopologicallyNilpotent hz
    (Filter.Eventually.of_forall fun n => ha.mul_pow hQ (n := n))
  apply (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr
  rw [Nat.cofinite_eq_atTop]
  simpa using hz.mul hi

theorem summable_logLambertTail_of_shift (a Q : R)
    (hQ : IsTopologicallyNilpotent Q) (ha : IsTopologicallyNilpotent (a*Q)) :
    Summable (fun n : ℕ => a*Q^n*bInv (1-a*Q^n)) := by
  apply (summable_nat_add_iff 1).mp
  apply (summable_logLambertTail (a*Q) Q ha hQ).congr
  intro n
  have he : a*Q^(n+1)=(a*Q)*Q^n := by rw [pow_succ]; ring
  rw [he]

theorem logLambertTail_split (a Q : R)
    (hQ : IsTopologicallyNilpotent Q) (ha : IsTopologicallyNilpotent (a*Q)) :
    logLambertTail a Q = a*bInv (1-a) + logLambertTail (a*Q) Q := by
  rw [logLambertTail, (summable_logLambertTail_of_shift a Q hQ ha).tsum_eq_zero_add]
  simp only [pow_zero, mul_one]
  congr 1
  apply tsum_congr
  intro n
  have he : a*Q^(n+1)=(a*Q)*Q^n := by rw [pow_succ]; ring
  rw [he]

/-- First coefficient of a single convergent Pochhammer factor. -/
theorem pochhammer_first (a Q : R) (Z : (PowerSeries R)ˣ)
    (hQ : IsTopologicallyNilpotent Q) (hZ : constantCoeff (Z : PowerSeries R)=1)
    (hs : Summable (fun n : ℕ => a*Q^n*bInv (1-a*Q^n)))
    (hu : ∀ n : ℕ, IsUnit (1-a*Q^n)) :
    coeff 1 ((PowerSeries.C a*(Z : PowerSeries R); PowerSeries.C Q)_∞) =
      -((a;Q)_∞)*logLambertTail a Q*coeff 1 (Z : PowerSeries R) := by
  have hCQ : IsTopologicallyNilpotent (PowerSeries.C Q) := hQ.map continuous_C
  have hf := hasProd_qPochhammerInf (a := PowerSeries.C a*(Z : PowerSeries R)) hCQ
  have hd := hs.hasSum.neg.mul_right (coeff 1 (Z : PowerSeries R))
  have he := FirstCoefficient.coeff_hasProd hf hd
  have hn (n : ℕ) : coeff 1 (1-PowerSeries.C a*(Z : PowerSeries R)*(PowerSeries.C Q)^n) =
      constantCoeff (1-PowerSeries.C a*(Z : PowerSeries R)*(PowerSeries.C Q)^n)*
        (-(a*Q^n*bInv (1-a*Q^n))*coeff 1 (Z : PowerSeries R)) := by
    simp only [← map_pow, map_sub, coeff_one, if_neg (by decide : (1 : ℕ) ≠ 0),
      coeff_one_mul, coeff_C, constantCoeff_C, map_one, map_mul, hZ, mul_one, zero_mul,
      zero_add, add_zero]
    have hh := (hu n).mul_bInv_cancel
    linear_combination (a*Q^n)*coeff 1 (Z : PowerSeries R)*hh
  have hc : constantCoeff ((PowerSeries.C a*(Z : PowerSeries R); PowerSeries.C Q)_∞) = (a;Q)_∞ := by
    rw [map_qPochhammerInf constantCoeff (continuous_constantCoeff R) _ hCQ]
    simp [hZ]
  simpa only [hc, logLambertTail, mul_neg, neg_mul, mul_assoc] using he hn

private theorem pochhammer_constant (a Q : R) (Z : (PowerSeries R)ˣ)
    (hQ : IsTopologicallyNilpotent Q) (hZ : constantCoeff (Z : PowerSeries R)=1) :
    constantCoeff ((PowerSeries.C a*(Z : PowerSeries R); PowerSeries.C Q)_∞) = (a;Q)_∞ := by
  rw [map_qPochhammerInf constantCoeff (continuous_constantCoeff R) _ (hQ.map continuous_C)]
  simp [hZ]

/-- An individual Jacobi first jet for any formal unit parameter, with explicit
convergence and invertibility of every denominator in the two tails. -/
theorem jacobi_first_coefficient (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p : R)) (hZ : constantCoeff (Z : PowerSeries R)=1)
    (hsu : Summable (fun n : ℕ => (u : R)*((p : R)^2)^n*bInv (1-(u : R)*((p : R)^2)^n)))
    (hu : ∀ n : ℕ, IsUnit (1-(u : R)*((p : R)^2)^n))
    (hsv : Summable (fun n : ℕ => ((p^2/u : Rˣ) : R)*((p : R)^2)^n*
      bInv (1-((p^2/u : Rˣ) : R)*((p : R)^2)^n)))
    (hv : ∀ n : ℕ, IsUnit (1-((p^2/u : Rˣ) : R)*((p : R)^2)^n)) :
    coeff 1 (ThetaAddition.jacobi (unitC p) (unitC u*Z)) =
      ThetaAddition.jacobi p u *
        (-logLambertTail (u : R) ((p : R)^2) +
          logLambertTail ((p^2/u : Rˣ) : R) ((p : R)^2)) * coeff 1 (Z : PowerSeries R) := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have hCp : IsTopologicallyNilpotent ((unitC p : (PowerSeries R)ˣ) : PowerSeries R) :=
    hp.map continuous_C
  have hi := JacobiParameter.inverse_coefficients Z hZ
  have ha := pochhammer_first (u : R) ((p : R)^2) Z hp2 hZ hsu hu
  have hb := pochhammer_first ((p^2/u : Rˣ) : R) ((p : R)^2) Z⁻¹ hp2 hi.1 hsv hv
  have hc := pochhammer_constant (u : R) ((p : R)^2) Z hp2 hZ
  have hd := pochhammer_constant ((p^2/u : Rˣ) : R) ((p : R)^2) Z⁻¹ hp2 hi.1
  have hcomp : (unitC p)^2/(unitC u*Z)=unitC (p^2/u)*Z⁻¹ := by
    simp only [unitC, div_eq_mul_inv, mul_inv_rev, map_mul, map_inv, map_pow]
    simp only [mul_left_comm, mul_comm]
  rw [ThetaAddition.jacobi_eq_product _ _ hCp, hcomp,
    ThetaAddition.jacobi_eq_product p u hp]
  simp only [Units.val_mul, unitC_val, ← map_pow]
  rw [← map_qPochhammerInf PowerSeries.C continuous_C ((p : R)^2) hp2]
  simp only [
    coeff_one_mul, coeff_C, if_neg (by decide : (1 : ℕ) ≠ 0),
    map_mul, constantCoeff_C, ha, hb, hc, hd, hi.2.1]
  ring

/-- The explicitly split logarithmic Jacobi Lambert series. -/
noncomputable def jacobiLogarithmicLambert (p u : Rˣ) : R :=
  -(u : R)*bInv (1-(u : R)) - logLambertTail ((u : R)*(p : R)^2) ((p : R)^2) +
    logLambertTail ((p^2/u : Rˣ) : R) ((p : R)^2)

/-- Constant unit arguments are allowed: only the shifted positive tail and
complementary tail must be nilpotent, and the initial denominator must be a unit. -/
theorem jacobi_first_coefficient_of_shift (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p : R)) (hZ : constantCoeff (Z : PowerSeries R)=1)
    (hu : IsTopologicallyNilpotent ((u : R)*(p : R)^2)) (hu0 : IsUnit (1-(u : R)))
    (hv : IsTopologicallyNilpotent ((p^2/u : Rˣ) : R)) :
    coeff 1 (ThetaAddition.jacobi (unitC p) (unitC u*Z)) =
      ThetaAddition.jacobi p u * jacobiLogarithmicLambert p u * coeff 1 (Z : PowerSeries R) := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  rw [jacobi_first_coefficient p u Z hp hZ
    (summable_logLambertTail_of_shift _ _ hp2 hu)
    (JacobiParameter.units_lambertTail_of_shift _ _ hp2 hu hu0)
    (summable_logLambertTail _ _ hv hp2)
    (fun n => (hv.mul_pow hp2 (n := n)).isUnit_one_sub)]
  rw [logLambertTail_split _ _ hp2 hu]
  unfold jacobiLogarithmicLambert
  ring

/-- The same shifted-tail hypotheses make the actual Jacobi factor invertible. -/
theorem isUnit_jacobi_of_shift (p u : Rˣ)
    (hp : IsTopologicallyNilpotent (p : R))
    (hu : IsTopologicallyNilpotent ((u : R)*(p : R)^2)) (hu0 : IsUnit (1-(u : R)))
    (hv : IsTopologicallyNilpotent ((p^2/u : Rˣ) : R)) : IsUnit (ThetaAddition.jacobi p u) := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have ha : IsUnit (((u : R); (p : R)^2)_∞) := by
    rw [qPochhammerInf_eq_one_sub_mul_qPochhammerInf hp2]
    exact hu0.mul (isUnit_qPochhammerInf hu hp2)
  rw [ThetaAddition.jacobi_eq_product p u hp]
  exact ((isUnit_qPochhammerInf hp2 hp2).mul ha).mul (isUnit_qPochhammerInf hv hp2)

/-- The normalized individual Jacobi first jet, with no extra invertibility premise. -/
theorem jacobi_normalized_first_of_shift (p u : Rˣ)
    (hp : IsTopologicallyNilpotent (p : R))
    (hu : IsTopologicallyNilpotent ((u : R)*(p : R)^2)) (hu0 : IsUnit (1-(u : R)))
    (hv : IsTopologicallyNilpotent ((p^2/u : Rˣ) : R)) :
    coeff 1 (ThetaAddition.jacobi (unitC p) (unitC u*oneAddX)) *
      bInv (ThetaAddition.jacobi p u) = jacobiLogarithmicLambert p u := by
  rw [jacobi_first_coefficient_of_shift p u oneAddX hp (by simp) hu hu0 hv]
  have hh := (isUnit_jacobi_of_shift p u hp hu hu0 hv).mul_bInv_cancel
  simp only [oneAddX_val, map_add, coeff_one, coeff_X,
    if_neg (by decide : (1 : ℕ) ≠ 0), if_true, zero_add, mul_one]
  linear_combination jacobiLogarithmicLambert p u * hh

end KanadeRussell.Infra.JacobiFirstJet
