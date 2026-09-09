import KanadeRussell.Infra.SecondCoefficient
import KanadeRussell.Infra.WeierstrassAddition

/-! Formal second-order variation of the paired Jacobi factors. -/
open PowerSeries PowerSeries.WithPiTopology Filter Topology
open scoped QTheory
namespace KanadeRussell.Infra.JacobiJets
open SecondCoefficient
variable {R : Type*} [CommRing R]

noncomputable def oneAddX : (PowerSeries R)ˣ :=
  (isUnit_iff_constantCoeff.mpr (by simp : IsUnit (constantCoeff (1 + X : PowerSeries R)))).unit

@[simp] theorem oneAddX_val : ((oneAddX : (PowerSeries R)ˣ) : PowerSeries R) = 1 + X :=
  IsUnit.unit_spec _

@[simp] theorem constantCoeff_inv :
    constantCoeff (((oneAddX : (PowerSeries R)ˣ)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) = 1 := by
  have h := congrArg constantCoeff (Units.mul_inv (oneAddX : (PowerSeries R)ˣ))
  simpa using h

@[simp] theorem coeff_one_inv :
    coeff 1 (((oneAddX : (PowerSeries R)ˣ)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) = -1 := by
  have h := congrArg (coeff 1) (Units.mul_inv (oneAddX : (PowerSeries R)ˣ))
  simp [coeff_one_mul] at h
  linear_combination h

@[simp] theorem coeff_two_inv :
    coeff 2 (((oneAddX : (PowerSeries R)ˣ)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) = 1 := by
  have h := congrArg (coeff 2) (Units.mul_inv (oneAddX : (PowerSeries R)ˣ))
  simp [coeff_two_mul, coeff_X] at h
  linear_combination h

noncomputable def pair (a : R) : PowerSeries R :=
  (1 - PowerSeries.C a * ((oneAddX : (PowerSeries R)ˣ) : PowerSeries R)) *
    (1 - PowerSeries.C a * (((oneAddX : (PowerSeries R)ˣ)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R))

@[simp] theorem pair_constant (a : R) : constantCoeff (pair a) = (1-a)^2 := by
  simp [pair, pow_two]

@[simp] theorem pair_first (a : R) : coeff 1 (pair a) = 0 := by
  simp [pair, coeff_one_mul]

@[simp] theorem pair_second (a : R) : coeff 2 (pair a) = -a := by
  simp [pair, coeff_two_mul, coeff_X]
  ring

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def pochPair (a Q : R) : PowerSeries R :=
  (PowerSeries.C a * (oneAddX : (PowerSeries R)ˣ); PowerSeries.C Q)_∞ *
    (PowerSeries.C a * (((oneAddX : (PowerSeries R)ˣ)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R);
      PowerSeries.C Q)_∞

noncomputable def lambertTail (a Q : R) : R :=
  ∑' n : ℕ, a * Q^n * bInv (1 - a * Q^n)^2

theorem summable_lambertTail (a Q : R) (ha : IsTopologicallyNilpotent a)
    (hQ : IsTopologicallyNilpotent Q) :
    Summable (fun n : ℕ => a * Q^n * bInv (1 - a * Q^n)^2) := by
  have hz : Tendsto (fun n : ℕ => a * Q^n) atTop (𝓝 0) := by
    simpa using hQ.const_mul a
  have hi := tendsto_bInv_one_of_tendsto_zero_of_isTopologicallyNilpotent hz
    (Filter.Eventually.of_forall fun n => ha.mul_pow hQ (n := n))
  apply (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr
  rw [Nat.cofinite_eq_atTop]
  simpa using hz.mul (hi.pow 2)

omit [T2Space R] in
theorem hasProd_pair (a Q : R) (hQ : IsTopologicallyNilpotent Q) :
    HasProd (fun n : ℕ => pair (a*Q^n)) (pochPair a Q) := by
  have hCQ : IsTopologicallyNilpotent (PowerSeries.C Q) := hQ.map continuous_C
  apply (HasProd.mul
    (hasProd_qPochhammerInf (a := PowerSeries.C a * (oneAddX : (PowerSeries R)ˣ)) hCQ)
    (hasProd_qPochhammerInf
      (a := PowerSeries.C a * (((oneAddX : (PowerSeries R)ˣ)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R))
      hCQ)).congr_fun
  intro n
  simp only [pair, map_mul, map_pow]
  ring

/-- A complete formal second-order expansion of the paired infinite product. -/
theorem pochPair_coefficients (a Q : R) (ha : IsTopologicallyNilpotent a)
    (hQ : IsTopologicallyNilpotent Q) :
    coeff 1 (pochPair a Q) = 0 ∧
    coeff 2 (pochPair a Q) = -constantCoeff (pochPair a Q) * lambertTail a Q := by
  have hs := (summable_lambertTail a Q ha hQ).hasSum.neg
  have hh := coeff_hasProd (hasProd_pair a Q hQ) hs
    (fun n => pair_first (a*Q^n))
  have hnorm (n : ℕ) : coeff 2 (pair (a*Q^n)) =
      constantCoeff (pair (a*Q^n)) * -(a*Q^n * bInv (1-a*Q^n)^2) := by
    rw [pair_second, pair_constant]
    have hu := (ha.mul_pow hQ (n := n)).isUnit_one_sub.mul_bInv_cancel
    calc
      -(a*Q^n) = -(a*Q^n) * ((1-a*Q^n) * bInv (1-a*Q^n))^2 := by rw [hu]; ring
      _ = _ := by ring
  simpa only [lambertTail, mul_neg, neg_mul] using hh hnorm

@[simp] theorem pochPair_constant (a Q : R) (hQ : IsTopologicallyNilpotent Q) :
    constantCoeff (pochPair a Q) = (a; Q)_∞^2 := by
  have hCQ : IsTopologicallyNilpotent (PowerSeries.C Q) := hQ.map continuous_C
  simp only [pochPair, map_mul, map_qPochhammerInf constantCoeff
    (continuous_constantCoeff R) _ hCQ, constantCoeff_C, oneAddX_val,
    map_add, map_one, constantCoeff_X, add_zero, constantCoeff_inv, mul_one, pow_two]

noncomputable def unitC (u : Rˣ) : (PowerSeries R)ˣ :=
  Units.map PowerSeries.C.toMonoidHom u

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
@[simp] theorem unitC_val (u : Rˣ) :
    ((unitC u : (PowerSeries R)ˣ) : PowerSeries R) = PowerSeries.C (u : R) := rfl

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem complement_mul (p u z : Rˣ) : p^2/(u*z) = (p^2/u)*z⁻¹ := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

omit [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] in
private theorem complement_div (p u z : Rˣ) : p^2/(u/z) = (p^2/u)*z := by
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ac_rfl

/-- Jacobi's triple product factors the symmetric variation into the two
paired products for u and p²/u. -/
theorem kernel_eq_pochPair (p u : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    ThetaAddition.kernel (unitC p) (unitC u) oneAddX =
      PowerSeries.C (((p : R)^2; (p : R)^2)_∞)^2 *
        pochPair (u : R) ((p : R)^2) * pochPair ((p^2/u : Rˣ) : R) ((p : R)^2) := by
  have hCp : IsTopologicallyNilpotent ((unitC p : (PowerSeries R)ˣ) : PowerSeries R) :=
    hp.map continuous_C
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have hcomp : (unitC p)^2 / unitC u = unitC (p^2/u) := by
    simp only [unitC, map_div, map_pow]
  rw [ThetaAddition.kernel, ThetaAddition.jacobi_eq_product _ _ hCp,
    ThetaAddition.jacobi_eq_product _ _ hCp, complement_mul, complement_div]
  simp only [hcomp, pochPair, div_eq_mul_inv, Units.val_mul]
  simp only [unitC_val, ← map_pow, map_qPochhammerInf PowerSeries.C continuous_C _ hp2,
    Units.val_mul]
  ring

/-- The two-sided Lambert sum associated to a Jacobi argument. -/
noncomputable def ellipticLambert (p u : Rˣ) : R :=
  lambertTail (u : R) ((p : R)^2) + lambertTail ((p^2/u : Rˣ) : R) ((p : R)^2)

theorem kernel_coefficients (p u : Rˣ) (hp : IsTopologicallyNilpotent (p : R))
    (hu : IsTopologicallyNilpotent (u : R))
    (hv : IsTopologicallyNilpotent ((p^2/u : Rˣ) : R)) :
    coeff 1 (ThetaAddition.kernel (unitC p) (unitC u) oneAddX) = 0 ∧
    coeff 2 (ThetaAddition.kernel (unitC p) (unitC u) oneAddX) =
      -constantCoeff (ThetaAddition.kernel (unitC p) (unitC u) oneAddX) * ellipticLambert p u := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  obtain ⟨h1, h2⟩ := pochPair_coefficients (u : R) ((p : R)^2) hu hp2
  obtain ⟨k1, k2⟩ := pochPair_coefficients ((p^2/u : Rˣ) : R) ((p : R)^2) hv hp2
  rw [kernel_eq_pochPair p u hp]
  rw [← map_pow]
  constructor
  · simp only [coeff_one_mul, coeff_C_mul, h1, k1, zero_mul, mul_zero, add_zero]
  · simp only [coeff_two_mul, coeff_C_mul, map_mul, constantCoeff_C, h1, k1, h2, k2,
      ellipticLambert]
    ring

theorem kernel_constant (p u : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    constantCoeff (ThetaAddition.kernel (unitC p) (unitC u) oneAddX) =
      (ThetaAddition.jacobi p u)^2 := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  rw [kernel_eq_pochPair p u hp, ThetaAddition.jacobi_eq_product p u hp]
  simp only [map_mul, map_pow, constantCoeff_C, pochPair_constant _ _ hp2]
  ring

/-- At the central zero the entire first-order factor can be removed exactly. -/
theorem jacobi_oneAddX (p : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    ThetaAddition.jacobi (unitC p) oneAddX =
      -X * PowerSeries.C (((p : R)^2; (p : R)^2)_∞) * pochPair ((p : R)^2) ((p : R)^2) := by
  have hCp : IsTopologicallyNilpotent ((unitC p : (PowerSeries R)ˣ) : PowerSeries R) :=
    hp.map continuous_C
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have hCQ : IsTopologicallyNilpotent (PowerSeries.C ((p : R)^2)) := hp2.map continuous_C
  rw [ThetaAddition.jacobi_eq_product _ _ hCp]
  simp only [div_eq_mul_inv, Units.val_mul, Units.val_pow_eq_pow_val, unitC_val,
    ← map_pow]
  rw [qPochhammerInf_eq_one_sub_mul_qPochhammerInf (a := ((oneAddX : (PowerSeries R)ˣ) : PowerSeries R)) hCQ]
  rw [map_qPochhammerInf PowerSeries.C continuous_C _ hp2]
  simp only [pochPair, oneAddX_val]
  rw [mul_comm (1 + X) (PowerSeries.C ((p : R)^2))]
  ring

/-- The squared Jacobi zero has second coefficient E_Q^6. -/
theorem jacobi_square_coefficients (p : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    constantCoeff ((ThetaAddition.jacobi (unitC p) oneAddX)^2) = 0 ∧
    coeff 1 ((ThetaAddition.jacobi (unitC p) oneAddX)^2) = 0 ∧
    coeff 2 ((ThetaAddition.jacobi (unitC p) oneAddX)^2) =
      (((p : R)^2; (p : R)^2)_∞)^6 := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  rw [jacobi_oneAddX p hp]
  have h : (-X * PowerSeries.C (((p : R)^2; (p : R)^2)_∞) *
      pochPair ((p : R)^2) ((p : R)^2))^2 =
      X^2 * (PowerSeries.C (((p : R)^2; (p : R)^2)_∞)^2 *
        (pochPair ((p : R)^2) ((p : R)^2))^2) := by ring
  rw [h]
  simp only [map_mul, map_pow, constantCoeff_X, zero_pow (by decide : 2 ≠ 0), zero_mul,
    coeff_X_pow_mul', show ¬ (2 : ℕ) ≤ 1 by decide, if_false, le_refl, if_true,
    Nat.sub_self, coeff_zero_eq_constantCoeff_apply, constantCoeff_C,
    pochPair_constant _ _ hp2, true_and]
  ring

/-- Constant coefficient inclusion preserves the bilateral Jacobi series. -/
theorem jacobi_unitC (p u : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    ThetaAddition.jacobi (unitC p) (unitC u) = PowerSeries.C (ThetaAddition.jacobi p u) := by
  have hCp : IsTopologicallyNilpotent ((unitC p : (PowerSeries R)ˣ) : PowerSeries R) :=
    hp.map continuous_C
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have hcomp : (unitC p)^2 / unitC u = unitC (p^2/u) := by
    simp only [unitC, map_div, map_pow]
  rw [ThetaAddition.jacobi_eq_product _ _ hCp, ThetaAddition.jacobi_eq_product p u hp]
  simp only [hcomp, unitC_val, ← map_pow, map_mul,
    map_qPochhammerInf PowerSeries.C continuous_C _ hp2]

theorem kernel_unitC (p u v : Rˣ) (hp : IsTopologicallyNilpotent (p : R)) :
    ThetaAddition.kernel (unitC p) (unitC u) (unitC v) =
      PowerSeries.C (ThetaAddition.kernel p u v) := by
  have hm : unitC u * unitC v = unitC (u*v) := by simp only [unitC, map_mul]
  have hd : unitC u / unitC v = unitC (u/v) := by simp only [unitC, map_div]
  simp only [ThetaAddition.kernel, hm, hd, jacobi_unitC _ _ hp, map_mul]

end KanadeRussell.Infra.JacobiJets
