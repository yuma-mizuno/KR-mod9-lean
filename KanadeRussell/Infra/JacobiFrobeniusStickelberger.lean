import KanadeRussell.Infra.JacobiTripleAddition
import KanadeRussell.Infra.JacobiFirstJet
import KanadeRussell.Infra.JacobiCubicJet
import KanadeRussell.Infra.TripleProductJetCriterion
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped QTheory
namespace KanadeRussell.Infra.JacobiFrobeniusStickelberger
open JacobiJets JacobiFirstJet
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

/-- Specialization at the constant term of an arbitrary unit parameter. -/
theorem jacobi_constant (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p : R)) (hZ : constantCoeff (Z : PowerSeries R)=1) :
    constantCoeff (ThetaAddition.jacobi (unitC p) (unitC u*Z)) = ThetaAddition.jacobi p u := by
  have hp2 : IsTopologicallyNilpotent ((p : R)^2) := hp.pow (by decide)
  have hCp : IsTopologicallyNilpotent ((unitC p : (PowerSeries R)ˣ) : PowerSeries R) := hp.map continuous_C
  have hi := (JacobiParameter.inverse_coefficients Z hZ).1
  have hcomp : (unitC p)^2/(unitC u*Z)=unitC (p^2/u)*Z⁻¹ := by
    simp only [unitC, div_eq_mul_inv, mul_inv_rev, map_mul, map_inv, map_pow]
    simp only [mul_left_comm, mul_comm]
  rw [ThetaAddition.jacobi_eq_product _ _ hCp, hcomp, ThetaAddition.jacobi_eq_product p u hp]
  simp only [map_mul, Units.val_mul, unitC_val, ← map_pow,
    map_qPochhammerInf constantCoeff (continuous_constantCoeff R) _ (hp2.map continuous_C),
    constantCoeff_C, hZ, hi, mul_one]

noncomputable def normalizedJacobi (p u : Rˣ) (Z : (PowerSeries R)ˣ) : PowerSeries R :=
  PowerSeries.C (bInv (ThetaAddition.jacobi p u))*ThetaAddition.jacobi (unitC p) (unitC u*Z)

private theorem normalized_constant (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p : R)) (hZ : constantCoeff (Z : PowerSeries R)=1)
    (hj : IsUnit (ThetaAddition.jacobi p u)) : constantCoeff (normalizedJacobi p u Z)=1 := by
  simp only [normalizedJacobi, map_mul, constantCoeff_C, jacobi_constant p u Z hp hZ]
  exact hj.bInv_mul_cancel

omit [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] in
private theorem normalized_kernel (p u : Rˣ) :
    normalizedJacobi p u oneAddX * normalizedJacobi p u oneAddX⁻¹ =
      PowerSeries.C (bInv (ThetaAddition.jacobi p u)^2)*
        ThetaAddition.kernel (unitC p) (unitC u) oneAddX := by
  simp only [normalizedJacobi, ThetaAddition.kernel, div_eq_mul_inv, map_pow]
  ring

/-- The actual Jacobi jets imply Frobenius--Stickelberger from the exact balanced
triple product. No jet identities are premises. -/
theorem of_balanced_product (p : Rˣ) (u : Fin 3 → Rˣ)
    (hp : IsTopologicallyNilpotent (p : R))
    (hu : ∀ i, IsTopologicallyNilpotent ((u i : R)*(p : R)^2))
    (hu0 : ∀ i, IsUnit (1-(u i : R)))
    (hv : ∀ i, IsTopologicallyNilpotent ((p^2/u i : Rˣ) : R))
    (hprod : ThetaAddition.jacobi (unitC p) oneAddX *
      ((oneAddX : (PowerSeries R)ˣ) *
        ThetaAddition.jacobi (unitC p) (unitC (u 2)*oneAddX) *
        ThetaAddition.jacobi (unitC p) (unitC (u 0)/oneAddX) *
        ThetaAddition.jacobi (unitC p) (unitC (u 1)/oneAddX) +
        ThetaAddition.jacobi (unitC p) (unitC (u 0)*oneAddX) *
        ThetaAddition.jacobi (unitC p) (unitC (u 1)*oneAddX) *
        ThetaAddition.jacobi (unitC p) (unitC (u 2)/oneAddX)) =
      ThetaAddition.jacobi (unitC p) (oneAddX^2) *
        PowerSeries.C (ThetaAddition.jacobi p (u 0)) *
        PowerSeries.C (ThetaAddition.jacobi p (u 1)) *
        PowerSeries.C (ThetaAddition.jacobi p (u 2))) :
    (1-2*(jacobiLogarithmicLambert p (u 0)+jacobiLogarithmicLambert p (u 1)-
      jacobiLogarithmicLambert p (u 2)))^2 =
      1-24*lambertTail ((p : R)^2) ((p : R)^2) +
        4*(ellipticLambert p (u 0)+ellipticLambert p (u 1)+ellipticLambert p (u 2)) := by
  let f := fun i => normalizedJacobi p (u i) oneAddX
  let g := fun i => normalizedJacobi p (u i) oneAddX⁻¹
  let A : R := (((p : R)^2; (p : R)^2)_∞)^3
  let c := PowerSeries.C (bInv A)*ThetaAddition.jacobi (unitC p) oneAddX
  let d := PowerSeries.C (bInv A)*ThetaAddition.jacobi (unitC p) (oneAddX^2)
  have hj (i : Fin 3) := isUnit_jacobi_of_shift p (u i) hp (hu i) (hu0 i) (hv i)
  have hA : IsUnit A := (isUnit_qPochhammerInf (hp.pow (by decide : 2 ≠ 0))
    (hp.pow (by decide : 2 ≠ 0))).pow 3
  have hAc := hA.bInv_mul_cancel
  have hf (i) : constantCoeff (f i)=1 := normalized_constant p (u i) oneAddX hp (by simp) (hj i)
  have hg (i) : constantCoeff (g i)=1 := normalized_constant p (u i) oneAddX⁻¹ hp (by simp) (hj i)
  have hk (i) := JacobiParameter.kernel_coefficients_of_shift p (u i) oneAddX hp (by simp)
    (hu i) (hu0 i) (by simpa using (hv i).mul_pow (hp.pow (by decide : 2 ≠ 0)) (n := 1))
    (hv i).isUnit_one_sub
  have hk1 (i) : coeff 1 (f i*g i)=0 := by
    change coeff 1 (normalizedJacobi p (u i) oneAddX * normalizedJacobi p (u i) oneAddX⁻¹)=0
    rw [normalized_kernel, coeff_C_mul, (hk i).1, mul_zero]
  have hk2 (i) : coeff 2 (f i*g i)= -ellipticLambert p (u i) := by
    change coeff 2 (normalizedJacobi p (u i) oneAddX * normalizedJacobi p (u i) oneAddX⁻¹)=_
    rw [normalized_kernel, coeff_C_mul, (hk i).2]
    simp only [oneAddX_val, map_add, coeff_one, coeff_X,
      if_neg (by decide : (1 : ℕ) ≠ 0), if_true, zero_add, one_pow, mul_one]
    have hh := (hj i).bInv_mul_cancel
    calc
      _ = -(bInv (ThetaAddition.jacobi p (u i))*ThetaAddition.jacobi p (u i))^2*
        ellipticLambert p (u i) := by ring
      _ = _ := by rw [hh]; ring
  have hc := jacobi_oneAddX_cubic p hp
  have hc0 : constantCoeff c=0 := by simp [c, hc.1]
  have hc1 : coeff 1 c = -1 := by
    simp only [c, coeff_C_mul, hc.2.1]
    change bInv A * -A = -1
    rw [mul_neg, hAc]
  have hc2 : coeff 2 c=0 := by simp [c, hc.2.2.1]
  have hc3 : coeff 3 c=lambertTail ((p : R)^2) ((p : R)^2) := by
    simp only [c, coeff_C_mul, hc.2.2.2]
    change bInv A*(A*_) = _
    rw [← mul_assoc, hAc, one_mul]
  have hd3 : coeff 3 d=8*lambertTail ((p : R)^2) ((p : R)^2) := by
    rw [show d=PowerSeries.C (bInv A)*ThetaAddition.jacobi (unitC p) (oneAddX^2) from rfl,
      coeff_C_mul, jacobi_parameter_third p (oneAddX^2) hp (by simp)]
    have h1 : coeff 1 ((oneAddX^2 : (PowerSeries R)ˣ) : PowerSeries R)=2 := by
      simp [pow_two, coeff_one_mul, coeff_X]; ring
    have h3 : coeff 3 ((oneAddX^2 : (PowerSeries R)ˣ) : PowerSeries R)=0 := by
      simp [oneAddX_val, pow_two, coeff_mul, Finset.antidiagonal, coeff_X]
    rw [h1, h3]
    change bInv A*(A*_) = _
    rw [← mul_assoc, hAc]
    ring
  have hbalanced : c*((1+X)*f 2*g 0*g 1+f 0*f 1*g 2)=d := by
    have hh := congrArg (fun F : PowerSeries R =>
      PowerSeries.C (bInv A * bInv (ThetaAddition.jacobi p (u 0)) *
        bInv (ThetaAddition.jacobi p (u 1)) * bInv (ThetaAddition.jacobi p (u 2)))*F) hprod
    have h0 := congrArg PowerSeries.C (hj 0).bInv_mul_cancel
    have h1 := congrArg PowerSeries.C (hj 1).bInv_mul_cancel
    have h2 := congrArg PowerSeries.C (hj 2).bInv_mul_cancel
    simp only [map_mul, map_one] at h0 h1 h2
    have hr : PowerSeries.C (bInv A * bInv (ThetaAddition.jacobi p (u 0)) *
        bInv (ThetaAddition.jacobi p (u 1)) * bInv (ThetaAddition.jacobi p (u 2))) *
      (ThetaAddition.jacobi (unitC p) (oneAddX^2) *
        PowerSeries.C (ThetaAddition.jacobi p (u 0)) *
        PowerSeries.C (ThetaAddition.jacobi p (u 1)) *
        PowerSeries.C (ThetaAddition.jacobi p (u 2))) = d := by
      simp only [map_mul]
      calc
        _ = (PowerSeries.C (bInv (ThetaAddition.jacobi p (u 0)))*PowerSeries.C (ThetaAddition.jacobi p (u 0))) *
          (PowerSeries.C (bInv (ThetaAddition.jacobi p (u 1)))*PowerSeries.C (ThetaAddition.jacobi p (u 1))) *
          (PowerSeries.C (bInv (ThetaAddition.jacobi p (u 2)))*PowerSeries.C (ThetaAddition.jacobi p (u 2))) * d := by
            simp only [d]
            ring
        _ = d := by rw [h0, h1, h2]; simp
    rw [hr] at hh
    simp only [c, d, f, g, normalizedJacobi, oneAddX_val, div_eq_mul_inv, map_mul] at hh ⊢
    linear_combination hh
  have he := TripleProductJetCriterion.first_jet_identity f g c d
    (fun i => ellipticLambert p (u i)) (lambertTail ((p : R)^2) ((p : R)^2))
    hf hg hk1 hk2 hc0 hc1 hc2 hc3 hd3 hbalanced
  have hf1 (i) : coeff 1 (f i)=jacobiLogarithmicLambert p (u i) := by
    simp only [f, normalizedJacobi, coeff_C_mul]
    rw [mul_comm]
    exact jacobi_normalized_first_of_shift p (u i) hp (hu i) (hu0 i) (hv i)
  simpa only [hf1] using he

/-- Frobenius--Stickelberger for the actual Jacobi/Lambert functions. The first
argument is `a²`; this explicit square root is the hypothesis of the balanced
addition formula used here. All tail hypotheses concern the actual arguments. -/
theorem frobenius_stickelberger (p a v : Rˣ)
    (hp : IsTopologicallyNilpotent (p : R)) (ha : IsUnit (ThetaAddition.jacobi p a))
    (hu : ∀ i : Fin 3, IsTopologicallyNilpotent ((![a^2,v,a^2*v] i : Rˣ) * (p : R)^2))
    (hu0 : ∀ i : Fin 3, IsUnit (1-(![a^2,v,a^2*v] i : R)))
    (hv : ∀ i : Fin 3, IsTopologicallyNilpotent ((p^2/(![a^2,v,a^2*v] i) : Rˣ) : R)) :
    (1-2*(jacobiLogarithmicLambert p (a^2)+jacobiLogarithmicLambert p v-
      jacobiLogarithmicLambert p (a^2*v)))^2 =
      1-24*lambertTail ((p : R)^2) ((p : R)^2) +
        4*(ellipticLambert p (a^2)+ellipticLambert p v+ellipticLambert p (a^2*v)) := by
  have hanchor : IsUnit (ThetaAddition.jacobi (unitC p) (oneAddX*unitC a)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [mul_comm oneAddX, jacobi_constant p a oneAddX hp (by simp)]
    exact ha
  have h := ThetaAddition.jacobi_triple_addition (unitC p) (unitC a) (unitC v) oneAddX
    (hp.map continuous_C) hanchor
  have hpowers : (unitC a)^2=unitC (a^2) := by simp only [unitC, map_pow]
  have hmul : unitC (a^2)*unitC v=unitC (a^2*v) := by simp only [unitC, map_mul]
  rw [hpowers, hmul] at h
  simp only [JacobiJets.jacobi_unitC _ _ hp] at h
  have he := of_balanced_product p ![a^2,v,a^2*v] hp hu hu0 hv
    (by simpa using h)
  simpa using he

end KanadeRussell.Infra.JacobiFrobeniusStickelberger
