import KanadeRussell.Infra.SecondCoefficient

/-! The finite jet consequence of the balanced triple-product relation.
The product identity and its paired jets remain explicit hypotheses here;
this file uses no analytic differentiation or division. -/
set_option autoImplicit false
open PowerSeries
namespace KanadeRussell.Infra.TripleProductJetCriterion
open SecondCoefficient
variable {R : Type*} [CommRing R]

private theorem coeff_three_mul (f g : PowerSeries R) :
    coeff 3 (f*g) = coeff 3 f * constantCoeff g + coeff 2 f * coeff 1 g +
      coeff 1 f * coeff 2 g + constantCoeff f * coeff 3 g := by
  simp only [coeff_mul, show Finset.antidiagonal 3 = {(0,3),(1,2),(2,1),(3,0)} by decide]
  simp
  ring

/-- The quadratic first-jet identity follows from one balanced product identity
and its actual central and paired jets, over any commutative ring. -/
theorem first_jet_identity
    (f g : Fin 3 → PowerSeries R) (c d : PowerSeries R) (E : Fin 3 → R) (L : R)
    (hf : ∀ i, constantCoeff (f i) = 1) (hg : ∀ i, constantCoeff (g i) = 1)
    (hk1 : ∀ i, coeff 1 (f i*g i) = 0)
    (hk2 : ∀ i, coeff 2 (f i*g i) = -E i)
    (hc0 : constantCoeff c = 0) (hc1 : coeff 1 c = -1)
    (hc2 : coeff 2 c = 0) (hc3 : coeff 3 c = L) (hd3 : coeff 3 d = 8*L)
    (hprod : c*((1+X)*f 2*g 0*g 1 + f 0*f 1*g 2) = d) :
    (1-2*(coeff 1 (f 0)+coeff 1 (f 1)-coeff 1 (f 2)))^2 =
      1-24*L+4*(E 0+E 1+E 2) := by
  have hfirst (i : Fin 3) : coeff 1 (g i) = -coeff 1 (f i) := by
    have h := hk1 i
    simp only [coeff_one_mul, hf, hg, mul_one] at h
    linear_combination h
  have hsecond (i : Fin 3) : coeff 2 (f i)+coeff 2 (g i) = (coeff 1 (f i))^2-E i := by
    have h := hk2 i
    simp only [coeff_two_mul, hf, hg, one_mul, mul_one, hfirst] at h
    linear_combination h
  let B : PowerSeries R := (1+X)*f 2*g 0*g 1 + f 0*f 1*g 2
  have hB0 : constantCoeff B = 2 := by
    norm_num [B, hf, hg]
  have hB2 : coeff 2 B =
      (coeff 1 (f 0)+coeff 1 (f 1)-coeff 1 (f 2))^2 -
        (coeff 1 (f 0)+coeff 1 (f 1)-coeff 1 (f 2))-(E 0+E 1+E 2) := by
    simp [B, coeff_two_mul, coeff_one_mul, coeff_X, hf, hg, hfirst]
    linear_combination hsecond 0 + hsecond 1 + hsecond 2
  have hc := congrArg (coeff 3) hprod
  change coeff 3 (c*B) = coeff 3 d at hc
  rw [coeff_three_mul, hc0, hc1, hc2, hc3, hd3, hB0, hB2] at hc
  linear_combination -4*hc

end KanadeRussell.Infra.TripleProductJetCriterion
