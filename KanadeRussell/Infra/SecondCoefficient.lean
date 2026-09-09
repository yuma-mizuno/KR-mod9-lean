import KanadeRussell.Infra.PowerSeriesTopology

/-! The second coefficient of a convergent product whose individual factors
have zero first coefficient. These are the formal Taylor rules needed for the
Weierstrass difference formula; no analytic differentiation is used. -/
open PowerSeries PowerSeries.WithPiTopology Filter Topology
namespace KanadeRussell.Infra.SecondCoefficient
variable {R : Type*} [CommRing R]

theorem coeff_two_mul (f g : PowerSeries R) :
    coeff 2 (f*g) = coeff 2 f * constantCoeff g +
      coeff 1 f * coeff 1 g + constantCoeff f * coeff 2 g := by
  simp only [coeff_mul, show Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} by decide]
  simp
  ring

/-- Finite product rule with the normalization kept denominator-free. -/
theorem coeff_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries R) (d : ι → R)
    (h1 : ∀ i, coeff 1 (f i) = 0)
    (h2 : ∀ i, coeff 2 (f i) = constantCoeff (f i) * d i) :
    coeff 1 (∏ i ∈ s, f i) = 0 ∧
    coeff 2 (∏ i ∈ s, f i) = constantCoeff (∏ i ∈ s, f i) * ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    constructor
    · simp only [coeff_one_mul, h1, ih.1, zero_mul, add_zero]
    · rw [coeff_two_mul, h1, h2, ih.1, ih.2, map_mul]
      ring

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/-- Coefficient extraction commutes with the actual convergent product. -/
theorem coeff_hasProd {ι : Type*} {f : ι → PowerSeries R} {F : PowerSeries R}
    {d : ι → R} {D : R} (hf : HasProd f F) (hd : HasSum d D)
    (h1 : ∀ i, coeff 1 (f i) = 0)
    (h2 : ∀ i, coeff 2 (f i) = constantCoeff (f i) * d i) :
    coeff 1 F = 0 ∧ coeff 2 F = constantCoeff F * D := by
  have hfirst := (continuous_coeff R 1).tendsto F |>.comp hf
  have hsecond := (continuous_coeff R 2).tendsto F |>.comp hf
  have hc := (continuous_constantCoeff R).tendsto F |>.comp hf
  constructor
  · apply tendsto_nhds_unique hfirst
    simpa only [Function.comp_def, (coeff_prod _ f d h1 h2).1] using
      (tendsto_const_nhds : Tendsto (fun _ : Finset ι => (0 : R)) (SummationFilter.unconditional ι).filter (𝓝 0))
  · apply tendsto_nhds_unique hsecond
    simpa only [Function.comp_def, (coeff_prod _ f d h1 h2).2] using hc.mul hd

end KanadeRussell.Infra.SecondCoefficient
