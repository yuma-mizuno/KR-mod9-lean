import KanadeRussell.Infra.SecondCoefficient
set_option autoImplicit false
open PowerSeries PowerSeries.WithPiTopology Filter Topology
namespace KanadeRussell.Infra.FirstCoefficient
variable {R : Type*} [CommRing R]

/-- The finite logarithmic product rule, without division by the product. -/
theorem coeff_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries R) (d : ι → R)
    (h : ∀ i, coeff 1 (f i) = constantCoeff (f i) * d i) :
    coeff 1 (∏ i ∈ s, f i) = constantCoeff (∏ i ∈ s, f i) * ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, coeff_one_mul, h, ih, map_mul]
    ring

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
/-- The first logarithmic coefficient commutes with the convergent product. -/
theorem coeff_hasProd {ι : Type*} {f : ι → PowerSeries R} {F : PowerSeries R}
    {d : ι → R} {D : R} (hf : HasProd f F) (hd : HasSum d D)
    (h : ∀ i, coeff 1 (f i) = constantCoeff (f i) * d i) :
    coeff 1 F = constantCoeff F * D := by
  have hfirst := (continuous_coeff R 1).tendsto F |>.comp hf
  have hc := (continuous_constantCoeff R).tendsto F |>.comp hf
  apply tendsto_nhds_unique hfirst
  simpa only [Function.comp_def, coeff_prod _ f d h] using hc.mul hd
end KanadeRussell.Infra.FirstCoefficient
