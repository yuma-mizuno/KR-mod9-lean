import KanadeRussell.Infra.Weighted
import KanadeRussell.Infra.QDifference
set_option backward.isDefEq.respectTransparency false

/-! Coefficient maps preserve the source operators and convergent specialization. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Infra

section Algebra
variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_scalarEquation (hom : R →+* S) (q : R) (f : PowerSeries R) :
    PowerSeries.map hom (scalarEquation q f) = scalarEquation (hom q) (PowerSeries.map hom f) := by
  simp only [scalarEquation, map_add, map_sub, map_mul, map_pow, map_C, map_X,
    ← rescale_map, map_one]

theorem map_exteriorEquation (hom : R →+* S) (q : R) (f : PowerSeries R) :
    PowerSeries.map hom (exteriorEquation q f) = exteriorEquation (hom q) (PowerSeries.map hom f) := by
  simp only [exteriorEquation, map_add, map_sub, map_mul, map_pow, map_C, map_X,
    ← rescale_map, map_one]
end Algebra

theorem SummableCoeff.map {f : PowerSeries QSeries} (hf : SummableCoeff f)
    (hom : QSeries →+* QSeries) (hhom : Continuous hom) : SummableCoeff (PowerSeries.map hom f) := by
  simpa only [SummableCoeff, coeff_map, Function.comp_def] using (hf.hasSum.map hom hhom).summable

theorem sumCoeff_map {f : PowerSeries QSeries} (hf : SummableCoeff f)
    (hom : QSeries →+* QSeries) (hhom : Continuous hom) :
    sumCoeff (PowerSeries.map hom f) = hom (sumCoeff f) := by
  exact ((hf.hasSum.map hom hhom).congr_fun (fun n => by simp only [coeff_map, Function.comp_def])).tsum_eq

end KanadeRussell.Infra
