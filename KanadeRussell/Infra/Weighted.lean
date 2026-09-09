import KanadeRussell.Infra.SumCoeff
set_option backward.isDefEq.respectTransparency false

/-! Grouping a summable family by a natural-number weight. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity

namespace KanadeRussell.Infra

variable {α : Type*}

/-- A coefficient-defined generating series, grouped by the weight `w`. -/
noncomputable def weightedSeries (w : α → ℕ) (f : α → QSeries) : PowerSeries QSeries :=
  mk fun k => ∑' a, if k = w a then f a else 0

private theorem summable_weight_fiber (w : α → ℕ) {f : α → QSeries}
    (hf : Summable f) (k : ℕ) : Summable (fun a => if k = w a then f a else 0) := by
  classical
  exact (hf.indicator {a | k = w a}).congr (fun a => by
    simp only [Set.indicator_apply, Set.mem_setOf_eq])

/-- The grouped series is also the convergent sum of its weighted monomials. -/
theorem hasSum_weightedSeries (w : α → ℕ) {f : α → QSeries} (hf : Summable f) :
    HasSum (fun a => monomial (w a) (f a)) (weightedSeries w f) := by
  rw [hasSum_iff_hasSum_coeff]
  intro k
  simpa only [weightedSeries, coeff_mk, coeff_monomial] using
    (summable_weight_fiber w hf k).hasSum

/-- Regrouping does not change the sum when x is specialized to one. -/
theorem hasSum_weightedSeries_coeff (w : α → ℕ) {f : α → QSeries} (hf : Summable f) :
    HasSum (fun k => coeff k (weightedSeries w f)) (∑' a, f a) := by
  let graph : α → ℕ × α := fun a => (w a, a)
  have hinj : Function.Injective graph := by
    intro a b h
    exact congrArg Prod.snd h
  let g : ℕ × α → QSeries := fun ka => if ka.1 = w ka.2 then f ka.2 else 0
  have hoff : ∀ ka ∉ Set.range graph, g ka = 0 := by
    intro ka hka
    have hne : ka.1 ≠ w ka.2 := by
      intro he
      apply hka
      exact ⟨ka.2, Prod.ext he.symm rfl⟩
    simp [g, hne]
  have hg : HasSum g (∑' a, f a) := (hinj.hasSum_iff hoff).mp (by simpa [g, graph, Function.comp_def] using hf.hasSum)
  apply hg.prod_fiberwise
  intro k
  simpa only [g, weightedSeries, coeff_mk] using (summable_weight_fiber w hf k).hasSum

theorem weightedSeries_summableCoeff (w : α → ℕ) {f : α → QSeries} (hf : Summable f) :
    SummableCoeff (weightedSeries w f) := (hasSum_weightedSeries_coeff w hf).summable

theorem sumCoeff_weightedSeries (w : α → ℕ) {f : α → QSeries} (hf : Summable f) :
    sumCoeff (weightedSeries w f) = ∑' a, f a := (hasSum_weightedSeries_coeff w hf).tsum_eq

/-- Coefficientwise continuity of q-rescaling in the iterated power-series ring. -/
theorem continuous_rescale (r : QSeries) :
    Continuous (rescale r : PowerSeries QSeries → PowerSeries QSeries) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro k
  simp only [coeff_rescale]
  exact (continuous_const.mul (continuous_coeff QSeries k)).continuousAt

/-- An arbitrary family of formal q-series is bounded, so it preserves summability
when multiplied by a summable family. -/
theorem summable_series_mul {f : α → QSeries} (hf : Summable f) (g : α → QSeries) :
    Summable (fun a => g a * f a) := by
  have hg : g.BoundedRange := PowerSeries.bounded _
  apply (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr
  exact hg.mul_tendsto_zero ((NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f).mp hf)

theorem weightedSeries_rescale (r : QSeries) (w : α → ℕ) {f : α → QSeries} (hf : Summable f) :
    rescale r (weightedSeries w f) = weightedSeries w (fun a => r ^ w a * f a) := by
  have hh := (hasSum_weightedSeries w hf).map (rescale r) (continuous_rescale r)
  have hc := hasSum_weightedSeries w (summable_series_mul hf (fun a => r ^ w a))
  have ht : HasSum (fun a => monomial (w a) (r ^ w a * f a)) (rescale r (weightedSeries w f)) := by
    apply hh.congr_fun
    intro a
    apply PowerSeries.ext
    intro k
    simp only [Function.comp_apply, coeff_monomial, coeff_rescale]
    split_ifs with h
    · rw [h]
    · simp
  exact ht.unique hc

end KanadeRussell.Infra
