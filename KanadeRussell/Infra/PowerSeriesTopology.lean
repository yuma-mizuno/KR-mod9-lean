import Mathlib
import RogersRamanujan

/-! The coefficient topology on formal power series over a strongly
nonarchimedean ring is again strongly nonarchimedean. This lets the theta
addition theorem be evaluated at an auxiliary formal parameter. -/
open PowerSeries PowerSeries.WithPiTopology Filter Topology
namespace KanadeRussell.Infra
variable {R : Type*} [CommRing R] [TopologicalSpace R] [StrongNonarchimedeanRing R]

private def coeffSubrng (N : ℕ) (V : OpenSubrng R) : OpenSubrng (PowerSeries R) where
  carrier := {f | ∀ k : Fin (N+1), coeff k.val f ∈ V}
  zero_mem' k := by simp
  add_mem' hf hg k := by simpa using add_mem (hf k) (hg k)
  neg_mem' hf k := by simpa using neg_mem (hf k)
  mul_mem' hf hg k := by
    rw [coeff_mul]
    apply sum_mem
    intro p hp
    have hh := Finset.mem_antidiagonal.mp hp
    exact mul_mem (hf ⟨p.1, by omega⟩) (hg ⟨p.2, by omega⟩)
  isOpen' := by
    simpa only [Set.preimage, Set.setOf_forall, SetLike.mem_coe] using
      (isOpen_iInter_of_finite fun k : Fin (N+1) =>
        V.isOpen.preimage (continuous_coeff R k.val))

private theorem exists_coeffSubrng (U : Set (PowerSeries R)) (hU : U ∈ 𝓝 0) :
    ∃ (N : ℕ) (V : OpenSubrng R), (coeffSubrng N V : Set (PowerSeries R)) ⊆ U := by
  change U ∈ 𝓝 (0 : (Unit →₀ ℕ) → R) at hU
  obtain ⟨⟨I, s⟩, ⟨hI, _⟩, hsU⟩ :=
    (nhds_pi (A := fun _ : Unit →₀ ℕ => R) ▸ Filter.hasBasis_pi fun _ =>
      hasBasis_nhds_zero_openSubrng (R := R)).mem_iff.mp hU
  have hV : (⋂ i ∈ I, (s i : Set R)) ∈ 𝓝 (0 : R) :=
    Filter.biInter_mem hI |>.mpr fun i _ => (s i).mem_nhds_zero
  obtain ⟨V, _, hVs⟩ := hasBasis_nhds_zero_openSubrng.mem_iff.mp hV
  classical
  refine ⟨hI.toFinset.sup (fun d => d ()), V, ?_⟩
  intro f hf
  apply hsU
  intro i hi
  have hb : i () ≤ hI.toFinset.sup (fun d => d ()) :=
    Finset.le_sup (f := fun d => d ()) (hI.mem_toFinset.mpr hi)
  have hcoeff := hf ⟨i (), by omega⟩
  have hin := Set.mem_iInter₂.mp (hVs hcoeff) i hi
  convert hin using 1
  change f i = f (Finsupp.single () (i ()))
  congr 1
  ext
  simp

/-- Strong nonarchimedean structure for the coefficient topology, without a
requirement that the coefficient ring be discrete. -/
instance powerSeriesStrongNonarchimedean : StrongNonarchimedeanRing (PowerSeries R) where
  is_nonarchimedean U hU := by
    obtain ⟨N, V, h⟩ := exists_coeffSubrng U hU
    exact ⟨(coeffSubrng N V).toOpenAddSubgroup, h⟩
  exists_mul_subset_self U hU := by
    obtain ⟨N, V, h⟩ := exists_coeffSubrng U hU
    exact ⟨coeffSubrng N V, zero_mem _, (coeffSubrng N V).isOpen, h,
      Set.mul_subset_iff.mpr fun _ ha _ hb => mul_mem ha hb⟩

end KanadeRussell.Infra
