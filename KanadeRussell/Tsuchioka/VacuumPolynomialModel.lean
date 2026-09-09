import KanadeRussell.Tsuchioka.VacuumCoordinates

/-! Two independent families of relative oscillator coordinates give a
polynomial model for the full diagonal Heisenberg vacuum in triple Fock space.
This is not an identification of any affine standard-module summand. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

abbrev RelativeSpace (K : Type*) [CommSemiring K] :=
  MvPolynomial (Fin 2 × Mode) K

noncomputable def relativeEmbedding : RelativeSpace K →ₐ[K] Space K :=
  aeval fun s : Fin 2 × Mode => X (s.1.succ, s.2) - X (0, s.2)

noncomputable def relativeExtraction : Space K →ₐ[K] RelativeSpace K :=
  aeval fun s : Fin 3 × Mode => if h : s.1 = 0 then 0 else X (s.1.pred h, s.2)

@[simp] theorem relativeEmbedding_X (s : Fin 2 × Mode) :
    relativeEmbedding (X s : RelativeSpace K) = X (s.1.succ, s.2) - X (0, s.2) := by
  simp [relativeEmbedding]

@[simp] theorem relativeExtraction_X (s : Fin 3 × Mode) :
    relativeExtraction (X s : Space K) =
      if h : s.1 = 0 then 0 else X (s.1.pred h, s.2) := by
  simp [relativeExtraction]

theorem relativeExtraction_comp_relativeEmbedding :
    (relativeExtraction (K := K)).comp relativeEmbedding =
      AlgHom.id K (RelativeSpace K) := by
  apply MvPolynomial.algHom_ext
  intro s
  simp [AlgHom.comp_apply]

@[simp] theorem relativeExtraction_relativeEmbedding (f : RelativeSpace K) :
    relativeExtraction (relativeEmbedding f) = f :=
  AlgHom.congr_fun relativeExtraction_comp_relativeEmbedding f

theorem relativeEmbedding_injective :
    Function.Injective (relativeEmbedding (K := K)) :=
  Function.LeftInverse.injective relativeExtraction_relativeEmbedding

theorem relativeEmbedding_comp_relativeExtraction :
    (relativeEmbedding (K := K)).comp relativeExtraction = relativeProjection := by
  apply MvPolynomial.algHom_ext
  rintro ⟨j, n⟩
  simp only [AlgHom.comp_apply, relativeExtraction_X, relativeProjection_X]
  by_cases h : j = 0
  · subst j
    simp
  · simp [h]

theorem relativeEmbedding_relativeExtraction (f : Space K) :
    relativeEmbedding (relativeExtraction f) = relativeProjection f :=
  AlgHom.congr_fun relativeEmbedding_comp_relativeExtraction f

@[simp] theorem relativeProjection_relativeEmbedding (f : RelativeSpace K) :
    relativeProjection (relativeEmbedding f) = relativeEmbedding f := by
  rw [← relativeEmbedding_relativeExtraction, relativeExtraction_relativeEmbedding]

theorem relativeEmbedding_mem_heisenbergVacuum (w : K) (f : RelativeSpace K) :
    relativeEmbedding f ∈ heisenbergVacuum w := by
  have h := relativeProjection_mem_heisenbergVacuum w (relativeEmbedding f)
  rwa [relativeProjection_relativeEmbedding] at h

/-- The two relative coordinate families generate the entire common kernel,
and the explicit extraction map proves they are algebraically independent. -/
theorem range_relativeEmbedding_eq_heisenbergVacuum (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    LinearMap.range (relativeEmbedding (K := K)).toLinearMap = heisenbergVacuum w := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact relativeEmbedding_mem_heisenbergVacuum w f
  · intro f hf
    refine ⟨relativeExtraction f, ?_⟩
    change relativeEmbedding (relativeExtraction f) = f
    rw [relativeEmbedding_relativeExtraction,
      (mem_heisenbergVacuum_iff_relativeProjection w hw f).mp hf]

noncomputable def relativeVacuumEmbedding (w : K) :
    RelativeSpace K →ₗ[K] heisenbergVacuum w where
  toFun f := ⟨relativeEmbedding f, relativeEmbedding_mem_heisenbergVacuum w f⟩
  map_add' f g := Subtype.ext (map_add relativeEmbedding f g)
  map_smul' c f := Subtype.ext (map_smul relativeEmbedding c f)

theorem relativeVacuumEmbedding_bijective (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    Function.Bijective (relativeVacuumEmbedding w) := by
  constructor
  · intro f g h
    apply relativeEmbedding_injective
    exact congrArg Subtype.val h
  · intro f
    refine ⟨relativeExtraction f.val, Subtype.ext ?_⟩
    change relativeEmbedding (relativeExtraction f.val) = f.val
    rw [relativeEmbedding_relativeExtraction,
      (mem_heisenbergVacuum_iff_relativeProjection w hw f.val).mp f.property]

noncomputable def relativeVacuumEquiv (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    RelativeSpace K ≃ₗ[K] heisenbergVacuum w :=
  LinearEquiv.ofBijective (relativeVacuumEmbedding w) (relativeVacuumEmbedding_bijective w hw)

@[simp] theorem relativeVacuumEquiv_apply (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (f : RelativeSpace K) :
    (relativeVacuumEquiv w hw f).val = relativeEmbedding f := rfl

end KanadeRussell.Tsuchioka.Fock
