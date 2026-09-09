import KanadeRussell.Representation.NegativeWords
import KanadeRussell.Representation.PrincipalDerivation
import KanadeRussell.Representation.WeightIndependence

/-! The full Cartan action includes the principal derivation. Its weights are
supported on the actual weights of lowering words, hence below the highest weight. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open Tsuchioka.Fock
open scoped Classical
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

noncomputable def extendedCartan : Fin 4 → Module.End K V :=
  Fin.cases M.principalDerivation M.action.H

def negativeWordWeight (u : List (Fin 3)) : Fin 4 → K :=
  Fin.cases (-(u.length : K))
    (fun i => (M.highestWeight i : K) - (u.map (fun j => (affineCartanMatrix i j : K))).sum)

noncomputable def extendedWeightSpace (mu : Fin 4 → K) : Submodule K V :=
  ⨅ i, (M.extendedCartan i).eigenspace (mu i)

theorem mem_extendedWeightSpace (mu : Fin 4 → K) (v : V) :
    v ∈ M.extendedWeightSpace mu ↔ ∀ i, M.extendedCartan i v = mu i • v := by
  simp [extendedWeightSpace, Module.End.mem_eigenspace_iff]

theorem negativeWordValue_mem_extendedWeightSpace (u : List (Fin 3)) :
    M.negativeWordValue u ∈ M.extendedWeightSpace (M.negativeWordWeight u) := by
  rw [M.mem_extendedWeightSpace]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [extendedCartan, negativeWordWeight] using
      M.principalDerivation_of_mem (u.length : ℤ) _ (M.negativeWordValue_mem_grade u)
  · exact M.H_negativeWordValue j u

theorem extendedWeightSpace_iSupIndep : iSupIndep M.extendedWeightSpace :=
  iSupIndep_joint_eigenspaces M.extendedCartan

theorem extendedWeightSpace_supported_iSup_eq_top :
    (⨆ mu ∈ Set.range M.negativeWordWeight, M.extendedWeightSpace mu) = ⊤ := by
  apply top_unique
  rw [← M.negativeWordSpan_eq_top]
  apply Submodule.span_le.mpr
  rintro v ⟨u, rfl⟩
  exact Submodule.mem_iSup_of_mem (M.negativeWordWeight u)
    (Submodule.mem_iSup_of_mem (show M.negativeWordWeight u ∈ Set.range M.negativeWordWeight
      from ⟨u, rfl⟩) (M.negativeWordValue_mem_extendedWeightSpace u))

theorem extendedWeightSpace_iSup_eq_top : (⨆ mu, M.extendedWeightSpace mu) = ⊤ := by
  apply top_unique
  rw [← M.extendedWeightSpace_supported_iSup_eq_top]
  exact iSup_le fun mu => iSup_le fun _ => le_iSup M.extendedWeightSpace mu

theorem extendedWeightSpace_isInternal : DirectSum.IsInternal M.extendedWeightSpace := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    M.extendedWeightSpace_iSupIndep M.extendedWeightSpace_iSup_eq_top

/-- Every occurring full weight is the weight of a lowering word. -/
theorem extendedWeightSpace_support (mu : Fin 4 → K)
    (hmu : M.extendedWeightSpace mu ≠ ⊥) :
    ∃ u : List (Fin 3), M.negativeWordWeight u = mu :=
  M.extendedWeightSpace_iSupIndep.mem_of_biSup_eq_top
    M.extendedWeightSpace_supported_iSup_eq_top hmu

/-- A nonzero homogeneous Cartan eigenvector has highest weight minus a positive
sum of simple roots, with height exactly its principal degree. -/
theorem homogeneous_weight_support [CharZero K] (n : ℤ) (mu : Fin 3 → K) (v : V)
    (hv : v ≠ 0) (hgrade : v ∈ M.grade n)
    (hweight : ∀ i, M.action.H i v = mu i • v) :
    ∃ u : List (Fin 3), (u.length : ℤ) = n ∧
      ∀ i, mu i = (M.highestWeight i : K) -
        (u.map (fun j => (affineCartanMatrix i j : K))).sum := by
  let nu : Fin 4 → K := Fin.cases (-(n : K)) mu
  have hmem : v ∈ M.extendedWeightSpace nu := by
    rw [M.mem_extendedWeightSpace]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact M.principalDerivation_of_mem n v hgrade
    · exact hweight j
  have hne : M.extendedWeightSpace nu ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hmem
    exact hv hmem
  obtain ⟨u, hu⟩ := M.extendedWeightSpace_support nu hne
  refine ⟨u, ?_, ?_⟩
  · have hd := congrFun hu 0
    simp only [negativeWordWeight, nu, Fin.cases_zero, neg_inj] at hd
    exact Int.cast_injective (by simpa using hd : ((u.length : ℤ) : K) = (n : K))
  · intro i
    exact (congrFun hu i.succ).symm

end KanadeRussell.Representation.PrincipalHighestWeightModule
