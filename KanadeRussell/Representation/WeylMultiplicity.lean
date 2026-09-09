import KanadeRussell.Representation.WeylOperators
import KanadeRussell.Representation.WeylWeightReflection
import KanadeRussell.Representation.RootOccupationGrading

/-! Actual Weyl operators give linear equivalences of reflected full weight
spaces, hence equal finite weight multiplicities. -/
namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

theorem simpleWeyl_mem_extendedWeightSpace (i : Fin 3) (mu : Fin 4 → K) (v : V)
    (hv : v ∈ M.extendedWeightSpace mu) :
    M.simpleWeyl i v ∈ M.extendedWeightSpace (reflectFullWeight i mu) := by
  rw [M.mem_extendedWeightSpace]
  intro j
  exact M.simpleWeyl_weight i mu v hv j

theorem simpleWeyl_symm_mem_extendedWeightSpace (i : Fin 3) (mu : Fin 4 → K) (v : V)
    (hv : v ∈ M.extendedWeightSpace mu) :
    (M.simpleWeyl i).symm v ∈ M.extendedWeightSpace (reflectFullWeight i mu) := by
  rw [M.mem_extendedWeightSpace]
  intro j
  exact M.simpleWeyl_symm_weight i mu v hv j

noncomputable def simpleWeylWeightEquiv (i : Fin 3) (mu : Fin 4 → K) :
    M.extendedWeightSpace mu ≃ₗ[K] M.extendedWeightSpace (reflectFullWeight i mu) where
  toFun v := ⟨M.simpleWeyl i v, M.simpleWeyl_mem_extendedWeightSpace i mu v v.property⟩
  invFun v := ⟨(M.simpleWeyl i).symm v, by
    have h := M.simpleWeyl_symm_mem_extendedWeightSpace i (reflectFullWeight i mu) v v.property
    simpa only [reflectFullWeight_involutive i mu] using h⟩
  left_inv v := by apply Subtype.ext; exact (M.simpleWeyl i).symm_apply_apply v
  right_inv v := by apply Subtype.ext; exact (M.simpleWeyl i).apply_symm_apply v
  map_add' v w := by apply Subtype.ext; exact map_add (M.simpleWeyl i) (v : V) (w : V)
  map_smul' c v := by apply Subtype.ext; exact map_smul (M.simpleWeyl i) c (v : V)

theorem finrank_extendedWeightSpace_reflect (i : Fin 3) (mu : Fin 4 → K) :
    Module.finrank K (M.extendedWeightSpace mu) =
      Module.finrank K (M.extendedWeightSpace (reflectFullWeight i mu)) :=
  (M.simpleWeylWeightEquiv i mu).finrank_eq

noncomputable def simpleWeylRootEquiv (i : Fin 3) (beta : RootCoefficients) :
    M.rootGrade beta ≃ₗ[K] M.rootGrade (simpleReflection M.highestWeightLabels i beta) := by
  unfold rootGrade
  rw [occupationWeight_simpleReflection]
  exact M.simpleWeylWeightEquiv i _

theorem finrank_rootGrade_simpleReflection (i : Fin 3) (beta : RootCoefficients) :
    Module.finrank K (M.rootGrade beta) =
      Module.finrank K (M.rootGrade (simpleReflection M.highestWeightLabels i beta)) :=
  (M.simpleWeylRootEquiv i beta).finrank_eq

/-- Multiplicity is invariant under every finite word of simple reflections. -/
theorem finrank_rootGrade_reflectionWord (u : List (Fin 3)) (beta : RootCoefficients) :
    Module.finrank K (M.rootGrade (u.foldr (simpleReflection M.highestWeightLabels) beta)) =
      Module.finrank K (M.rootGrade beta) := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    simp only [List.foldr_cons]
    exact (M.finrank_rootGrade_simpleReflection i _).symm.trans ih

end KanadeRussell.Representation.PrincipalHighestWeightModule
