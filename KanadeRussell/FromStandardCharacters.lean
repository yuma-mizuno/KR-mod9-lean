import KanadeRussell.Pending.StandardCharacters
import KanadeRussell.FromLowerBounds
import KanadeRussell.Tsuchioka.ComplexPhase

/-! Kanade–Russell from explicit standard-module character applications.
The three spanning bounds, vacuum lifting, product specializations, both norm
identities, and coefficient rigidity are proved. Only the named character
application input remains in these statements. -/
namespace KanadeRussell
open Tsuchioka Tsuchioka.Fock Representation
variable {K : Type*} [Field K] [CharZero K]

theorem lowerBounds_of_standard_characters (w : K) (hw : w^4-w^2+1=0)
    (h : StandardCharacters w hw) : LowerBounds := by
  rcases h with ⟨h₁, h₂, h₃⟩
  rcases h₁ with ⟨S₁, hS₁, _, _, hc₁, hf₁⟩
  rcases h₂ with ⟨S₂, hS₂, _, _, hc₂, hf₂⟩
  rcases h₃ with ⟨S₃, hS₃, _, _, hc₃, hf₃⟩
  have hv₁ := Product.vacuum_eq_K₁_of_standard_character_formulas _ _ hc₁ hf₁
  have hv₂ := Product.vacuum_eq_K₂_of_standard_character_formulas _ _ hc₂ hf₂
  have hv₃ := Product.vacuum_eq_K₃_of_standard_character_formulas _ _ hc₃ hf₃
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [← hv₁]
    exact coeff_skewQuotientVacuumCharacter_le_A w hw S₁ hS₁ n
  · intro n
    rw [← hv₂]
    exact coeff_vacuumQuotientVacuumCharacter_le_B w hw S₂ hS₂ n
  · intro n
    rw [← hv₃]
    exact coeff_alternatingQuotientVacuumCharacter_le_C w hw S₃ hS₃ n

theorem kanade_russell_of_standard_characters_over (w : K) (hw : w^4-w^2+1=0)
    (h : StandardCharacters w hw) : A = K₁ ∧ B = K₂ ∧ C = K₃ :=
  kanade_russell_of_lowerBounds (lowerBounds_of_standard_characters w hw h)

/-- The final specialization has no coefficient-field or Coxeter-root existence input. -/
theorem kanade_russell_of_standard_characters
    (h : StandardCharacters complexPhase complexPhase_relation) :
    A = K₁ ∧ B = K₂ ∧ C = K₃ :=
  kanade_russell_of_standard_characters_over complexPhase complexPhase_relation h

end KanadeRussell
