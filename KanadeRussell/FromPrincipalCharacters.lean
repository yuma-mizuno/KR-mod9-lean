import KanadeRussell.FromStandardCharacters
import KanadeRussell.Pending.PrincipalCharacters
import KanadeRussell.Representation.ConcreteHeisenbergCharacter

/-! The three Kanade–Russell identities from the principally specialized
character formulas alone. All three Heisenberg factorizations are proved. -/
namespace KanadeRussell
open Tsuchioka Tsuchioka.Fock Representation
variable {K : Type*} [Field K] [CharZero K]

theorem standardCharacters_of_principalCharacterFormulas (w : K) (hw : w^4-w^2+1=0)
    (h : PrincipalCharacterFormulas w) : StandardCharacters w hw := by
  have hg (m : ℤ) (f : Space K) (hf : f ∈ (⊥ : Submodule K (Space K))) :
      MvPolynomial.weightedHomogeneousComponent variableWeight m f ∈
        (⊥ : Submodule K (Space K)) := by
    rw [Submodule.mem_bot] at hf ⊢
    rw [hf, map_zero]
  refine ⟨⟨⊥, bot_chevalleyStable w, hg, ?_, h.1, skew_heisenberg_character w hw⟩,
    ⟨⊥, bot_chevalleyStable w, hg, ?_, h.2.1, vacuum_heisenberg_character w hw⟩,
    ⟨⊥, bot_chevalleyStable w, hg, ?_, h.2.2, alternating_heisenberg_character w hw⟩⟩
  · simpa only [Submodule.mem_bot] using Sectors.skewSeed_ne_zero (K := K)
  · simpa only [Submodule.mem_bot] using (one_ne_zero : (1 : Space K) ≠ 0)
  · simpa only [Submodule.mem_bot] using alternatingSeed_ne_zero (K := K)

theorem lowerBounds_of_principalCharacterFormulas (w : K) (hw : w^4-w^2+1=0)
    (h : PrincipalCharacterFormulas w) : LowerBounds :=
  lowerBounds_of_standard_characters w hw (standardCharacters_of_principalCharacterFormulas w hw h)

theorem kanade_russell_of_principal_characters_over (w : K) (hw : w^4-w^2+1=0)
    (h : PrincipalCharacterFormulas w) : A = K₁ ∧ B = K₂ ∧ C = K₃ :=
  kanade_russell_of_lowerBounds (lowerBounds_of_principalCharacterFormulas w hw h)

theorem kanade_russell_of_principal_characters
    (h : PrincipalCharacterFormulas complexPhase) : A = K₁ ∧ B = K₂ ∧ C = K₃ :=
  kanade_russell_of_principal_characters_over complexPhase complexPhase_relation h

end KanadeRussell
