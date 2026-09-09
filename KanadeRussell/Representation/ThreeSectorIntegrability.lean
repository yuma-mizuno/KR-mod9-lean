import KanadeRussell.Representation.VacuumIntegrability
import KanadeRussell.Tsuchioka.AffineSkewIntegrability
import KanadeRussell.Tsuchioka.AffineAlternatingIntegrability

/-! All three concrete tensor cyclic actions are integrable. This does not
identify them with standard modules or assert a character formula. -/
namespace KanadeRussell.Tsuchioka.Fock
open KanadeRussell.Sectors
variable {K : Type*} [Field K] [CharZero K]

theorem skew_tensor_integrable (w : K) (hw : w^4-w^2+1=0) :
    ∀ i : Fin 3, ∀ p ∈ tensorCyclicSpan w (skewSeed : Space K),
      (∃ n : ℕ, ((chevalleyE w i)^n) p = 0) ∧
      (∃ n : ℕ, ((chevalleyF w i)^n) p = 0) := by
  intro i p hp
  exact ⟨chevalleyE_locally_nilpotent w i p,
    chevalleyF_locally_nilpotent_on_tensorCyclicSpan w hw skewSeed 1 skewSeed_grade i
      ⟨_, chevalleyF_skewSeed_integrability w hw i⟩ p hp⟩

theorem alternating_tensor_integrable (w : K) (hw : w^4-w^2+1=0) :
    ∀ i : Fin 3, ∀ p ∈ tensorCyclicSpan w (alternatingSeed : Space K),
      (∃ n : ℕ, ((chevalleyE w i)^n) p = 0) ∧
      (∃ n : ℕ, ((chevalleyF w i)^n) p = 0) := by
  intro i p hp
  exact ⟨chevalleyE_locally_nilpotent w i p,
    chevalleyF_locally_nilpotent_on_tensorCyclicSpan w hw alternatingSeed 3 alternatingSeed_grade i
      ⟨_, chevalleyF_alternatingSeed_integrability w hw i⟩ p hp⟩

theorem three_sector_tensor_integrable (w : K) (hw : w^4-w^2+1=0) :
    ∀ seed ∈ ({skewSeed, 1, alternatingSeed} : Set (Space K)),
      ∀ i : Fin 3, ∀ p ∈ tensorCyclicSpan w seed,
        (∃ n : ℕ, ((chevalleyE w i)^n) p = 0) ∧
        (∃ n : ℕ, ((chevalleyF w i)^n) p = 0) := by
  intro seed hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl
  · exact skew_tensor_integrable w hw
  · exact vacuum_tensor_integrable w hw
  · exact alternating_tensor_integrable w hw

end KanadeRussell.Tsuchioka.Fock
