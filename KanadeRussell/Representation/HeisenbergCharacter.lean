import KanadeRussell.Heisenberg.FiniteVacuumCharacter
import KanadeRussell.Representation.HeisenbergEulerTruncation

/-! Principal Heisenberg character factorization from the actual oscillator
relations, nonnegative grading, and finite grade dimensions. -/
namespace KanadeRussell.Representation
open PowerSeries Heisenberg Tsuchioka.Fock
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem principalHeisenbergEuler_mul_character
    (G : GradedSystem K V Mode) (hweight : ∀ m, G.weight m = m.val)
    (hfin : ∀ d : ℤ, Module.Finite K (G.grade d)) :
    Product.principalHeisenbergEuler * G.character = G.vacuumCharacter := by
  ext n
  rw [coeff_principalHeisenbergEuler_mul_eq_finite G.character n n le_rfl,
    finiteHeisenbergEuler_eq_prod_boundedModes]
  have hprod := G.prod_one_sub_X_pow_mul_character hfin (boundedModes n)
  simp_rw [hweight] at hprod
  rw [hprod]
  apply G.coeff_finiteVacuumCharacter_eq_vacuumCharacter
  intro m hm
  rw [mem_boundedModes]
  simpa only [hweight] using hm

end KanadeRussell.Representation
