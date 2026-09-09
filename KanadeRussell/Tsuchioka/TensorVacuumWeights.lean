import KanadeRussell.Tsuchioka.TensorLieCoordinates

/-! Exact actions of the concrete tensor modes on the polynomial vacuum. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock
open RootData (Lattice)
variable {K : Type*} [Field K] [CharZero K]

theorem tensorRootMode_vacuum_zero (w : K) (beta : Lattice) :
    tensorRootMode w beta 0 (1 : Space K) = (1/4 : K) • (1 : Space K) := by
  have hs (j : Fin 3) : (tensorRootSummand w beta j (1 : Space K)).coeff 0 = 1 := by
    change ((tensorRootCreation w beta j : LaurentSeries (Space K)) *
      tensorRootAnnihilation w beta j 1).coeff 0 = 1
    rw [map_one, mul_one]
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, LaurentSeries.coeff_coe_powerSeries]
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact FormalSeries.constantCoeff_exponential (constantCoeff_tensorRootCreationLog w beta j)
  simp only [tensorRootMode, tensorRootField, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.smul_apply, LinearMap.sum_apply, neg_zero, HahnSeries.coeff_smul,
    HahnSeries.coeff_sum, hs, Fin.sum_univ_three, LinearMap.add_apply, HahnSeries.coeff_add]
  module

theorem heisenbergMode_vacuum_pos (w : K) (a : ℤ) (ha : 0 < a) :
    heisenbergMode w a (1 : Space K) = 0 := by
  by_cases hm : IsMode a.natAbs
  · simp only [heisenbergMode, dif_pos hm, if_pos ha]
    exact (mem_heisenbergVacuum w 1).mp (one_mem_heisenbergVacuum w) ⟨a.natAbs,hm⟩
  · simp [heisenbergMode, hm]

end KanadeRussell.Tsuchioka.Fock
