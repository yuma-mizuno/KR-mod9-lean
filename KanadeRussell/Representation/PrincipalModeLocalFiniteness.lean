import KanadeRussell.Representation.PrincipalModePairing
import KanadeRussell.Representation.PositiveModeGeneration
import KanadeRussell.Heisenberg.PolynomialGrading

/-! Every polynomial is killed by all sufficiently large positive principal
modes. Consequently the normal-ordered quadratic mode sum is locally finite. -/

set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
open KanadeRussell.Heisenberg
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

theorem heisenbergMode_mem_grade (w : K) (n d : ℤ) (p : Space K)
    (hp : p ∈ grade d) : heisenbergMode w n p ∈ grade (d-n) := by
  by_cases hn : IsMode n.natAbs
  · by_cases hpos : 0 < n
    · have he : (n.natAbs : ℤ) = n := by omega
      simp only [heisenbergMode, dif_pos hn, if_pos hpos, heisenbergPositive_apply]
      simpa only [he] using (grade (d-n.natAbs)).smul_mem
        (n.natAbs * contraction w n.natAbs / 12 : K)
        (diagonalDerivative_mem_grade ⟨n.natAbs, hn⟩ d p hp)
    · have he : (n.natAbs : ℤ) = -n := by omega
      simp only [heisenbergMode, dif_pos hn, if_neg hpos, heisenbergNegative_apply]
      change MvPolynomial.IsWeightedHomogeneous variableWeight (diagonalCoordinate (⟨n.natAbs, hn⟩ : Mode) * p) (d-n)
      have h := (diagonalCoordinate_mem_grade (K := K) ⟨n.natAbs, hn⟩).mul hp
      simpa only [grade, he, sub_eq_add_neg, add_comm] using h
  · rw [heisenbergMode_not_mode w n hn, LinearMap.zero_apply]
    exact (grade (d-n)).zero_mem

theorem principalMode_mem_grade (w : K) (n : ℤ) (r : Fin 3) (d : ℤ)
    (p : Space K) (hp : p ∈ grade d) : principalMode w n r p ∈ grade (d-n) := by
  fin_cases r
  · exact tensorRootMode_mem_grade w _ n d p hp
  · exact tensorRootMode_mem_grade w _ n d p hp
  · exact heisenbergMode_mem_grade w n d p hp

theorem principalMode_eq_zero_of_degree_lt (w : K) (n : ℤ) (r : Fin 3)
    (d : ℤ) (p : Space K) (hp : p ∈ grade d) (hn : d<n) :
    principalMode w n r p = 0 := by
  have h := principalMode_mem_grade w n r d p hp
  rw [grade_negative _ (by omega), Submodule.mem_bot] at h
  exact h

theorem principalMode_eventually_zero (w : K) (p : Space K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : Fin 3, principalMode w n r p = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    refine ⟨(Finsupp.weight variableWeight m).toNat+1, ?_⟩
    intro n hn r
    exact principalMode_eq_zero_of_degree_lt w n r (Finsupp.weight variableWeight m)
      _ (MvPolynomial.isWeightedHomogeneous_monomial variableWeight m c rfl) (by omega)
  | add p q hp hq =>
    obtain ⟨N, hN⟩ := hp
    obtain ⟨L, hL⟩ := hq
    refine ⟨max N L, ?_⟩
    intro n hn r
    simp only [map_add, hN n (le_trans (le_max_left _ _) hn) r,
      hL n (le_trans (le_max_right _ _) hn) r, add_zero]

theorem normalOrderedMode_eq_zero (w : K) (n : ℤ) (p : Space K)
    (hp : ∀ r, principalMode w n r p = 0) : normalOrderedMode w n p = 0 := by
  simp [normalOrderedMode, LinearMap.sum_apply, Module.End.mul_apply, hp]

theorem normalOrderedMode_eventually_zero (w : K) (p : Space K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → normalOrderedMode w (n+1) p = 0 := by
  obtain ⟨N, hN⟩ := principalMode_eventually_zero w p
  refine ⟨N, ?_⟩
  intro n hn
  apply normalOrderedMode_eq_zero
  intro r
  exact_mod_cast hN (n+1) (by omega) r

theorem positive_principalMode_kills (w : K) (hw : w^4-w^2+1=0)
    (p : Space K) (hp : ∀ i, chevalleyE w i p = 0) (n : ℤ) (hn : 0<n)
    (r : Fin 3) : principalMode w n r p = 0 := by
  fin_cases r
  · exact positive_simple_tensor_mode_kills w hw p hp 0 n hn
  · exact positive_simple_tensor_mode_kills w hw p hp 1 n hn
  · exact positive_heisenberg_mode_kills w hw p hp n hn

theorem normalOrderedMode_kills_primitive (w : K) (hw : w^4-w^2+1=0)
    (p : Space K) (hp : ∀ i, chevalleyE w i p = 0) (n : ℤ) (hn : 0<n) :
    normalOrderedMode w n p = 0 :=
  normalOrderedMode_eq_zero w n p (positive_principalMode_kills w hw p hp n hn)

end KanadeRussell.Tsuchioka.Fock
