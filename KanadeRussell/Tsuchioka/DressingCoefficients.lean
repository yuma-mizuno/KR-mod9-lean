import KanadeRussell.Tsuchioka.TensorRootFields
import KanadeRussell.Tsuchioka.RatioContraction

/-! Dressing coefficients are finite polynomials in negative Heisenberg
operators. Multiplying a Laurent field by either dressing factor therefore
preserves any subspace stable under those operators. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries
open FormalSeries
open RootData (Lattice)

variable {K : Type*} [Field K] [CharZero K]

noncomputable def diagonalCreationAlgebra : Subalgebra K (Space K) :=
  Algebra.adjoin K (Set.range (diagonalCoordinate (K := K)))

theorem diagonalCoordinate_mem_creationAlgebra (n : Mode) :
    diagonalCoordinate (K := K) n ∈ diagonalCreationAlgebra :=
  Algebra.subset_adjoin ⟨n, rfl⟩

theorem diagonalCreationAlgebra_preserves (S : Submodule K (Space K))
    (hS : ∀ n f, f ∈ S → heisenbergNegative n f ∈ S)
    (a : Space K) (ha : a ∈ diagonalCreationAlgebra) :
    ∀ f ∈ S, a * f ∈ S := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨n, rfl⟩ := ha
    intro f hf
    exact hS n f hf
  | algebraMap c =>
    intro f hf
    simpa only [← Algebra.smul_def] using S.smul_mem c hf
  | add a b ha hb hia hib =>
    intro f hf
    rw [add_mul]
    exact S.add_mem (hia f hf) (hib f hf)
  | mul a b ha hb hia hib =>
    intro f hf
    rw [mul_assoc]
    exact hia _ (hib f hf)

theorem coeff_mul_mem_subalgebra (A : Subalgebra K (Space K))
    (f g : PowerSeries (Space K)) (hf : ∀ n, coeff n f ∈ A)
    (hg : ∀ n, coeff n g ∈ A) (n : ℕ) :
    coeff n (f * g) ∈ A := by
  rw [coeff_mul]
  exact A.sum_mem (fun ij hij => A.mul_mem (hf ij.1) (hg ij.2))

theorem coeff_pow_mem_subalgebra (A : Subalgebra K (Space K))
    (f : PowerSeries (Space K)) (hf : ∀ n, coeff n f ∈ A) (k n : ℕ) :
    coeff n (f ^ k) ∈ A := by
  classical
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, coeff_one]
    split_ifs
    · exact A.one_mem
    · exact A.zero_mem
  | succ k ih =>
    rw [pow_succ]
    exact coeff_mul_mem_subalgebra A (f ^ k) f ih hf n

theorem coeff_exponential_mem_subalgebra (A : Subalgebra K (Space K))
    (f : PowerSeries (Space K)) (hf0 : constantCoeff f = 0)
    (hf : ∀ n, coeff n f ∈ A) (n : ℕ) :
    coeff n (exponential f) ∈ A := by
  rw [coeff_exponential hf0]
  apply A.sum_mem
  intro k hk
  apply A.mul_mem
  · rw [IsScalarTower.algebraMap_apply ℚ K (Space K)]
    exact A.algebraMap_mem _
  · exact coeff_pow_mem_subalgebra A f hf k n

theorem coeff_diagonalRootCreationLog_mem (w : K) (β : Lattice) (n : ℕ) :
    coeff n (diagonalRootCreationLog w β) ∈ diagonalCreationAlgebra := by
  rw [diagonalRootCreationLog, coeff_mk]
  split_ifs with hn
  · exact diagonalCreationAlgebra.mul_mem (diagonalCreationAlgebra.algebraMap_mem _)
      (diagonalCoordinate_mem_creationAlgebra ⟨n, hn⟩)
  · exact diagonalCreationAlgebra.zero_mem

theorem coeff_diagonalRootCreation_mem (w : K) (β : Lattice) (n : ℕ) :
    coeff n (diagonalRootCreation w β) ∈ diagonalCreationAlgebra :=
  coeff_exponential_mem_subalgebra diagonalCreationAlgebra (diagonalRootCreationLog w β)
    (constantCoeff_diagonalRootCreationLog w β) (coeff_diagonalRootCreationLog_mem w β) n

theorem coeff_inverseDiagonalRootCreation_mem (w : K) (β : Lattice) (n : ℕ) :
    coeff n (inverseDiagonalRootCreation w β) ∈ diagonalCreationAlgebra := by
  apply coeff_exponential_mem_subalgebra diagonalCreationAlgebra
    (-diagonalRootCreationLog w β) (by simp)
  intro m
  rw [map_neg]
  exact diagonalCreationAlgebra.neg_mem (coeff_diagonalRootCreationLog_mem w β m)

theorem coePowerSeries_coeff_mem_subalgebra (A : Subalgebra K (Space K))
    (f : PowerSeries (Space K)) (hf : ∀ n, coeff n f ∈ A) (d : ℤ) :
    (f : LaurentSeries (Space K)).coeff d ∈ A := by
  cases d with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, LaurentSeries.coeff_coe_powerSeries] using hf n
  | negSucc n =>
    simp only [PowerSeries.coeff_coe, Int.negSucc_lt_zero, if_true]
    exact A.zero_mem

/-- The convolution has proved finite support, so every coefficient lies in
the ordinary algebraic subspace S. -/
theorem laurent_dressing_coeff_mem (S : Submodule K (Space K))
    (hS : ∀ n f, f ∈ S → heisenbergNegative n f ∈ S)
    (F G : LaurentSeries (Space K))
    (hF : ∀ d, F.coeff d ∈ diagonalCreationAlgebra)
    (hG : ∀ d, G.coeff d ∈ S) (d : ℤ) :
    (F * G).coeff d ∈ S := by
  classical
  rw [laurent_coeff_mul_finsum, finsum_eq_sum _ (laurent_convolution_finite F G d)]
  exact S.sum_mem (fun i hi => diagonalCreationAlgebra_preserves S hS
    (F.coeff i) (hF i) (G.coeff (d - i)) (hG (d - i)))

theorem diagonalRootCreation_mul_coeff_mem (w : K) (β : Lattice)
    (S : Submodule K (Space K)) (hS : ∀ n f, f ∈ S → heisenbergNegative n f ∈ S)
    (G : LaurentSeries (Space K)) (hG : ∀ d, G.coeff d ∈ S) (d : ℤ) :
    ((diagonalRootCreation w β : LaurentSeries (Space K)) * G).coeff d ∈ S :=
  laurent_dressing_coeff_mem S hS _ G
    (coePowerSeries_coeff_mem_subalgebra diagonalCreationAlgebra _
      (coeff_diagonalRootCreation_mem w β)) hG d

theorem inverseDiagonalRootCreation_mul_coeff_mem (w : K) (β : Lattice)
    (S : Submodule K (Space K)) (hS : ∀ n f, f ∈ S → heisenbergNegative n f ∈ S)
    (G : LaurentSeries (Space K)) (hG : ∀ d, G.coeff d ∈ S) (d : ℤ) :
    ((inverseDiagonalRootCreation w β : LaurentSeries (Space K)) * G).coeff d ∈ S :=
  laurent_dressing_coeff_mem S hS _ G
    (coePowerSeries_coeff_mem_subalgebra diagonalCreationAlgebra _
      (coeff_inverseDiagonalRootCreation_mem w β)) hG d

end KanadeRussell.Tsuchioka.Fock
