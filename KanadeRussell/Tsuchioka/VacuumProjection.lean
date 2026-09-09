import KanadeRussell.Tsuchioka.VacuumPolynomialModel

/-! The projection that kills the diagonal creation variables and fixes the
Heisenberg vacuum. It is the projection used in the cyclicity argument. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable def centerProjection : Space K →ₐ[K] Space K :=
  aeval fun s : Fin 3 × Mode => X s - (1 / 3 : K) • diagonalCoordinate s.2

@[simp] theorem centerProjection_X (s : Fin 3 × Mode) :
    centerProjection (X s : Space K) = X s - (1 / 3 : K) • diagonalCoordinate s.2 := by
  simp [centerProjection]

theorem centerProjection_diagonalCoordinate (n : Mode) :
    centerProjection (diagonalCoordinate (K := K) n) = 0 := by
  simp only [diagonalCoordinate, Fin.sum_univ_three, map_add, centerProjection_X]
  module

theorem centerProjection_relativeEmbedding (f : RelativeSpace K) :
    centerProjection (relativeEmbedding f) = relativeEmbedding f := by
  have h : (centerProjection (K := K)).comp relativeEmbedding = relativeEmbedding := by
    apply MvPolynomial.algHom_ext
    intro s
    rw [AlgHom.comp_apply, relativeEmbedding_X, map_sub, centerProjection_X, centerProjection_X]
    abel
  exact AlgHom.congr_fun h f

theorem centerProjection_eq_self_of_mem_heisenbergVacuum (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (f : Space K) (hf : f ∈ heisenbergVacuum w) :
    centerProjection f = f := by
  have he : relativeEmbedding (relativeExtraction f) = f := by
    rw [relativeEmbedding_relativeExtraction,
      (mem_heisenbergVacuum_iff_relativeProjection w hw f).mp hf]
  calc
    centerProjection f = centerProjection (relativeEmbedding (relativeExtraction f)) :=
      congrArg centerProjection he.symm
    _ = relativeEmbedding (relativeExtraction f) := centerProjection_relativeEmbedding _
    _ = f := he

theorem diagonalDerivative_centerProjection_X (n : Mode) (s : Fin 3 × Mode) :
    diagonalDerivative n (centerProjection (X s : Space K)) = 0 := by
  classical
  rw [centerProjection_X, map_sub, Derivation.map_smul,
    diagonalDerivative_X, diagonalDerivative_coordinate]
  have hc : (1 / 3 : K) • (3 : Space K) = 1 := by
    have h3 : (3 : Space K) = (3 : K) • (1 : Space K) := by
      simp [Algebra.smul_def, map_ofNat]
    rw [h3, smul_smul]
    norm_num
  split_ifs
  · rw [hc, sub_self]
  · simp

theorem diagonalDerivative_centerProjection (n : Mode) (f : Space K) :
    diagonalDerivative n (centerProjection f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [centerProjection]
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | mul_X f s hf =>
    simp only [map_mul, diagonalDerivative_mul, hf,
      diagonalDerivative_centerProjection_X, zero_mul, mul_zero, add_zero]

theorem centerProjection_mem_heisenbergVacuum (w : K) (f : Space K) :
    centerProjection f ∈ heisenbergVacuum w := by
  rw [mem_heisenbergVacuum]
  intro n
  simp only [heisenbergPositive_apply, diagonalDerivative_centerProjection, smul_zero]

theorem centerProjection_idempotent (f : Space K) :
    centerProjection (centerProjection f) = centerProjection f := by
  have he : relativeProjection (centerProjection f) = centerProjection f :=
    relativeProjection_eq_self_of_derivative_zero _ (fun n => diagonalDerivative_centerProjection n f)
  have h := centerProjection_relativeEmbedding (relativeExtraction (centerProjection f))
  rwa [relativeEmbedding_relativeExtraction, he] at h

theorem centerProjection_heisenbergNegative (n : Mode) (f : Space K) :
    centerProjection (heisenbergNegative n f) = 0 := by
  simp only [heisenbergNegative_apply, map_mul, centerProjection_diagonalCoordinate, zero_mul]

end KanadeRussell.Tsuchioka.Fock
