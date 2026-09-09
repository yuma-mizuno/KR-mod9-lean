import KanadeRussell.Tsuchioka.DiagonalHeisenberg
import KanadeRussell.Tsuchioka.PolynomialDerivativeKernel

/-! An explicit polynomial projection onto the diagonal Heisenberg vacuum.
Its image consists of polynomials in x_(1,n)-x_(0,n) and x_(2,n)-x_(0,n). -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Add the reference coordinate to each of the other two coordinates. -/
noncomputable def relativeExpansion : Space K →ₐ[K] Space K :=
  aeval fun s : Fin 3 × Mode =>
    if s.1 = 0 then X s else X s + X (0, s.2)

/-- The inverse triangular change of polynomial coordinates. -/
noncomputable def relativeCollapse : Space K →ₐ[K] Space K :=
  aeval fun s : Fin 3 × Mode =>
    if s.1 = 0 then X s else X s - X (0, s.2)

@[simp] theorem relativeExpansion_X (s : Fin 3 × Mode) :
    relativeExpansion (X s : Space K) =
      if s.1 = 0 then X s else X s + X (0, s.2) := by
  simp [relativeExpansion]

@[simp] theorem relativeCollapse_X (s : Fin 3 × Mode) :
    relativeCollapse (X s : Space K) =
      if s.1 = 0 then X s else X s - X (0, s.2) := by
  simp [relativeCollapse]

theorem relativeCollapse_comp_relativeExpansion :
    (relativeCollapse (K := K)).comp relativeExpansion = AlgHom.id K (Space K) := by
  apply MvPolynomial.algHom_ext
  intro s
  simp only [AlgHom.comp_apply, relativeExpansion_X, AlgHom.id_apply]
  by_cases h : s.1 = 0
  · simp [h]
  · simp [h]

theorem relativeExpansion_comp_relativeCollapse :
    (relativeExpansion (K := K)).comp relativeCollapse = AlgHom.id K (Space K) := by
  apply MvPolynomial.algHom_ext
  intro s
  simp only [AlgHom.comp_apply, relativeCollapse_X, AlgHom.id_apply]
  by_cases h : s.1 = 0
  · simp [h]
  · simp [h]

@[simp] theorem relativeCollapse_relativeExpansion (f : Space K) :
    relativeCollapse (relativeExpansion f) = f :=
  AlgHom.congr_fun relativeCollapse_comp_relativeExpansion f

@[simp] theorem relativeExpansion_relativeCollapse (f : Space K) :
    relativeExpansion (relativeCollapse f) = f :=
  AlgHom.congr_fun relativeExpansion_comp_relativeCollapse f

theorem pderiv_relativeExpansion_X (n : Mode) (s : Fin 3 × Mode) :
    pderiv (0, n) (relativeExpansion (X s : Space K)) =
      relativeExpansion (diagonalDerivative n (X s)) := by
  classical
  rcases s with ⟨j, m⟩
  rw [relativeExpansion_X, diagonalDerivative_X]
  by_cases h : j = 0
  · subst j
    simp [pderiv_X, Pi.single_apply, Prod.mk.injEq]
  · simp [h, pderiv_X, Pi.single_apply, Prod.mk.injEq]

/-- Under the triangular coordinate change, the diagonal derivative is a
single ordinary partial derivative. -/
theorem pderiv_relativeExpansion (n : Mode) (f : Space K) :
    pderiv (0, n) (relativeExpansion f) = relativeExpansion (diagonalDerivative n f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [relativeExpansion]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f s hf =>
    simp only [map_mul, pderiv_mul, diagonalDerivative_mul, map_add, hf,
      pderiv_relativeExpansion_X]

/-- Delete the reference-coordinate variables after changing coordinates. -/
noncomputable def deleteReference : Space K →ₐ[K] Space K :=
  aeval fun s : Fin 3 × Mode => if s.1 ≠ 0 then X s else 0

@[simp] theorem deleteReference_X (s : Fin 3 × Mode) :
    deleteReference (X s : Space K) = if s.1 ≠ 0 then X s else 0 := by
  simp [deleteReference]

theorem deleteReference_relativeExpansion (f : Space K)
    (hf : ∀ n : Mode, diagonalDerivative n f = 0) :
    deleteReference (relativeExpansion f) = relativeExpansion f := by
  classical
  apply PolynomialDerivatives.aeval_delete_eq_self {s : Fin 3 × Mode | s.1 ≠ 0}
  intro s hs
  have hz : s.1 = 0 := by simpa using hs
  have he : s = (0, s.2) := Prod.ext hz rfl
  rw [he, pderiv_relativeExpansion, hf, map_zero]

/-- Replace every tensor variable by its difference from the reference factor. -/
noncomputable def relativeProjection : Space K →ₐ[K] Space K :=
  aeval fun s : Fin 3 × Mode => X s - X (0, s.2)

@[simp] theorem relativeProjection_X (s : Fin 3 × Mode) :
    relativeProjection (X s : Space K) = X s - X (0, s.2) := by
  simp [relativeProjection]

theorem relativeProjection_factorization :
    relativeProjection (K := K) =
      relativeCollapse.comp (deleteReference.comp relativeExpansion) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨j, n⟩
  simp only [AlgHom.comp_apply, relativeProjection_X, relativeExpansion_X]
  by_cases h : j = 0
  · subst j
    simp
  · simp [h]

theorem relativeProjection_eq_self_of_derivative_zero (f : Space K)
    (hf : ∀ n : Mode, diagonalDerivative n f = 0) :
    relativeProjection f = f := by
  rw [relativeProjection_factorization]
  change relativeCollapse (deleteReference (relativeExpansion f)) = f
  rw [deleteReference_relativeExpansion f hf, relativeCollapse_relativeExpansion]

theorem diagonalDerivative_relativeProjection (n : Mode) (f : Space K) :
    diagonalDerivative n (relativeProjection f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [relativeProjection]
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | mul_X f s hf =>
    simp only [map_mul, diagonalDerivative_mul, relativeProjection_X,
      map_sub, diagonalDerivative_X, sub_self, hf, zero_mul, mul_zero, add_zero]

theorem relativeProjection_idempotent (f : Space K) :
    relativeProjection (relativeProjection f) = relativeProjection f :=
  relativeProjection_eq_self_of_derivative_zero _
    (fun n => diagonalDerivative_relativeProjection n f)

theorem relativeProjection_mem_heisenbergVacuum (w : K) (f : Space K) :
    relativeProjection f ∈ heisenbergVacuum w := by
  rw [mem_heisenbergVacuum]
  intro n
  simp only [heisenbergPositive_apply, diagonalDerivative_relativeProjection, smul_zero]

/-- This is a full kernel description, rather than a finite-degree check. -/
theorem mem_heisenbergVacuum_iff_relativeProjection (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (f : Space K) :
    f ∈ heisenbergVacuum w ↔ relativeProjection f = f := by
  constructor
  · intro hf
    exact relativeProjection_eq_self_of_derivative_zero f
      ((mem_heisenbergVacuum_iff_derivative w hw f).mp hf)
  · intro hf
    rw [← hf]
    exact relativeProjection_mem_heisenbergVacuum w f

theorem range_relativeProjection_eq_heisenbergVacuum (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    LinearMap.range (relativeProjection (K := K)).toLinearMap = heisenbergVacuum w := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact relativeProjection_mem_heisenbergVacuum w f
  · intro f hf
    exact ⟨f, (mem_heisenbergVacuum_iff_relativeProjection w hw f).mp hf⟩

end KanadeRussell.Tsuchioka.Fock
