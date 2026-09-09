import KanadeRussell.Representation.RootMultiplicityFunction
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Finite principal specialization of the actual root multiplicities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Representation
open AffineWeightLattice

/-- All nonnegative root occupations of a fixed principal degree. -/
abbrev PrincipalDegreeOccupation (n : ℕ) :=
  { b : Fin 3 → Fin (n+1) // ∑ i, (b i).val = n }

def PrincipalDegreeOccupation.root {n : ℕ} (b : PrincipalDegreeOccupation n) :
    RootCoefficients := fun i => ((b.val i).val : ℤ)

theorem PrincipalDegreeOccupation.root_injective (n : ℕ) :
    Function.Injective (root (n := n)) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply Fin.ext
  have h : ((a.val i).val : ℤ) = ((b.val i).val : ℤ) := congrFun hab i
  exact_mod_cast h

theorem PrincipalDegreeOccupation.root_degree {n : ℕ} (b : PrincipalDegreeOccupation n) :
    totalDegree b.root = n := by
  change (∑ i, ((b.val i).val : ℤ)) = (n : ℤ)
  exact_mod_cast b.property

theorem PrincipalDegreeOccupation.exists_root (n : ℕ) (beta : RootCoefficients)
    (hbeta : ∀ i, 0 ≤ beta i) (hdegree : totalDegree beta = n) :
    ∃ b : PrincipalDegreeOccupation n, b.root = beta := by
  have hbound (i : Fin 3) : beta i ≤ n := by
    rw [← hdegree]
    exact Finset.single_le_sum (fun j _ => hbeta j) (Finset.mem_univ i)
  let b : Fin 3 → Fin (n+1) := fun i => ⟨(beta i).toNat, by have := hbound i; omega⟩
  have hb (i : Fin 3) : ((b i).val : ℤ) = beta i := Int.toNat_of_nonneg (hbeta i)
  have hs : ∑ i, (b i).val = n := by
    have h : (∑ i, ((b i).val : ℤ)) = n := by
      simpa only [hb, totalDegree] using hdegree
    exact_mod_cast h
  exact ⟨⟨b, hs⟩, funext hb⟩

namespace PrincipalHighestWeightModule
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

theorem grade_eq_iSup_degreeOccupation (n : ℕ) :
    M.grade (n : ℤ) = ⨆ b : PrincipalDegreeOccupation n, M.rootGrade b.root := by
  rw [M.grade_eq_iSup_rootGrade]
  apply le_antisymm
  · apply iSup_le
    intro beta
    apply iSup_le
    intro hbeta
    by_cases hzero : M.rootGrade beta = ⊥
    · simp only [hzero, bot_le]
    · obtain ⟨b, rfl⟩ := PrincipalDegreeOccupation.exists_root n beta
        (M.rootGrade_support beta hzero) hbeta
      exact le_iSup (fun b : PrincipalDegreeOccupation n => M.rootGrade b.root) b
  · apply iSup_le
    intro b
    exact le_iSup_of_le b.root (le_iSup_of_le b.root_degree le_rfl)

/-- The principal grade has the sum of the dimensions of its finitely many
nonnegative root occupations. -/
theorem finrank_grade_eq_sum_rootGrade (n : ℕ) :
    Module.finrank K (M.grade (n : ℤ)) =
      ∑ b : PrincipalDegreeOccupation n, Module.finrank K (M.rootGrade b.root) := by
  classical
  let A : PrincipalDegreeOccupation n → Submodule K V := fun b => M.rootGrade b.root
  have hi : iSupIndep A := M.rootGrade_iSupIndep.comp
    (PrincipalDegreeOccupation.root_injective n)
  let f := DirectSum.coeLinearMap A
  have hf : Function.Injective f := hi.dfinsupp_lsum_injective
  have hr : LinearMap.range f = M.grade (n : ℤ) :=
    DirectSum.range_coeLinearMap.trans (M.grade_eq_iSup_degreeOccupation n).symm
  letI (b : PrincipalDegreeOccupation n) : Module.Finite K (A b) := M.rootGrade_finite b.root
  have h := (LinearEquiv.ofInjective f hf).finrank_eq
  rw [hr] at h
  rw [← h, Module.finrank_directSum]

theorem coeff_character_eq_sum_rootGrade (n : ℕ) :
    PowerSeries.coeff n M.character =
      ∑ b : PrincipalDegreeOccupation n, (Module.finrank K (M.rootGrade b.root) : ℤ) := by
  rw [M.coeff_character, M.finrank_grade_eq_sum_rootGrade, Nat.cast_sum]

theorem coeff_character_cast_eq_sum_rootMultiplicity (n : ℕ) :
    ((PowerSeries.coeff n M.character : ℤ) : K) =
      ∑ b : PrincipalDegreeOccupation n, M.rootMultiplicity b.root := by
  rw [M.coeff_character_eq_sum_rootGrade, Int.cast_sum]
  simp only [rootMultiplicity, Int.cast_natCast]

/-- Equality of actual root multiplicities determines the original principal character. -/
theorem character_eq_of_rootMultiplicity_eq
    {W : Type*} [AddCommGroup W] [Module K W]
    (N : PrincipalHighestWeightModule K W) (h : M.rootMultiplicity = N.rootMultiplicity) :
    M.character = N.character := by
  ext n
  apply Int.cast_injective (α := K)
  rw [M.coeff_character_cast_eq_sum_rootMultiplicity,
    N.coeff_character_cast_eq_sum_rootMultiplicity, h]
end PrincipalHighestWeightModule
end KanadeRussell.Representation
