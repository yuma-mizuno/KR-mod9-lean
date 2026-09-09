import KanadeRussell.Representation.PrimitiveUniqueness

/-! The normal-ordered Casimir recurrence, conditional on explicit equations
for an actual endomorphism. No such endomorphism is asserted to exist here. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation.AffineWeightLattice
open Tsuchioka.Fock

private theorem fin_three_two_normalize : (2 : Fin 3) = ⟨2, by decide⟩ := by decide

theorem casimir_rho_single_add (lambda beta : RootCoefficients) (i : Fin 3) :
    casimir (fun j => lambda j + 1) (Pi.single i 1 + beta) =
      casimir (fun j => lambda j + 1) beta -
        symmetrizer i * weightLabels lambda beta i := by
  fin_cases i <;>
    norm_num [casimir_eq, Pi.add_apply, Pi.single_apply, weightLabels,
      Fin.sum_univ_three, symmetrizer, affineCartanMatrix, Matrix.cons_val_two] <;>
    norm_num only [Fin.ext_iff] <;> norm_num <;>
    (try simp only [fin_three_two_normalize]) <;> ring

end KanadeRussell.Representation.AffineWeightLattice

namespace KanadeRussell.Representation.PrincipalHighestWeightModule
open AffineWeightLattice
attribute [local instance] LieRing.ofAssociativeRing
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable (M : PrincipalHighestWeightModule K V)

/-- Each actual root grade is spanned by the lowering words of its occupation. -/
theorem rootGrade_eq_span_negativeWords (beta : RootCoefficients) :
    M.rootGrade beta = Submodule.span K
      (M.negativeWordValue '' {u : List (Fin 3) | wordOccupation u = beta}) := by
  let S : RootCoefficients → Submodule K V := fun gamma => Submodule.span K
    (M.negativeWordValue '' {u : List (Fin 3) | wordOccupation u = gamma})
  have htop : (⨆ gamma, S gamma) = ⊤ := by
    apply top_unique
    rw [← M.negativeWordSpan_eq_top]
    apply Submodule.span_le.mpr
    rintro v ⟨u, rfl⟩
    exact Submodule.mem_iSup_of_mem (wordOccupation u)
      (show M.negativeWordValue u ∈ S (wordOccupation u) from
        Submodule.subset_span ⟨u, rfl, rfl⟩)
  have hle : S ≤ M.rootGrade := by
    intro gamma
    apply Submodule.span_le.mpr
    rintro v ⟨u, hu, rfl⟩
    simpa only [Set.mem_setOf_eq] using hu ▸ M.negativeWordValue_mem_rootGrade u
  have heq : S = M.rootGrade :=
    (M.rootGrade_iSupIndep.le_iff_eq_of_iSup_eq_top htop).mp hle
  exact (congrFun heq beta).symm

theorem casimir_negativeWordValue (omega : Module.End K V)
    (hhighest : omega M.highestVector = 0)
    (hcomm : ∀ i, ⁅omega, M.action.F i⁆ =
      (2 * (symmetrizer i : K)) • (M.action.F i * M.action.H i))
    (u : List (Fin 3)) :
    omega (M.negativeWordValue u) =
      ((-2 * casimir (fun i => M.highestWeightLabels i + 1) (wordOccupation u) : ℤ) : K) •
        M.negativeWordValue u := by
  induction u with
  | nil => simp [hhighest, casimir, rootQuadratic]
  | cons i u ih =>
    have hH := M.rootGrade_H (wordOccupation u) (M.negativeWordValue u)
      (M.negativeWordValue_mem_rootGrade u) i
    have hc := congrArg (fun a : Module.End K V => a (M.negativeWordValue u)) (hcomm i)
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, ih, hH, map_smul] at hc
    rw [sub_eq_iff_eq_add] at hc
    rw [negativeWordValue_cons, hc, wordOccupation_cons, casimir_rho_single_add]
    push_cast
    module

theorem casimir_rootGrade (omega : Module.End K V)
    (hhighest : omega M.highestVector = 0)
    (hcomm : ∀ i, ⁅omega, M.action.F i⁆ =
      (2 * (symmetrizer i : K)) • (M.action.F i * M.action.H i))
    (beta : RootCoefficients) (v : V) (hgrade : v ∈ M.rootGrade beta) :
    omega v = ((-2 * casimir (fun i => M.highestWeightLabels i + 1) beta : ℤ) : K) • v := by
  rw [M.rootGrade_eq_span_negativeWords] at hgrade
  induction hgrade using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u, hu, rfl⟩ := hv
    have h := M.casimir_negativeWordValue omega hhighest hcomm u
    simpa only [Set.mem_setOf_eq] using hu ▸ h
  | zero => simp
  | add v w hv hw hiv hiw => simp only [map_add, hiv, hiw, smul_add]
  | smul c v hv hi => simpa only [map_smul, hi] using smul_comm c _ v

theorem primitive_mem_highestLine_of_casimir_operator (omega : Module.End K V)
    (hhighest : omega M.highestVector = 0)
    (hcomm : ∀ i, ⁅omega, M.action.F i⁆ =
      (2 * (symmetrizer i : K)) • (M.action.F i * M.action.H i))
    (beta : RootCoefficients) (v : V) (hv : v ≠ 0)
    (hgrade : v ∈ M.rootGrade beta) (hE : ∀ i, M.action.E i v = 0)
    (homega : omega v = 0) : v ∈ Submodule.span K {M.highestVector} := by
  have hscalar := M.casimir_rootGrade omega hhighest hcomm beta v hgrade
  rw [homega] at hscalar
  have hcast : ((-2 * casimir (fun i => M.highestWeightLabels i + 1) beta : ℤ) : K) = 0 :=
    (smul_eq_zero.mp hscalar.symm).resolve_right hv
  have hinteger : -2 * casimir (fun i => M.highestWeightLabels i + 1) beta = 0 :=
    Int.cast_injective (show ((-2 * casimir (fun i => M.highestWeightLabels i + 1) beta : ℤ) : K) = ((0 : ℤ) : K) from by simpa only [Int.cast_zero] using hcast)
  exact M.primitive_mem_highestLine_of_casimir beta v hv hgrade hE (by omega)

end KanadeRussell.Representation.PrincipalHighestWeightModule
