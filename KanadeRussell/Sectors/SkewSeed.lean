import KanadeRussell.Sectors.SkewSector
import KanadeRussell.Tsuchioka.DiagonalHeisenberg

/-! A concrete nonzero degree-one seed and its minimum-one initial relation.
This does not identify its cyclic representation with an affine standard module. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KanadeRussell.Sectors
open Tsuchioka Tsuchioka.Fock PowerSeries
variable {K : Type*} [Field K] [CharZero K]

noncomputable def skewSeed : Space K := degreeOneVariable 0 - degreeOneVariable 1

omit [CharZero K] in
theorem skewSeed_mem : skewSeed (K := K) ∈ skewSpace := by
  rw [mem_skewSpace]
  simp [skewSeed, degreeOneVariable, swap01]

theorem skewSeed_ne_zero : skewSeed (K := K) ≠ 0 := by
  intro h
  have he := congrArg
    (MvPolynomial.eval fun s : Fin 3 × Mode => if s.1.val = 0 then (1 : K) else 0) h
  norm_num [skewSeed, degreeOneVariable] at he

omit [CharZero K] in
theorem skewSeed_grade : skewSeed (K := K) ∈ grade 1 := by
  exact (grade (K := K) 1).sub_mem
    (MvPolynomial.isWeightedHomogeneous_X K variableWeight (0, firstMode))
    (MvPolynomial.isWeightedHomogeneous_X K variableWeight (1, firstMode))

noncomputable def skewVacuum : skewSpace (K := K) := ⟨skewSeed, skewSeed_mem⟩

omit [CharZero K] in
theorem skewVacuum_grade : skewVacuum (K := K) ∈ skewGrade 0 := skewSeed_grade

noncomputable def skewHighestWeightAction (w : K) :
    HighestWeightAction K (skewSpace (K := K)) where
  grade := skewGrade
  negative := skewGrade_negative
  mode := skewMode w
  mode_mem := skewMode_mem_grade w
  vacuum := skewVacuum
  vacuum_mem := skewVacuum_grade

theorem mode_skewSeed_pos (w : K) (i : ℤ) (hi : 0 < i) :
    mode w i (skewSeed (K := K)) = 0 := by
  have h := skewMode_mem_grade w i 0 skewVacuum skewVacuum_grade
  rw [skewGrade_negative (0-i) (by omega), Submodule.mem_bot] at h
  exact congrArg Subtype.val h

theorem skewSeed_heisenbergVacuum (w : K) : skewSeed (K := K) ∈ heisenbergVacuum w := by
  rw [mem_heisenbergVacuum]
  intro n
  simp [heisenbergPositive_apply, skewSeed, degreeOneVariable, diagonalDerivative_X]

theorem mode_zero_degreeOneVariable (w : K) (a : Fin 3) :
    mode w 0 (degreeOneVariable a) = (1/12:K) • ∑ j : Fin 3,
      (degreeOneVariable a + coeff 1 (creation (K := K) j) *
        MvPolynomial.C (tensorExponent a j * contraction w 1 / 3)) := by
  change ((1/12:K) • ∑ j : Fin 3, summand w j (degreeOneVariable a)).coeff 0 = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [summand, LinearMap.coe_mk, AddHom.coe_mk, degreeOneVariable,
    annihilation, MvPolynomial.eval₂Hom_X', firstMode, mul_add, HahnSeries.C_apply,
    HahnSeries.coeff_add, HahnSeries.coeff_mul_single]
  change (creation (K := K) j : LaurentSeries (Space K)).coeff 0 * _ +
    (creation (K := K) j : LaurentSeries (Space K)).coeff 1 * _ = _
  rw [show (creation (K := K) j : LaurentSeries (Space K)).coeff 0 = 1 from by
    exact (HahnSeries.ofPowerSeries_apply_coeff (creation j) 0).trans (by simpa only [coeff_zero_eq_constantCoeff] using constantCoeff_creation j)]
  rw [show (creation (K := K) j : LaurentSeries (Space K)).coeff 1 = coeff 1 (creation j) from
    HahnSeries.ofPowerSeries_apply_coeff (creation j) 1]
  simp

theorem mode_zero_skewSeed (w : K) :
    mode w 0 (skewSeed (K := K)) = (1/4 - contraction w 1) • skewSeed := by
  rw [skewSeed, map_sub, mode_zero_degreeOneVariable, mode_zero_degreeOneVariable]
  simp only [coeff_one_creation, Fin.sum_univ_three, tensorExponent]
  norm_num [Algebra.smul_def, map_ofNat, map_sub, map_div₀, map_mul, skewSeed]
  have h : MvPolynomial.C (σ := Fin 3 × Mode) (1/12:K) *
      (3 + 12 * MvPolynomial.C (-(2 * contraction w 1)/3) -
        12 * MvPolynomial.C (contraction w 1 / 3)) =
      MvPolynomial.C (1/4:K) - MvPolynomial.C (contraction w 1) := by
    have hs := congrArg (MvPolynomial.C (σ := Fin 3 × Mode))
      (show (1/12:K) * (3 + 12 * (-(2 * contraction w 1)/3) -
        12 * (contraction w 1 / 3)) = 1/4 - contraction w 1 by ring)
    simpa only [map_mul, map_add, map_sub, map_ofNat] using hs
  linear_combination (degreeOneVariable 0 - degreeOneVariable 1) * h


/-- The initial relation needed by straightening with minimum part one. -/
theorem skew_initial_reduction (w : K) (i : ℤ) (hi : -1 < i) :
    (skewHighestWeightAction w).wordValue [i] ∈
      higherSpan (K := K) (skewHighestWeightAction w).wordValue [i] := by
  by_cases hpos : 0 < i
  · have hz : (skewHighestWeightAction w).wordValue [i] = 0 := by
      apply Subtype.ext
      exact mode_skewSeed_pos w i hpos
    rw [hz]
    exact Submodule.zero_mem _
  · have hzero : i = 0 := by omega
    subst i
    have he : (skewHighestWeightAction w).wordValue [] ∈
        higherSpan (K := K) (skewHighestWeightAction w).wordValue [0] :=
      mem_higherSpan _ (Or.inl (by simp)) (by simp)
    have hs := (higherSpan (K := K) (skewHighestWeightAction w).wordValue [0]).smul_mem
      (1/4 - contraction w 1) he
    have hv : (skewHighestWeightAction w).wordValue [0] =
        (1/4 - contraction w 1) • (skewHighestWeightAction w).wordValue [] := by
      apply Subtype.ext
      exact mode_zero_skewSeed w
    rw [hv]
    exact hs

end KanadeRussell.Sectors
