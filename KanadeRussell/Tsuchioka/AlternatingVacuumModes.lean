import KanadeRussell.Tsuchioka.TensorAlternatingWeights

/-! The alternating vector is highest for every positive root mode. Inverse
dressing transfers these conditions and the root zero modes to the Z action. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KanadeRussell.Tsuchioka.Fock
open PowerSeries
open RootData (Lattice)
variable {K : Type*} [Field K] [CharZero K]

theorem tensorRootMode_two_alternatingSeed (w : K) (beta : Lattice) :
    tensorRootMode w beta 2 (alternatingSeed (K := K)) = 0 := by
  have hs (j : Fin 3) : (tensorRootSummand w beta j alternatingSeed).coeff (-2) =
      (contraction w 1 * RootData.rootWeight w beta)^2 • alternatingQuadraticCoefficient j := by
    rw [tensorRootSummand_alternatingSeed_coeff]
    have hneg (a : ℤ) (ha : a < 0) :
        (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff a = 0 := by
      rw [PowerSeries.coeff_coe, if_pos ha]
    have hz : (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff 0 = 1 := by
      exact (HahnSeries.ofPowerSeries_apply_coeff (tensorRootCreation w beta j) 0).trans
        (by simpa only [coeff_zero_eq_constantCoeff, tensorRootCreation] using
          FormalSeries.constantCoeff_exponential (constantCoeff_tensorRootCreationLog w beta j))
    norm_num only [Int.reduceAdd, hneg (-2) (by decide), hneg (-1) (by decide), hz,
      zero_mul, zero_add, one_mul, MvPolynomial.C_mul']
  change ((1/12:K) • ∑ j : Fin 3,
    tensorRootSummand w beta j alternatingSeed).coeff (-2) = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_sum, hs, ← Finset.smul_sum,
    sum_alternatingQuadraticCoefficient, smul_zero]

theorem tensorRootMode_alternatingSeed_pos (w : K) (beta : Lattice) (i : ℤ) (hi : 0 < i) :
    tensorRootMode w beta i (alternatingSeed (K := K)) = 0 := by
  by_cases h1 : i = 1
  · subst i; exact tensorRootMode_one_alternatingSeed w beta
  by_cases h2 : i = 2
  · subst i; exact tensorRootMode_two_alternatingSeed w beta
  have hs (j : Fin 3) : (tensorRootSummand w beta j alternatingSeed).coeff (-i) = 0 := by
    rw [tensorRootSummand_alternatingSeed_coeff]
    have hneg (a : ℤ) (ha : a < 0) :
        (tensorRootCreation w beta j : LaurentSeries (Space K)).coeff a = 0 := by
      rw [PowerSeries.coeff_coe, if_pos ha]
    rw [hneg (-i) (by omega), hneg (-i+1) (by omega), hneg (-i+2) (by omega)]
    simp
  change ((1/12:K) • ∑ j : Fin 3,
    tensorRootSummand w beta j alternatingSeed).coeff (-i) = _
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_sum, hs, Finset.sum_const_zero, smul_zero]

theorem rootMode_pos_of_tensorRootMode_pos (w : K) (hw : w^4-w^2+1=0)
    (beta : Lattice) (f : Space K) (hf : f ∈ heisenbergVacuum w)
    (hX : ∀ j : ℤ, 0 < j → tensorRootMode w beta j f = 0) (i : ℤ) (hi : 0 < i) :
    rootMode w beta i f = 0 := by
  change (rootField w beta f).coeff (-i) = 0
  rw [rootField_eq_inverse_tensorRootField_on_vacuum w hw beta f hf, HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have he : ab.1 + ab.2 = -i := (Finset.mem_addAntidiagonal.mp hab).2.2
  by_cases ha : ab.1 < 0
  · rw [PowerSeries.coeff_coe, if_pos ha, zero_mul]
  · have hz := hX (-ab.2) (by omega)
    change (tensorRootField w beta f).coeff (-(-ab.2)) = 0 at hz
    rw [neg_neg] at hz
    rw [hz, mul_zero]

theorem rootMode_zero_of_tensorRootMode_pos (w : K) (hw : w^4-w^2+1=0)
    (beta : Lattice) (f : Space K) (hf : f ∈ heisenbergVacuum w)
    (hX : ∀ j : ℤ, 0 < j → tensorRootMode w beta j f = 0) :
    rootMode w beta 0 f = tensorRootMode w beta 0 f := by
  let p : PowerSeries (Space K) := PowerSeries.mk fun n : ℕ => (tensorRootField w beta f).coeff n
  have hp : (p : LaurentSeries (Space K)) = tensorRootField w beta f := by
    apply HahnSeries.ext
    funext n
    rw [PowerSeries.coeff_coe]
    by_cases hn : n < 0
    · rw [if_pos hn]
      have hz := hX (-n) (by omega)
      change (tensorRootField w beta f).coeff (-(-n)) = 0 at hz
      simpa only [neg_neg] using hz.symm
    · rw [if_neg hn]
      simp only [p, coeff_mk, ← Int.eq_natAbs_of_nonneg (by omega : 0 ≤ n)]
  change (rootField w beta f).coeff 0 = (tensorRootField w beta f).coeff 0
  rw [rootField_eq_inverse_tensorRootField_on_vacuum w hw beta f hf, ← hp, ← PowerSeries.coe_mul]
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
    LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries]
  simp only [coeff_zero_eq_constantCoeff, map_mul, inverseDiagonalRootCreation]
  rw [FormalSeries.constantCoeff_exponential (by simp :
    constantCoeff (-diagonalRootCreationLog w beta) = 0), one_mul]

theorem rootMode_alternatingSeed_pos (w : K) (hw : w^4-w^2+1=0)
    (beta : Lattice) (i : ℤ) (hi : 0 < i) :
    rootMode w beta i (alternatingSeed (K := K)) = 0 :=
  rootMode_pos_of_tensorRootMode_pos w hw beta alternatingSeed
    (alternatingSeed_heisenbergVacuum w) (tensorRootMode_alternatingSeed_pos w beta) i hi

theorem rootMode_zero_alternatingSeed (w : K) (hw : w^4-w^2+1=0) (beta : Lattice) :
    rootMode w beta 0 (alternatingSeed (K := K)) = tensorRootMode w beta 0 alternatingSeed :=
  rootMode_zero_of_tensorRootMode_pos w hw beta alternatingSeed
    (alternatingSeed_heisenbergVacuum w) (tensorRootMode_alternatingSeed_pos w beta)

end KanadeRussell.Tsuchioka.Fock
