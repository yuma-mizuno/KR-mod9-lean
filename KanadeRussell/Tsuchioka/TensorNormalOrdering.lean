import KanadeRussell.Tsuchioka.TensorRootFields
import KanadeRussell.Tsuchioka.TwoFields

/-! Wick normal ordering for the source tensor root fields. Equal positions
have the full G1-cubed first-root scalar; distinct positions have no scalar
contraction. The tensor root-root commutator is not assumed. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open PowerSeries
open RootData (Lattice rootWeight simpleRoot)
open FormalSeries (mapLaurent)

variable {K : Type*} [Field K] [CharZero K]

noncomputable def tensorWickLog (w : K) (β γ : Lattice) (s t : Fin 3) :
    PowerSeries (LaurentSeries (Space K)) :=
  PowerSeries.mk fun n => if IsMode n then HahnSeries.single (-(n : ℤ))
    (MvPolynomial.C ((12 * rootWeight (w ^ (-(n : ℤ))) γ / (n : K)) *
      (if t = s then -contraction w n * rootWeight (w ^ (n : ℤ)) β else 0))) else 0

@[simp] theorem constantCoeff_tensorWickLog (w : K) (β γ : Lattice) (s t : Fin 3) :
    constantCoeff (tensorWickLog w β γ s t) = 0 := by
  simp [tensorWickLog, IsMode]

theorem tensorRootAnnihilation_creationLog (w : K) (β γ : Lattice) (s t : Fin 3) :
    PowerSeries.map (tensorRootAnnihilation w β s) (tensorRootCreationLog w γ t) =
      PowerSeries.map HahnSeries.C (tensorRootCreationLog w γ t) + tensorWickLog w β γ s t := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, map_add]
  rw [tensorRootCreationLog, coeff_mk, tensorWickLog, coeff_mk]
  by_cases hn : IsMode n
  · simp only [dif_pos hn, if_pos hn]
    rw [map_mul]
    simp only [tensorRootAnnihilation, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      RingHom.coe_comp, Function.comp_apply]
    rw [mul_add, ← map_mul]
    congr 1
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, ← map_mul]
  · simp [hn]

theorem tensorRootAnnihilation_creation (w : K) (β γ : Lattice) (s t : Fin 3) :
    PowerSeries.map (tensorRootAnnihilation w β s) (tensorRootCreation w γ t) =
      PowerSeries.map HahnSeries.C (tensorRootCreation w γ t) *
        FormalSeries.exponential (tensorWickLog w β γ s t) := by
  rw [tensorRootCreation, FormalSeries.map_exponential (tensorRootAnnihilation w β s)
    (constantCoeff_tensorRootCreationLog w γ t), tensorRootAnnihilation_creationLog]
  rw [FormalSeries.exponential_add
    (by rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
            constantCoeff_tensorRootCreationLog, map_zero]) (constantCoeff_tensorWickLog w β γ s t)]
  congr 1
  exact (FormalSeries.map_exponential
    (HahnSeries.C : Space K →+* LaurentSeries (Space K))
      (constantCoeff_tensorRootCreationLog w γ t)).symm

theorem tensorWickLog_distinct (w : K) (β γ : Lattice) (s t : Fin 3) (hst : s ≠ t) :
    tensorWickLog w β γ s t = 0 := by
  ext n
  simp [tensorWickLog, Ne.symm hst]

theorem tensorWickLog_first_same (w : K) (s : Fin 3) :
    tensorWickLog w (simpleRoot 0) (simpleRoot 0) s s =
      rootFactorLog w + rootFactorLog w + rootFactorLog w := by
  apply PowerSeries.ext
  intro n
  simp only [tensorWickLog, rootFactorLog, map_add, coeff_mk, RootData.rootWeight_first, if_true]
  split_ifs with hn
  · rw [← HahnSeries.single_add, ← HahnSeries.single_add, ← map_add, ← map_add]
    congr 2
    ring
  · simp

theorem exponential_tensorWickLog_first_same (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (s : Fin 3) :
    FormalSeries.exponential (tensorWickLog w (simpleRoot 0) (simpleRoot 0) s s) =
      sourceG1 w ^ 3 := by
  rw [tensorWickLog_first_same,
    FormalSeries.exponential_add (by simp) (constantCoeff_rootFactorLog w),
    FormalSeries.exponential_add (constantCoeff_rootFactorLog w) (constantCoeff_rootFactorLog w)]
  change rootFactor w * rootFactor w * rootFactor w = _
  rw [rootFactor_eq_sourceG1 w hw]
  ring

theorem tensorRootAnnihilation_creation_distinct (w : K) (β γ : Lattice)
    (s t : Fin 3) (hst : s ≠ t) :
    PowerSeries.map (tensorRootAnnihilation w β s) (tensorRootCreation w γ t) =
      PowerSeries.map HahnSeries.C (tensorRootCreation w γ t) := by
  rw [tensorRootAnnihilation_creation, tensorWickLog_distinct w β γ s t hst,
    FormalSeries.exponential_zero, mul_one]

noncomputable def tensorTwoSummands (w : K) (β γ : Lattice) (s t : Fin 3) (f : Space K) :
    LaurentSeries (LaurentSeries (Space K)) :=
  (tensorRootSummand w γ t f).map (tensorRootSummand w β s).toAddMonoidHom

theorem tensorRootSummand_coefficientMap (w : K) (β : Lattice) (s : Fin 3)
    (g : LaurentSeries (Space K)) :
    g.map (tensorRootSummand w β s).toAddMonoidHom =
      HahnSeries.C (tensorRootCreation w β s : LaurentSeries (Space K)) *
        mapLaurent (tensorRootAnnihilation w β s) g := by
  apply HahnSeries.ext
  funext n
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rfl

theorem tensorTwoSummands_coeff (w : K) (β γ : Lattice) (s t : Fin 3)
    (f : Space K) (a b : ℤ) :
    ((tensorTwoSummands w β γ s t f).coeff (-b)).coeff (-a) =
      (tensorRootSummand w β s ((tensorRootSummand w γ t f).coeff (-b))).coeff (-a) := rfl

noncomputable def tensorNormalProduct (w : K) (β γ : Lattice) (s t : Fin 3) (f : Space K) :
    LaurentSeries (LaurentSeries (Space K)) :=
  HahnSeries.C (tensorRootCreation w β s : LaurentSeries (Space K)) *
    ((PowerSeries.map (HahnSeries.C : Space K →+* LaurentSeries (Space K))
      (tensorRootCreation w γ t) : PowerSeries (LaurentSeries (Space K))) :
        LaurentSeries (LaurentSeries (Space K))) *
    mapLaurent (tensorRootAnnihilation w β s) (tensorRootAnnihilation w γ t f)

theorem tensorTwoSummands_normalOrdered (w : K) (β γ : Lattice) (s t : Fin 3)
    (f : Space K) :
    tensorTwoSummands w β γ s t f = tensorNormalProduct w β γ s t f *
      (FormalSeries.exponential (tensorWickLog w β γ s t) :
        LaurentSeries (LaurentSeries (Space K))) := by
  rw [tensorTwoSummands, tensorRootSummand_coefficientMap]
  change HahnSeries.C (tensorRootCreation w β s : LaurentSeries (Space K)) *
    mapLaurent (tensorRootAnnihilation w β s)
      ((tensorRootCreation w γ t : LaurentSeries (Space K)) * tensorRootAnnihilation w γ t f) = _
  rw [map_mul, FormalSeries.mapLaurent_powerSeries, tensorRootAnnihilation_creation,
    PowerSeries.coe_mul, tensorNormalProduct]
  ring

/-- The scalar for a tensor first-root self-pair is the full source G1 cubed. -/
theorem tensorTwoSummands_first_same_source (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s : Fin 3) (f : Space K) :
    tensorTwoSummands w (simpleRoot 0) (simpleRoot 0) s s f =
      tensorNormalProduct w (simpleRoot 0) (simpleRoot 0) s s f *
        ((sourceG1 w ^ 3 : PowerSeries (LaurentSeries (Space K))) :
          LaurentSeries (LaurentSeries (Space K))) := by
  rw [tensorTwoSummands_normalOrdered, exponential_tensorWickLog_first_same w hw]

theorem tensorTwoSummands_distinct_normalOrdered (w : K) (β γ : Lattice)
    (s t : Fin 3) (hst : s ≠ t) (f : Space K) :
    tensorTwoSummands w β γ s t f = tensorNormalProduct w β γ s t f := by
  rw [tensorTwoSummands_normalOrdered, tensorWickLog_distinct w β γ s t hst,
    FormalSeries.exponential_zero, PowerSeries.coe_one, mul_one]

noncomputable def tensorTwoFields (w : K) (β γ : Lattice) (f : Space K) :
    LaurentSeries (LaurentSeries (Space K)) :=
  (tensorRootField w γ f).map (tensorRootField w β).toAddMonoidHom

theorem tensorTwoFields_coeff (w : K) (β γ : Lattice) (f : Space K) (a b : ℤ) :
    ((tensorTwoFields w β γ f).coeff (-b)).coeff (-a) =
      tensorRootMode w β a (tensorRootMode w γ b f) := rfl

theorem tensorTwoFields_eq_sum (w : K) (β γ : Lattice) (f : Space K) :
    tensorTwoFields w β γ f =
      (1 / 144 : K) • ∑ s : Fin 3, ∑ t : Fin 3, tensorTwoSummands w β γ s t f := by
  apply HahnSeries.ext
  funext b
  apply HahnSeries.ext
  funext a
  simp only [tensorTwoFields, tensorTwoSummands, HahnSeries.map_coeff,
    tensorRootField, LinearMap.smul_apply, LinearMap.sum_apply, HahnSeries.coeff_smul,
    HahnSeries.coeff_sum]
  simp [← Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  congr 1
  norm_num [← mul_inv]

end KanadeRussell.Tsuchioka.Fock
