import KanadeRussell.Tsuchioka.Contractions
import KanadeRussell.Tsuchioka.FormalExponential

/-!
The creation-annihilation normal-ordering calculation on the polynomial model.
The outer formal variable records creation; the coefficient Laurent variable
records annihilation. Thus every coefficient map below is algebraically defined.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem tensorExponent_dot (s t : Fin 3) :
    ∑ i : Fin 3, tensorExponent (K := K) i s * tensorExponent i t =
      if s.val = t.val then 6 else -3 := by
  fin_cases s <;> fin_cases t <;> norm_num [Fin.sum_univ_three, tensorExponent, show (2 : Fin 3) ≠ 0 from by decide]

noncomputable def wickCoefficient (w : K) (s t : Fin 3) (n : ℕ) : K :=
  (-4 / (3 * (n : K))) * contraction w n *
    ∑ i : Fin 3, tensorExponent i s * tensorExponent i t

theorem wickCoefficient_eq (w : K) (s t : Fin 3) (n : ℕ) :
    wickCoefficient w s t n =
      if s.val = t.val then -8 * contraction w n / (n : K)
      else 4 * contraction w n / (n : K) := by
  rw [wickCoefficient, tensorExponent_dot]
  split_ifs <;> simp [div_eq_mul_inv, mul_inv_rev] <;> ring

/-- The scalar logarithm produced by annihilation crossing creation. -/
noncomputable def wickLog (w : K) (s t : Fin 3) :
    PowerSeries (LaurentSeries (Space K)) :=
  PowerSeries.mk fun n =>
    if IsMode n then
      HahnSeries.single (-(n : ℤ)) (MvPolynomial.C (wickCoefficient w s t n))
    else 0

omit [CharZero K] in
@[simp] theorem constantCoeff_wickLog (w : K) (s t : Fin 3) :
    constantCoeff (wickLog w s t) = 0 := by
  simp [wickLog, IsMode]

theorem annihilation_creationLog (w : K) (s t : Fin 3) :
    PowerSeries.map (annihilation w s) (creationLog (K := K) t) =
      PowerSeries.map HahnSeries.C (creationLog (K := K) t) + wickLog w s t := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, map_add]
  rw [creationLog, coeff_mk, wickLog, coeff_mk]
  by_cases hn : IsMode n
  · simp only [dif_pos hn, if_pos hn, map_sum]
    have hi (i : Fin 3) :
        annihilation w s
          (MvPolynomial.C (-4 * tensorExponent i t / (n : K)) *
            MvPolynomial.X (i, (⟨n, hn⟩ : Mode))) =
        HahnSeries.C
          (MvPolynomial.C (-4 * tensorExponent i t / (n : K)) *
            MvPolynomial.X (i, (⟨n, hn⟩ : Mode))) +
          HahnSeries.single (-(n : ℤ))
            (MvPolynomial.C
              ((-4 * tensorExponent i t / (n : K)) *
                (tensorExponent i s * contraction w n / 3))) := by
      rw [map_mul]
      simp only [annihilation, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
        RingHom.coe_comp, Function.comp_apply]
      rw [mul_add, ← map_mul]
      congr 1
      rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, ← map_mul]
    simp_rw [hi]
    rw [Finset.sum_add_distrib]
    congr 1
    apply HahnSeries.ext
    funext e
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_single]
    by_cases he : e = -(n : ℤ)
    · simp only [he, if_pos, ← map_sum]
      congr 1
      rw [wickCoefficient, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp [he]
  · simp [hn]

/-- Exact Wick factorization of the constructed annihilation substitution
and creation exponential. This is a proved operator calculation, not a
hypothesis about the source's generalized commutation relations. -/
theorem annihilation_creation (w : K) (s t : Fin 3) :
    PowerSeries.map (annihilation w s) (creation (K := K) t) =
      PowerSeries.map HahnSeries.C (creation (K := K) t) *
        FormalSeries.exponential (wickLog w s t) := by
  rw [creation, FormalSeries.map_exponential (annihilation w s)
    (constantCoeff_creationLog t), annihilation_creationLog]
  rw [FormalSeries.exponential_add
    (by rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
            constantCoeff_creationLog, map_zero]) (constantCoeff_wickLog w s t)]
  congr 1
  exact (FormalSeries.map_exponential
    (HahnSeries.C : Space K →+* LaurentSeries (Space K)) (constantCoeff_creationLog t)).symm

/-- The logarithm of the scalar factor G1 in the ratio of the two variables.
ScalarFactors identifies it with the paper's full binomial product. -/
noncomputable def rootFactorLog (w : K) : PowerSeries (LaurentSeries (Space K)) :=
  PowerSeries.mk fun n =>
    if IsMode n then
      HahnSeries.single (-(n : ℤ)) (MvPolynomial.C (-4 * contraction w n / (n : K)))
    else 0

noncomputable def rootFactor (w : K) : PowerSeries (LaurentSeries (Space K)) :=
  FormalSeries.exponential (rootFactorLog w)

omit [CharZero K] in
@[simp] theorem constantCoeff_rootFactorLog (w : K) :
    constantCoeff (rootFactorLog w) = 0 := by
  simp [rootFactorLog, IsMode]

theorem wickLog_same (w : K) (s : Fin 3) :
    wickLog w s s = rootFactorLog w + rootFactorLog w := by
  apply PowerSeries.ext
  intro n
  simp only [wickLog, rootFactorLog, map_add, coeff_mk, wickCoefficient_eq]
  split_ifs with hn
  · rw [← HahnSeries.single_add, ← map_add]
    congr 2
    ring
  · simp

theorem wickLog_distinct (w : K) (s t : Fin 3) (hst : s ≠ t) :
    wickLog w s t = -rootFactorLog w := by
  apply PowerSeries.ext
  intro n
  have hv : s.val ≠ t.val := fun he => hst (Fin.ext he)
  simp only [wickLog, rootFactorLog, map_neg, coeff_mk, wickCoefficient_eq, if_neg hv]
  split_ifs with hn
  · rw [← HahnSeries.single_neg, ← map_neg]
    congr 2
    ring
  · simp

/-- Equal tensor factors give the square of the scalar root factor. -/
theorem annihilation_creation_same (w : K) (s : Fin 3) :
    PowerSeries.map (annihilation w s) (creation (K := K) s) =
      PowerSeries.map HahnSeries.C (creation (K := K) s) * rootFactor w ^ 2 := by
  rw [annihilation_creation, wickLog_same, FormalSeries.exponential_add
    (constantCoeff_rootFactorLog w) (constantCoeff_rootFactorLog w), pow_two]
  rfl

/-- Distinct tensor factors give the inverse scalar root factor, expressed
as a product identity so no inverse convention is implicit. -/
theorem annihilation_creation_distinct (w : K) (s t : Fin 3) (hst : s ≠ t) :
    PowerSeries.map (annihilation w s) (creation (K := K) t) * rootFactor w =
      PowerSeries.map HahnSeries.C (creation (K := K) t) := by
  rw [annihilation_creation, wickLog_distinct w s t hst, mul_assoc]
  have he := FormalSeries.exponential_mul_neg (constantCoeff_rootFactorLog w)
  rw [rootFactor, mul_comm (FormalSeries.exponential (-rootFactorLog w)), he, mul_one]

/-- Creation logarithm in one of the three tensor factors. -/
noncomputable def creationLogFactor (i j : Fin 3) : PowerSeries (Space K) :=
  PowerSeries.mk fun n =>
    if h : IsMode n then
      MvPolynomial.C (-4 * tensorExponent i j / (n : K)) *
        MvPolynomial.X (i, (⟨n, h⟩ : Mode))
    else 0

omit [CharZero K] in
@[simp] theorem constantCoeff_creationLogFactor (i j : Fin 3) :
    constantCoeff (creationLogFactor (K := K) i j) = 0 := by
  simp [creationLogFactor, IsMode]

omit [CharZero K] in
theorem creationLog_eq_sum_factors (j : Fin 3) :
    creationLog (K := K) j = ∑ i : Fin 3, creationLogFactor i j := by
  apply PowerSeries.ext
  intro n
  simp only [creationLog, creationLogFactor, coeff_mk, map_sum]
  by_cases hn : IsMode n <;> simp [hn]

/-- The combined creation exponential equals the product of the three
tensor-factor exponentials in the source's normal-ordered formula. -/
theorem creation_eq_product_factors (j : Fin 3) :
    creation (K := K) j =
      ∏ i : Fin 3, FormalSeries.exponential (creationLogFactor i j) := by
  rw [creation, creationLog_eq_sum_factors]
  apply FormalSeries.exponential_sum
  intro i hi
  exact constantCoeff_creationLogFactor i j

@[simp] theorem constantCoeff_rootFactor (w : K) : constantCoeff (rootFactor w) = 1 :=
  FormalSeries.constantCoeff_exponential (constantCoeff_rootFactorLog w)

/-- The first coefficient obtained from the constructed Wick factor
is exactly the paper's c^(1)_1, including its normalization. -/
theorem coeff_one_rootFactor (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0) :
    coeff 1 (rootFactor w) =
      HahnSeries.single (-1 : ℤ)
        (MvPolynomial.C ((-6 - 4 * w + 2 * w ^ 3) / 3)) := by
  rw [rootFactor, FormalSeries.coeff_one_exponential (constantCoeff_rootFactorLog w)]
  rw [rootFactorLog, coeff_mk, if_pos (show IsMode 1 from by decide)]
  have hk := contraction_fin w hw (1 : Fin 12)
  norm_num [spectralValue] at hk
  simp only [Nat.cast_one, div_one]
  rw [hk]
  congr 2
  ring

end KanadeRussell.Tsuchioka.Fock
