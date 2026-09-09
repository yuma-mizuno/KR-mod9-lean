import KanadeRussell.Tsuchioka.RatioContraction
import KanadeRussell.Tsuchioka.FormalExponential

/-! Coefficientwise derivations of Laurent fields. All product coefficients
and exponential coefficients used in the proof are finite sums. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.FormalSeries

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

noncomputable def laurentDerivation (D : Derivation K A A) :
    LaurentSeries A →ₗ[K] LaurentSeries A where
  toFun f := f.map D.toLinearMap
  map_add' f g := by
    apply HahnSeries.ext
    funext n
    simp only [HahnSeries.map_coeff, HahnSeries.coeff_add, map_add]
  map_smul' c f := by
    apply HahnSeries.ext
    funext n
    simp only [HahnSeries.map_coeff, HahnSeries.coeff_smul, map_smul, RingHom.id_apply]

@[simp] theorem coeff_laurentDerivation (D : Derivation K A A)
    (f : LaurentSeries A) (n : ℤ) : (laurentDerivation D f).coeff n = D (f.coeff n) := rfl

theorem laurentDerivation_mul (D : Derivation K A A) (f g : LaurentSeries A) :
    laurentDerivation D (f * g) =
      laurentDerivation D f * g + f * laurentDerivation D g := by
  apply HahnSeries.ext
  funext n
  simp only [coeff_laurentDerivation, HahnSeries.coeff_add, laurent_coeff_mul_finsum]
  have hm : D (∑ᶠ i : ℤ, f.coeff i * g.coeff (n - i)) =
      ∑ᶠ i : ℤ, D (f.coeff i * g.coeff (n - i)) :=
    D.toLinearMap.toAddMonoidHom.map_finsum (laurent_convolution_finite f g n)
  rw [hm]
  have he (i : ℤ) : D (f.coeff i * g.coeff (n - i)) =
      D (f.coeff i) * g.coeff (n - i) + f.coeff i * D (g.coeff (n - i)) := by
    simpa only [smul_eq_mul, mul_comm, add_comm] using D.leibniz (f.coeff i) (g.coeff (n - i))
  simp only [he]
  exact finsum_add_distrib
    (laurent_convolution_finite (laurentDerivation D f) g n)
    (laurent_convolution_finite f (laurentDerivation D g) n)

theorem laurentDerivation_single (D : Derivation K A A) (n : ℤ) (a : A) :
    laurentDerivation D (HahnSeries.single n a) = HahnSeries.single n (D a) := by
  classical
  apply HahnSeries.ext
  funext i
  simp only [coeff_laurentDerivation, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem laurentDerivation_C (D : Derivation K A A) (a : A) :
    laurentDerivation D (HahnSeries.C a) = HahnSeries.C (D a) :=
  laurentDerivation_single D 0 a

theorem laurentDerivation_powerSeries_eq_zero (D : Derivation K A A)
    (f : PowerSeries A) (hf : ∀ n, D (PowerSeries.coeff n f) = 0) :
    laurentDerivation D (f : LaurentSeries A) = 0 := by
  apply HahnSeries.ext
  funext i
  cases i with
  | ofNat n =>
    simp only [coeff_laurentDerivation, Int.ofNat_eq_natCast,
      LaurentSeries.coeff_coe_powerSeries, hf, HahnSeries.coeff_zero]
  | negSucc n =>
    simp only [coeff_laurentDerivation, PowerSeries.coeff_coe, Int.negSucc_lt_zero,
      if_true, map_zero, HahnSeries.coeff_zero]

theorem derivation_coeff_mul_zero (D : Derivation K A A) (f g : PowerSeries A)
    (hf : ∀ n, D (PowerSeries.coeff n f) = 0)
    (hg : ∀ n, D (PowerSeries.coeff n g) = 0) (n : ℕ) :
    D (PowerSeries.coeff n (f * g)) = 0 := by
  rw [PowerSeries.coeff_mul, map_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  simp only [D.leibniz, hf, hg, smul_zero, add_zero]

theorem derivation_coeff_pow_zero (D : Derivation K A A) (f : PowerSeries A)
    (hf : ∀ n, D (PowerSeries.coeff n f) = 0) (k n : ℕ) :
    D (PowerSeries.coeff n (f ^ k)) = 0 := by
  induction k generalizing n with
  | zero =>
    classical
    simp only [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp [D.map_one_eq_zero]
  | succ k ih =>
    rw [pow_succ]
    exact derivation_coeff_mul_zero D (f ^ k) f ih hf n

theorem derivation_coeff_exponential_zero [Algebra ℚ K] [Algebra ℚ A]
    [IsScalarTower ℚ K A] (D : Derivation K A A) (f : PowerSeries A)
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hf : ∀ n, D (PowerSeries.coeff n f) = 0) (n : ℕ) :
    D (PowerSeries.coeff n (exponential f)) = 0 := by
  rw [coeff_exponential hf0, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  have hrat (q : ℚ) : D (algebraMap ℚ A q) = 0 := by
    rw [IsScalarTower.algebraMap_apply ℚ K A, D.map_algebraMap]
  simp only [D.leibniz, hrat, derivation_coeff_pow_zero D f hf, smul_zero, add_zero]

end KanadeRussell.Tsuchioka.FormalSeries
