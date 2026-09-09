import KanadeRussell.Representation.RootMultiplicitySeries
import Mathlib.Algebra.BigOperators.Finprod

/-! Coefficients on the integer root lattice, extended by zero outside the
positive cone. Convolution is algebraic and finitely supported at each target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

noncomputable def exponentOfRootCoefficients (beta : RootCoefficients) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (beta i).toNat)

@[simp] theorem exponentOfRootCoefficients_apply (beta : RootCoefficients) (i : Fin 3) :
    exponentOfRootCoefficients beta i = (beta i).toNat := rfl

@[simp] theorem exponentOfRootCoefficients_ofExponent (e : Fin 3 →₀ ℕ) :
    exponentOfRootCoefficients (rootCoefficientsOfExponent e) = e := by
  ext i
  simp [rootCoefficientsOfExponent]

theorem rootCoefficientsOfExponent_ofRoot (beta : RootCoefficients) (hb : ∀ i, 0 ≤ beta i) :
    rootCoefficientsOfExponent (exponentOfRootCoefficients beta) = beta := by
  ext i
  exact Int.toNat_of_nonneg (hb i)

noncomputable def rootCoefficient (f : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) : K :=
  if ∀ i, 0 ≤ beta i then MvPowerSeries.coeff (exponentOfRootCoefficients beta) f else 0

theorem rootCoefficient_of_nonneg (f : MvPowerSeries (Fin 3) K)
    (beta : RootCoefficients) (hb : ∀ i, 0 ≤ beta i) :
    rootCoefficient f beta = MvPowerSeries.coeff (exponentOfRootCoefficients beta) f := if_pos hb

theorem rootCoefficient_of_not_nonneg (f : MvPowerSeries (Fin 3) K)
    (beta : RootCoefficients) (hb : ¬ (∀ i, 0 ≤ beta i)) : rootCoefficient f beta = 0 := if_neg hb

@[simp] theorem rootCoefficient_ofExponent (f : MvPowerSeries (Fin 3) K) (e : Fin 3 →₀ ℕ) :
    rootCoefficient f (rootCoefficientsOfExponent e) = MvPowerSeries.coeff e f := by
  rw [rootCoefficient_of_nonneg f _ (rootCoefficientsOfExponent_nonneg e),
    exponentOfRootCoefficients_ofExponent]

noncomputable def rootCoefficientLinear (beta : RootCoefficients) :
    MvPowerSeries (Fin 3) K →ₗ[K] K where
  toFun f := rootCoefficient f beta
  map_add' f g := by
    classical
    unfold rootCoefficient
    split_ifs <;> simp
  map_smul' c f := by
    classical
    unfold rootCoefficient
    split_ifs <;> simp

@[simp] theorem rootCoefficientLinear_apply (beta : RootCoefficients) (f : MvPowerSeries (Fin 3) K) :
    rootCoefficientLinear beta f = rootCoefficient f beta := rfl

@[simp] theorem rootCoefficient_rootCharacter {V : Type*} [CharZero K] [AddCommGroup V] [Module K V]
    (M : PrincipalHighestWeightModule K V) (beta : RootCoefficients) :
    rootCoefficient M.rootCharacter beta = M.rootMultiplicity beta := by
  by_cases hb : ∀ i, 0 ≤ beta i
  · rw [rootCoefficient_of_nonneg _ _ hb, M.coeff_rootCharacter,
      rootCoefficientsOfExponent_ofRoot beta hb]
  · rw [rootCoefficient_of_not_nonneg _ _ hb, M.rootMultiplicity_eq_zero_of_not_nonneg beta hb]

@[simp] theorem rootCoefficient_sum {ι : Type*} (S : Finset ι)
    (f : ι → MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient (∑ p ∈ S, f p) beta = ∑ p ∈ S, rootCoefficient (f p) beta :=
  map_sum (rootCoefficientLinear beta) f S

@[simp] theorem rootCoefficient_add (f g : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient (f+g) beta = rootCoefficient f beta+rootCoefficient g beta :=
  (rootCoefficientLinear beta).map_add f g

@[simp] theorem rootCoefficient_zero (beta : RootCoefficients) :
    rootCoefficient (0 : MvPowerSeries (Fin 3) K) beta = 0 := (rootCoefficientLinear beta).map_zero

@[simp] theorem rootCoefficient_monomial (e : Fin 3 →₀ ℕ) (a : K) (beta : RootCoefficients) :
    rootCoefficient (MvPowerSeries.monomial e a) beta =
      if beta = rootCoefficientsOfExponent e then a else 0 := by
  classical
  by_cases he : beta = rootCoefficientsOfExponent e
  · subst beta
    simp
  · by_cases hb : ∀ i, 0 ≤ beta i
    · have hne : exponentOfRootCoefficients beta ≠ e := by
        intro h
        apply he
        rw [← h, rootCoefficientsOfExponent_ofRoot beta hb]
      rw [rootCoefficient_of_nonneg _ _ hb, MvPowerSeries.coeff_monomial, if_neg hne, if_neg he]
    · rw [rootCoefficient_of_not_nonneg _ _ hb, if_neg he]

theorem rootCoefficient_nonneg_of_ne_zero (f : MvPowerSeries (Fin 3) K)
    (beta : RootCoefficients) (h : rootCoefficient f beta ≠ 0) : ∀ i, 0 ≤ beta i := by
  by_contra hb
  exact h (rootCoefficient_of_not_nonneg f beta hb)

/-- Integer convolution at a fixed target is supported by a finite antidiagonal image. -/
theorem rootCoefficient_convolution_support (f g : MvPowerSeries (Fin 3) K)
    (beta : RootCoefficients) :
    Function.support (fun alpha => rootCoefficient f alpha * rootCoefficient g (beta-alpha)) ⊆
      ↑((Finset.antidiagonal (exponentOfRootCoefficients beta)).image
        (fun p => rootCoefficientsOfExponent p.1)) := by
  classical
  intro alpha ha
  have ha0 := rootCoefficient_nonneg_of_ne_zero f alpha (left_ne_zero_of_mul ha)
  have hd0 := rootCoefficient_nonneg_of_ne_zero g (beta-alpha) (right_ne_zero_of_mul ha)
  have hb : ∀ i, 0 ≤ beta i := by
    intro i
    have hi := ha0 i
    have hj := hd0 i
    simp only [Pi.sub_apply] at hj
    omega
  apply Finset.mem_image.mpr
  refine ⟨(exponentOfRootCoefficients alpha, exponentOfRootCoefficients (beta-alpha)), ?_,
    rootCoefficientsOfExponent_ofRoot alpha ha0⟩
  apply Finset.mem_antidiagonal.mpr
  apply rootCoefficientsOfExponent_injective
  rw [rootCoefficientsOfExponent_add, rootCoefficientsOfExponent_ofRoot alpha ha0,
    rootCoefficientsOfExponent_ofRoot (beta-alpha) hd0, rootCoefficientsOfExponent_ofRoot beta hb]
  abel

theorem rootCoefficient_convolution_finite (f g : MvPowerSeries (Fin 3) K)
    (beta : RootCoefficients) :
    (Function.support (fun alpha => rootCoefficient f alpha * rootCoefficient g (beta-alpha))).Finite :=
  (Finset.finite_toSet _).subset (rootCoefficient_convolution_support f g beta)

/-- Product coefficients are the finite convolution over the full integer root lattice. -/
theorem rootCoefficient_mul (f g : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient (f*g) beta =
      ∑ᶠ alpha : RootCoefficients, rootCoefficient f alpha * rootCoefficient g (beta-alpha) := by
  classical
  by_cases hb : ∀ i, 0 ≤ beta i
  · rw [rootCoefficient_of_nonneg _ _ hb, MvPowerSeries.coeff_mul,
      finsum_eq_sum_of_support_subset _ (rootCoefficient_convolution_support f g beta)]
    have hinj : Set.InjOn (fun p : (Fin 3 →₀ ℕ) × (Fin 3 →₀ ℕ) => rootCoefficientsOfExponent p.1)
        ↑(Finset.antidiagonal (exponentOfRootCoefficients beta)) := by
      intro p hp q hq h
      have h1 : p.1=q.1 := rootCoefficientsOfExponent_injective h
      apply Prod.ext h1
      apply add_left_cancel (a := p.1)
      rw [Finset.mem_antidiagonal.mp hp, h1, Finset.mem_antidiagonal.mp hq]
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro p hp
    have hd : beta-rootCoefficientsOfExponent p.1 = rootCoefficientsOfExponent p.2 := by
      rw [← rootCoefficientsOfExponent_ofRoot beta hb, ← Finset.mem_antidiagonal.mp hp,
        rootCoefficientsOfExponent_add]
      abel
    rw [hd, rootCoefficient_ofExponent, rootCoefficient_ofExponent]
  · rw [rootCoefficient_of_not_nonneg _ _ hb]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro alpha
    by_cases ha : rootCoefficient f alpha = 0
    · rw [ha, zero_mul]
    · have hd : ¬ (∀ i, 0 ≤ (beta-alpha) i) := by
        intro hh
        apply hb
        intro i
        have hi := rootCoefficient_nonneg_of_ne_zero f alpha ha i
        have hj := hh i
        simp only [Pi.sub_apply] at hj
        omega
      rw [rootCoefficient_of_not_nonneg _ _ hd, mul_zero]

@[simp] theorem rootCoefficient_smul (c : K) (f : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient (c • f) beta = c * rootCoefficient f beta :=
  (rootCoefficientLinear beta).map_smul c f

@[simp] theorem rootCoefficient_neg (f : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient (-f) beta = -rootCoefficient f beta := (rootCoefficientLinear beta).map_neg f

/-- Multiplication by a monomial translates the extended coefficient function. -/
theorem rootCoefficient_monomial_mul (e : Fin 3 →₀ ℕ) (a : K)
    (f : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient (MvPowerSeries.monomial e a * f) beta =
      a * rootCoefficient f (beta-rootCoefficientsOfExponent e) := by
  classical
  rw [rootCoefficient_mul]
  rw [finsum_eq_single _ (rootCoefficientsOfExponent e) (by
    intro alpha ha
    rw [rootCoefficient_monomial, if_neg ha, zero_mul])]
  rw [rootCoefficient_monomial, if_pos rfl]

/-- The simple-root monomial shift, valid at every integer occupation. -/
theorem rootCoefficient_simpleRoot_mul (i : Fin 3)
    (f : MvPowerSeries (Fin 3) K) (beta : RootCoefficients) :
    rootCoefficient (MvPowerSeries.X i * f) beta = rootCoefficient f (beta-Pi.single i 1) := by
  rw [MvPowerSeries.X, rootCoefficient_monomial_mul, one_mul]
  congr 2
  ext j
  by_cases h : i=j
  · subst j
    simp [rootCoefficientsOfExponent]
  · simp [rootCoefficientsOfExponent, Ne.symm h]

theorem rootCoefficient_ext {f g : MvPowerSeries (Fin 3) K}
    (h : ∀ beta, rootCoefficient f beta = rootCoefficient g beta) : f=g := by
  ext e
  simpa only [rootCoefficient_ofExponent] using h (rootCoefficientsOfExponent e)

end KanadeRussell.Representation
