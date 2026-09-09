import KanadeRussell.Representation.AffineCasimirPolarization
import KanadeRussell.Representation.RootMultiplicityFunction
import Mathlib.RingTheory.MvPowerSeries.Basic

/-! Multivariate series of actual root multiplicities and a coefficientwise
Casimir operator. No denominator or character formula is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

def rootCoefficientsOfExponent (e : Fin 3 →₀ ℕ) : RootCoefficients := fun i => (e i : ℤ)

@[simp] theorem rootCoefficientsOfExponent_zero : rootCoefficientsOfExponent 0 = 0 := rfl

@[simp] theorem rootCoefficientsOfExponent_add (e f : Fin 3 →₀ ℕ) :
    rootCoefficientsOfExponent (e+f) = rootCoefficientsOfExponent e + rootCoefficientsOfExponent f := by
  ext i
  simp [rootCoefficientsOfExponent]

theorem rootCoefficientsOfExponent_nonneg (e : Fin 3 →₀ ℕ) (i : Fin 3) :
    0 ≤ rootCoefficientsOfExponent e i := Int.natCast_nonneg _

theorem rootCoefficientsOfExponent_injective : Function.Injective rootCoefficientsOfExponent := by
  intro e f h
  ext i
  have hi := congrFun h i
  dsimp [rootCoefficientsOfExponent] at hi
  exact_mod_cast hi

namespace PrincipalHighestWeightModule
variable {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def rootCharacter (M : PrincipalHighestWeightModule K V) : MvPowerSeries (Fin 3) K :=
  fun e => M.rootMultiplicity (rootCoefficientsOfExponent e)

@[simp] theorem coeff_rootCharacter (M : PrincipalHighestWeightModule K V) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e M.rootCharacter = M.rootMultiplicity (rootCoefficientsOfExponent e) := rfl

@[simp] theorem constantCoeff_rootCharacter [CharZero K] (M : PrincipalHighestWeightModule K V) :
    MvPowerSeries.constantCoeff M.rootCharacter = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_rootCharacter,
    rootCoefficientsOfExponent_zero, M.rootMultiplicity_zero]

end PrincipalHighestWeightModule

/-- Multiplication by the integer Casimir value on each exponent coefficient. -/
noncomputable def rootCasimirOperator (lambda : RootCoefficients) :
    MvPowerSeries (Fin 3) K →ₗ[K] MvPowerSeries (Fin 3) K where
  toFun f e := (casimir lambda (rootCoefficientsOfExponent e) : K) * MvPowerSeries.coeff e f
  map_add' f g := by
    ext e
    change (casimir lambda (rootCoefficientsOfExponent e) : K) * (f e + g e) = _
    exact mul_add _ _ _
  map_smul' c f := by
    ext e
    simp [MvPowerSeries.coeff_apply, mul_left_comm]

@[simp] theorem coeff_rootCasimirOperator (lambda : RootCoefficients)
    (f : MvPowerSeries (Fin 3) K) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (rootCasimirOperator lambda f) =
      (casimir lambda (rootCoefficientsOfExponent e) : K) * MvPowerSeries.coeff e f := rfl

/-- The precise finite convolution to which polarization can be applied. -/
theorem coeff_rootCasimirOperator_mul (lambda : RootCoefficients)
    (f g : MvPowerSeries (Fin 3) K) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (rootCasimirOperator lambda (f*g)) =
      ∑ p ∈ Finset.antidiagonal e,
        (casimir lambda (rootCoefficientsOfExponent e) : K) *
          (MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) := by
  rw [coeff_rootCasimirOperator, MvPowerSeries.coeff_mul, Finset.mul_sum]

/-- The coefficient Euler operator in one simple-root direction. -/
noncomputable def rootEulerOperator (i : Fin 3) :
    MvPowerSeries (Fin 3) K →ₗ[K] MvPowerSeries (Fin 3) K where
  toFun f e := (e i : K) * MvPowerSeries.coeff e f
  map_add' f g := by
    ext e
    change (e i : K) * (f e + g e) = _
    exact mul_add _ _ _
  map_smul' c f := by
    ext e
    simp [MvPowerSeries.coeff_apply, mul_left_comm]

@[simp] theorem coeff_rootEulerOperator (i : Fin 3)
    (f : MvPowerSeries (Fin 3) K) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (rootEulerOperator i f) = (e i : K) * MvPowerSeries.coeff e f := rfl

/-- The exact polarized product rule for the coefficient Casimir. -/
theorem rootCasimirOperator_mul (lambda : RootCoefficients)
    (f g : MvPowerSeries (Fin 3) K) :
    rootCasimirOperator lambda (f*g) =
      (rootCasimirOperator lambda f)*g + f*(rootCasimirOperator lambda g) +
        ∑ i : Fin 3, ∑ j : Fin 3,
          ((symmetrizer i * Tsuchioka.Fock.affineCartanMatrix i j : ℤ) : K) •
            ((rootEulerOperator j f)*(rootEulerOperator i g)) := by
  ext e
  simp only [map_add, map_smul, MvPowerSeries.coeff_mul,
    coeff_rootCasimirOperator, coeff_rootEulerOperator, Fin.sum_univ_three,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1+p.2=e := Finset.mem_antidiagonal.mp hp
  rw [← he, rootCoefficientsOfExponent_add, casimir_add]
  norm_num [rootBilinear_eq, rootCoefficientsOfExponent, symmetrizer,
    Tsuchioka.Fock.affineCartanMatrix, Matrix.cons_val_two]
  ring

/-- The translated Cartan label, acting coefficientwise. -/
noncomputable def rootWeightLabelOperator (lambda : RootCoefficients) (i : Fin 3) :
    MvPowerSeries (Fin 3) K →ₗ[K] MvPowerSeries (Fin 3) K where
  toFun f e := (weightLabels lambda (rootCoefficientsOfExponent e) i : K) * MvPowerSeries.coeff e f
  map_add' f g := by
    ext e
    change (weightLabels lambda (rootCoefficientsOfExponent e) i : K) * (f e + g e) = _
    exact mul_add _ _ _
  map_smul' c f := by
    ext e
    simp [MvPowerSeries.coeff_apply, mul_left_comm]

@[simp] theorem coeff_rootWeightLabelOperator (lambda : RootCoefficients) (i : Fin 3)
    (f : MvPowerSeries (Fin 3) K) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (rootWeightLabelOperator lambda i f) =
      (weightLabels lambda (rootCoefficientsOfExponent e) i : K) * MvPowerSeries.coeff e f := rfl

/-- Rho-shifted product rule in terms of the translated weight labels. -/
theorem rootCasimirOperator_rho_mul (lambda : RootCoefficients)
    (f g : MvPowerSeries (Fin 3) K) :
    rootCasimirOperator (fun i => lambda i+1) (f*g) =
      (rootCasimirOperator (fun i => lambda i+1) f)*g +
        f*(rootCasimirOperator (fun _ => 1) g) -
        ∑ i : Fin 3, (symmetrizer i : K) •
          ((rootWeightLabelOperator lambda i f)*(rootEulerOperator i g)) := by
  ext e
  simp only [map_add, map_sub, map_smul, MvPowerSeries.coeff_mul,
    coeff_rootCasimirOperator, coeff_rootEulerOperator, coeff_rootWeightLabelOperator,
    Fin.sum_univ_three, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1+p.2=e := Finset.mem_antidiagonal.mp hp
  rw [← he, rootCoefficientsOfExponent_add]
  have h := congrArg (fun z : ℤ => (z : K))
    (casimir_rho_translation lambda (rootCoefficientsOfExponent p.1) (rootCoefficientsOfExponent p.2))
  norm_num [Fin.sum_univ_three, rootCoefficientsOfExponent, symmetrizer, Matrix.cons_val_two] at h ⊢
  linear_combination h * (MvPowerSeries.coeff p.1 f) * (MvPowerSeries.coeff p.2 g)

end KanadeRussell.Representation
