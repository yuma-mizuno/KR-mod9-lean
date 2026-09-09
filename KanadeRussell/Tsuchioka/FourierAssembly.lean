import KanadeRussell.Tsuchioka.FourierSymmetry

/-! Assembly of the scalar Fourier formulas from reciprocal geometric pairs. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Scalar

open PowerSeries FormalSeries

variable {K : Type*} [Field K] [CharZero K]

theorem symmetric_geometric_self (z : K) (hz : z⁻¹ = z) :
    symmetricFourier (2 * geometric z - 1) = fun n => 2 * delta z n := by
  simpa only [hz, two_mul] using symmetric_geometric_pair z

/-- The constant relation is exactly what is needed at exponent zero. -/
theorem symmetric_weighted_pairs (a b c d e z : K) (hz : z⁻¹ = z)
    (hconst : 2 * a + 2 * b + c = 2) :
    symmetricFourier
      (C a * (geometric d + geometric d⁻¹) +
       C b * (geometric e + geometric e⁻¹) + C c * geometric z - 1) =
      fun n => a * (delta d n + delta d⁻¹ n) +
        b * (delta e n + delta e⁻¹ n) + c * delta z n := by
  let F := C a * (geometric d + geometric d⁻¹) +
    C b * (geometric e + geometric e⁻¹) + C c * geometric z - 1
  have hform : C (2 : K) * F =
      C (2 * a) * (geometric d + geometric d⁻¹ - 1) +
      C (2 * b) * (geometric e + geometric e⁻¹ - 1) +
      C c * (2 * geometric z - 1) := by
    have hc := congrArg (C : K →+* PowerSeries K) hconst
    dsimp [F]
    norm_num only [map_add, map_mul, map_ofNat] at hc ⊢
    linear_combination hc
  have hh := congrArg symmetricFourier hform
  simp only [symmetricFourier_C_mul, symmetricFourier_add,
    symmetric_geometric_pair, symmetric_geometric_self z hz] at hh
  funext n
  have hn := congrFun hh n
  simp only [Pi.add_apply] at hn
  change 2 * symmetricFourier F n =
    (2 * a) * (delta d n + delta d⁻¹ n) +
    (2 * b) * (delta e n + delta e⁻¹ n) + c * (2 * delta z n) at hn
  change symmetricFourier F n = _
  linear_combination (1 / 2) * hn

theorem antisymmetric_euler (a : K) :
    antisymmetricFourier (1 + C a * eulerGeometric (-1)) =
      fun n => a * eulerDelta (-1) n := by
  exact odd_eulerGeometric_neg_one a

theorem antisymmetric_euler_pair (a b d : K) :
    antisymmetricFourier
      ((1 + C a * eulerGeometric (-1)) + C b * (geometric d - geometric d⁻¹)) =
      fun n => a * eulerDelta (-1) n + b * (delta d n - delta d⁻¹ n) := by
  rw [antisymmetricFourier_add, antisymmetric_euler, antisymmetricFourier_C_mul,
    antisymmetric_geometric_pair]
  rfl

theorem antisymmetric_C (a : K) :
    antisymmetricFourier (C a) = 0 := by
  have h := antisymmetricFourier_C_mul a (1 : PowerSeries K)
  funext n
  have hn := congrFun h n
  simpa using hn

theorem antisymmetric_weighted_pairs (k a b d e : K) :
    antisymmetricFourier
      (C k + C a * (geometric d - geometric d⁻¹) +
       C b * (geometric e - geometric e⁻¹)) =
      fun n => a * (delta d n - delta d⁻¹ n) + b * (delta e n - delta e⁻¹ n) := by
  rw [antisymmetricFourier_add, antisymmetricFourier_add, antisymmetric_C,
    antisymmetricFourier_C_mul, antisymmetricFourier_C_mul,
    antisymmetric_geometric_pair, antisymmetric_geometric_pair]
  simp only [zero_add]
  rfl

end KanadeRussell.Tsuchioka.Scalar
