import Mathlib.RingTheory.PowerSeries.Basic
set_option autoImplicit false
noncomputable section
namespace KanadeRussell.Representation
variable {K : Type*} [Field K]
/-- A scalar Lambert coefficient transform; `h+1` is the root height and `k+1`
is its repetition number. -/
def scalarLambertTransform : (ℕ → ℕ → K) →ₗ[K] PowerSeries K where
  toFun f := PowerSeries.mk fun n => ∑ h ∈ Finset.range n, ∑ k ∈ Finset.range (n+1),
    if (k+1)*(h+1)=n then f h k else 0
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add, Pi.add_apply]
    simp only [ite_add_zero, Finset.sum_add_distrib]
  map_smul' c f := by
    ext n
    simp only [PowerSeries.coeff_mk, map_smul, Pi.smul_apply, smul_eq_mul]
    simp only [mul_ite, mul_zero, Finset.mul_sum, RingHom.id_apply]

@[simp] theorem coeff_scalarLambertTransform (f : ℕ → ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (scalarLambertTransform f) =
      ∑ h ∈ Finset.range n, ∑ k ∈ Finset.range (n+1),
        if (k+1)*(h+1)=n then f h k else 0 := by simp [scalarLambertTransform]
end KanadeRussell.Representation
