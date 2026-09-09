import Mathlib
import RogersRamanujan
set_option backward.isDefEq.respectTransparency false

/-! Smoke test: the instance path for the rings used in the formalization. -/

open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory

-- ℤ⟦t⟧ : the base ring of the source side (q = t^4).
example : StrongNonarchimedeanRing ℤ⟦X⟧ := inferInstance
example : CompleteSpace ℤ⟦X⟧ := inferInstance
example : T2Space ℤ⟦X⟧ := inferInstance
example : IsUniformAddGroup ℤ⟦X⟧ := inferInstance
example : IsTopologicallyNilpotent (X : ℤ⟦X⟧) := by simp
example : IsTopologicallyNilpotent (X ^ 4 : ℤ⟦X⟧) := by simp

-- ℤ⟦t⟧⟦x⟧ : the x-extension (iterated power series, pi topology over pi topology).
example : StrongNonarchimedeanRing (ℤ⟦X⟧)⟦X⟧ := inferInstance
example : CompleteSpace (ℤ⟦X⟧)⟦X⟧ := inferInstance
example : T2Space (ℤ⟦X⟧)⟦X⟧ := inferInstance
example : IsUniformAddGroup (ℤ⟦X⟧)⟦X⟧ := inferInstance
example : IsTopologicallyNilpotent (X : (ℤ⟦X⟧)⟦X⟧) := PowerSeries.HasEval.X

-- The q-shift x ↦ q x is `rescale`, a ring hom, with the expected coefficient law.
example (f : (ℤ⟦X⟧)⟦X⟧) (n : ℕ) :
    coeff n (rescale (X : ℤ⟦X⟧) f) = (X : ℤ⟦X⟧) ^ n * coeff n f := by
  simp [coeff_rescale]

-- The base change ι : ℤ⟦q⟧ → ℤ⟦t⟧, q ↦ t^4, as strong evaluation.
noncomputable example : ℤ⟦X⟧ →+* ℤ⟦X⟧ := intEval (X ^ 4 : ℤ⟦X⟧)
example : Continuous (intEval (X ^ 4 : ℤ⟦X⟧)) := by fun_prop

-- Euler's identity and its inverse form from the library, at a nilpotent argument.
example (k : ℕ) :
    HasSum (fun n ↦ qPochhammerInfInner (-(X ^ (k + 1))) X n) ((X ^ (k + 1); X)_∞ : ℤ⟦X⟧) :=
  hasSum_qPochhammerInf _ (by simp)
example (k : ℕ) :
    HasSum (fun n ↦ bInv (X; X)_n * (X ^ (k + 1)) ^ n) (bInv ((X ^ (k + 1); X)_∞ : ℤ⟦X⟧)) :=
  hasSum_bInv_qPochhammerInf _ _ (by simp) (by simp)

-- Jacobi triple product from the library, at the arguments used for θ(q) = ∑ q^{n²}.
example : HasSum (fun n : ℤ ↦ abPow (-(-(X : ℤ⟦X⟧))) (-(-X)) n * (X ^ 2) ^ n.natAbs.choose 2)
    ((X ^ 2; X ^ 2)_∞ * (-X; X ^ 2)_∞ * (-X; X ^ 2)_∞ : ℤ⟦X⟧) :=
  jacobi_triple_product_hasSum' (by simp) (by ring)

-- Finite Pochhammer symbols with nilpotent parameters are units (needed for `bInv`).
example (m : ℕ) : IsUnit ((X; X)_m : ℤ⟦X⟧) := isUnit_qPochhammer (by simp) (by simp) m

-- Cauchy product in a nonarchimedean ring (needed for evaluation at x = 1).
example (f g : ℕ → ℤ⟦X⟧) (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) * (∑' n, g n) = ∑' n, ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 :=
  hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean hg
