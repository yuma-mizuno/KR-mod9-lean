import Mathlib.Algebra.MvPolynomial.PDeriv

/-! A characteristic-zero partial derivative vanishes exactly when its
variable does not occur. The coefficient argument applies to arbitrary
polynomials, with no degree cutoff. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.PolynomialDerivatives

open MvPolynomial Finsupp

variable {K σ : Type*} [Field K] [CharZero K]

theorem coeff_pderiv_sub_single (i : σ) (m : σ →₀ ℕ) (hm : m i ≠ 0)
    (p : MvPolynomial σ K) :
    coeff (m - Finsupp.single i 1) (pderiv i p) = (m i : K) * coeff m p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [pderiv_monomial]
    by_cases he : e = m
    · subst e
      simp [mul_comm]
    · have hc : coeff m (monomial e c) = 0 := by simp [coeff_monomial, he]
      rw [hc, mul_zero]
      by_cases hei : e i = 0
      · simp [hei]
      · have hsub : e - Finsupp.single i 1 ≠ m - Finsupp.single i 1 := by
          intro h
          have hh := congrArg (fun u : σ →₀ ℕ => u + Finsupp.single i 1) h
          rw [Finsupp.sub_add_single_one_cancel hei,
            Finsupp.sub_add_single_one_cancel hm] at hh
          exact he hh
        simp [coeff_monomial, hsub]
  | add p q hp hq =>
    simp only [map_add, coeff_add, hp, hq, mul_add]

theorem notMem_vars_of_pderiv_eq_zero (i : σ) (p : MvPolynomial σ K)
    (hp : pderiv i p = 0) : i ∉ p.vars := by
  classical
  intro hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  have hc : coeff m p ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hmn : m i ≠ 0 := Finsupp.mem_support_iff.mp hmi
  have h := coeff_pderiv_sub_single i m hmn p
  rw [hp, coeff_zero] at h
  exact (mul_ne_zero (Nat.cast_ne_zero.mpr hmn) hc) h.symm

theorem pderiv_eq_zero_iff_notMem_vars (i : σ) (p : MvPolynomial σ K) :
    pderiv i p = 0 ↔ i ∉ p.vars :=
  ⟨notMem_vars_of_pderiv_eq_zero i p, fun h => pderiv_eq_zero_of_notMem_vars h⟩

theorem aeval_delete_eq_self (s : Set σ) [DecidablePred (· ∈ s)] (p : MvPolynomial σ K)
    (hp : ∀ i, i ∉ s → pderiv i p = 0) :
    MvPolynomial.aeval (fun i => if i ∈ s then X i else 0) p = p := by
  classical
  apply MvPolynomial.aeval_ite_mem_eq_self
  intro i hi
  by_contra his
  exact notMem_vars_of_pderiv_eq_zero i p (hp i his) hi

end KanadeRussell.Tsuchioka.PolynomialDerivatives
