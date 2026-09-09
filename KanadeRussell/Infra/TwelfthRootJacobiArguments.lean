import KanadeRussell.Infra.TwelfthRootTorsionWeights
set_option autoImplicit false
namespace KanadeRussell.Infra.TwelfthRootJacobiArguments
open TwelfthRootTorsionWeights
variable {K : Type*} [Field K] [CharZero K]

theorem torsion_pow_ne_one (w : K) (hw : w^4-w^2+1=0)
    (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) : w^j ≠ 1 := by
  have hsmall : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → w^k ≠ 1 := by
    intro k hk hk6 he
    have h := (isUnit_iff_ne_zero.mp (denominator_isUnit w hw ⟨k-1, by omega⟩))
    have heq : k-1+1=k := by omega
    simp only [heq, he, sub_self] at h
    exact h rfl
  by_cases h6 : j ≤ 6
  · exact hsmall j hj h6
  intro he
  apply hsmall (12-j) (by omega) (by omega)
  have h := pow_twelve w hw
  rw [show 12=(12-j)+j by omega, pow_add, he, mul_one] at h
  exact h

theorem torsion_denominator_isUnit (w : K) (hw : w^4-w^2+1=0)
    (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) : IsUnit (1-w^j) := by
  apply isUnit_iff_ne_zero.mpr
  exact sub_ne_zero.mpr (Ne.symm (torsion_pow_ne_one w hw j hj hj12))

omit [CharZero K] in
theorem squareRoot_pow_twentyFour (w a : K) (hw : w^4-w^2+1=0)
    (ha : a^2=w) : a^24=1 := by
  rw [show 24=2*12 by decide, pow_mul, ha, pow_twelve w hw]

theorem squareRoot_pow_ne_one (w a : K) (hw : w^4-w^2+1=0)
    (ha : a^2=w) (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) : a^j ≠ 1 := by
  intro he
  apply torsion_pow_ne_one w hw j hj hj12
  rw [← ha, ← pow_mul, Nat.mul_comm 2 j, pow_mul, he, one_pow]

theorem squareRoot_denominator_isUnit (w a : K) (hw : w^4-w^2+1=0)
    (ha : a^2=w) (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) :
    IsUnit (1-a^j) := by
  exact isUnit_iff_ne_zero.mpr
    (sub_ne_zero.mpr (Ne.symm (squareRoot_pow_ne_one w a hw ha j hj hj12)))

/-- The initial Jacobi denominator remains a unit under any coefficient map. -/
theorem mapped_torsion_denominator_isUnit {R : Type*} [CommRing R]
    (f : K →+* R) (w : K) (hw : w^4-w^2+1=0)
    (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) : IsUnit (1-f w^j) := by
  simpa only [map_sub, map_one, map_pow] using
    (torsion_denominator_isUnit w hw j hj hj12).map f

theorem mapped_squareRoot_denominator_isUnit {R : Type*} [CommRing R]
    (f : K →+* R) (w a : K) (hw : w^4-w^2+1=0) (ha : a^2=w)
    (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) : IsUnit (1-f a^j) := by
  simpa only [map_sub, map_one, map_pow] using
    (squareRoot_denominator_isUnit w a hw ha j hj hj12).map f

end KanadeRussell.Infra.TwelfthRootJacobiArguments
