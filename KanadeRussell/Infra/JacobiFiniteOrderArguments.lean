import KanadeRussell.Infra.JacobiFirstJet
import KanadeRussell.Infra.TwelfthRootJacobiArguments
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Infra.JacobiFiniteOrderArguments
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

omit [IsUniformAddGroup R] [CompleteSpace R] [T2Space R] in
theorem shifted_tails_nilpotent (p u : Rˣ) {m : ℕ} (hm : m ≠ 0)
    (hu : u^m=1) (hp : IsTopologicallyNilpotent (p:R)) :
    IsTopologicallyNilpotent ((u:R)*(p:R)^2) ∧
    IsTopologicallyNilpotent ((p^2/u:Rˣ):R) := by
  have hval : (u:R)^m=1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hu
  have hi : ((u⁻¹:Rˣ):R)^m=1 := by
    have h : (u⁻¹)^m=1 := by rw [inv_pow, hu, inv_one]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val h
  constructor
  · exact JacobiParameter.root_mul_nilpotent _ _ hm hval (hp.pow (by decide))
  · have h := JacobiParameter.root_mul_nilpotent _ _ hm hi (hp.pow (by decide : 2 ≠ 0))
    simpa only [div_eq_mul_inv, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm] using h

theorem isUnit_jacobi (p u : Rˣ) {m : ℕ} (hm : m ≠ 0)
    (hu : u^m=1) (hp : IsTopologicallyNilpotent (p:R))
    (hden : IsUnit (1-(u:R))) : IsUnit (ThetaAddition.jacobi p u) := by
  obtain ⟨hplus,hminus⟩ := shifted_tails_nilpotent p u hm hu hp
  exact JacobiFirstJet.isUnit_jacobi_of_shift p u hp hplus hden hminus

/-- Actual square-root torsion anchors under an arbitrary coefficient map. -/
theorem isUnit_jacobi_mapped_squareRoot {K : Type*} [Field K] [CharZero K]
    (f : K →+* R) (w a : K) (hw : w^4-w^2+1=0) (ha : a^2=w)
    (j : ℕ) (hj : 1 ≤ j) (hj12 : j < 12) (p u : Rˣ)
    (hu : (u:R)=f a^j) (hp : IsTopologicallyNilpotent (p:R)) :
    IsUnit (ThetaAddition.jacobi p u) := by
  have ho : u^24=1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, hu]
    rw [← pow_mul, Nat.mul_comm j 24, pow_mul, ← map_pow,
      TwelfthRootJacobiArguments.squareRoot_pow_twentyFour w a hw ha, map_one, one_pow]
  apply isUnit_jacobi p u (by decide : 24 ≠ 0) ho hp
  rw [hu]
  exact TwelfthRootJacobiArguments.mapped_squareRoot_denominator_isUnit f w a hw ha j hj hj12

end KanadeRussell.Infra.JacobiFiniteOrderArguments
