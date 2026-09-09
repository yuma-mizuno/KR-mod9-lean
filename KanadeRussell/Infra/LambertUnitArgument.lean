import KanadeRussell.Infra.JacobiKernelParameter
set_option backward.isDefEq.respectTransparency false

/-! Lambert tails with an invertible initial denominator and a nilpotent tail. -/
open PowerSeries PowerSeries.WithPiTopology
namespace KanadeRussell.Infra.JacobiParameter
open JacobiJets
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]

theorem summable_lambertTail_of_shift (a Q : R)
    (hQ : IsTopologicallyNilpotent Q) (ha : IsTopologicallyNilpotent (a*Q)) :
    Summable (fun n : ℕ => a*Q^n*bInv (1-a*Q^n)^2) := by
  apply (summable_nat_add_iff 1).mp
  have hs := summable_lambertTail (a*Q) Q ha hQ
  apply hs.congr
  intro n
  have he : a*Q^(n+1) = (a*Q)*Q^n := by rw [pow_succ]; ring
  rw [he]

theorem lambertTail_split (a Q : R)
    (hQ : IsTopologicallyNilpotent Q) (ha : IsTopologicallyNilpotent (a*Q)) :
    lambertTail a Q = a*bInv (1-a)^2+lambertTail (a*Q) Q := by
  have hs := summable_lambertTail_of_shift a Q hQ ha
  rw [lambertTail, hs.tsum_eq_zero_add]
  simp only [pow_zero, mul_one]
  congr 1
  apply tsum_congr
  intro n
  have he : a*Q^(n+1) = (a*Q)*Q^n := by rw [pow_succ]; ring
  rw [he]

theorem units_lambertTail_of_shift (a Q : R)
    (hQ : IsTopologicallyNilpotent Q) (ha : IsTopologicallyNilpotent (a*Q))
    (h0 : IsUnit (1-a)) : ∀ n : ℕ, IsUnit (1-a*Q^n) := by
  intro n
  cases n with
  | zero => simpa using h0
  | succ n =>
    have he : a*Q^(n+1) = (a*Q)*Q^n := by rw [pow_succ]; ring
    rw [he]
    exact (ha.mul_pow hQ (n:=n)).isUnit_one_sub

omit [IsUniformAddGroup R] [CompleteSpace R] [T2Space R] in
theorem root_mul_nilpotent (w Q : R) {m : ℕ} (hm : m ≠ 0) (hw : w^m = 1)
    (hQ : IsTopologicallyNilpotent Q) : IsTopologicallyNilpotent (w*Q) := by
  apply IsTopologicallyNilpotent.of_pow (n:=m) _ hm
  rw [mul_pow, hw, one_mul]
  exact hQ.pow hm

/-- This version applies at a root of unity even though its initial argument is not nilpotent. -/
theorem kernel_coefficients_of_shift (p u : Rˣ) (Z : (PowerSeries R)ˣ)
    (hp : IsTopologicallyNilpotent (p:R)) (hZ : constantCoeff (Z:PowerSeries R) = 1)
    (hu : IsTopologicallyNilpotent ((u:R)*(p:R)^2)) (hu0 : IsUnit (1-(u:R)))
    (hv : IsTopologicallyNilpotent (((p^2/u:Rˣ):R)*(p:R)^2))
    (hv0 : IsUnit (1-((p^2/u:Rˣ):R))) :
    coeff 1 (ThetaAddition.kernel (unitC p) (unitC u) Z) = 0 ∧
    coeff 2 (ThetaAddition.kernel (unitC p) (unitC u) Z) =
      -(ThetaAddition.jacobi p u)^2*ellipticLambert p u*(coeff 1 (Z:PowerSeries R))^2 := by
  have hp2 : IsTopologicallyNilpotent ((p:R)^2) := hp.pow (by decide)
  exact kernel_coefficients p u Z hp hZ
    (summable_lambertTail_of_shift _ _ hp2 hu) (units_lambertTail_of_shift _ _ hp2 hu hu0)
    (summable_lambertTail_of_shift _ _ hp2 hv) (units_lambertTail_of_shift _ _ hp2 hv hv0)

end KanadeRussell.Infra.JacobiParameter
