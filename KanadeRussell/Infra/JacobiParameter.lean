import KanadeRussell.Infra.JacobiJets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Symmetric Jacobi coefficients for an arbitrary formal unit parameter. -/
open PowerSeries PowerSeries.WithPiTopology Filter Topology
open scoped QTheory
namespace KanadeRussell.Infra.JacobiParameter
open SecondCoefficient JacobiJets
variable {R : Type*} [CommRing R]

theorem inverse_coefficients (Z : (PowerSeries R)ˣ) (hZ : constantCoeff (Z:PowerSeries R) = 1) :
    constantCoeff (↑Z⁻¹ : PowerSeries R) = 1 ∧
    coeff 1 (↑Z⁻¹ : PowerSeries R) = -coeff 1 (Z:PowerSeries R) ∧
    coeff 2 (↑Z⁻¹ : PowerSeries R) = (coeff 1 (Z:PowerSeries R))^2-coeff 2 (Z:PowerSeries R) := by
  have h0 := congrArg constantCoeff (Units.mul_inv Z)
  have hi0 : constantCoeff (↑Z⁻¹ : PowerSeries R) = 1 := by
    simpa only [map_mul, hZ, one_mul, map_one] using h0
  have h1 := congrArg (coeff 1) (Units.mul_inv Z)
  have hi1 : coeff 1 (↑Z⁻¹ : PowerSeries R) = -coeff 1 (Z:PowerSeries R) := by
    simp only [coeff_one_mul, hZ, hi0, mul_one, coeff_one, if_neg (by decide : (1:ℕ) ≠ 0)] at h1
    linear_combination h1
  refine ⟨hi0,hi1,?_⟩
  have h2 := congrArg (coeff 2) (Units.mul_inv Z)
  simp only [coeff_two_mul, hZ, hi0, hi1, one_mul, mul_one, coeff_one,
    if_neg (by decide : (2:ℕ) ≠ 0)] at h2
  linear_combination h2

noncomputable def pair (a : R) (Z : (PowerSeries R)ˣ) : PowerSeries R :=
  (1-PowerSeries.C a*(Z:PowerSeries R))*(1-PowerSeries.C a*(↑Z⁻¹:PowerSeries R))

theorem pair_coefficients (a : R) (Z : (PowerSeries R)ˣ)
    (hZ : constantCoeff (Z:PowerSeries R) = 1) :
    constantCoeff (pair a Z) = (1-a)^2 ∧ coeff 1 (pair a Z) = 0 ∧
      coeff 2 (pair a Z) = -a*(coeff 1 (Z:PowerSeries R))^2 := by
  obtain ⟨h0,h1,h2⟩ := inverse_coefficients Z hZ
  constructor
  · simp [pair, hZ, h0, pow_two]
  constructor
  · simp [pair, coeff_one_mul, hZ, h0, h1]
  · simp [pair, coeff_two_mul, hZ, h0, h1, h2]
    ring

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]

noncomputable def pochPair (a Q : R) (Z : (PowerSeries R)ˣ) : PowerSeries R :=
  (PowerSeries.C a*(Z:PowerSeries R); PowerSeries.C Q)_∞ * (PowerSeries.C a*(↑Z⁻¹:PowerSeries R); PowerSeries.C Q)_∞

omit [T2Space R] in
theorem hasProd_pair (a Q : R) (Z : (PowerSeries R)ˣ) (hQ : IsTopologicallyNilpotent Q) :
    HasProd (fun n : ℕ => pair (a*Q^n) Z) (pochPair a Q Z) := by
  have hCQ : IsTopologicallyNilpotent (PowerSeries.C Q) := hQ.map continuous_C
  apply (HasProd.mul (hasProd_qPochhammerInf (a:=PowerSeries.C a*(Z:PowerSeries R)) hCQ)
    (hasProd_qPochhammerInf (a:=PowerSeries.C a*(↑Z⁻¹:PowerSeries R)) hCQ)).congr_fun
  intro n
  simp only [pair, map_mul, map_pow]
  ring

/-- Only convergence of the Lambert terms and the stated units are needed. -/
theorem pochPair_coefficients (a Q : R) (Z : (PowerSeries R)ˣ)
    (hQ : IsTopologicallyNilpotent Q) (hZ : constantCoeff (Z:PowerSeries R) = 1)
    (hs : Summable (fun n : ℕ => a*Q^n*bInv (1-a*Q^n)^2))
    (hu : ∀ n : ℕ, IsUnit (1-a*Q^n)) :
    coeff 1 (pochPair a Q Z) = 0 ∧
    coeff 2 (pochPair a Q Z) = -constantCoeff (pochPair a Q Z)*
      lambertTail a Q*(coeff 1 (Z:PowerSeries R))^2 := by
  have hd := hs.hasSum.neg.mul_right ((coeff 1 (Z:PowerSeries R))^2)
  have hh := coeff_hasProd (hasProd_pair a Q Z hQ) hd
    (fun n => (pair_coefficients (a*Q^n) Z hZ).2.1)
  have hn (n : ℕ) : coeff 2 (pair (a*Q^n) Z) = constantCoeff (pair (a*Q^n) Z)*
      (-(a*Q^n*bInv (1-a*Q^n)^2)*(coeff 1 (Z:PowerSeries R))^2) := by
    rw [(pair_coefficients (a*Q^n) Z hZ).1, (pair_coefficients (a*Q^n) Z hZ).2.2]
    have he := (hu n).mul_bInv_cancel
    calc
      -(a*Q^n)*(coeff 1 (Z:PowerSeries R))^2 =
          -(a*Q^n)*(coeff 1 (Z:PowerSeries R))^2*((1-a*Q^n)*bInv (1-a*Q^n))^2 := by rw [he]; ring
      _ = _ := by ring
  simpa only [lambertTail, mul_neg, neg_mul, mul_assoc] using hh hn

theorem pochPair_constant (a Q : R) (Z : (PowerSeries R)ˣ)
    (hQ : IsTopologicallyNilpotent Q) (hZ : constantCoeff (Z:PowerSeries R) = 1) :
    constantCoeff (pochPair a Q Z) = (a;Q)_∞^2 := by
  have hCQ : IsTopologicallyNilpotent (PowerSeries.C Q) := hQ.map continuous_C
  have hi := (inverse_coefficients Z hZ).1
  simp only [pochPair, map_mul, map_qPochhammerInf constantCoeff (continuous_constantCoeff R) _ hCQ,
    constantCoeff_C, hZ, hi, mul_one, pow_two]

end KanadeRussell.Infra.JacobiParameter
