import Comparator.Submission

/-! Proofs of the main KR identities and the auxiliary product coefficient checks.
The definitions come from Comparator.Problem; this module does not import Challenge.lean. -/
namespace Challenge

/-! ## Main challenge: the three Kanade–Russell identities -/

theorem kr₁ : KRChallenge.KR₁ := KRChallenge.Submitted.kr₁

theorem kr₂ : KRChallenge.KR₂ := KRChallenge.Submitted.kr₂

theorem kr₃ : KRChallenge.KR₃ := KRChallenge.Submitted.kr₃

/-! ## Auxiliary checks: initial product coefficients -/

theorem product₁_initial_coefficients : KRChallenge.Product₁InitialCoefficients :=
  KRChallenge.Submitted.product₁_initial_coefficients

theorem product₂_initial_coefficients : KRChallenge.Product₂InitialCoefficients :=
  KRChallenge.Submitted.product₂_initial_coefficients

theorem product₃_initial_coefficients : KRChallenge.Product₃InitialCoefficients :=
  KRChallenge.Submitted.product₃_initial_coefficients

end Challenge
