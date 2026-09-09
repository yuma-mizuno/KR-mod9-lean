import Comparator.Submission

/-! Solution to the four independently stated Comparator targets.
This module never imports Challenge.lean or its proof placeholders. -/
namespace Challenge

theorem kr₁ : KRChallenge.KR₁ := KRChallenge.Submitted.kr₁

theorem kr₂ : KRChallenge.KR₂ := KRChallenge.Submitted.kr₂

theorem kr₃ : KRChallenge.KR₃ := KRChallenge.Submitted.kr₃

theorem constantCoefficientNontriviality : KRChallenge.ConstantCoefficientNontriviality :=
  KRChallenge.Submitted.constantCoefficientNontriviality

end Challenge
