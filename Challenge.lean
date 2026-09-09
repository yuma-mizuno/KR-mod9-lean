import Mathlib
import RogersRamanujan

/-! Independent statement of the three Kanade–Russell identities modulo nine.
The formulas below are independent of the production proof. The four proof placeholders at the end are the complete challenge. -/
set_option autoImplicit false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KRChallenge

noncomputable def q : PowerSeries ℤ := PowerSeries.X

noncomputable def summand (a b : ℕ) (mn : ℕ × ℕ) : PowerSeries ℤ :=
  q^(mn.1^2+3*mn.1*mn.2+3*mn.2^2+a*mn.1+b*mn.2) *
    bInv (∏ j ∈ Finset.range mn.1, (1-q^(j+1))) *
    bInv (∏ j ∈ Finset.range mn.2, (1-q^(3*(j+1))))

noncomputable def source (a b : ℕ) : PowerSeries ℤ := ∑' mn, summand a b mn

noncomputable def reciprocalProduct (r₁ r₂ r₃ r₄ : ℕ) : PowerSeries ℤ :=
  bInv (∏' n : ℕ, (1-q^(9*n+r₁))*(1-q^(9*n+r₂))*
    (1-q^(9*n+r₃))*(1-q^(9*n+r₄)))

noncomputable def product₁ : PowerSeries ℤ := reciprocalProduct 1 3 6 8
noncomputable def product₂ : PowerSeries ℤ := reciprocalProduct 2 3 6 7
noncomputable def product₃ : PowerSeries ℤ := reciprocalProduct 3 4 5 6

def KR₁ : Prop := HasSum (summand 0 0) product₁
def KR₂ : Prop := HasSum (summand 1 3) product₂
def KR₃ : Prop := HasSum (summand 2 3) product₃

def ConstantCoefficientNontriviality : Prop :=
  PowerSeries.coeff 0 (source 0 0) ≠ 0 ∧
  PowerSeries.coeff 0 (source 1 3) ≠ 0 ∧
  PowerSeries.coeff 0 (source 2 3) ≠ 0 ∧
  PowerSeries.coeff 0 product₁ ≠ 0 ∧
  PowerSeries.coeff 0 product₂ ≠ 0 ∧
  PowerSeries.coeff 0 product₃ ≠ 0

end KRChallenge

namespace Challenge

theorem kr₁ : KRChallenge.KR₁ := by
  sorry

theorem kr₂ : KRChallenge.KR₂ := by
  sorry

theorem kr₃ : KRChallenge.KR₃ := by
  sorry

theorem constantCoefficientNontriviality : KRChallenge.ConstantCoefficientNontriviality := by
  sorry

end Challenge
