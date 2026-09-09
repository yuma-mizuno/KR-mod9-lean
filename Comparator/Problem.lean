import Mathlib
import RogersRamanujan

/-!
The main challenge is the three Kanade–Russell identities modulo nine:
`KR₁`, `KR₂`, and `KR₃` assert the full double-sum/product identities with convergence.
The initial product coefficients are auxiliary checks of the definitions.
All formulas are stated independently of the production proof.
-/
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

/-! Main statements: the three full Kanade–Russell identities. -/
def KR₁ : Prop := HasSum (summand 0 0) product₁
def KR₂ : Prop := HasSum (summand 1 3) product₂
def KR₃ : Prop := HasSum (summand 2 3) product₃

/-! Auxiliary checks: coefficients of each product in degrees 0, 1, and 2. -/
def Product₁InitialCoefficients : Prop :=
  PowerSeries.coeff 0 product₁ = 1 ∧
  PowerSeries.coeff 1 product₁ = 1 ∧
  PowerSeries.coeff 2 product₁ = 1

def Product₂InitialCoefficients : Prop :=
  PowerSeries.coeff 0 product₂ = 1 ∧
  PowerSeries.coeff 1 product₂ = 0 ∧
  PowerSeries.coeff 2 product₂ = 1

def Product₃InitialCoefficients : Prop :=
  PowerSeries.coeff 0 product₃ = 1 ∧
  PowerSeries.coeff 1 product₃ = 0 ∧
  PowerSeries.coeff 2 product₃ = 0

end KRChallenge
