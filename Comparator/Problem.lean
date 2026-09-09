import Mathlib

/-!
The main challenge is the three Kanade–Russell identities modulo nine:
`KR₁`, `KR₂`, and `KR₃` assert the full double-sum/product identities with convergence.
The initial product coefficients are auxiliary checks of the definitions.
All formulas use Mathlib definitions and are independent of the production proof.
`Ring.inverse` is the multiplicative inverse of a unit, and is zero on nonunits.
-/
set_option autoImplicit false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KRChallenge

/-- The formal variable in the ring of integer power series. -/
noncomputable def q : PowerSeries ℤ := PowerSeries.X

/-- The summand q^(m²+3mn+3n²+am+bn)/((q;q)_m (q³;q³)_n),
with both finite denominator products written explicitly. -/
noncomputable def summand (a b : ℕ) (mn : ℕ × ℕ) : PowerSeries ℤ :=
  q^(mn.1^2+3*mn.1*mn.2+3*mn.2^2+a*mn.1+b*mn.2) *
    Ring.inverse (∏ j ∈ Finset.range mn.1, (1-q^(j+1))) *
    Ring.inverse (∏ j ∈ Finset.range mn.2, (1-q^(3*(j+1))))

/-- The reciprocal of the four Euler products on progressions 9n+rᵢ, n ≥ 0. -/
noncomputable def reciprocalProduct (r₁ r₂ r₃ r₄ : ℕ) : PowerSeries ℤ :=
  Ring.inverse (∏' n : ℕ, (1-q^(9*n+r₁))*(1-q^(9*n+r₂))*
    (1-q^(9*n+r₃))*(1-q^(9*n+r₄)))

/-- The first KR product, with residues 1, 3, 6, 8 modulo nine. -/
noncomputable def product₁ : PowerSeries ℤ := reciprocalProduct 1 3 6 8
/-- The second KR product, with residues 2, 3, 6, 7 modulo nine. -/
noncomputable def product₂ : PowerSeries ℤ := reciprocalProduct 2 3 6 7
/-- The third KR product, with residues 3, 4, 5, 6 modulo nine. -/
noncomputable def product₃ : PowerSeries ℤ := reciprocalProduct 3 4 5 6

/-! Main statements: the three full Kanade–Russell identities. -/
/-- The first KR double sum converges to the first reciprocal product. -/
def KR₁ : Prop := HasSum (summand 0 0) product₁
/-- The second KR double sum converges to the second reciprocal product. -/
def KR₂ : Prop := HasSum (summand 1 3) product₂
/-- The third KR double sum converges to the third reciprocal product. -/
def KR₃ : Prop := HasSum (summand 2 3) product₃

/-! Auxiliary checks: coefficients of each product in degrees 0, 1, and 2. -/
/-- The first product has coefficients (1, 1, 1) in degrees (0, 1, 2). -/
def Product₁InitialCoefficients : Prop :=
  PowerSeries.coeff 0 product₁ = 1 ∧
  PowerSeries.coeff 1 product₁ = 1 ∧
  PowerSeries.coeff 2 product₁ = 1

/-- The second product has coefficients (1, 0, 1) in degrees (0, 1, 2). -/
def Product₂InitialCoefficients : Prop :=
  PowerSeries.coeff 0 product₂ = 1 ∧
  PowerSeries.coeff 1 product₂ = 0 ∧
  PowerSeries.coeff 2 product₂ = 1

/-- The third product has coefficients (1, 0, 0) in degrees (0, 1, 2). -/
def Product₃InitialCoefficients : Prop :=
  PowerSeries.coeff 0 product₃ = 1 ∧
  PowerSeries.coeff 1 product₃ = 0 ∧
  PowerSeries.coeff 2 product₃ = 0

end KRChallenge
