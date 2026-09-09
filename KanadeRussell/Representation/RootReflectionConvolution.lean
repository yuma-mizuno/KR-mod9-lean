import KanadeRussell.Representation.RootReflectionAlgebra
import Mathlib.Algebra.BigOperators.Finprod

/-! Reflection of convolution on integer root coefficients. -/
set_option autoImplicit false
namespace KanadeRussell.Representation.AffineWeightLattice
variable {K : Type*} [Field K]

noncomputable def rootFunctionConvolution (a b : RootCoefficients → K)
    (beta : RootCoefficients) : K := ∑ᶠ alpha, a alpha * b (beta-alpha)

theorem rootFunctionConvolution_antisymmetric (lambda mu : RootCoefficients)
    (i : Fin 3) (a b : RootCoefficients → K)
    (ha : ∀ alpha, a (simpleReflection lambda i alpha) = a alpha)
    (hb : ∀ alpha, b (simpleReflection mu i alpha) = -b alpha)
    (beta : RootCoefficients) :
    rootFunctionConvolution a b (simpleReflection (lambda+mu) i beta) =
      -rootFunctionConvolution a b beta := by
  unfold rootFunctionConvolution
  calc
    (∑ᶠ alpha, a alpha * b (simpleReflection (lambda+mu) i beta-alpha)) =
        ∑ᶠ alpha, a (simpleReflection lambda i alpha) *
          b (simpleReflection (lambda+mu) i beta-simpleReflection lambda i alpha) :=
      (finsum_comp_equiv (rootReflectionEquiv lambda i)).symm
    _ = -(∑ᶠ alpha, a alpha*b (beta-alpha)) := by
      simp_rw [simpleReflection_difference, ha, hb, mul_neg]
      exact finsum_neg_distrib (fun alpha => a alpha * b (beta-alpha))

end KanadeRussell.Representation.AffineWeightLattice
