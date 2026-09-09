import KanadeRussell.Representation.WeylWeightReflection

/-! Additive and affine reflection identities for root coefficients. -/
set_option autoImplicit false
namespace KanadeRussell.Representation.AffineWeightLattice

theorem simpleReflection_add_weights (lambda mu : RootCoefficients) (i : Fin 3)
    (alpha beta : RootCoefficients) :
    simpleReflection (lambda+mu) i (alpha+beta) =
      simpleReflection lambda i alpha + simpleReflection mu i beta := by
  funext j
  by_cases hji : j=i
  · subst j
    simp only [simpleReflection, Pi.add_apply, Pi.single_eq_same, weightLabels,
      mul_add, Finset.sum_add_distrib]
    ring
  · simp [simpleReflection, hji]

@[simp] theorem simpleReflection_zero_zero (i : Fin 3) :
    simpleReflection 0 i 0 = 0 := by
  simp [simpleReflection, weightLabels]

theorem simpleReflection_zero_add (i : Fin 3) (alpha beta : RootCoefficients) :
    simpleReflection 0 i (alpha+beta) = simpleReflection 0 i alpha + simpleReflection 0 i beta := by
  simpa only [add_zero] using simpleReflection_add_weights 0 0 i alpha beta

def linearRootReflection (i : Fin 3) : RootCoefficients ≃+ RootCoefficients where
  toFun := simpleReflection 0 i
  invFun := simpleReflection 0 i
  left_inv := simpleReflection_involutive 0 i
  right_inv := simpleReflection_involutive 0 i
  map_add' := simpleReflection_zero_add i

@[simp] theorem linearRootReflection_apply (i : Fin 3) (beta : RootCoefficients) :
    linearRootReflection i beta = simpleReflection 0 i beta := rfl

theorem simpleReflection_zero_sum {ι : Type*} (i : Fin 3) (s : Finset ι)
    (f : ι → RootCoefficients) :
    simpleReflection 0 i (∑ j ∈ s, f j) = ∑ j ∈ s, simpleReflection 0 i (f j) :=
  map_sum (linearRootReflection i) f s

def rootReflectionEquiv (lambda : RootCoefficients) (i : Fin 3) :
    RootCoefficients ≃ RootCoefficients where
  toFun := simpleReflection lambda i
  invFun := simpleReflection lambda i
  left_inv := simpleReflection_involutive lambda i
  right_inv := simpleReflection_involutive lambda i

@[simp] theorem rootReflectionEquiv_apply (lambda : RootCoefficients) (i : Fin 3)
    (beta : RootCoefficients) : rootReflectionEquiv lambda i beta = simpleReflection lambda i beta := rfl

theorem simpleReflection_difference (lambda mu : RootCoefficients) (i : Fin 3)
    (alpha beta : RootCoefficients) :
    simpleReflection (lambda+mu) i beta - simpleReflection lambda i alpha =
      simpleReflection mu i (beta-alpha) := by
  have h := simpleReflection_add_weights lambda mu i alpha (beta-alpha)
  have hab : alpha+(beta-alpha) = beta := by abel
  rw [hab] at h
  rw [h]
  abel

theorem simpleReflection_rho_eq (i : Fin 3) (beta : RootCoefficients) :
    simpleReflection (fun _ => 1) i beta = simpleReflection 0 i beta + Pi.single i 1 := by
  funext j
  by_cases hji : j=i
  · subst j
    simp only [simpleReflection, Pi.add_apply, Pi.single_eq_same, weightLabels, Pi.zero_apply]
    ring
  · simp [simpleReflection, hji]

theorem simpleReflection_rho_sub_simple (i : Fin 3) (beta : RootCoefficients) :
    simpleReflection (fun _ => 1) i beta - Pi.single i 1 = simpleReflection 0 i beta := by
  rw [simpleReflection_rho_eq]
  abel

theorem simpleReflection_zero_rho (i : Fin 3) (beta : RootCoefficients) :
    simpleReflection 0 i (simpleReflection (fun _ => 1) i beta) = beta-Pi.single i 1 := by
  have h := simpleReflection_rho_eq i (simpleReflection (fun _ => 1) i beta)
  rw [simpleReflection_twice] at h
  exact eq_sub_iff_add_eq.mpr h.symm

end KanadeRussell.Representation.AffineWeightLattice
