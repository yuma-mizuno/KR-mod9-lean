import KanadeRussell.Representation.RootCoefficientFunction
import KanadeRussell.Representation.RootReflectionAlgebra

/-! Cancellation of an invariant factor with constant coefficient one, using
finite coefficient convolution and descent on paired total degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

private theorem totalDegree_pos_of_nonneg_ne_zero (alpha : RootCoefficients)
    (ha : ∀ i, 0 ≤ alpha i) (hne : alpha ≠ 0) : 0 < totalDegree alpha := by
  have hex : ∃ i, alpha i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => ha j)
    ⟨i, Finset.mem_univ i, lt_of_le_of_ne (ha i) (Ne.symm hi)⟩

/-- Invariance of a product and of its constant-one factor forces invariance
of the remaining actual power series. No infinite-series Weyl action is used. -/
theorem rootCoefficient_invariant_of_mul
    (L : RootCoefficients ≃+ RootCoefficients) (U F : MvPowerSeries (Fin 3) K)
    (hzero : rootCoefficient U 0 = 1)
    (hU : ∀ alpha, rootCoefficient U (L alpha) = rootCoefficient U alpha)
    (hUF : ∀ beta, rootCoefficient (U*F) (L beta) = rootCoefficient (U*F) beta)
    (beta : RootCoefficients) : rootCoefficient F (L beta) = rootCoefficient F beta := by
  classical
  let degree (gamma : RootCoefficients) :=
    max (totalDegree gamma).toNat (totalDegree (L gamma)).toNat
  have heq : ∀ n : ℕ, ∀ gamma : RootCoefficients, degree gamma = n →
      rootCoefficient F (L gamma) = rootCoefficient F gamma := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro gamma hdegree
      let f : RootCoefficients → K := fun alpha =>
        rootCoefficient U alpha * rootCoefficient F (L (gamma-alpha))
      let g : RootCoefficients → K := fun alpha =>
        rootCoefficient U alpha * rootCoefficient F (gamma-alpha)
      have hf_eq : f = (fun alpha => rootCoefficient U alpha *
          rootCoefficient F (L gamma-alpha)) ∘ L := by
        funext alpha
        simp only [f, Function.comp_apply, map_sub, hU]
      have hf : (Function.support f).Finite := by
        rw [hf_eq, Function.support_comp_eq_preimage]
        exact (rootCoefficient_convolution_finite U F (L gamma)).preimage L.injective.injOn
      have hg : (Function.support g).Finite := rootCoefficient_convolution_finite U F gamma
      have hs : (∑ᶠ alpha, f alpha) = ∑ᶠ alpha, g alpha := by
        rw [hf_eq]
        simp only [Function.comp_apply]
        rw [finsum_comp (fun alpha => L alpha) L.bijective (g := fun alpha => rootCoefficient U alpha *
          rootCoefficient F (L gamma-alpha))]
        exact (rootCoefficient_mul U F (L gamma)).symm.trans
          ((hUF gamma).trans (rootCoefficient_mul U F gamma))
      have hterms : ∀ alpha, alpha ≠ 0 → f alpha-g alpha = 0 := by
        intro alpha hne
        by_cases ha : rootCoefficient U alpha = 0
        · simp [f, g, ha]
        have ha0 := rootCoefficient_nonneg_of_ne_zero U alpha ha
        have hLa : rootCoefficient U (L alpha) ≠ 0 := by rwa [hU]
        have hLa0 := rootCoefficient_nonneg_of_ne_zero U (L alpha) hLa
        have hLne : L alpha ≠ 0 := by
          intro hz
          apply hne
          exact L.injective (hz.trans (map_zero L).symm)
        have hapos := totalDegree_pos_of_nonneg_ne_zero alpha ha0 hne
        have hLapos := totalDegree_pos_of_nonneg_ne_zero (L alpha) hLa0 hLne
        by_cases hboth : rootCoefficient F (gamma-alpha) = 0 ∧
            rootCoefficient F (L (gamma-alpha)) = 0
        · simp only [f, g, hboth.1, hboth.2, mul_zero, sub_self]
        have hnonneg : 0 ≤ totalDegree (gamma-alpha) ∨
            0 ≤ totalDegree (L (gamma-alpha)) := by
          push Not at hboth
          by_cases hc : rootCoefficient F (gamma-alpha) = 0
          · right
            exact Finset.sum_nonneg (fun i _ => rootCoefficient_nonneg_of_ne_zero F _ (hboth hc) i)
          · left
            exact Finset.sum_nonneg (fun i _ => rootCoefficient_nonneg_of_ne_zero F _ hc i)
        have hsub : totalDegree (gamma-alpha) = totalDegree gamma-totalDegree alpha := by
          simp [totalDegree, Finset.sum_sub_distrib]
        have hLsub : totalDegree (L (gamma-alpha)) = totalDegree (L gamma)-totalDegree (L alpha) := by
          simp [map_sub, totalDegree, Finset.sum_sub_distrib]
        have hlt : degree (gamma-alpha) < n := by
          rw [← hdegree]
          unfold degree
          have hleft := le_max_left (totalDegree gamma).toNat (totalDegree (L gamma)).toNat
          have hright := le_max_right (totalDegree gamma).toNat (totalDegree (L gamma)).toNat
          have hpos : 0 < max (totalDegree gamma).toNat (totalDegree (L gamma)).toNat := by
            rcases hnonneg with hh | hh <;> omega
          rw [max_lt_iff]
          constructor <;> omega
        have hsmall := ih (degree (gamma-alpha)) hlt (gamma-alpha) rfl
        simp only [f, g, hsmall, sub_self]
      have hsumzero : (∑ᶠ alpha, (f alpha - g alpha)) = 0 := by
        rw [finsum_sub_distrib hf hg, hs, sub_self]
      rw [finsum_eq_single _ 0 hterms] at hsumzero
      simpa only [f, g, sub_zero, hzero, one_mul, sub_eq_zero] using hsumzero
  exact heq (degree beta) beta rfl

end KanadeRussell.Representation
