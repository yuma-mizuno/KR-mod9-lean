import KanadeRussell.Representation.PrincipalRootComplementEuler
import KanadeRussell.Representation.PrincipalActiveRootReflection
import KanadeRussell.Representation.RootEulerSubsetCoefficients
import KanadeRussell.Representation.RootReflectionAlgebra

/-! Reflection symmetry of the simple-root complement, proved on finite
reflection-invariant sets of actual root slots before passing to coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open AffineWeightLattice
variable {K : Type*} [Field K]

theorem positiveModeOccupation_eq_simple_iff (i : Fin 3) (n : ℕ) (r : Fin 3) :
    positiveModeOccupation n r = Pi.single i 1 ↔ n = 0 ∧ r = i := by
  constructor
  · intro h
    have hd := congrArg totalDegree h
    rw [positiveModeOccupation_degree] at hd
    have hn : n = 0 := by
      have hs : totalDegree (Pi.single i (1 : ℤ)) = 1 := by
        simp [totalDegree]
      rw [hs] at hd
      omega
    subst n
    refine ⟨rfl, ?_⟩
    exact (by decide : ∀ i r : Fin 3,
      positiveModeOccupation 0 r = Pi.single i 1 → r = i) i r h
  · rintro ⟨rfl, hri⟩
    subst r
    exact (by decide : ∀ i : Fin 3, positiveModeOccupation 0 i = Pi.single i 1) i

noncomputable def principalRootComplementPrefix (i : Fin 3) (B : ℕ) :
    Finset (PrincipalActiveRootComplement i) := by
  classical
  exact (((Finset.range B).product (Finset.univ : Finset (Fin 3))).subtype
    (fun p => principalWeightSlotActive (positiveModeResidue p.1) p.2)).subtype
      (fun p => positiveModeOccupation p.val.1 p.val.2 ≠ Pi.single i 1)

@[simp] theorem mem_principalRootComplementPrefix (i : Fin 3) (B : ℕ)
    (p : PrincipalActiveRootComplement i) :
    p ∈ principalRootComplementPrefix i B ↔ p.val.val.1 < B := by
  classical
  simp [principalRootComplementPrefix]

noncomputable def principalRootComplementExponent (i : Fin 3) (p : PrincipalActiveRootComplement i) :
    Fin 3 →₀ ℕ := positiveModeExponent p.val.val.1 p.val.val.2

theorem principalRootComplementPartial_eq_prefix (i : Fin 3) (B : ℕ) :
    principalRootComplementPartial (K := K) i B =
      ∏ p ∈ principalRootComplementPrefix i B,
        (1-MvPowerSeries.monomial (principalRootComplementExponent i p) 1) := by
  classical
  unfold principalRootComplementPrefix principalRootComplementExponent
  rw [Finset.prod_subtype_eq_prod_filter (fun p :
    {p : ℕ × Fin 3 // principalWeightSlotActive (positiveModeResidue p.1) p.2} =>
    (1-MvPowerSeries.monomial (positiveModeExponent p.val.1 p.val.2) (1 : K))),
    Finset.prod_filter]
  rw [Finset.prod_subtype_eq_prod_filter (fun p : ℕ × Fin 3 =>
    if positiveModeOccupation p.1 p.2 ≠ Pi.single i 1 then
      (1-MvPowerSeries.monomial (positiveModeExponent p.1 p.2) (1 : K)) else 1),
    Finset.prod_filter]
  rw [Finset.product_eq_sprod]
  rw [Finset.prod_product (Finset.range B) (Finset.univ : Finset (Fin 3))
    (fun a : ℕ × Fin 3 =>
      if principalWeightSlotActive (positiveModeResidue a.1) a.2 then
        if positiveModeOccupation a.1 a.2 ≠ Pi.single i 1 then
          (1-MvPowerSeries.monomial (positiveModeExponent a.1 a.2) (1 : K)) else 1
      else 1)]
  unfold principalRootComplementPartial
  apply Finset.prod_congr rfl
  intro n hn
  apply Finset.prod_congr rfl
  intro r hr
  simp only [principalRootComplementFactor, principalRootEulerFactor]
  split_ifs <;> simp_all [positiveModeOccupation_eq_simple_iff]

theorem principalActiveRootReflection_twice (i : Fin 3)
    (p : PrincipalActiveRootComplement i) :
    principalActiveRootReflectionEquiv i (principalActiveRootReflectionEquiv i p) = p := by
  let E := principalRootComplementEquiv i
  let R := principalRootSlotReflectionEquiv i
  change E (R (E.symm (E (R (E.symm p))))) = p
  rw [E.symm_apply_apply]
  have hR (q : {p : ℕ × Fin 28 // p ≠ (0, principalRootSimpleIndex i)}) : R (R q) = q := by
    apply Subtype.ext
    exact principalRootSlotReflection_twice i q.val q.property
  rw [hR, E.apply_symm_apply]

theorem principalRootComplementEuler_agree_finite (i : Fin 3) (e : Fin 3 →₀ ℕ)
    (S : Finset (PrincipalActiveRootComplement i))
    (hS : principalRootComplementPrefix i (rootExponentDegree e) ⊆ S) :
    RootCoeffAgree e (principalRootComplementEuler (K := K) i)
      (∏ p ∈ S, (1-MvPowerSeries.monomial (principalRootComplementExponent i p) 1)) := by
  classical
  have hD := principalRootComplementEuler_agree (K := K) i e (rootExponentDegree e) le_rfl
  rw [principalRootComplementPartial_eq_prefix] at hD
  apply hD.trans
  apply RootCoeffAgree.symm
  apply rootCoeffAgree_eulerProduct_of_subset _ S _ e hS
  intro p hp hnot hle
  apply hnot
  apply (mem_principalRootComplementPrefix i _ p).mpr
  exact positiveModeExponent_le_degree e p.val.val.1 p.val.val.2 hle

theorem rootCoefficient_principalRootComplementEuler_finite (i : Fin 3)
    (beta : RootCoefficients) (S : Finset (PrincipalActiveRootComplement i))
    (hS : principalRootComplementPrefix i
      (rootExponentDegree (exponentOfRootCoefficients beta)) ⊆ S) :
    rootCoefficient (principalRootComplementEuler (K := K) i) beta =
      rootCoefficient
        (∏ p ∈ S, (1-MvPowerSeries.monomial (principalRootComplementExponent i p) 1)) beta := by
  by_cases hb : ∀ j, 0 ≤ beta j
  · rw [rootCoefficient_of_nonneg _ _ hb, rootCoefficient_of_nonneg _ _ hb]
    exact principalRootComplementEuler_agree_finite i _ S hS _ le_rfl
  · rw [rootCoefficient_of_not_nonneg _ _ hb, rootCoefficient_of_not_nonneg _ _ hb]

theorem rootCoefficient_principalRootComplementFinite_reflection (i : Fin 3)
    (S : Finset (PrincipalActiveRootComplement i))
    (hS : ∀ p ∈ S, principalActiveRootReflectionEquiv i p ∈ S) (beta : RootCoefficients) :
    rootCoefficient
      (∏ p ∈ S, (1-MvPowerSeries.monomial (principalRootComplementExponent i p) (1 : K)))
      (simpleReflection 0 i beta) =
    rootCoefficient
      (∏ p ∈ S, (1-MvPowerSeries.monomial (principalRootComplementExponent i p) (1 : K))) beta := by
  classical
  let R := principalActiveRootReflectionEquiv i
  let f := principalRootComplementExponent i
  have hprod : (∏ p ∈ S, (1-MvPowerSeries.monomial (f (R p)) (1 : K))) =
      ∏ p ∈ S, (1-MvPowerSeries.monomial (f p) (1 : K)) := by
    apply Finset.prod_bij (fun p _ => R p)
    · exact hS
    · intro a ha b hb hab
      exact R.injective hab
    · intro p hp
      exact ⟨R p, hS p hp, principalActiveRootReflection_twice i p⟩
    · intro p hp
      rfl
  have h := rootCoefficient_eulerProduct_transport (K := K) S f (fun p => f (R p))
    (linearRootReflection i) (fun p _ => by
      simpa only [f, R, principalRootComplementExponent,
        rootCoefficientsOfExponent_positiveModeExponent, linearRootReflection_apply]
        using principalActiveRootReflection_occupation i p) beta
  rw [hprod] at h
  exact h

/-- The stabilized simple-root complement is invariant under the actual
simple reflection, including coefficients outside the positive cone. -/
theorem rootCoefficient_principalRootComplementEuler_reflection (i : Fin 3)
    (beta : RootCoefficients) :
    rootCoefficient (principalRootComplementEuler (K := K) i) (simpleReflection 0 i beta) =
      rootCoefficient (principalRootComplementEuler (K := K) i) beta := by
  classical
  let B := max (rootExponentDegree (exponentOfRootCoefficients beta))
    (rootExponentDegree (exponentOfRootCoefficients (simpleReflection 0 i beta)))
  let T := principalRootComplementPrefix i B
  let R := principalActiveRootReflectionEquiv i
  let S := T ∪ T.image R
  have hprefix (b : ℕ) (hb : b ≤ B) : principalRootComplementPrefix i b ⊆ S := by
    intro p hp
    apply Finset.mem_union_left
    apply (mem_principalRootComplementPrefix i B p).mpr
    exact lt_of_lt_of_le ((mem_principalRootComplementPrefix i b p).mp hp) hb
  have hstable : ∀ p ∈ S, R p ∈ S := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      rw [show R (R q) = q from principalActiveRootReflection_twice i q]
      exact Finset.mem_union_left _ hq
  rw [rootCoefficient_principalRootComplementEuler_finite i _ S
    (hprefix _ (le_max_right _ _)),
    rootCoefficient_principalRootComplementEuler_finite i _ S
    (hprefix _ (le_max_left _ _))]
  exact rootCoefficient_principalRootComplementFinite_reflection i S hstable beta

end KanadeRussell.Representation
