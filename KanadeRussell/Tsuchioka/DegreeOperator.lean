import KanadeRussell.Tsuchioka.AllRootGeneration

/-! The concrete degree operator on the polynomial Fock space and its
commutators with every root mode. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

variable {K : Type*} [Field K] [CharZero K]

/-- The diagonal degree operator on the actual monomial basis. -/
noncomputable def degreeOperator : Module.End K (Space K) :=
  (MvPolynomial.basisMonomials (Fin 3 × Mode) K).constr K
    (fun m => (Finsupp.weight variableWeight m : K) • MvPolynomial.monomial m 1)

theorem degreeOperator_monomial_one (m : (Fin 3 × Mode) →₀ ℕ) :
    degreeOperator (MvPolynomial.monomial m (1 : K)) =
      (Finsupp.weight variableWeight m : K) • MvPolynomial.monomial m 1 :=
  (MvPolynomial.basisMonomials (Fin 3 × Mode) K).constr_basis K _ m

theorem degreeOperator_monomial (m : (Fin 3 × Mode) →₀ ℕ) (c : K) :
    degreeOperator (MvPolynomial.monomial m c) =
      (Finsupp.weight variableWeight m : K) • MvPolynomial.monomial m c := by
  have he : MvPolynomial.monomial m c = c • MvPolynomial.monomial m 1 := by
    simp [MvPolynomial.smul_monomial, smul_eq_mul]
  rw [he, map_smul, degreeOperator_monomial_one]
  module

theorem coeff_degreeOperator (m : (Fin 3 × Mode) →₀ ℕ) (f : Space K) :
    MvPolynomial.coeff m (degreeOperator f) =
      (Finsupp.weight variableWeight m : K) * MvPolynomial.coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [degreeOperator_monomial, MvPolynomial.coeff_smul]
    by_cases he : e = m
    · subst e
      simp [smul_eq_mul]
    · simp [MvPolynomial.coeff_monomial, he]
  | add f g hf hg =>
    simp only [map_add, MvPolynomial.coeff_add, hf, hg, mul_add]

theorem degreeOperator_eq_of_grade (d : ℤ) (f : Space K) (hf : f ∈ grade d) :
    degreeOperator f = (d : K) • f := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_degreeOperator, MvPolynomial.coeff_smul]
  by_cases hm : MvPolynomial.coeff m f = 0
  · simp only [hm, mul_zero, smul_zero]
  · rw [hf hm]
    rfl

theorem degreeOperator_mode_commutator (w : K) (i : ℤ) :
    degreeOperator.comp (mode w i) - (mode w i).comp degreeOperator =
      (-(i : K)) • mode w i := by
  apply (MvPolynomial.basisMonomials (Fin 3 × Mode) K).ext
  intro m
  change degreeOperator (mode w i (MvPolynomial.monomial m 1)) -
      mode w i (degreeOperator (MvPolynomial.monomial m 1)) =
        (-(i : K)) • mode w i (MvPolynomial.monomial m 1)
  have hm : (MvPolynomial.monomial m (1 : K)) ∈
      grade (Finsupp.weight variableWeight m) :=
    MvPolynomial.isWeightedHomogeneous_monomial variableWeight m 1 rfl
  rw [degreeOperator_monomial_one, map_smul,
    degreeOperator_eq_of_grade _ _ (mode_mem_grade w i _ _ hm)]
  push_cast
  module

theorem degreeOperator_rootMode_commutator (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (β : RootData.Root) (i : ℤ) :
    degreeOperator.comp (rootMode w β.val i) - (rootMode w β.val i).comp degreeOperator =
      (-(i : K)) • rootMode w β.val i := by
  apply (MvPolynomial.basisMonomials (Fin 3 × Mode) K).ext
  intro m
  change degreeOperator (rootMode w β.val i (MvPolynomial.monomial m 1)) -
      rootMode w β.val i (degreeOperator (MvPolynomial.monomial m 1)) =
        (-(i : K)) • rootMode w β.val i (MvPolynomial.monomial m 1)
  have hm : (MvPolynomial.monomial m (1 : K)) ∈
      grade (Finsupp.weight variableWeight m) :=
    MvPolynomial.isWeightedHomogeneous_monomial variableWeight m 1 rfl
  rw [degreeOperator_monomial_one, map_smul,
    degreeOperator_eq_of_grade _ _ (rootMode_mem_grade w hw β i _ _ hm)]
  push_cast
  module


theorem wordOperator_mem_grade (w : K) (u : Word) (d : ℤ)
    (f : Space K) (hf : f ∈ grade d) :
    (highestWeightAction w).wordOperator u f ∈ grade (d - u.sum) := by
  induction u with
  | nil => simpa only [HighestWeightAction.wordOperator, LinearMap.id_apply,
      List.sum_nil, sub_zero] using hf
  | cons i u ih =>
    have hh := mode_mem_grade w i (d - u.sum) _ ih
    change mode w i ((highestWeightAction w).wordOperator u f) ∈ grade (d - (i + u.sum))
    rw [show d - u.sum - i = d - (i + u.sum) by ring] at hh
    exact hh

theorem firstWordSpan_le_grade (w : K) (seed : Space K) (d e : ℤ)
    (hseed : seed ∈ grade d) : firstWordSpan w seed e ≤ grade (d - e) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u, hu, rfl⟩
  change u.sum = e at hu
  change (highestWeightAction w).wordOperator u seed ∈ grade (d - e)
  rw [← hu]
  exact wordOperator_mem_grade w u d seed hseed

theorem degreeOperator_mem_firstWordSpan (w : K) (seed : Space K) (d e : ℤ)
    (hseed : seed ∈ grade d) (f : Space K) (hf : f ∈ firstWordSpan w seed e) :
    degreeOperator f ∈ firstWordSpan w seed e := by
  rw [degreeOperator_eq_of_grade _ _ (firstWordSpan_le_grade w seed d e hseed hf)]
  exact (firstWordSpan w seed e).smul_mem _ hf

/-- The affine derivation has the opposite sign to the nonnegative energy. -/
noncomputable def principalDerivation : Module.End K (Space K) := -degreeOperator

theorem principalDerivation_eq_of_grade (d : ℤ) (f : Space K) (hf : f ∈ grade d) :
    principalDerivation f = (-(d : K)) • f := by
  simp only [principalDerivation, LinearMap.neg_apply, degreeOperator_eq_of_grade d f hf,
    neg_smul]

theorem principalDerivation_rootMode_commutator (w : K)
    (hw : w ^ 4 - w ^ 2 + 1 = 0) (β : RootData.Root) (i : ℤ) :
    principalDerivation.comp (rootMode w β.val i) -
      (rootMode w β.val i).comp principalDerivation = (i : K) • rootMode w β.val i := by
  apply LinearMap.ext
  intro f
  have h := LinearMap.congr_fun (degreeOperator_rootMode_commutator w hw β i) f
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] at h
  change -(degreeOperator (rootMode w β.val i f)) -
    rootMode w β.val i (-degreeOperator f) = (i : K) • rootMode w β.val i f
  rw [map_neg]
  calc
    _ = -(degreeOperator (rootMode w β.val i f) - rootMode w β.val i (degreeOperator f)) := by abel
    _ = _ := by rw [h, neg_smul, neg_neg]

end KanadeRussell.Tsuchioka.Fock
