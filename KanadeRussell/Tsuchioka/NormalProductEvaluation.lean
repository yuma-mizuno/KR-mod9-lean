import KanadeRussell.Tsuchioka.DiagonalEvaluation

/-!
The coefficientwise diagonal evaluation of the actual normal product agrees
with its concrete pole specialization, including all annihilation terms.
-/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open FormalSeries
open RootData (simpleRoot)

variable {K : Type*} [Field K] [CharZero K]

noncomputable def normalWithPolynomial (f g : LaurentSeries (Space K))
    (p : MvPolynomial (Fin 2) (Space K)) : LaurentSeries (LaurentSeries (Space K)) :=
  separated f g * jointLaurentEmbedding p

theorem normalWithPolynomial_bounded (f g : LaurentSeries (Space K))
    (p : MvPolynomial (Fin 2) (Space K)) :
    ∃ l r : ℤ, RectangularBound (normalWithPolynomial f g p) l r := by
  obtain ⟨l, r, hp⟩ := jointLaurentEmbedding_bounded p
  exact ⟨f.order + l, g.order + r, rectangular_mul (separated_bounded f g) hp⟩

/-- Evaluate inverse variables at u^(-1)*t^(-1), t^(-1). -/
noncomputable def polynomialPoleEvaluation (u : (Space K)ˣ) :
    MvPolynomial (Fin 2) (Space K) →+* LaurentSeries (Space K) :=
  MvPolynomial.eval₂Hom HahnSeries.C fun v =>
    if v = 0 then HahnSeries.single (-1) (u⁻¹ : (Space K)ˣ)
    else HahnSeries.single (-1) 1

theorem normalWithPolynomial_add (f g : LaurentSeries (Space K))
    (p q : MvPolynomial (Fin 2) (Space K)) :
    normalWithPolynomial f g (p + q) =
      normalWithPolynomial f g p + normalWithPolynomial f g q := by
  simp only [normalWithPolynomial, map_add, mul_add]

/-- Multiplication by an inverse-variable monomial commutes with diagonal
evaluation; polynomial induction handles every finite annihilation input. -/
theorem normalWithPolynomial_diagonal (u : (Space K)ˣ)
    (f g : LaurentSeries (Space K)) (p : MvPolynomial (Fin 2) (Space K)) (d : ℤ) :
    diagonalCoefficient u (normalWithPolynomial f g p) d =
      (laurentRescale u f * g * polynomialPoleEvaluation u p).coeff d := by
  induction p using MvPolynomial.induction_on generalizing d with
  | C c =>
    rw [normalWithPolynomial, jointLaurentEmbedding, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply, HahnSeries.C_apply, HahnSeries.C_apply,
      mul_comm (separated f g), diagonalCoefficient_single_mul (separated_bounded f g),
      diagonalCoefficient_separated]
    simp only [zpow_zero, Units.val_one, one_mul, sub_zero,
      polynomialPoleEvaluation, MvPolynomial.eval₂Hom_C, HahnSeries.C_apply,
      HahnSeries.coeff_mul_single_zero]
    ring
  | add p q hp hq =>
    obtain ⟨l, r, hb⟩ := normalWithPolynomial_bounded f g p
    obtain ⟨l', r', hc⟩ := normalWithPolynomial_bounded f g q
    rw [normalWithPolynomial_add, diagonalCoefficient_add hb hc, hp, hq,
      map_add, mul_add, HahnSeries.coeff_add]
  | mul_X p v hp =>
    obtain ⟨l, r, hb⟩ := normalWithPolynomial_bounded f g p
    have hmul : normalWithPolynomial f g (p * MvPolynomial.X v) =
        jointLaurentEmbedding (MvPolynomial.X v : MvPolynomial (Fin 2) (Space K)) *
          normalWithPolynomial f g p := by
      simp only [normalWithPolynomial, map_mul]
      ring
    rw [hmul, map_mul, ← mul_assoc]
    by_cases hv : v = 0
    · simp only [jointLaurentEmbedding, MvPolynomial.eval₂Hom_X', if_pos hv,
        HahnSeries.C_apply]
      rw [diagonalCoefficient_single_mul hb, hp]
      simp only [sub_neg_eq_add, sub_zero, zpow_neg_one, mul_one,
        polynomialPoleEvaluation, MvPolynomial.eval₂Hom_X', if_pos hv,
        HahnSeries.coeff_mul_single]
      ring
    · simp only [jointLaurentEmbedding, MvPolynomial.eval₂Hom_X', if_neg hv,
        HahnSeries.C_apply]
      rw [diagonalCoefficient_single_mul hb, hp]
      simp only [sub_neg_eq_add, sub_zero, zpow_zero, Units.val_one, mul_one, one_mul,
        polynomialPoleEvaluation, MvPolynomial.eval₂Hom_X', if_neg hv,
        HahnSeries.coeff_mul_single]

theorem polynomialPoleEvaluation_phaseUnit (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (p : ℤ) :
    polynomialPoleEvaluation (phaseUnit w hw p) = poleEvaluation w p := by
  have hu : (((phaseUnit w hw p)⁻¹ : (Space K)ˣ) : Space K) =
      MvPolynomial.C (w ^ p) := by
    have h := phaseUnit_zpow w hw p (-1)
    simpa only [zpow_neg_one, mul_neg_one, neg_neg] using h
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [polynomialPoleEvaluation, poleEvaluation, MvPolynomial.eval₂Hom_C]
  · intro v
    simp only [polynomialPoleEvaluation, poleEvaluation, MvPolynomial.eval₂Hom_X']
    split_ifs <;> simp [hu]

theorem normalProduct_eq_normalWithPolynomial (w : K) (s t : Fin 3) (f : Space K) :
    normalProduct w s t f =
      normalWithPolynomial (creation (K := K) s) (creation (K := K) t)
        (jointAnnihilationPolynomial w (simpleRoot 0) (simpleRoot 0) s t f) := by
  rw [normalWithPolynomial, separated, mapLaurent_powerSeries]
  rfl

/-- Actual pole specialization of the normal product, in every total exponent. -/
theorem normalProduct_diagonal (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s t : Fin 3) (f : Space K) (p d : ℤ) :
    diagonalCoefficient (phaseUnit w hw p) (normalProduct w s t f) d =
      (poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) s t p f).coeff d := by
  rw [normalProduct_eq_normalWithPolynomial, normalWithPolynomial_diagonal,
    polynomialPoleEvaluation_phaseUnit]
  have h := RingHom.congr_fun
    (poleEvaluation_jointAnnihilation w (simpleRoot 0) (simpleRoot 0) s t p) f
  simp only [RingHom.comp_apply] at h
  rw [h, poleNormalProduct]
  simp only [rootCreation_first]

/-- The formal delta residue of the actual operator normal product. -/
theorem normalProduct_delta_contraction (w : K) (hw : w ^ 4 - w ^ 2 + 1 = 0)
    (s t : Fin 3) (f : Space K) (p a b : ℤ) :
    contract (fun n => ((phaseUnit w hw p ^ n : (Space K)ˣ) : Space K))
        (normalProduct w s t f) a b =
      MvPolynomial.C (w ^ (p * a)) *
        (poleNormalProduct w hw (simpleRoot 0) (simpleRoot 0) s t p f).coeff (a + b) := by
  obtain ⟨l, r, h⟩ := normalProduct_bounded w s t f
  rw [contract_delta h, normalProduct_diagonal, phaseUnit_zpow]
  simp only [neg_mul_neg]

end KanadeRussell.Tsuchioka.Fock
