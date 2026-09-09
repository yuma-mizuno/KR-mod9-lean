import KanadeRussell.Tsuchioka.ChevalleyCoefficients

/-! Integer root occupations, simple reflections, and the quadratic invariant
for the actual D4^(3) Cartan matrix. The symmetrizer is (1,1,3), and the null
root has coefficients (1,2,1). No dominance or character formula is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation.AffineWeightLattice
open Tsuchioka.Fock

private theorem fin_three_two : (2 : Fin 3) = ⟨2, by decide⟩ := by decide

abbrev RootCoefficients := Fin 3 → ℤ

def symmetrizer : Fin 3 → ℤ := ![1, 1, 3]

def marks : RootCoefficients := ![1, 2, 1]

def weightLabels (lambda beta : RootCoefficients) : RootCoefficients :=
  fun i => lambda i - ∑ j : Fin 3, affineCartanMatrix i j * beta j

/-- Reflection on root occupations for the weight `lambda - A beta`. -/
def simpleReflection (lambda : RootCoefficients) (i : Fin 3)
    (beta : RootCoefficients) : RootCoefficients :=
  beta + Pi.single i (weightLabels lambda beta i)

def totalDegree (beta : RootCoefficients) : ℤ := ∑ i : Fin 3, beta i

def level (lambda : RootCoefficients) : ℤ := lambda 0 + 2 * lambda 1 + 3 * lambda 2

def rootQuadratic (beta : RootCoefficients) : ℤ :=
  (∑ i : Fin 3, symmetrizer i * beta i ^ 2) +
    ∑ i : Fin 3, ∑ j : Fin 3,
      if i < j then symmetrizer i * affineCartanMatrix i j * beta i * beta j else 0

/-- Half the symmetrized root norm minus pairing with the specified weight. -/
def casimir (lambda beta : RootCoefficients) : ℤ :=
  rootQuadratic beta - ∑ i : Fin 3, symmetrizer i * lambda i * beta i

theorem symmetrizer_positive (i : Fin 3) : 0 < symmetrizer i := by
  fin_cases i <;> norm_num [symmetrizer, Matrix.cons_val_two]

theorem symmetrizer_cartan_symmetric (i j : Fin 3) :
    symmetrizer i * affineCartanMatrix i j =
      symmetrizer j * affineCartanMatrix j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetrizer, affineCartanMatrix, Matrix.cons_val_two]

theorem cartan_marks (i : Fin 3) :
    (∑ j : Fin 3, affineCartanMatrix i j * marks j) = 0 := by
  fin_cases i <;> norm_num [Fin.sum_univ_three, affineCartanMatrix, marks, Matrix.cons_val_two]

@[simp] theorem totalDegree_marks : totalDegree marks = 4 := by
  norm_num [totalDegree, marks, Fin.sum_univ_three, Matrix.cons_val_two]

theorem weightLabels_simpleReflection (lambda beta : RootCoefficients) (i j : Fin 3) :
    weightLabels lambda (simpleReflection lambda i beta) j =
      weightLabels lambda beta j - affineCartanMatrix j i * weightLabels lambda beta i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [weightLabels, simpleReflection, Fin.sum_univ_three, Pi.single_apply,
      affineCartanMatrix, Matrix.cons_val_two] <;>
      norm_num only [Fin.ext_iff, Fin.lt_def] <;>
      norm_num <;> (try simp only [fin_three_two]) <;> ring

@[simp] theorem weightLabels_simpleReflection_self (lambda beta : RootCoefficients) (i : Fin 3) :
    weightLabels lambda (simpleReflection lambda i beta) i = -weightLabels lambda beta i := by
  rw [weightLabels_simpleReflection]
  have hii : affineCartanMatrix i i = 2 := by
    fin_cases i <;> norm_num [affineCartanMatrix, Matrix.cons_val_two]
  rw [hii]
  ring

theorem simpleReflection_involutive (lambda : RootCoefficients) (i : Fin 3) :
    Function.Involutive (simpleReflection lambda i) := by
  intro beta
  change simpleReflection lambda i beta +
    Pi.single i (weightLabels lambda (simpleReflection lambda i beta) i) = beta
  rw [weightLabels_simpleReflection_self]
  funext j
  by_cases hji : j = i <;> simp [simpleReflection, hji]

@[simp] theorem simpleReflection_twice (lambda beta : RootCoefficients) (i : Fin 3) :
    simpleReflection lambda i (simpleReflection lambda i beta) = beta :=
  simpleReflection_involutive lambda i beta

theorem level_weightLabels (lambda beta : RootCoefficients) :
    level (weightLabels lambda beta) = level lambda := by
  norm_num [level, weightLabels, Fin.sum_univ_three, affineCartanMatrix, Matrix.cons_val_two]
  ring

theorem rootQuadratic_eq (beta : RootCoefficients) :
    rootQuadratic beta = beta 0 ^ 2 + beta 1 ^ 2 + 3 * beta 2 ^ 2 -
      beta 0 * beta 1 - 3 * beta 1 * beta 2 := by
  norm_num [rootQuadratic, Fin.sum_univ_three, symmetrizer, affineCartanMatrix, Matrix.cons_val_two]
  norm_num only [Fin.ext_iff, Fin.lt_def]
  norm_num
  ring

theorem casimir_eq (lambda beta : RootCoefficients) :
    casimir lambda beta = beta 0 ^ 2 + beta 1 ^ 2 + 3 * beta 2 ^ 2 -
      beta 0 * beta 1 - 3 * beta 1 * beta 2 -
      lambda 0 * beta 0 - lambda 1 * beta 1 - 3 * lambda 2 * beta 2 := by
  rw [casimir, rootQuadratic_eq]
  norm_num [Fin.sum_univ_three, symmetrizer, Matrix.cons_val_two]
  ring

theorem casimir_simpleReflection (lambda beta : RootCoefficients) (i : Fin 3) :
    casimir lambda (simpleReflection lambda i beta) = casimir lambda beta := by
  fin_cases i <;>
    norm_num [casimir_eq, simpleReflection, weightLabels, Fin.sum_univ_three,
      Pi.single_apply, affineCartanMatrix, Matrix.cons_val_two] <;>
      norm_num only [Fin.ext_iff, Fin.lt_def] <;>
      norm_num <;> (try simp only [fin_three_two]) <;> ring

theorem weightLabels_add_marks (lambda beta : RootCoefficients) (t : ℤ) :
    weightLabels lambda (beta + t • marks) = weightLabels lambda beta := by
  funext i
  fin_cases i <;>
    norm_num [weightLabels, Fin.sum_univ_three, affineCartanMatrix, marks, Matrix.cons_val_two] <;> ring

theorem rootQuadratic_add_marks (beta : RootCoefficients) (t : ℤ) :
    rootQuadratic (beta + t • marks) = rootQuadratic beta := by
  norm_num [rootQuadratic_eq, marks, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

theorem casimir_add_marks (lambda beta : RootCoefficients) (t : ℤ) :
    casimir lambda (beta + t • marks) = casimir lambda beta - t * level lambda := by
  norm_num [casimir_eq, marks, level, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

/-- The semidefinite root form, expressed without denominators. -/
theorem four_mul_rootQuadratic (beta : RootCoefficients) :
    4 * rootQuadratic beta = (2 * beta 0 - beta 1)^2 + 3 * (2 * beta 2 - beta 1)^2 := by
  rw [rootQuadratic_eq]
  ring

theorem rootQuadratic_nonneg (beta : RootCoefficients) : 0 ≤ rootQuadratic beta := by
  have h := four_mul_rootQuadratic beta
  nlinarith [sq_nonneg (2 * beta 0 - beta 1), sq_nonneg (2 * beta 2 - beta 1)]

theorem rootQuadratic_eq_zero_iff (beta : RootCoefficients) :
    rootQuadratic beta = 0 ↔ beta 0 = beta 2 ∧ beta 1 = 2 * beta 2 := by
  constructor
  · intro hz
    have h := four_mul_rootQuadratic beta
    have h0 : (2 * beta 0 - beta 1)^2 = 0 := by
      nlinarith [sq_nonneg (2 * beta 0 - beta 1), sq_nonneg (2 * beta 2 - beta 1)]
    have h2 : (2 * beta 2 - beta 1)^2 = 0 := by
      nlinarith [sq_nonneg (2 * beta 0 - beta 1), sq_nonneg (2 * beta 2 - beta 1)]
    rw [sq_eq_zero_iff] at h0 h2
    omega
  · rintro ⟨h0, h1⟩
    rw [rootQuadratic_eq, h0, h1]
    ring

theorem rootQuadratic_eq_zero_iff_multiple_marks (beta : RootCoefficients) :
    rootQuadratic beta = 0 ↔ ∃ t : ℤ, beta = t • marks := by
  constructor
  · intro hz
    obtain ⟨h0, h1⟩ := (rootQuadratic_eq_zero_iff beta).mp hz
    refine ⟨beta 2, ?_⟩
    funext i
    fin_cases i
    · simpa [marks] using h0
    · simpa [marks, mul_comm] using h1
    · norm_num [marks, Matrix.cons_val_two]
      exact congrArg beta fin_three_two.symm
  · rintro ⟨t, rfl⟩
    norm_num [rootQuadratic_eq, marks, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    ring

/-- The finite part obtained by setting the affine coefficient to zero is positive definite. -/
theorem rootQuadratic_pos_of_affine_zero (beta : RootCoefficients)
    (h0 : beta 0 = 0) (hne : beta ≠ 0) : 0 < rootQuadratic beta := by
  have hnonneg := rootQuadratic_nonneg beta
  by_contra h
  have hz : rootQuadratic beta = 0 := by omega
  obtain ⟨h02, h12⟩ := (rootQuadratic_eq_zero_iff beta).mp hz
  have h2 : beta 2 = 0 := by omega
  have h1 : beta 1 = 0 := by omega
  apply hne
  funext i
  fin_cases i <;> simp [h0, h1, h2]

theorem eq_of_totalDegree_eq_of_weightLabels_eq (lambda beta gamma : RootCoefficients)
    (hd : totalDegree beta = totalDegree gamma)
    (hw : weightLabels lambda beta = weightLabels lambda gamma) : beta = gamma := by
  have h0 := congrFun hw 0
  have h2 := congrFun hw 2
  norm_num [weightLabels, Fin.sum_univ_three, affineCartanMatrix, Matrix.cons_val_two] at h0 h2
  simp only [totalDegree, Fin.sum_univ_three] at hd
  have hb0 : beta 0 = gamma 0 := by omega
  have hb1 : beta 1 = gamma 1 := by omega
  have hb2 : beta 2 = gamma 2 := by omega
  funext i
  fin_cases i
  · exact hb0
  · exact hb1
  · exact hb2

theorem totalDegree_weightLabels_injective (lambda : RootCoefficients) :
    Function.Injective (fun beta : RootCoefficients => (totalDegree beta, weightLabels lambda beta)) := by
  intro beta gamma h
  exact eq_of_totalDegree_eq_of_weightLabels_eq lambda beta gamma
    (congrArg Prod.fst h) (congrArg Prod.snd h)

end KanadeRussell.Representation.AffineWeightLattice
