import KanadeRussell.Tsuchioka.TensorRootFields
import KanadeRussell.Tsuchioka.HeisenbergSpanning

/-! Principal grading and derivation brackets of the source tensor fields. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open PowerSeries MvPolynomial
open RootData (Lattice)

variable {K : Type*} [Field K] [CharZero K]

theorem tensorRootCreationLog_homogeneous (w : K) (β : Lattice) (j : Fin 3) :
    LaurentHomogeneous (tensorRootCreationLog w β j : LaurentSeries (Space K)) 0 := by
  rw [laurent_coe_iff]
  intro n
  rw [tensorRootCreationLog, coeff_mk]
  split_ifs with hn
  · exact (isWeightedHomogeneous_X K variableWeight (j, (⟨n, hn⟩ : Mode))).C_mul _
  · exact isWeightedHomogeneous_zero K variableWeight (n : ℤ)

theorem tensorRootCreation_homogeneous (w : K) (β : Lattice) (j : Fin 3) :
    LaurentHomogeneous (tensorRootCreation w β j : LaurentSeries (Space K)) 0 := by
  rw [laurent_coe_iff]
  intro n
  rw [tensorRootCreation, FormalSeries.coeff_exponential
    (constantCoeff_tensorRootCreationLog w β j)]
  apply IsWeightedHomogeneous.sum
  intro k hk
  have hp := laurent_pow (tensorRootCreationLog_homogeneous w β j) k
  rw [← PowerSeries.coe_pow] at hp
  simp only [smul_zero] at hp
  have hc := (laurent_coe_iff _).mp hp n
  rw [MvPolynomial.algebraMap_apply]
  exact hc.C_mul _

theorem tensorRootAnnihilation_variable_homogeneous (w : K) (β : Lattice)
    (j : Fin 3) (s : Fin 3 × Mode) :
    LaurentHomogeneous (tensorRootAnnihilation w β j (MvPolynomial.X s)) (variableWeight s) := by
  simp only [tensorRootAnnihilation, eval₂Hom_X']
  apply laurent_add
  · apply laurent_single (e := 0)
    simpa using isWeightedHomogeneous_X K variableWeight s
  · apply laurent_single
    simpa [variableWeight] using isWeightedHomogeneous_C variableWeight
      (if s.1 = j then -contraction w s.2.val * RootData.rootWeight (w ^ (s.2.val : ℤ)) β else 0)

theorem tensorRootAnnihilation_monomial_homogeneous (w : K) (β : Lattice)
    (j : Fin 3) (d : (Fin 3 × Mode) →₀ ℕ) (c : K) :
    LaurentHomogeneous (tensorRootAnnihilation w β j (monomial d c))
      (Finsupp.weight variableWeight d) := by
  classical
  have hv (s : Fin 3 × Mode) :
      LaurentHomogeneous (tensorRootAnnihilation w β j (MvPolynomial.X s) ^ d s)
        (d s • variableWeight s) :=
    laurent_pow (tensorRootAnnihilation_variable_homogeneous w β j s) (d s)
  have hp := laurent_prod d.support
    (fun s => tensorRootAnnihilation w β j (MvPolynomial.X s) ^ d s)
    (fun s => d s • variableWeight s) (fun s _ => hv s)
  have hc : LaurentHomogeneous (HahnSeries.C (MvPolynomial.C c) : LaurentSeries (Space K)) 0 :=
    laurent_single (by simpa using isWeightedHomogeneous_C variableWeight c)
  have hm := laurent_mul hc hp
  simpa [tensorRootAnnihilation, eval₂Hom_monomial, eval₂Hom_X', Finsupp.prod,
    Finsupp.weight_apply, Finsupp.sum] using hm

theorem tensorRootAnnihilation_homogeneous (w : K) (β : Lattice) (j : Fin 3)
    {p : Space K} {d : ℤ} (hp : IsWeightedHomogeneous variableWeight p d) :
    LaurentHomogeneous (tensorRootAnnihilation w β j p) d := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa using laurent_zero (K := K) d
  | add p q hp hq ihp ihq => simpa using laurent_add ihp ihq
  | monomial e c he =>
    rw [← he]
    exact tensorRootAnnihilation_monomial_homogeneous w β j e c

theorem tensorRootField_homogeneous (w : K) (β : Lattice) {p : Space K} {d : ℤ}
    (hp : IsWeightedHomogeneous variableWeight p d) :
    LaurentHomogeneous (tensorRootField w β p) d := by
  change LaurentHomogeneous ((1 / 12 : K) • ∑ j : Fin 3, tensorRootSummand w β j p) d
  apply laurent_smul
  apply laurent_sum
  intro j hj
  simpa only [zero_add, tensorRootSummand, LinearMap.coe_mk, AddHom.coe_mk] using
    laurent_mul (tensorRootCreation_homogeneous w β j)
      (tensorRootAnnihilation_homogeneous w β j hp)

theorem tensorRootMode_mem_grade (w : K) (β : Lattice) (i d : ℤ)
    (p : Space K) (hp : p ∈ grade d) : tensorRootMode w β i p ∈ grade (d - i) := by
  have h := tensorRootField_homogeneous w β hp (-i)
  simpa [grade, tensorRootMode, sub_eq_add_neg] using h

theorem tensorRootMode_eq_zero_of_degree_lt (w : K) (β : Lattice) (i d : ℤ)
    (p : Space K) (hp : p ∈ grade d) (hi : d < i) : tensorRootMode w β i p = 0 := by
  have h := tensorRootMode_mem_grade w β i d p hp
  rw [grade_negative (d - i) (by omega), Submodule.mem_bot] at h
  exact h

theorem tensorRootMode_vacuum_pos (w : K) (β : Lattice) (i : ℤ) (hi : 0 < i) :
    tensorRootMode w β i 1 = 0 :=
  tensorRootMode_eq_zero_of_degree_lt w β i 0 1 (isWeightedHomogeneous_one K variableWeight) hi

theorem degreeOperator_tensorRootMode_commutator (w : K) (β : Lattice) (i : ℤ) :
    degreeOperator.comp (tensorRootMode w β i) -
        (tensorRootMode w β i).comp degreeOperator = (-(i : K)) • tensorRootMode w β i := by
  apply (MvPolynomial.basisMonomials (Fin 3 × Mode) K).ext
  intro m
  change degreeOperator (tensorRootMode w β i (MvPolynomial.monomial m 1)) -
      tensorRootMode w β i (degreeOperator (MvPolynomial.monomial m 1)) =
        (-(i : K)) • tensorRootMode w β i (MvPolynomial.monomial m 1)
  have hm : (MvPolynomial.monomial m (1 : K)) ∈
      grade (Finsupp.weight variableWeight m) :=
    MvPolynomial.isWeightedHomogeneous_monomial variableWeight m 1 rfl
  rw [degreeOperator_monomial_one, map_smul,
    degreeOperator_eq_of_grade _ _ (tensorRootMode_mem_grade w β i _ _ hm)]
  push_cast
  module

theorem principalDerivation_tensorRootMode_commutator (w : K) (β : Lattice) (i : ℤ) :
    principalDerivation.comp (tensorRootMode w β i) -
        (tensorRootMode w β i).comp principalDerivation = (i : K) • tensorRootMode w β i := by
  apply LinearMap.ext
  intro f
  have h := LinearMap.congr_fun (degreeOperator_tensorRootMode_commutator w β i) f
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] at h
  change -(degreeOperator (tensorRootMode w β i f)) -
    tensorRootMode w β i (-degreeOperator f) = (i : K) • tensorRootMode w β i f
  rw [map_neg]
  calc
    _ = -(degreeOperator (tensorRootMode w β i f) -
        tensorRootMode w β i (degreeOperator f)) := by abel
    _ = _ := by rw [h, neg_smul, neg_neg]

theorem principalDerivation_heisenbergPositive_commutator (w : K) (n : Mode) :
    principalDerivation.comp (heisenbergPositive w n) -
        (heisenbergPositive w n).comp principalDerivation =
      (n.val : K) • heisenbergPositive w n := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    principalDerivation, LinearMap.neg_apply, heisenbergPositive_apply, map_neg,
    map_smul, diagonalDerivative_degreeOperator, smul_add, smul_smul]
  module

theorem principalDerivation_heisenbergNegative_commutator (n : Mode) :
    principalDerivation.comp (heisenbergNegative (K := K) n) -
        (heisenbergNegative n).comp principalDerivation =
      (-(n.val : K)) • heisenbergNegative n := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    principalDerivation, LinearMap.neg_apply, map_neg, degreeOperator_heisenbergNegative]
  module

end KanadeRussell.Tsuchioka.Fock
