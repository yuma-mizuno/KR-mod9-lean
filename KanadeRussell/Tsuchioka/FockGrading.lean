import KanadeRussell.Tsuchioka.Fock
import KanadeRussell.Tsuchioka.LocalReduction

/-! The constructed Fock modes preserve the principal grading. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock

open scoped BigOperators
open PowerSeries MvPolynomial

variable {K : Type*} [Field K]

def variableWeight (s : Fin 3 × Mode) : ℤ := s.2.val

noncomputable def grade (d : ℤ) : Submodule K (Space K) :=
  weightedHomogeneousSubmodule K variableWeight d

/-- The Laurent exponent records the change in polynomial weight. -/
def LaurentHomogeneous (f : LaurentSeries (Space K)) (d : ℤ) : Prop :=
  ∀ e : ℤ, IsWeightedHomogeneous variableWeight (f.coeff e) (d + e)

theorem laurent_zero (d : ℤ) : LaurentHomogeneous (0 : LaurentSeries (Space K)) d := by
  intro e
  exact isWeightedHomogeneous_zero K variableWeight (d + e)

theorem laurent_add {f g : LaurentSeries (Space K)} {d : ℤ}
    (hf : LaurentHomogeneous f d) (hg : LaurentHomogeneous g d) :
    LaurentHomogeneous (f + g) d := by
  intro e
  exact (hf e).add (hg e)

theorem laurent_smul {f : LaurentSeries (Space K)} {d : ℤ}
    (hf : LaurentHomogeneous f d) (c : K) : LaurentHomogeneous (c • f) d := by
  intro e
  change c • f.coeff e ∈ grade (d + e)
  exact (grade (d + e)).smul_mem c (hf e)

theorem laurent_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries (Space K)) (d : ℤ)
    (h : ∀ i ∈ s, LaurentHomogeneous (f i) d) :
    LaurentHomogeneous (∑ i ∈ s, f i) d := by
  intro e
  rw [HahnSeries.coeff_sum]
  exact IsWeightedHomogeneous.sum s _ (d + e) (fun i hi => h i hi e)

theorem laurent_single {p : Space K} {d e : ℤ}
    (hp : IsWeightedHomogeneous variableWeight p (d + e)) :
    LaurentHomogeneous (HahnSeries.single e p) d := by
  intro k
  classical
  rw [HahnSeries.coeff_single]
  split_ifs with h
  · subst k
    exact hp
  · exact isWeightedHomogeneous_zero K variableWeight (d + k)

theorem laurent_mul {f g : LaurentSeries (Space K)} {d e : ℤ}
    (hf : LaurentHomogeneous f d) (hg : LaurentHomogeneous g e) :
    LaurentHomogeneous (f * g) (d + e) := by
  intro k
  rw [HahnSeries.coeff_mul]
  apply IsWeightedHomogeneous.sum
  intro ij hij
  have hsum : ij.1 + ij.2 = k := (Finset.mem_addAntidiagonal.mp hij).2.2
  convert (hf ij.1).mul (hg ij.2) using 1 <;> omega

theorem laurent_one : LaurentHomogeneous (1 : LaurentSeries (Space K)) 0 := by
  apply laurent_single (e := 0)
  simpa using isWeightedHomogeneous_one K variableWeight

theorem laurent_pow {f : LaurentSeries (Space K)} {d : ℤ}
    (hf : LaurentHomogeneous f d) (n : ℕ) :
    LaurentHomogeneous (f ^ n) (n • d) := by
  induction n with
  | zero => simpa using (laurent_one (K := K))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact laurent_mul ih hf

theorem laurent_prod {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries (Space K))
    (d : ι → ℤ) (h : ∀ i ∈ s, LaurentHomogeneous (f i) (d i)) :
    LaurentHomogeneous (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (laurent_one (K := K))
  | @insert i s his ih =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact laurent_mul (h i (by simp)) (ih (by simpa using fun j hj => h j (by simp [hj])))

theorem laurent_coe_iff (f : PowerSeries (Space K)) :
    LaurentHomogeneous (f : LaurentSeries (Space K)) 0 ↔
      ∀ n : ℕ, IsWeightedHomogeneous variableWeight (coeff n f) (n : ℤ) := by
  constructor
  · intro h n
    simpa [LaurentSeries.coeff_coe_powerSeries] using h n
  · intro h e
    rw [PowerSeries.coeff_coe]
    split_ifs with he
    · exact isWeightedHomogeneous_zero K variableWeight (0 + e)
    · have hn : (e.natAbs : ℤ) = e := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
      simpa [hn] using h e.natAbs

theorem creationLog_homogeneous (j : Fin 3) :
    LaurentHomogeneous (creationLog (K := K) j : LaurentSeries (Space K)) 0 := by
  rw [laurent_coe_iff]
  intro n
  rw [creationLog, coeff_mk]
  split_ifs with hn
  · apply IsWeightedHomogeneous.sum
    intro i hi
    exact (isWeightedHomogeneous_X K variableWeight (i, (⟨n, hn⟩ : Mode))).C_mul _
  · exact isWeightedHomogeneous_zero K variableWeight (n : ℤ)

variable [CharZero K]

theorem creation_homogeneous (j : Fin 3) :
    LaurentHomogeneous (creation (K := K) j : LaurentSeries (Space K)) 0 := by
  rw [laurent_coe_iff]
  intro n
  rw [creation, FormalSeries.coeff_exponential (constantCoeff_creationLog j)]
  apply IsWeightedHomogeneous.sum
  intro k hk
  have hp := laurent_pow (creationLog_homogeneous (K := K) j) k
  rw [← PowerSeries.coe_pow] at hp
  simp only [smul_zero] at hp
  have hc := (laurent_coe_iff _).mp hp n
  rw [MvPolynomial.algebraMap_apply]
  exact hc.C_mul _

omit [CharZero K] in
theorem annihilation_variable_homogeneous (w : K) (j : Fin 3) (s : Fin 3 × Mode) :
    LaurentHomogeneous (annihilation w j (MvPolynomial.X s)) (variableWeight s) := by
  simp only [annihilation, eval₂Hom_X']
  apply laurent_add
  · apply laurent_single (e := 0)
    simpa using isWeightedHomogeneous_X K variableWeight s
  · apply laurent_single
    simpa [variableWeight] using
      isWeightedHomogeneous_C variableWeight
        (tensorExponent s.1 j * contraction w s.2.val / 3)

theorem annihilation_monomial_homogeneous (w : K) (j : Fin 3)
    (d : (Fin 3 × Mode) →₀ ℕ) (c : K) :
    LaurentHomogeneous (annihilation w j (monomial d c)) (Finsupp.weight variableWeight d) := by
  classical
  have hv (s : Fin 3 × Mode) :
      LaurentHomogeneous (annihilation w j (MvPolynomial.X s) ^ d s)
        (d s • variableWeight s) := laurent_pow (annihilation_variable_homogeneous w j s) (d s)
  have hp := laurent_prod d.support
    (fun s => annihilation w j (MvPolynomial.X s) ^ d s)
    (fun s => d s • variableWeight s) (fun s _ => hv s)
  have hc : LaurentHomogeneous (HahnSeries.C (MvPolynomial.C c) : LaurentSeries (Space K)) 0 :=
    laurent_single (by simpa using isWeightedHomogeneous_C variableWeight c)
  have hm := laurent_mul hc hp
  simpa [annihilation, eval₂Hom_monomial, eval₂Hom_X', Finsupp.prod,
    Finsupp.weight_apply, Finsupp.sum] using hm

theorem annihilation_homogeneous (w : K) (j : Fin 3) {p : Space K} {d : ℤ}
    (hp : IsWeightedHomogeneous variableWeight p d) :
    LaurentHomogeneous (annihilation w j p) d := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa using laurent_zero (K := K) d
  | add p q hp hq ihp ihq => simpa using laurent_add ihp ihq
  | monomial e c he =>
    rw [← he]
    exact annihilation_monomial_homogeneous w j e c

theorem field_homogeneous (w : K) {p : Space K} {d : ℤ}
    (hp : IsWeightedHomogeneous variableWeight p d) :
    LaurentHomogeneous (field w p) d := by
  change LaurentHomogeneous ((1 / 12 : K) • ∑ j : Fin 3, summand w j p) d
  apply laurent_smul
  apply laurent_sum
  intro j hj
  exact (by simpa [summand] using
    laurent_mul (creation_homogeneous j) (annihilation_homogeneous w j hp))

theorem mode_mem_grade (w : K) (i d : ℤ) (p : Space K) (hp : p ∈ grade d) :
    mode w i p ∈ grade (d - i) := by
  have h := field_homogeneous w hp (-i)
  simpa [grade, mode, sub_eq_add_neg] using h

omit [CharZero K] in
theorem grade_negative (d : ℤ) (hd : d < 0) : grade (K := K) d = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  rw [Submodule.mem_bot]
  apply MvPolynomial.ext
  intro m
  by_contra hm
  have hn : 0 ≤ Finsupp.weight variableWeight m := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_nonneg
    intro s hs
    exact nsmul_nonneg (Int.natCast_nonneg _) _
  have he : Finsupp.weight variableWeight m = d := hp (by simpa using hm)
  omega

/-- A concrete instance of the graded action used by the straightening induction.
No operator relation or character formula is included as an assumption. -/
noncomputable def highestWeightAction (w : K) : HighestWeightAction K (Space K) where
  grade := grade
  negative := grade_negative
  mode := mode w
  mode_mem := mode_mem_grade w
  vacuum := 1
  vacuum_mem := isWeightedHomogeneous_one K variableWeight

theorem mode_eq_zero_of_degree_lt (w : K) (i d : ℤ) (p : Space K)
    (hp : p ∈ grade d) (hi : d < i) : mode w i p = 0 := by
  have hm := mode_mem_grade w i d p hp
  rw [grade_negative (d - i) (by omega), Submodule.mem_bot] at hm
  exact hm

/-- The actual initial reduction for the triple vacuum (minimum part two).
At index zero the shorter word is retained with coefficient 1/4. -/
theorem initial_reduction (w : K) (i : ℤ) (hi : -2 < i) :
    (highestWeightAction w).wordValue [i] ∈
      higherSpan (K := K) (highestWeightAction w).wordValue [i] := by
  change mode w i 1 ∈ _
  by_cases hpos : 0 < i
  · rw [mode_vacuum_pos w i hpos]
    exact Submodule.zero_mem _
  have hc : i = -1 ∨ i = 0 := by omega
  rcases hc with rfl | rfl
  · rw [mode_neg_one_vacuum]
    exact Submodule.zero_mem _
  · rw [mode_zero_vacuum]
    have he : (highestWeightAction w).wordValue [] ∈
        higherSpan (K := K) (highestWeightAction w).wordValue [0] :=
      mem_higherSpan _ (Or.inl (by simp)) (by simp)
    have hs := (higherSpan (K := K) (highestWeightAction w).wordValue [0]).smul_mem
      (1 / 4 : K) he
    simpa [HighestWeightAction.wordValue, highestWeightAction, Algebra.smul_def] using hs

/-- On each suffix vector, both quadratic tails stop at an explicit
finite cutoff. This supports finite extraction of source mode identities. -/
theorem pair_tails_eventually_zero (w : K) (a b : ℤ) (t : Word) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p →
      (highestWeightAction w).wordValue ([a - p, b + p] ++ t) = 0 ∧
      (highestWeightAction w).wordValue ([b - p, a + p] ++ t) = 0 := by
  let d : ℤ := -t.sum
  refine ⟨(max (d - a) (d - b)).toNat + 1, ?_⟩
  intro p hp
  have ht : (highestWeightAction w).wordValue t ∈ grade d :=
    (highestWeightAction w).wordValue_mem t
  have ha : d < a + p := by omega
  have hb : d < b + p := by omega
  have hz1 := mode_eq_zero_of_degree_lt w (a + p) d _ ht ha
  have hz2 := mode_eq_zero_of_degree_lt w (b + p) d _ ht hb
  constructor <;>
    simp only [List.cons_append, List.nil_append, HighestWeightAction.wordValue]
  · change mode w (a - p) (mode w (b + p) ((highestWeightAction w).wordValue t)) = 0
    rw [hz2, map_zero]
  · change mode w (b - p) (mode w (a + p) ((highestWeightAction w).wordValue t)) = 0
    rw [hz1, map_zero]

end KanadeRussell.Tsuchioka.Fock
