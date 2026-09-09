import KanadeRussell.Representation.PrincipalHighestWeight
import KanadeRussell.Representation.PrincipalGrading
import KanadeRussell.Representation.ThreeSectorIntegrability
import KanadeRussell.Representation.ConcreteCharacters

/-! The actual three cyclic modules satisfy every hypothesis of the universal
graded integrable highest-weight character theorem. No character formula is used. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock Heisenberg Sectors
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def tensorPrincipalHighestWeightModule (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hd : seed ∈ grade d)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥)
    (hne : seed ≠ 0) (lambda : Fin 3 → ℕ)
    (hE : ∀ i, chevalleyE w i seed = 0)
    (hH : ∀ i, chevalleyH w i seed = (lambda i : K) • seed)
    (hint : ∀ i : Fin 3, ∀ v ∈ tensorCyclicSpan w seed,
      (∃ n : ℕ, ((chevalleyE w i)^n) v = 0) ∧
      (∃ n : ℕ, ((chevalleyF w i)^n) v = 0)) :
    PrincipalHighestWeightModule K (tensorCyclicSpan w seed) where
  action := tensorCyclicChevalleyAction w hw seed
  grade := (shiftedTensorCyclicGrading w hw seed d hlow).grade
  grading_internal := tensorCyclicSpan_shiftedGrade_isInternal w hw seed d hd
  grade_negative := (shiftedTensorCyclicGrading w hw seed d hlow).negative
  grade_finite := shiftedTensorCyclicGrading_grade_finite w hw seed d hlow
  E_grade i n v hv := by
    change chevalleyE w i v.val ∈ grade ((n-1)+d)
    have h := chevalleyE_mem_grade w i (n+d) v.val hv
    convert h using 1 <;> congr 1 <;> ring
  F_grade i n v hv := by
    change chevalleyF w i v.val ∈ grade ((n+1)+d)
    have h := chevalleyF_mem_grade w i (n+d) v.val hv
    convert h using 1 <;> congr 1 <;> ring
  H_grade i n v hv := chevalleyH_mem_grade w i (n+d) v.val hv
  highestVector := ⟨seed, tensorCyclicSpan_seed w seed⟩
  highestVector_ne_zero h := hne (congrArg Subtype.val h)
  highestVector_grade := by change seed ∈ grade (0+d); simpa using hd
  highestWeight := lambda
  E_highestVector i := by apply Subtype.ext; exact hE i
  H_highestVector i := by apply Subtype.ext; exact hH i
  E_locally_nilpotent i v := by
    obtain ⟨n, hn⟩ := (hint i v.val v.property).1
    refine ⟨n, ?_⟩
    apply Subtype.ext
    have h := Heisenberg.intertwine_pow (tensorCyclicSpan w seed).subtype
      ((tensorCyclicChevalleyAction w hw seed).E i) (chevalleyE w i) (fun _ => rfl) n v
    exact h.trans hn
  F_locally_nilpotent i v := by
    obtain ⟨n, hn⟩ := (hint i v.val v.property).2
    refine ⟨n, ?_⟩
    apply Subtype.ext
    have h := Heisenberg.intertwine_pow (tensorCyclicSpan w seed).subtype
      ((tensorCyclicChevalleyAction w hw seed).F i) (chevalleyF w i) (fun _ => rfl) n v
    exact h.trans hn
  cyclic := tensorCyclicChevalleyAction_cyclic w hw seed d hd

theorem tensorPrincipalHighestWeightModule_character_eq (w : K) (hw : w^4-w^2+1=0)
    (seed : Space K) (d : ℤ) (hd : seed ∈ grade d)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥)
    (hne : seed ≠ 0) (lambda : Fin 3 → ℕ)
    (hE : ∀ i, chevalleyE w i seed = 0)
    (hH : ∀ i, chevalleyH w i seed = (lambda i : K) • seed)
    (hint : ∀ i : Fin 3, ∀ v ∈ tensorCyclicSpan w seed,
      (∃ n : ℕ, ((chevalleyE w i)^n) v = 0) ∧
      (∃ n : ℕ, ((chevalleyF w i)^n) v = 0)) :
    (tensorPrincipalHighestWeightModule w hw seed d hd hlow hne lambda hE hH hint).character =
      shiftedQuotientFullCharacter w seed d ⊥ :=
  shiftedTensorCyclicGrading_character_eq w hw seed d hlow

noncomputable def skewPrincipalModule (w : K) (hw : w^4-w^2+1=0) :
    PrincipalHighestWeightModule K (tensorCyclicSpan w (skewSeed : Space K)) :=
  tensorPrincipalHighestWeightModule w hw skewSeed 1 skewSeed_grade
    (tensor_skew_grade_below_one w hw) skewSeed_ne_zero (fun i => if i=2 then 0 else 1)
    (chevalleyE_skewSeed w) (by intro i; simpa using chevalleyH_skewSeed w hw i)
    (skew_tensor_integrable w hw)

noncomputable def vacuumPrincipalModule (w : K) (hw : w^4-w^2+1=0) :
    PrincipalHighestWeightModule K (tensorCyclicSpan w (1 : Space K)) :=
  tensorPrincipalHighestWeightModule w hw 1 0
    (MvPolynomial.isWeightedHomogeneous_one K variableWeight)
    (tensor_vacuum_grade_below_zero w) one_ne_zero (fun i => if i=0 then 3 else 0)
    (chevalleyE_vacuum w) (by intro i; simpa using chevalleyH_vacuum w i)
    (vacuum_tensor_integrable w hw)

noncomputable def alternatingPrincipalModule (w : K) (hw : w^4-w^2+1=0) :
    PrincipalHighestWeightModule K (tensorCyclicSpan w (alternatingSeed : Space K)) :=
  tensorPrincipalHighestWeightModule w hw alternatingSeed 3 alternatingSeed_grade
    (tensor_alternating_grade_below_three w hw) alternatingSeed_ne_zero
    (fun i => if i=2 then 1 else 0) (chevalleyE_alternatingSeed w)
    (by intro i; simpa using chevalleyH_alternatingSeed w hw i)
    (alternating_tensor_integrable w hw)

theorem skewPrincipalModule_character (w : K) (hw : w^4-w^2+1=0) :
    (skewPrincipalModule w hw).character = shiftedQuotientFullCharacter w skewSeed 1 ⊥ :=
  tensorPrincipalHighestWeightModule_character_eq _ _ _ _ _ _ _ _ _ _ _

theorem vacuumPrincipalModule_character (w : K) (hw : w^4-w^2+1=0) :
    (vacuumPrincipalModule w hw).character = shiftedQuotientFullCharacter w 1 0 ⊥ :=
  tensorPrincipalHighestWeightModule_character_eq _ _ _ _ _ _ _ _ _ _ _

theorem alternatingPrincipalModule_character (w : K) (hw : w^4-w^2+1=0) :
    (alternatingPrincipalModule w hw).character = shiftedQuotientFullCharacter w alternatingSeed 3 ⊥ :=
  tensorPrincipalHighestWeightModule_character_eq _ _ _ _ _ _ _ _ _ _ _

end KanadeRussell.Representation
