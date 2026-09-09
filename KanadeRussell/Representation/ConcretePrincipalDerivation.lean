import KanadeRussell.Representation.ConcreteHighestWeight
import KanadeRussell.Representation.PrincipalDerivation

/-! The abstract principal derivation is precisely the original tensor derivation
plus the scalar that normalizes the chosen seed to degree zero. -/
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Representation
open Tsuchioka Tsuchioka.Fock Heisenberg Sectors
variable {K : Type*} [Field K] [CharZero K]

theorem tensorPrincipalHighestWeightModule_principalDerivation_val
    (w : K) (hw : w^4-w^2+1=0) (seed : Space K) (d : ℤ) (hd : seed ∈ grade d)
    (hlow : ∀ e : ℤ, e < d → tensorCyclicSpan w seed ⊓ grade e = ⊥)
    (hne : seed ≠ 0) (lambda : Fin 3 → ℕ)
    (hE : ∀ i, chevalleyE w i seed = 0)
    (hH : ∀ i, chevalleyH w i seed = (lambda i : K) • seed)
    (hint : ∀ i : Fin 3, ∀ v ∈ tensorCyclicSpan w seed,
      (∃ n : ℕ, ((chevalleyE w i)^n) v = 0) ∧
      (∃ n : ℕ, ((chevalleyF w i)^n) v = 0))
    (v : tensorCyclicSpan w seed) :
    ((tensorPrincipalHighestWeightModule w hw seed d hd hlow hne lambda hE hH hint).principalDerivation v).val =
      Fock.principalDerivation v.val + (d : K) • v.val := by
  let M := tensorPrincipalHighestWeightModule w hw seed d hd hlow hne lambda hE hH hint
  let e := (tensorCyclicSpan w seed).subtype
  have he : e.comp M.principalDerivation = Fock.principalDerivation.comp e + (d:K) • e := by
    apply M.linearMap_ext_on_grade
    intro n p hp
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
    rw [M.principalDerivation_of_mem n p hp, map_smul]
    have hg : p.val ∈ grade (n+d) := hp
    change -(n:K) • p.val = -degreeOperator p.val + (d:K) • p.val
    rw [degreeOperator_eq_of_grade (n+d) p.val hg]
    push_cast
    module
  exact DFunLike.congr_fun he v

theorem skewPrincipalModule_principalDerivation_val (w : K) (hw : w^4-w^2+1=0)
    (v : tensorCyclicSpan w (skewSeed : Space K)) :
    ((skewPrincipalModule w hw).principalDerivation v).val =
      Fock.principalDerivation v.val + v.val := by
  simpa only [skewPrincipalModule, Int.cast_one, one_smul] using
    tensorPrincipalHighestWeightModule_principalDerivation_val w hw skewSeed 1 skewSeed_grade
      (tensor_skew_grade_below_one w hw) skewSeed_ne_zero (fun i => if i=2 then 0 else 1)
      (chevalleyE_skewSeed w) (by intro i; simpa using chevalleyH_skewSeed w hw i)
      (skew_tensor_integrable w hw) v

theorem vacuumPrincipalModule_principalDerivation_val (w : K) (hw : w^4-w^2+1=0)
    (v : tensorCyclicSpan w (1 : Space K)) :
    ((vacuumPrincipalModule w hw).principalDerivation v).val = Fock.principalDerivation v.val := by
  simpa only [vacuumPrincipalModule, Int.cast_zero, zero_smul, add_zero] using
    tensorPrincipalHighestWeightModule_principalDerivation_val w hw 1 0
      (MvPolynomial.isWeightedHomogeneous_one K variableWeight)
      (tensor_vacuum_grade_below_zero w) one_ne_zero (fun i => if i=0 then 3 else 0)
      (chevalleyE_vacuum w) (by intro i; simpa using chevalleyH_vacuum w i)
      (vacuum_tensor_integrable w hw) v

theorem alternatingPrincipalModule_principalDerivation_val (w : K) (hw : w^4-w^2+1=0)
    (v : tensorCyclicSpan w (alternatingSeed : Space K)) :
    ((alternatingPrincipalModule w hw).principalDerivation v).val =
      Fock.principalDerivation v.val + (3:K) • v.val := by
  simpa only [alternatingPrincipalModule, Int.cast_ofNat] using
    tensorPrincipalHighestWeightModule_principalDerivation_val w hw alternatingSeed 3 alternatingSeed_grade
      (tensor_alternating_grade_below_three w hw) alternatingSeed_ne_zero
      (fun i => if i=2 then 1 else 0) (chevalleyE_alternatingSeed w)
      (by intro i; simpa using chevalleyH_alternatingSeed w hw i)
      (alternating_tensor_integrable w hw) v

end KanadeRussell.Representation
