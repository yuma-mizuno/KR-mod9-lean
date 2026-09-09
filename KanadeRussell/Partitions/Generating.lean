import KanadeRussell.Partitions.Decomposition
import KanadeRussell.Partitions.Transfer
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Convergent generating functions for admissible partitions. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Partitions
open Infra

def Partition (minimum : ℕ) := {l : List ℕ // Admissible minimum l}

theorem finite_fixedWeight (minimum : ℕ) (hm : 1 ≤ minimum) (n : ℕ) :
    Finite {p : Partition minimum // p.val.sum = n} := by
  let f : {p : Partition minimum // p.val.sum = n} → Composition n := fun p =>
    ⟨p.val.val,fun ha => hm.trans (p.val.property.1 _ ha),p.property⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Composition.blocks h

theorem weight_tendsto (minimum : ℕ) (hm : 1 ≤ minimum) :
    Filter.Tendsto (fun p : Partition minimum => p.val.sum) Filter.cofinite Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro n
  rw [Filter.eventually_cofinite]
  have hf (k : Fin n) : Set.Finite {p : Partition minimum | p.val.sum = k.val} := by
    exact Set.finite_coe_iff.mp (finite_fixedWeight minimum hm k.val)
  apply (Set.finite_iUnion hf).subset
  intro p hp
  simp only [Set.mem_setOf_eq, not_le] at hp
  exact Set.mem_iUnion.mpr ⟨⟨p.val.sum,hp⟩,rfl⟩

theorem summable_partitionWeight (minimum : ℕ) (hm : 1 ≤ minimum) :
    Summable (fun p : Partition minimum => (q^p.val.sum : QSeries)) := by
  simpa using DiscreteTopology.summable_mul_pow_of_tendsto_atTop (weight_tendsto minimum hm)
    (f := fun _ => (1:QSeries)) (q := q) (by simp)

noncomputable def generating (minimum : ℕ) : PowerSeries QSeries :=
  weightedSeries (fun p : Partition minimum => p.val.length) (fun p => q^p.val.sum)

theorem hasSum_generating (minimum : ℕ) (hm : 1 ≤ minimum) :
    HasSum (fun p : Partition minimum => monomial p.val.length (q^p.val.sum)) (generating minimum) :=
  hasSum_weightedSeries _ (summable_partitionWeight minimum hm)

theorem generating_constant (minimum : ℕ) : constantCoeff (generating minimum) = 1 := by
  let e : Partition minimum := ⟨[],by simp [Admissible,Valid]⟩
  rw [← coeff_zero_eq_constantCoeff_apply, generating, weightedSeries, coeff_mk,
    tsum_eq_single e]
  · simp [e]
  · intro p hp
    have hh : ¬ 0 = p.val.length := by
      intro hl
      apply hp
      apply Subtype.ext
      exact List.length_eq_zero_iff.mp hl.symm
    simp [hh]

def InitialBlock (minimum : ℕ) := {i : Fin 7 // ∀ a ∈ block i, minimum ≤ a}

def assemble (minimum : ℕ) (hm : 1 ≤ minimum) (hm3 : minimum ≤ 3)
    (p : Σ i : InitialBlock minimum, Partition (nextMinimum i.val)) : Partition minimum :=
  ⟨block p.1.val ++ p.2.val.map (·+3),
    (admissible_block_append minimum hm hm3 p.1.val p.2.val
      (fun a ha => (nextMinimum_bounds p.1.val).1.trans (p.2.property.1 a ha))).mpr
        ⟨p.1.property,p.2.property⟩⟩

theorem assemble_bijective (minimum : ℕ) (hm : 1 ≤ minimum) (hm3 : minimum ≤ 3) :
    Function.Bijective (assemble minimum hm hm3) := by
  constructor
  · rintro ⟨⟨i,hi⟩,s⟩ ⟨⟨j,hj⟩,t⟩ he
    have hh := congrArg Subtype.val he
    obtain ⟨hij,hst⟩ := decomposition_unique i j s.val t.val
      (fun a ha => (nextMinimum_bounds i).1.trans (s.property.1 a ha))
      (fun a ha => (nextMinimum_bounds j).1.trans (t.property.1 a ha)) hh
    subst j
    have he : s = t := Subtype.ext hst
    subst t
    rfl
  · intro p
    obtain ⟨i,t,he,hb,ht⟩ := exists_decomposition minimum hm p.val p.property
    exact ⟨⟨⟨i,hb⟩,⟨t,ht⟩⟩,Subtype.ext he.symm⟩

theorem monomial_block_append (i : Fin 7) (t : List ℕ) :
    monomial (block i ++ t.map (·+3)).length (q^(block i ++ t.map (·+3)).sum) =
      monomial (block i).length (q^(block i).sum)*
        rescale (q^3) (monomial t.length (q^t.sum) : PowerSeries QSeries) := by
  have hr (n : ℕ) (a r : QSeries) : rescale r (monomial n a) = monomial n (r^n*a) := by
    ext k
    simp only [coeff_rescale,coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  rw [hr,monomial_mul_monomial]
  simp only [List.length_append,List.length_map,List.sum_append]
  congr 1
  have hs : (t.map (·+3)).sum = t.sum+3*t.length := by
    induction t with
    | nil => simp
    | cons a t ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; omega
  rw [hs,pow_add,pow_add,pow_mul]
  ring

theorem generating_recurrence (minimum : ℕ) (hm : 1 ≤ minimum) (hm3 : minimum ≤ 3) :
    generating minimum = ∑ i : Fin 7, if ∀ a ∈ block i, minimum ≤ a then
      monomial (block i).length (q^(block i).sum)*rescale (q^3) (generating (nextMinimum i)) else 0 := by
  classical
  letI : Fintype (InitialBlock minimum) := by unfold InitialBlock; infer_instance
  let e := Equiv.ofBijective (assemble minimum hm hm3) (assemble_bijective minimum hm hm3)
  let g (i : Fin 7) := monomial (block i).length (q^(block i).sum)*
    rescale (q^3) (generating (nextMinimum i))
  have ha := e.hasSum_iff.mpr (hasSum_generating minimum hm)
  have hb (i : InitialBlock minimum) : HasSum
      (fun t : Partition (nextMinimum i.val) =>
        monomial (block i.val ++ t.val.map (·+3)).length (q^(block i.val ++ t.val.map (·+3)).sum))
      (g i.val) := by
    apply (((hasSum_generating (nextMinimum i.val) (nextMinimum_bounds i.val).1).map
      (rescale (q^3)) (continuous_rescale (q^3))).mul_left
        (monomial (block i.val).length (q^(block i.val).sum))).congr_fun
    intro t
    exact monomial_block_append i.val t.val
  have hc := ha.sigma hb
  have he : generating minimum = ∑ i : InitialBlock minimum, g i.val := by
    exact hc.tsum_eq.symm.trans (tsum_fintype _)
  rw [he,← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i => ∀ a ∈ block i, minimum ≤ a))
    (by intro i; simp) g).symm

theorem generating_transfer : TransferSystem (fun i => generating (i.val+1)) := by
  intro i
  change generating (i.val+1) = _
  rw [generating_recurrence _ (by omega) (by omega)]
  fin_cases i <;>
    norm_num [block,nextMinimum,transition,Fin.sum_univ_succ] <;> ring

/-- The full length-refined double sums enumerate the admissible partitions. -/
theorem sources_eq_generating : sources = fun i => generating (i.val+1) := by
  apply transfer_unique _ _ sources_transfer generating_transfer
  intro i
  rw [generating_constant]
  fin_cases i <;> exact Source.LengthSeries.constantCoeff_T _ _

theorem first_generating : Source.LengthSeries.T 0 0 = generating 1 := by
  exact congrFun sources_eq_generating 0

theorem second_generating : Source.LengthSeries.T 1 3 = generating 2 := by
  exact congrFun sources_eq_generating 1

theorem third_generating : Source.LengthSeries.T 2 3 = generating 3 := by
  exact congrFun sources_eq_generating 2

end KanadeRussell.Partitions
