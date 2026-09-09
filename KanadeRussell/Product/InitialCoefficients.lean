import KanadeRussell.Partitions.Products

/-! The first three coefficients of the reciprocal products, computed directly
from their restricted-partition interpretation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Product
open PowerSeries

private def twoOnes : Nat.Partition 2 := Nat.Partition.ofSums 2 {1,1} rfl

private theorem twoOnes_parts : twoOnes.parts = {1,1} := by
  simp [twoOnes,Nat.Partition.ofSums]

private theorem restricted_two_first :
    Nat.Partition.restricted 2 (fun k => k%9 ∈ ({1,3,6,8}:Finset ℕ)) = {twoOnes} := by
  ext p
  simp only [Nat.Partition.restricted,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · intro hp
    have he : p.parts = Multiset.replicate p.parts.card 1 :=
      Multiset.eq_replicate_card.mpr (by
        intro k hk
        have hpos := p.parts_pos hk
        have hle : k ≤ 2 := (Multiset.le_sum_of_mem hk).trans_eq p.parts_sum
        have hm := hp k hk
        simp only [Finset.mem_insert,Finset.mem_singleton] at hm
        omega)
    have hc : p.parts.card = 2 := by
      have hh := (congrArg Multiset.sum he.symm).trans p.parts_sum
      simpa using hh
    apply Nat.Partition.ext
    rw [he,hc,twoOnes_parts]
    rfl
  · rintro rfl
    simp [twoOnes_parts]

private theorem restricted_two_second :
    Nat.Partition.restricted 2 (fun k => k%9 ∈ ({2,3,6,7}:Finset ℕ)) = {Nat.Partition.indiscrete 2} := by
  ext p
  simp only [Nat.Partition.restricted,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · intro hp
    have he : p.parts = Multiset.replicate p.parts.card 2 :=
      Multiset.eq_replicate_card.mpr (by
        intro k hk
        have hpos := p.parts_pos hk
        have hle : k ≤ 2 := (Multiset.le_sum_of_mem hk).trans_eq p.parts_sum
        have hm := hp k hk
        simp only [Finset.mem_insert,Finset.mem_singleton] at hm
        omega)
    have hc : p.parts.card = 1 := by
      have hh := (congrArg Multiset.sum he.symm).trans p.parts_sum
      simp at hh
      omega
    apply Nat.Partition.ext
    rw [he,hc]
    simp
  · rintro rfl
    simp

private theorem restricted_two_third :
    Nat.Partition.restricted 2 (fun k => k%9 ∈ ({3,4,5,6}:Finset ℕ)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  simp only [Nat.Partition.restricted,Finset.mem_filter,Finset.mem_univ,true_and] at hp
  have he : p.parts = 0 := Multiset.eq_zero_of_forall_notMem (by
    intro k hk
    have hpos := p.parts_pos hk
    have hle : k ≤ 2 := (Multiset.le_sum_of_mem hk).trans_eq p.parts_sum
    have hm := hp k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    omega)
  have hh := p.parts_sum
  rw [he] at hh
  norm_num at hh

/-- `K₁ = 1 + q + q² + O(q³)`. -/
theorem K₁_initial_coefficients : coeff 0 K₁ = 1 ∧ coeff 1 K₁ = 1 ∧ coeff 2 K₁ = 1 := by
  simp only [Partitions.coeff_K₁]
  rw [restricted_two_first]
  norm_num [Nat.Partition.restricted]

/-- `K₂ = 1 + q² + O(q³)`. -/
theorem K₂_initial_coefficients : coeff 0 K₂ = 1 ∧ coeff 1 K₂ = 0 ∧ coeff 2 K₂ = 1 := by
  simp only [Partitions.coeff_K₂]
  rw [restricted_two_second]
  norm_num [Nat.Partition.restricted]

/-- `K₃ = 1 + O(q³)`. -/
theorem K₃_initial_coefficients : coeff 0 K₃ = 1 ∧ coeff 1 K₃ = 0 ∧ coeff 2 K₃ = 0 := by
  simp only [Partitions.coeff_K₃]
  rw [restricted_two_third]
  norm_num [Nat.Partition.restricted]
end KanadeRussell.Product
