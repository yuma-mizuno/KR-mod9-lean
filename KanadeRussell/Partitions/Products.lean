import KanadeRussell.Product.Defs
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The product coefficients count partitions with the specified residues modulo nine. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Partitions

noncomputable def residueSeries (s : Finset ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ((Nat.Partition.restricted n (fun k => k%9 ∈ s)).card:ℤ)

theorem hasProd_residue (r : ℕ) (hr : 0 < r) (hr9 : r < 9) :
    HasProd (fun n : ℕ => if (n+1)%9 = r then 1-q^(n+1) else 1) (P9 r) := by
  have hinj : Function.Injective (fun k : ℕ => r+9*k-1) := by
    intro k l h
    dsimp at h
    omega
  apply (hinj.hasProd_iff ?_).mp
  · have hh := hasProd_P9 (r-1)
    rw [Nat.sub_add_cancel hr] at hh
    apply hh.congr_fun
    intro k
    dsimp only [Function.comp_def]
    have he : r+9*k-1+1 = r+9*k := by omega
    rw [he]
    have hm : (r+9*k)%9 = r := by omega
    rw [hm, if_pos rfl, pow_add, pow_mul]
  · intro k hk
    have he : (k+1)%9 ≠ r := by
      intro h
      apply hk
      refine ⟨(k+1)/9, ?_⟩
      change r+9*((k+1)/9)-1 = k
      omega
    simp [he]

theorem hasProd_residue_set (s : Finset ℕ) (hs : ∀ r ∈ s, 0 < r ∧ r < 9) :
    HasProd (fun n : ℕ => if (n+1)%9 ∈ s then 1-q^(n+1) else 1) (∏ r ∈ s, P9 r) := by
  have hh : HasProd (fun n : ℕ => ∏ r ∈ s, if (n+1)%9 = r then 1-q^(n+1) else 1)
      (∏ r ∈ s, P9 r) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert r s hr ih =>
      have hr' := hs r (Finset.mem_insert_self _ _)
      have hs' : ∀ j ∈ s, 0 < j ∧ j < 9 := fun j hj => hs j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.prod_insert hr] using (hasProd_residue r hr'.1 hr'.2).mul (ih hs')
  simpa only [Finset.prod_ite_eq] using hh

/-- This cardinality series is the inverse of the indicated convergent Euler product. -/
theorem residueSeries_mul (s : Finset ℕ) (hs : ∀ r ∈ s, 0 < r ∧ r < 9) :
    residueSeries s*(∏ r ∈ s, P9 r) = 1 := by
  have hg := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun k => k%9 ∈ s)
  have hh := hg.mul (hasProd_residue_set s hs)
  apply hh.unique
  apply (hasProd_one : HasProd (fun _ : ℕ => (1:PowerSeries ℤ)) 1).congr_fun
  intro n
  split_ifs
  · simp only [pow_mul]
    exact tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  · simp

theorem residueSeries_eq (s : Finset ℕ) (hs : ∀ r ∈ s, 0 < r ∧ r < 9) :
    residueSeries s = bInv (∏ r ∈ s, P9 r) := by
  have hu : IsUnit (∏ r ∈ s, P9 r) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert r s hr ih =>
      rw [Finset.prod_insert hr]
      exact (isUnit_P9 r (hs r (Finset.mem_insert_self _ _)).1).mul
        (ih (fun j hj => hs j (Finset.mem_insert_of_mem hj)))
  apply hu.mul_right_cancel
  rw [residueSeries_mul s hs, hu.bInv_mul_cancel]

theorem K₁_eq_residueSeries : K₁ = residueSeries {1,3,6,8} := by
  rw [residueSeries_eq _ (by intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr; rcases hr with rfl | rfl | rfl | rfl <;> omega)]
  norm_num [K₁, Finset.prod_insert, Finset.prod_singleton]
  congr 1
  ring

theorem K₂_eq_residueSeries : K₂ = residueSeries {2,3,6,7} := by
  rw [residueSeries_eq _ (by intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr; rcases hr with rfl | rfl | rfl | rfl <;> omega)]
  norm_num [K₂, Finset.prod_insert, Finset.prod_singleton]
  congr 1
  ring

theorem K₃_eq_residueSeries : K₃ = residueSeries {3,4,5,6} := by
  rw [residueSeries_eq _ (by intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr; rcases hr with rfl | rfl | rfl | rfl <;> omega)]
  norm_num [K₃, Finset.prod_insert, Finset.prod_singleton]
  congr 1
  ring


theorem coeff_K₁ (n : ℕ) : coeff n K₁ =
    ((Nat.Partition.restricted n (fun k => k%9 ∈ ({1,3,6,8}:Finset ℕ))).card:ℤ) := by
  rw [K₁_eq_residueSeries, residueSeries, coeff_mk]

theorem coeff_K₂ (n : ℕ) : coeff n K₂ =
    ((Nat.Partition.restricted n (fun k => k%9 ∈ ({2,3,6,7}:Finset ℕ))).card:ℤ) := by
  rw [K₂_eq_residueSeries, residueSeries, coeff_mk]

theorem coeff_K₃ (n : ℕ) : coeff n K₃ =
    ((Nat.Partition.restricted n (fun k => k%9 ∈ ({3,4,5,6}:Finset ℕ))).card:ℤ) := by
  rw [K₃_eq_residueSeries, residueSeries, coeff_mk]

end KanadeRussell.Partitions
