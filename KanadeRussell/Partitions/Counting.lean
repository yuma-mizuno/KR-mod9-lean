import KanadeRussell.Partitions.Generating
import KanadeRussell.Partitions.Products
import KanadeRussell.Pending.LowerBounds
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Exact cardinality interpretation of both sides of the remaining lower bounds. -/
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity
namespace KanadeRussell.Partitions
open Infra

noncomputable def count (minimum n : ℕ) : ℕ :=
  Nat.card {p : Partition minimum // p.val.sum = n}

theorem sumCoeff_generating (minimum : ℕ) (hm : 1 ≤ minimum) :
    sumCoeff (generating minimum) = ∑' p : Partition minimum, q^p.val.sum :=
  sumCoeff_weightedSeries _ (summable_partitionWeight minimum hm)

theorem coeff_partitionWeight (minimum : ℕ) (hm : 1 ≤ minimum) (n : ℕ) :
    coeff n (∑' p : Partition minimum, q^p.val.sum) = (count minimum n : ℤ) := by
  classical
  letI := finite_fixedWeight minimum hm n
  letI : Fintype {p : Partition minimum // p.val.sum = n} := Fintype.ofFinite _
  have hi : Function.Injective
      (Subtype.val : {p : Partition minimum // p.val.sum = n} → Partition minimum) :=
    Subtype.val_injective
  have hh : HasSum (fun p : Partition minimum => coeff n (q^p.val.sum)) (count minimum n : ℤ) := by
    apply (hi.hasSum_iff ?_).mp
    · have hf : HasSum (fun _ : {p : Partition minimum // p.val.sum = n} => (1:ℤ))
          (count minimum n : ℤ) := by
        simpa [count,Nat.card_eq_fintype_card] using
          (hasSum_fintype (fun _ : {p : Partition minimum // p.val.sum = n} => (1:ℤ)))
      apply hf.congr_fun
      intro p
      simp only [Function.comp_def,p.property]
      exact coeff_X_pow_self n
    · intro p hp
      have hn : p.val.sum ≠ n := by
        intro h
        exact hp ⟨⟨p,h⟩,rfl⟩
      simp [q,coeff_X_pow,Ne.symm hn]
  exact ((summable_partitionWeight minimum hm).hasSum.map (coeff n)
    (continuous_coeff ℤ n)).unique hh

theorem coeff_A_count (n : ℕ) : coeff n A = (count 1 n : ℤ) := by
  have he := congrArg sumCoeff first_generating
  rw [Source.LengthSeries.sumCoeff_T,sumCoeff_generating 1 (by omega)] at he
  rw [A,he,coeff_partitionWeight 1 (by omega)]

theorem coeff_B_count (n : ℕ) : coeff n B = (count 2 n : ℤ) := by
  have he := congrArg sumCoeff second_generating
  rw [Source.LengthSeries.sumCoeff_T,sumCoeff_generating 2 (by omega)] at he
  rw [B,he,coeff_partitionWeight 2 (by omega)]

theorem coeff_C_count (n : ℕ) : coeff n C = (count 3 n : ℤ) := by
  have he := congrArg sumCoeff third_generating
  rw [Source.LengthSeries.sumCoeff_T,sumCoeff_generating 3 (by omega)] at he
  rw [C,he,coeff_partitionWeight 3 (by omega)]

/-- The only remaining input is an inequality between explicitly defined finite counts. -/
theorem lowerBounds_iff_counts : LowerBounds ↔
    (∀ n, (Nat.Partition.restricted n (fun k => k%9 ∈ ({1,3,6,8}:Finset ℕ))).card ≤ count 1 n) ∧
    (∀ n, (Nat.Partition.restricted n (fun k => k%9 ∈ ({2,3,6,7}:Finset ℕ))).card ≤ count 2 n) ∧
    (∀ n, (Nat.Partition.restricted n (fun k => k%9 ∈ ({3,4,5,6}:Finset ℕ))).card ≤ count 3 n) := by
  simp only [LowerBounds,coeff_K₁,coeff_K₂,coeff_K₃,coeff_A_count,coeff_B_count,coeff_C_count]
  norm_cast

end KanadeRussell.Partitions
