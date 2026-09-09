import KanadeRussell.Representation.PrincipalModeDenominator
import KanadeRussell.Representation.PositivePrincipalModes

/-! Degree cutoffs of the principal Euler product agree at multiples of
twelve with the existing progression blocks. Their coefficient-topology
limit is the proved principal denominator. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Representation

noncomputable def principalEulerDegreePartial (B : ℕ) : PowerSeries ℤ :=
  ∏ n ∈ Finset.range B, ∏ r : Fin 3,
    if principalWeightSlotActive (positiveModeResidue n) r then (1-q^(n+1)) else 1

theorem principalEulerActiveProduct (k : Fin 12) (f : PowerSeries ℤ) :
    (∏ r : Fin 3, if principalWeightSlotActive k r then f else 1) =
      f ^ principalModeActiveSlotCount k := by
  rw [← Finset.prod_filter]
  simp [principalModeActiveSlotCount]

theorem positiveModeResidue_twelve_mul_add (N : ℕ) (k : Fin 12) :
    positiveModeResidue (12*N+k.val) = k := by
  apply Fin.ext
  dsimp only [positiveModeResidue]
  omega

theorem principalEulerDegreePartial_twelve_step (N : ℕ) :
    principalEulerDegreePartial (12*(N+1)) = principalEulerDegreePartial (12*N) *
      ∏ k : Fin 12, (1-q^(12*N+k.val+1)) ^ principalModeActiveSlotCount k := by
  unfold principalEulerDegreePartial
  rw [Nat.mul_add, Nat.mul_one, Finset.prod_range_add]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  rw [positiveModeResidue_twelve_mul_add, principalEulerActiveProduct]

theorem principalModeEulerBlock_step (N : ℕ) :
    principalModeEulerBlock (N+1) = principalModeEulerBlock N *
      ∏ k : Fin 12, (1-q^(12*N+k.val+1)) ^ principalModeActiveSlotCount k := by
  unfold principalModeEulerBlock
  simp only [qPochhammer_succ', mul_pow, Finset.prod_mul_distrib]
  apply congrArg (fun f : PowerSeries ℤ => principalModeEulerBlock N * f)
  apply Finset.prod_congr rfl
  intro k hk
  have hq : (q : PowerSeries ℤ)^(k.val+1) * (q^12)^N = q^(12*N+k.val+1) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hq]

theorem principalEulerDegreePartial_twelve (N : ℕ) :
    principalEulerDegreePartial (12*N) = principalModeEulerBlock N := by
  induction N with
  | zero => simp [principalEulerDegreePartial, principalModeEulerBlock]
  | succ N ih =>
    rw [principalEulerDegreePartial_twelve_step, ih, ← principalModeEulerBlock_step]

theorem principalEulerDegreePartial_twelve_tendsto :
    Filter.Tendsto (fun N : ℕ => principalEulerDegreePartial (12*N)) Filter.atTop
      (nhds (Product.dualAffineDenominator 1 1 1)) := by
  have h : (fun N : ℕ => principalEulerDegreePartial (12*N)) = principalModeEulerBlock :=
    funext principalEulerDegreePartial_twelve
  rw [h]
  exact principalModeEulerBlock_tendsto

end KanadeRussell.Representation
