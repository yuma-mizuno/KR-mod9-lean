import KanadeRussell.Straightening.FinitePairs
import KanadeRussell.Straightening.PairCoefficients
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-! The adjacent G2/G3/G6 combination, including its reversed endpoint. -/
namespace KanadeRussell.Straightening
open Tsuchioka PowerSeries
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

noncomputable def adjacentCombination (ρ : HighestWeightAction K V) (w : K)
    (a : ℤ) (t : Word) : V :=
  let r := Coefficients.tCoeff w/Coefficients.mCoeff w
  coeff 0 (Scalar.G6 w) •
    (pairSum ρ (fun p => coeff p (Scalar.G w 1)) a (a+1) t +
     pairSum ρ (fun p => coeff p (Scalar.G w 1)) (a+1) a t -
     r • (pairSum ρ (fun p => coeff p (Scalar.G w 2)) a (a+1) t +
          pairSum ρ (fun p => coeff p (Scalar.G w 2)) (a+1) a t)) +
  (1-r) • (pairSum ρ (fun p => coeff p (Scalar.G6 w)) a (a+1) t -
            pairSum ρ (fun p => coeff p (Scalar.G6 w)) (a+1) a t)

theorem adjacent_combination_eq (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1=0) (a : ℤ) (t : Word) :
    adjacentCombination ρ w a t =
      (8*(Coefficients.tCoeff w/Coefficients.mCoeff w)) • pairSum ρ (adjacentCoeff w) a (a+1) t := by
  let r := Coefficients.tCoeff w/Coefficients.mCoeff w
  let g := coeff 0 (Scalar.G6 w)
  let d (n : ℕ) := g*(coeff n (Scalar.G w 1)-r*coeff n (Scalar.G w 2)) + (1-r)*coeff n (Scalar.G6 w)
  let e (n : ℕ) := g*(coeff n (Scalar.G w 1)-r*coeff n (Scalar.G w 2)) - (1-r)*coeff n (Scalar.G6 w)
  have he : adjacentCombination ρ w a t = pairSum ρ d a (a+1) t + pairSum ρ e (a+1) a t := by
    simp only [adjacentCombination, d, e, pairSum_add, pairSum_sub, pairSum_smul]
    dsimp [r,g]
    module
  have he0 : e 0 = 0 := by
    dsimp [e,g]
    rw [Scalar.coeff_zero_G, Scalar.coeff_zero_G]
    ring
  rw [he, pairSum_succ_split ρ e (a+1) a t, show a+1-1=a by omega, he0,
    zero_smul, zero_add, ← pairSum_add, ← pairSum_smul]
  apply congrArg (fun c => pairSum ρ c a (a+1) t)
  funext n
  have hh := div_mul_cancel₀ (d n+e (n+1)) (adjacent_denominator_ne_zero w hw)
  dsimp [d,e,r,g] at hh ⊢
  unfold adjacentCoeff
  linear_combination -hh

theorem adjacent_expansion_of_combined_relation (ρ : HighestWeightAction K V) (w : K)
    (hw : w^4-w^2+1=0) (a : ℤ)
    (h : ∀ t, adjacentCombination ρ w a t ∈
      shorterSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a,a+1]) :
    PairExpansion ρ a (a+1) (adjacentCoeff w) := by
  apply pairExpansion_of_pairSum ρ a (a+1) _ (adjacentCoeff_zero w hw)
  intro t
  have hh := h t
  rw [adjacent_combination_eq ρ w hw a t] at hh
  exact ((shorterSpan (K := K) (fun u => ρ.wordValue (u ++ t)) [a,a+1]).smul_mem_iff
    (adjacent_denominator_ne_zero w hw)).mp hh

end KanadeRussell.Straightening
