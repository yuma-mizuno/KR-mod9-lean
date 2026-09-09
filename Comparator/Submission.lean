import Comparator.Problem
import KanadeRussell.Theorems

/-! A submission to the independent four-target challenge. The finite and
infinite products are matched explicitly to the production definitions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KRChallenge.Submitted

private theorem finite_product (d m : ℕ) :
    (∏ j ∈ Finset.range m, (1-q^(d*(j+1)))) = (q^d;q^d)_m := by
  unfold qPochhammer
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  rw [← pow_succ',← pow_mul]

private theorem summand_eq (a b : ℕ) : summand a b = KanadeRussell.sourceTerm a b := by
  funext mn
  rcases mn with ⟨m,n⟩
  have h1 : (∏ j ∈ Finset.range m, (1-q^(j+1))) = (q;q)_m := by
    simpa only [one_mul,pow_one] using finite_product 1 m
  dsimp only [summand]
  rw [h1,finite_product]
  rfl

private theorem hasProd_progression (r : ℕ) :
    HasProd (fun n : ℕ => (1-q^(9*n+r))) (KanadeRussell.P9 r) := by
  have h := hasProd_qPochhammerInf (a:=q^r)
    (show IsTopologicallyNilpotent (q^9) by simp [q])
  apply h.congr_fun
  intro n
  simp only [← pow_mul,← pow_add]
  rw [Nat.add_comm]

private theorem reciprocalProduct_eq (r₁ r₂ r₃ r₄ : ℕ) :
    reciprocalProduct r₁ r₂ r₃ r₄ =
      bInv (KanadeRussell.P9 r₁*KanadeRussell.P9 r₂*KanadeRussell.P9 r₃*KanadeRussell.P9 r₄) := by
  unfold reciprocalProduct
  congr 1
  exact (((hasProd_progression r₁).mul (hasProd_progression r₂)).mul
    (hasProd_progression r₃) |>.mul (hasProd_progression r₄)).tprod_eq

private theorem product₁_eq : product₁ = KanadeRussell.K₁ := reciprocalProduct_eq 1 3 6 8
private theorem product₂_eq : product₂ = KanadeRussell.K₂ := reciprocalProduct_eq 2 3 6 7
private theorem product₃_eq : product₃ = KanadeRussell.K₃ := reciprocalProduct_eq 3 4 5 6

theorem kr₁ : KR₁ := by
  change HasSum (summand 0 0) product₁
  rw [summand_eq,product₁_eq]
  exact KanadeRussell.kanade_russell_hasSum₁

theorem kr₂ : KR₂ := by
  change HasSum (summand 1 3) product₂
  rw [summand_eq,product₂_eq]
  exact KanadeRussell.kanade_russell_hasSum₂

theorem kr₃ : KR₃ := by
  change HasSum (summand 2 3) product₃
  rw [summand_eq,product₃_eq]
  exact KanadeRussell.kanade_russell_hasSum₃

theorem constantCoefficientNontriviality : ConstantCoefficientNontriviality := by
  unfold ConstantCoefficientNontriviality source
  rw [summand_eq,summand_eq,summand_eq,product₁_eq,product₂_eq,product₃_eq]
  simp only [coeff_zero_eq_constantCoeff]
  obtain ⟨hA,hB,hC,h₁,h₂,h₃⟩ := KanadeRussell.constantCoeff_eq_one
  change constantCoeff KanadeRussell.A ≠ 0 ∧ constantCoeff KanadeRussell.B ≠ 0 ∧
    constantCoeff KanadeRussell.C ≠ 0 ∧ constantCoeff KanadeRussell.K₁ ≠ 0 ∧
    constantCoeff KanadeRussell.K₂ ≠ 0 ∧ constantCoeff KanadeRussell.K₃ ≠ 0
  rw [hA,hB,hC,h₁,h₂,h₃]
  norm_num
end KRChallenge.Submitted
