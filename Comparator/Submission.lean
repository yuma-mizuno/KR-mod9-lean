import Comparator.Problem
import KanadeRussell.Theorems
import KanadeRussell.Product.InitialCoefficients

/-! Proof bridges for the main KR identities and auxiliary coefficient checks. The finite and
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

/-! ## Main challenge: full double-sum/product identities -/

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

/-! ## Auxiliary checks: initial product coefficients -/

/-- The first product is `1 + q + q²` through degree two. -/
theorem product₁_initial_coefficients :
    coeff 0 product₁ = 1 ∧ coeff 1 product₁ = 1 ∧ coeff 2 product₁ = 1 := by
  rw [product₁_eq]
  exact KanadeRussell.Product.K₁_initial_coefficients

/-- The second product is `1 + q²` through degree two. -/
theorem product₂_initial_coefficients :
    coeff 0 product₂ = 1 ∧ coeff 1 product₂ = 0 ∧ coeff 2 product₂ = 1 := by
  rw [product₂_eq]
  exact KanadeRussell.Product.K₂_initial_coefficients

/-- The third product is `1` through degree two. -/
theorem product₃_initial_coefficients :
    coeff 0 product₃ = 1 ∧ coeff 1 product₃ = 0 ∧ coeff 2 product₃ = 0 := by
  rw [product₃_eq]
  exact KanadeRussell.Product.K₃_initial_coefficients

end KRChallenge.Submitted
