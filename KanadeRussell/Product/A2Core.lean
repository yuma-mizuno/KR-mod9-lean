import KanadeRussell.Product.A2ConstantTerm
import KanadeRussell.Product.LambertComparison
import KanadeRussell.Infra.Theta
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The shifted A₂ product in the original integer power-series ring. -/
open PowerSeries PowerSeries.WithPiTopology MvLaurentSeries
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Product

def coreExponent (r s : ℤ) : ℤ := 3*(r^2+r*s+s^2)+r+2*s

theorem coreExponent_nonneg (r s : ℤ) : 0 ≤ coreExponent r s := by
  unfold coreExponent
  nlinarith [sq_nonneg (6*r+3*s+1), sq_nonneg (3*s+1)]

noncomputable def coreTheta : PowerSeries ℤ :=
  ∑' rs : ℤ × ℤ, q ^ (coreExponent rs.1 rs.2).toNat

theorem summable_coreTheta :
    Summable (fun rs : ℤ × ℤ => q ^ (coreExponent rs.1 rs.2).toNat) := by
  apply (summable_iff_summable_coeff _).mpr
  intro k
  apply summable_of_hasFiniteSupport
  apply ((Set.finite_Icc (-(4*(k:ℤ)+4)) (4*k+4)).prod
    (Set.finite_Icc (-(4*(k:ℤ)+4)) (4*k+4))).subset
  rintro ⟨r,s⟩ hn
  have he : (coreExponent r s).toNat = k := by
    by_contra he
    exact hn (by simp [q, coeff_X_pow, Ne.symm he])
  have hq : coreExponent r s = (k:ℤ) := by
    rw [← Int.toNat_of_nonneg (coreExponent_nonneg r s), he]
  have hb : r^2+s^2 ≤ 4*(k:ℤ)+4 := by
    dsimp only [coreExponent] at hq
    nlinarith [sq_nonneg (r+s), sq_nonneg (r+1), sq_nonneg (s+2)]
  change (-(4*(k:ℤ)+4) ≤ r ∧ r ≤ 4*k+4) ∧
    (-(4*(k:ℤ)+4) ≤ s ∧ s ≤ 4*k+4)
  constructor <;> constructor <;> nlinarith [sq_nonneg r, sq_nonneg s]

theorem baseChange2_coreTheta :
    LevelNine.baseChange2 coreTheta = A2ConstantTerm.core := by
  have h := summable_coreTheta.hasSum.map (LevelNine.baseChange2 (R := ℤ))
    LevelNine.baseChange2_continuous
  apply h.unique
  apply A2ConstantTerm.summable_core.hasSum.congr_fun
  rintro ⟨r,s⟩
  dsimp only [Function.comp_def]
  rw [LevelNine.baseChange2_q_pow, Int.toNat_of_nonneg (coreExponent_nonneg r s)]
  congr 1
  dsimp only [coreExponent]
  ring

/-- The shifted A₂ theta series is the three-core Euler quotient. -/
theorem coreTheta_product : E 1 * coreTheta = (E 3)^3 := by
  apply LevelNine.baseChange2_injective
  rw [map_mul, map_pow, baseChange2_coreTheta,
    LevelNine.baseChange2_E 1 (by decide), LevelNine.baseChange2_E 3 (by decide)]
  exact A2ConstantTerm.core_product

end KanadeRussell.Product
