import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! A concrete coefficient field and Coxeter phase for the final specialization. -/
namespace KanadeRussell.Tsuchioka

noncomputable def complexPhase : ℂ := ((Real.sqrt 3 : ℂ) + Complex.I) / 2

theorem complexPhase_relation : complexPhase ^ 4 - complexPhase ^ 2 + 1 = 0 := by
  have hs : (Real.sqrt 3 : ℂ)^2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  dsimp [complexPhase]
  linear_combination
    (((Real.sqrt 3 : ℂ)^2 + 4 * (Real.sqrt 3 : ℂ) * Complex.I + 6 * Complex.I^2 - 1) / 16) * hs +
    (((Complex.I : ℂ)^2 + 4 * (Real.sqrt 3 : ℂ) * Complex.I + 13) / 16) * Complex.I_sq

end KanadeRussell.Tsuchioka
