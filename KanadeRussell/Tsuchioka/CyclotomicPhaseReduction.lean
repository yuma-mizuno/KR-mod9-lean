import KanadeRussell.Tsuchioka.ScalarPhases

/-! Direct reduced polynomial representatives for arbitrary integer phases. -/

namespace KanadeRussell.Tsuchioka.Scalar
variable {K : Type*} [Field K] [CharZero K]

theorem zpow_phasePolynomial (w : K) (hw : w^4-w^2+1=0) (a : ℤ) :
    w ^ a = phasePolynomial w ⟨((-a)%12).toNat, by omega⟩ := by
  let p : Fin 12 := ⟨((-a)%12).toNat, by omega⟩
  have hp : (p.val : ℤ) = (-a)%12 := by
    dsimp [p]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  calc
    w ^ a = w ^ (-(p.val : ℤ)) := by
      apply Coefficients.zpow_eq_of_mod w hw
      rw [hp]
      omega
    _ = phasePolynomial w p := negative_phase w hw p

end KanadeRussell.Tsuchioka.Scalar
