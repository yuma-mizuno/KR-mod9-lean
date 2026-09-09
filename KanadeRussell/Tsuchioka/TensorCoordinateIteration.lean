import KanadeRussell.Tsuchioka.TensorLieCoordinates
import KanadeRussell.Tsuchioka.SerreUniversal

/-! Iterated finite coordinates evaluate to iterated adjoint actions. -/

set_option backward.isDefEq.respectTransparency false

namespace KanadeRussell.Tsuchioka.Fock
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

noncomputable def tensorCoordinateAd (w : K) (a : ℤ) (u v : Fin 4 → K) : ℕ → Fin 4 → K
  | 0 => v
  | n+1 => tensorCoordinateBracket w a (((n : ℤ)+1)*a) u (tensorCoordinateAd w a u v n)

theorem tensorModeEvaluate_ad (w : K) (hw : w^4-w^2+1=0) (a : ℤ)
    (u v : Fin 4 → K) (n : ℕ) :
    tensorModeEvaluate w (((n : ℤ)+1)*a) (tensorCoordinateAd w a u v n) =
      ((LieAlgebra.ad K (Module.End K (Space K)) (tensorModeEvaluate w a u))^n)
        (tensorModeEvaluate w a v) := by
  induction n with
  | zero => simp [tensorCoordinateAd]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, ← ih]
    change tensorModeEvaluate w ((((n+1 : ℕ) : ℤ)+1)*a)
      (tensorCoordinateBracket w a (((n : ℤ)+1)*a) u (tensorCoordinateAd w a u v n)) = _
    have hd : (((n+1 : ℕ) : ℤ)+1)*a = a+((n : ℤ)+1)*a := by push_cast; ring
    rw [hd, ← tensorModeEvaluate_lie w hw]

end KanadeRussell.Tsuchioka.Fock
