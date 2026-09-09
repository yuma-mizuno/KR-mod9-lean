import KanadeRussell.Representation.ModeCasimirOperatorCancellation
import KanadeRussell.Representation.TensorModeCasimir
import KanadeRussell.Representation.ModeCasimirTelescoping
import KanadeRussell.Representation.ModePairingBoundary

/-! Passing the finite normal-ordering telescopes to the actual locally finite
operator uses a common cutoff for a polynomial and its lowering image. -/

set_option backward.isDefEq.respectTransparency false
namespace KanadeRussell.Tsuchioka.Fock
open KanadeRussell.Representation
attribute [local instance] LieRing.ofAssociativeRing
variable {K : Type*} [Field K] [CharZero K]

theorem tensorModeCasimir_apply_eq_partial (w : K) (p : Space K) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → normalOrderedMode w ((n : ℤ)+1) p = 0) :
    tensorModeCasimir w p = modeCasimirPartial w N p := by
  rw [tensorModeCasimir_apply_eq_sum w p N hN]
  simp only [modeCasimirPartial, LinearMap.smul_apply, LinearMap.sum_apply]

theorem tensorModeCasimir_lie_of_cancellation (w : K) (hw : w^4-w^2+1=0)
    (i : Fin 3)
    (hbulk : ∀ n : ℕ, 1 ≤ n →
      modeCasimirLower w ((n:ℤ)+1) i + modeCasimirUpper w (n:ℤ) i = 0) :
    ⁅tensorModeCasimir w, chevalleyF w i⁆ =
      (2 * (AffineWeightLattice.symmetrizer i : K)) •
        (chevalleyF w i * chevalleyH w i) := by
  apply LinearMap.ext
  intro p
  obtain ⟨N, hN⟩ := principalMode_eventually_zero w p
  obtain ⟨L, hL⟩ := normalOrderedMode_eventually_zero w (chevalleyF w i p)
  let T := max N L + 1
  have ht : 1 ≤ T := by dsimp [T]; omega
  have hp : ∀ n : ℕ, T ≤ n → normalOrderedMode w ((n:ℤ)+1) p = 0 := by
    intro n hn
    apply normalOrderedMode_eq_zero
    intro r
    exact_mod_cast hN (n+1) (by dsimp [T] at hn; omega) r
  have hFp : ∀ n : ℕ, T ≤ n →
      normalOrderedMode w ((n:ℤ)+1) (chevalleyF w i p) = 0 := by
    intro n hn
    exact hL n (by dsimp [T] at hn; omega)
  have htail : modeCasimirUpper w (T:ℤ) i p = 0 :=
    modeCasimirUpper_apply_eq_zero w T i p (hN T (by dsimp [T]; omega))
  have hfinite := congrArg (fun a : Module.End K (Space K) => a p)
    (modeCasimirPartial_lie_of_boundary w T ht i (AffineWeightLattice.symmetrizer i : K)
      hbulk (modeCasimirLower_one w hw i))
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, htail, smul_zero, add_zero] at hfinite ⊢
  rw [tensorModeCasimir_apply_eq_partial w p T hp,
    tensorModeCasimir_apply_eq_partial w (chevalleyF w i p) T hFp]
  exact hfinite

theorem tensorModeCasimir_lie (w : K) (hw : w^4-w^2+1=0) (i : Fin 3) :
    ⁅tensorModeCasimir w, chevalleyF w i⁆ =
      (2 * (AffineWeightLattice.symmetrizer i : K)) •
        (chevalleyF w i * chevalleyH w i) :=
  tensorModeCasimir_lie_of_cancellation w hw i
    (fun n hn => modeCasimir_bulk_cancellation w hw n hn i)
end KanadeRussell.Tsuchioka.Fock
