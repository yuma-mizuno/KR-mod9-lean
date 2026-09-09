import KanadeRussell.Representation.PrincipalModeEigenframe
import KanadeRussell.Representation.CharacterSpecialization

/-! The Euler denominator of the proved active principal-mode enumeration.
No dimension or independence assertion for evaluated operators is made here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PowerSeries PowerSeries.WithPiTopology
open scoped DiscreteUniformity QTheory
namespace KanadeRussell.Representation
open Tsuchioka.Fock

def principalModeActiveSlotCount (k : Fin 12) : ℕ :=
  (Finset.univ.filter (principalWeightSlotActive k)).card

theorem principalModeActiveSlotCount_eq (k : Fin 12) :
    principalModeActiveSlotCount k = 2 + (if IsMode (k.val+1) then 1 else 0) := by
  fin_cases k <;> decide

noncomputable def principalModeEulerDenominator : PowerSeries ℤ :=
  ∏ k : Fin 12, (Product.progressionProduct 12 (k.val+1)) ^ principalModeActiveSlotCount k

theorem E_one_split_twelve : E 1 =
    ∏ k : Fin 12, Product.progressionProduct 12 (k.val+1) := by
  rw [E, pow_one,
    qPochhammerInf_eq_prod_range (by decide : 12 ≠ 0) (by simp [q])]
  rw [Fin.prod_univ_eq_prod_range (fun k => Product.progressionProduct 12 (k+1)) 12]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Product.progressionProduct, ← pow_succ']

/-- All positive degrees are included by their twelve residue progressions. -/
theorem principalModeEulerDenominator_eq :
    principalModeEulerDenominator = (E 1)^2 * Product.principalHeisenbergEuler := by
  rw [E_one_split_twelve]
  norm_num [principalModeEulerDenominator, principalModeActiveSlotCount_eq,
    Fin.prod_univ_succ, IsMode, Product.principalHeisenbergEuler]
  ring

theorem principalModeEulerDenominator_eq_dualAffineDenominator :
    principalModeEulerDenominator = Product.dualAffineDenominator 1 1 1 := by
  rw [Product.dualAffineDenominator_111, principalModeEulerDenominator_eq]

/-- Finite progression blocks: each residue includes its first `N` positive modes. -/
noncomputable def principalModeEulerBlock (N : ℕ) : PowerSeries ℤ :=
  ∏ k : Fin 12, (qPochhammer (q^(k.val+1)) (q^12) N) ^ principalModeActiveSlotCount k

/-- The finite blocks converge in the coefficient topology to the exact denominator. -/
theorem principalModeEulerBlock_tendsto :
    Filter.Tendsto principalModeEulerBlock Filter.atTop
      (nhds (Product.dualAffineDenominator 1 1 1)) := by
  rw [← principalModeEulerDenominator_eq_dualAffineDenominator]
  unfold principalModeEulerBlock principalModeEulerDenominator Product.progressionProduct
  apply tendsto_finsetProd
  intro k hk
  exact (tendsto_qPochhammer_qPochhammerInf (a := q^(k.val+1))
    (q := q^12) (by simp [q])).pow _

end KanadeRussell.Representation
